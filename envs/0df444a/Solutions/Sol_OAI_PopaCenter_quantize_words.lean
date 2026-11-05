-- Prove2me | solution 1 for OAI.PopaCenter.quantize_words
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:54:05.181202+00:00
-- url     : https://prove2.me/submissions/9479bdcf-25f2-481f-910e-6ad5d2b8ff2a

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_PopaCenter_exists_dyadic_system
import Theorems.Thm_OAI_PopaCenter_full_center_lift_norm
import Theorems.Thm_OAI_PopaCenter_exists_matrix_energy_decrease_center

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace HochschildRigidity
open Finset

section FourierWindows
variable {L : ℕ} [NeZero L]

end FourierWindows

section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

lemma preGNS_norm_star (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _

open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
lemma sum_preGNS_norm_mul_sq (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (q : ι → A) (hq : ∑ j, q j * star (q j) = 1) (a : A) :
    ∑ j, ‖τ.toPreGNS (a * q j)‖ ^ 2 = ‖τ.toPreGNS a‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_mul]
  calc
    _ = ∑ j, τ ((star a * a) * (q j * star (q j))) := by
      apply sum_congr rfl
      intro j _
      simpa only [mul_assoc] using htr (star (q j)) ((star a * a) * q j)
    _ = τ ((star a * a) * ∑ j, q j * star (q j)) := by rw [mul_sum, map_sum]
    _ = _ := by rw [hq, mul_one]
end TraceHilbertSpace
end HochschildRigidity
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

lemma norm_trace_le (a : A) : ‖τ a‖ ≤ ‖τ.toPreGNS a‖ := by
  have hin : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS a) = τ a := by
    simp [PositiveLinearMap.preGNS_inner_def]
  rw [← hin]
  have hone : ‖τ.toPreGNS 1‖ = 1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [hone,one_mul] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS 1) (τ.toPreGNS a)
end HochschildUltrapower
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakSubspace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def preannihilator (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ X where
  carrier := {z | ∀ f ∈ S, f z=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy f hf; simp [map_add,hx f hf,hy f hf]
  smul_mem' := by intro c x hx f hf; simp [map_smul,hx f hf]

lemma preannihilator_closed (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := by
  change IsClosed {z | ∀ f, f ∈ S → f z=0}
  simpa only [Set.ofPred_forall,WeakDual.toStrongDual_apply] using
    (isClosed_iInter fun (f : WeakDual ℂ X) => isClosed_iInter fun (_ : f ∈ S) =>
      isClosed_eq (WeakDual.toStrongDual f).continuous (continuous_const (y := (0 : ℂ))))

lemma mem_iff_annihilates (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) (f : WeakDual ℂ X) :
    f ∈ S ↔ ∀ z ∈ preannihilator S, f z=0 := by
  let : IsScalarTower ℝ ℂ (WeakDual ℂ X) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ X))
  let hc : LocallyConvexSpace ℝ (WeakDual ℂ X) :=
    @WeakBilin.locallyConvexSpace ℂ (StrongDual ℂ X) X _ _ _ _ _ _ _ _ _
  constructor
  · intro hf z hz
    exact hz f hf
  · intro hf
    by_contra hnot
    obtain ⟨F,c,hFc,hcf⟩ := @RCLike.geometric_hahn_banach_closed_point ℂ (WeakDual ℂ X)
      _ _ _ (S : Set (WeakDual ℂ X)) f _ _ _ _ _ hc
      (S.restrictScalars ℝ).convex hS hnot
    have hzero (a : WeakDual ℂ X) (ha : a ∈ S) : F a=0 := by
      by_contra hne
      have hb := hFc ((((c+1 : ℝ) : ℂ) / F a) • a) (S.smul_mem _ ha)
      rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hne] at hb
      simp only [RCLike.re_to_complex,Complex.ofReal_re] at hb
      linarith
    obtain ⟨z,hz⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ X) F
    have heval (a : WeakDual ℂ X) : F a=a z := by
      rw [← hz]
      rfl
    have hmem : z ∈ preannihilator S := by
      intro a ha
      rw [← heval]
      exact hzero a ha
    have hf0 := hf z hmem
    have hc0 := hFc 0 S.zero_mem
    simp only [map_zero] at hc0
    rw [heval,hf0] at hcf
    simp only [RCLike.zero_re] at hcf
    linarith

def strong (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ (StrongDual ℂ X) :=
  S.map WeakDual.toStrongDual.toLinearMap

lemma mem_strong (S : Submodule ℂ (WeakDual ℂ X)) (f : StrongDual ℂ X) :
    f ∈ strong S ↔ StrongDual.toWeakDual f ∈ S := by
  constructor
  · rintro ⟨g,hg,hgf⟩
    change WeakDual.toStrongDual g=f at hgf
    rw [← hgf]
    exact hg
  · intro hf
    exact ⟨StrongDual.toWeakDual f,hf,rfl⟩

instance preannihilator_closed_instance (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := preannihilator_closed S

lemma quotient_dual_norm (K : Submodule ℂ X) [IsClosed (K : Set X)]
    (F : StrongDual ℂ (X ⧸ K)) : ‖F.comp K.mkQL‖=‖F‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (F.comp K.mkQL) (norm_nonneg F)
    intro x
    exact (F.le_opNorm (K.mkQL x)).trans
      (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le K x) (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro q
    apply le_of_forall_pos_le_add
    intro ε hε
    let C := ‖F.comp K.mkQL‖
    have hC : 0 ≤ C := norm_nonneg _
    obtain ⟨x,hx,hxn⟩ := Submodule.Quotient.norm_mk_lt q (show 0 < ε/(C+1) by positivity)
    have hb := (F.comp K.mkQL).le_opNorm x
    change ‖F (Submodule.Quotient.mk x)‖ ≤ C*‖x‖ at hb
    rw [hx] at hb
    have hd : C*(ε/(C+1)) ≤ ε := by
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      nlinarith
    calc
      ‖F q‖ ≤ C*‖x‖ := hb
      _ ≤ C*(‖q‖+ε/(C+1)) := mul_le_mul_of_nonneg_left hxn.le hC
      _ ≤ C*‖q‖+ε := by nlinarith

def quotientDual (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) →ₗᵢ[ℂ] strong S where
  toFun F := ⟨F.comp (preannihilator S).mkQL,by
    rw [mem_strong,mem_iff_annihilates S hS]
    intro z hz
    change F (Submodule.Quotient.mk z)=0
    rw [(Submodule.Quotient.mk_eq_zero (preannihilator S)).mpr hz,map_zero]⟩
  map_add' F G := by ext z; rfl
  map_smul' c F := by ext z; rfl
  norm_map' F := quotient_dual_norm (preannihilator S) F

lemma quotientDual_surjective (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    Function.Surjective (quotientDual S hS) := by
  intro f
  have hk : preannihilator S ≤ f.val.ker := by
    intro z hz
    exact hz (StrongDual.toWeakDual f.val) ((mem_strong S f.val).mp f.property)
  refine ⟨(preannihilator S).liftQL f.val hk,?_⟩
  apply Subtype.ext
  ext z
  rfl

def quotientDualEquiv (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) ≃ₗᵢ[ℂ] strong S :=
  { LinearEquiv.ofBijective (quotientDual S hS).toLinearMap
      ⟨by
        intro a b hab
        ext q
        obtain ⟨z,rfl⟩ := (preannihilator S).mkQ_surjective q
        exact congrArg (fun f : strong S => f.val z) hab,
       quotientDual_surjective S hS⟩ with
    norm_map' := (quotientDual S hS).norm_map }
end WeakSubspace
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

end HochschildSakai

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem exists_abstract_star_preadjoint :
    ∃ P : X →L⋆[ℂ] X, ‖P‖ ≤ 1 ∧
      ∀ a z, e.symm (star a) z=star (e.symm a (P z)) := by
  classical
  choose P hP using exists_star_predual_vector e
  have heq {x y : X} (h : ∀ a : M, e.symm a x=e.symm a y) : x=y := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro f
    simpa only [e.symm_apply_apply] using h (e f)
  have hPa (x y : X) : P (x+y)=P x+P y := by
    apply heq
    intro a
    apply star_injective
    rw [← hP (x+y) a,map_add,map_add,star_add,← hP x a,← hP y a]
  have hPs (r : ℂ) (x : X) : P (r • x)=star r • P x := by
    apply heq
    intro a
    apply star_injective
    rw [← hP (r • x) a,map_smul,map_smul,star_smul,star_star,← hP x a]
  let L : X →ₗ⋆[ℂ] X :=
    { toFun := P
      map_add' := hPa
      map_smul' := hPs }
  have hb (z : X) : ‖L z‖ ≤ 1*‖z‖ := by
    rw [one_mul]
    apply NormedSpace.norm_le_dual_bound ℂ _ (norm_nonneg _)
    intro f
    have hn := congrArg norm (hP z (e f))
    simp only [norm_star,e.symm_apply_apply] at hn
    change ‖f (P z)‖ ≤ ‖z‖*‖f‖
    rw [mul_comm ‖z‖]
    rw [← hn]
    simpa only [e.symm.norm_map,norm_star,e.norm_map] using
      (e.symm (star (e f))).le_opNorm z
  refine ⟨L.mkContinuous 1 hb,?_,fun a z => hP z a⟩
  exact LinearMap.mkContinuous_norm_le _ zero_le_one hb
end HochschildSakai
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end Hilbert

omit [StarOrderedRing M] in
lemma trace_conjugate (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (u : unitary M) (a : M) : τ (conjugate u a)=τ a := by
  rw [conjugate_apply,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]
end HochschildDixmier
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)

lemma projection_trace_pos (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) : 0 < (τ p).re := by
  have hpos : 0 ≤ τ p := τ.map_nonneg hp.nonneg
  have hre : 0 ≤ (τ p).re := Complex.nonneg_iff.mp hpos |>.1
  apply lt_of_le_of_ne hre
  intro hz
  have he : τ p=0 := Complex.ext hz.symm (Complex.nonneg_iff.mp hpos).2.symm
  apply hp0
  apply hfaith p
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using he
end HochschildDiffuse
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakEquiv : WeakDual ℂ X ≃ₗ⋆[ℂ] M :=
  WeakDual.toStrongDual.trans e.toLinearEquiv

lemma weakEquiv_symm_continuous : Continuous (weakEquiv e).symm :=
  NormedSpace.Dual.toWeakDual_continuous.comp e.symm.continuous

lemma normal_continuous (A : M →L[ℂ] M) (hA : HasPreadjoint e A) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (A (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  obtain ⟨w,hw⟩ := hA z
  change Continuous (fun f : WeakDual ℂ X => e.symm (A (weakEquiv e f)) z)
  simp_rw [hw]
  simpa [weakEquiv] using WeakDual.eval_continuous (𝕜 := ℂ) w

lemma star_continuous (P : X →L⋆[ℂ] X)
    (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (star (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  change Continuous (fun f : WeakDual ℂ X => e.symm (star (weakEquiv e f)) z)
  simp_rw [hP]
  simpa [weakEquiv] using (WeakDual.eval_continuous (𝕜 := ℂ) (P z)).star

def linearClosure (A : StarSubalgebra ℂ M) : Submodule ℂ (WeakDual ℂ X) :=
  (A.toSubalgebra.toSubmodule.map (weakEquiv e).symm.toLinearMap).topologicalClosure

lemma linearClosure_closed (A : StarSubalgebra ℂ M) :
    IsClosed (linearClosure e A : Set (WeakDual ℂ X)) :=
  Submodule.isClosed_topologicalClosure _

lemma mem_linearClosure (A : StarSubalgebra ℂ M) {a : M} (ha : a ∈ A) :
    (weakEquiv e).symm a ∈ linearClosure e A :=
  Submodule.le_topologicalClosure _ ⟨a,ha,rfl⟩

lemma closure_stable (A : StarSubalgebra ℂ M) (T : WeakDual ℂ X → WeakDual ℂ X)
    (hT : Continuous T)
    (h : ∀ a ∈ A, T ((weakEquiv e).symm a) ∈ linearClosure e A) :
    ∀ f ∈ linearClosure e A, T f ∈ linearClosure e A := by
  apply closure_minimal _ ((linearClosure_closed e A).preimage hT)
  rintro f ⟨a,ha,rfl⟩
  exact h a ha

lemma mul_mem (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    {a b : M} (ha : (weakEquiv e).symm a ∈ linearClosure e A)
    (hb : (weakEquiv e).symm b ∈ linearClosure e A) :
    (weakEquiv e).symm (a*b) ∈ linearClosure e A := by
  have hleft (c : M) (hc : c ∈ A) :
      (weakEquiv e).symm (c*b) ∈ linearClosure e A := by
    have hs := closure_stable e A _ (normal_continuous e _ (hL c))
      (fun d hd => by
        simpa using mem_linearClosure e A (A.mul_mem hc hd))
      ((weakEquiv e).symm b) hb
    simpa using hs
  have hs := closure_stable e A _ (normal_continuous e _ (hR b))
    (fun c hc => by simpa using hleft c hc) ((weakEquiv e).symm a) ha
  simpa using hs

lemma star_mem (A : StarSubalgebra ℂ M)
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
    {a : M} (ha : (weakEquiv e).symm a ∈ linearClosure e A) :
    (weakEquiv e).symm (star a) ∈ linearClosure e A := by
  have hs := closure_stable e A _ (star_continuous e P hP)
    (fun c hc => by simpa using mem_linearClosure e A (A.star_mem' hc))
    ((weakEquiv e).symm a) ha
  simpa using hs

def closure (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    StarSubalgebra ℂ M where
  carrier := {a | (weakEquiv e).symm a ∈ linearClosure e A}
  zero_mem' := by simp [map_zero]
  one_mem' := mem_linearClosure e A A.one_mem
  add_mem' := by intro a b ha hb; simpa using (linearClosure e A).add_mem ha hb
  mul_mem' := mul_mem e A hL hR
  algebraMap_mem' c := mem_linearClosure e A (A.algebraMap_mem c)
  star_mem' := star_mem e A P hP

instance closure_closed (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    IsClosed (closure e A hL hR P hP : Set M) :=
  (linearClosure_closed e A).preimage (weakEquiv_symm_continuous e)

variable (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

def strongEquiv : WeakSubspace.strong (linearClosure e A) ≃ₗᵢ⋆[ℂ]
    closure e A hL hR P hP where
  toFun f := ⟨e f.val, by
    change (weakEquiv e).symm (e f.val) ∈ linearClosure e A
    simpa [weakEquiv] using (WeakSubspace.mem_strong (linearClosure e A) f.val).mp f.property⟩
  invFun a := ⟨e.symm a.val, by
    rw [WeakSubspace.mem_strong]
    exact a.property⟩
  left_inv f := by apply Subtype.ext; exact e.symm_apply_apply f.val
  right_inv a := by apply Subtype.ext; exact e.apply_symm_apply a.val
  map_add' f g := by apply Subtype.ext; exact map_add e f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smulₛₗ c f.val
  norm_map' f := e.norm_map f.val

def predualEquiv :
    StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) ≃ₗᵢ⋆[ℂ]
      closure e A hL hR P hP :=
  (WeakSubspace.quotientDualEquiv (linearClosure e A) (linearClosure_closed e A)).trans
    (strongEquiv e A hL hR P hP)

instance closure_wstar [CompleteSpace X] : WStarAlgebra (closure e A hL hR P hP) :=
  ⟨⟨X ⧸ WeakSubspace.preannihilator (linearClosure e A),inferInstance,inferInstance,
    inferInstance,⟨predualEquiv e A hL hR P hP⟩⟩⟩

lemma predualEquiv_apply (F : StrongDual ℂ
      (X ⧸ WeakSubspace.preannihilator (linearClosure e A))) (z : X) :
    e.symm ((predualEquiv e A hL hR P hP F : closure e A hL hR P hP) : M) z=
      F (Submodule.Quotient.mk z) := by
  change e.symm (e (F.comp (WeakSubspace.preannihilator (linearClosure e A)).mkQL)) z=_
  rw [e.symm_apply_apply]
  rfl

lemma predualEquiv_symm_apply_mk (a : closure e A hL hR P hP) (z : X) :
    (predualEquiv e A hL hR P hP).symm a (Submodule.Quotient.mk z)=e.symm a.val z := by
  have hs := predualEquiv_apply e A hL hR P hP
    ((predualEquiv e A hL hR P hP).symm a) z
  rw [LinearIsometryEquiv.apply_symm_apply] at hs
  exact hs.symm

end WeakAlgebra
end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
open HochschildTraceNorm
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
  (hτ : TraceInPredual e τ)

end WeakAlgebra
end BoundedHochschild

namespace BoundedHochschild
open TopologicalSpace
variable {M : Type*}

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

instance closedSubalgebra_starOrderedRing (B : StarSubalgebra ℂ M)
    [IsClosed (B : Set M)] [StarOrderedRing M] : StarOrderedRing B := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ B := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

def inheritedTrace : closure e A hL hR P hP →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (closure e A hL hR P hP).subtype.toLinearMap
  monotone' := fun _ _ h => OrderHomClass.mono τ h

@[simp] lemma inheritedTrace_apply (a : closure e A hL hR P hP) :
    inheritedTrace e τ A hL hR P hP a=τ (a:M) := rfl

include hL hR P hP in
lemma inheritedTrace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (predualEquiv e A hL hR P hP) (inheritedTrace e τ A hL hR P hP) := by
  obtain ⟨z,hz⟩ := hτ
  refine ⟨Submodule.Quotient.mk z,fun a => ?_⟩
  rw [predualEquiv_symm_apply_mk]
  exact hz a.val

lemma inheritedTrace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (a : closure e A hL hR P hP)
    (ha : inheritedTrace e τ A hL hR P hP (star a*a)=0) : a=0 := by
  apply Subtype.ext
  exact hfaith a.val ha

lemma inheritedTrace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (a b : closure e A hL hR P hP) :
    inheritedTrace e τ A hL hR P hP (a*b)=inheritedTrace e τ A hL hR P hP (b*a) :=
  htr a.val b.val

lemma inheritedTrace_one (h1 : τ 1=1) : inheritedTrace e τ A hL hR P hP 1=1 := h1
end WeakAlgebra
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

def incl : algebra hp →⋆ₙₐ[ℂ] M where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma incl_apply (a : algebra hp) : incl hp a=(a:M) := rfl

end PopaCorner

namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_norm_le (x : M) : ‖compress hp x‖ ≤ ‖x‖ := by
  change ‖p*x*p‖ ≤ ‖x‖
  calc
    _ ≤ (‖p‖*‖x‖)*‖p‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg p))
    _ ≤ (1*‖x‖)*1 := mul_le_mul (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg x)) hp.norm_le
      (norm_nonneg p) (by positivity)
    _ = ‖x‖ := by ring
end PopaCorner

open Filter Topology
open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)

def weakSpace : Submodule ℂ (WeakDual ℂ X) :=
  (algebra hp).toNonUnitalSubalgebra.toSubmodule.comap (WeakAlgebra.weakEquiv e).toLinearMap

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakSpace_closed : IsClosed (weakSpace e hp : Set (WeakDual ℂ X)) := by
  have hL := WeakAlgebra.normal_continuous e (ContinuousLinearMap.mul ℂ M p)
    ((HochschildSakai.abstract_multiplication_normal e).1 p)
  have hR := WeakAlgebra.normal_continuous e ((ContinuousLinearMap.mul ℂ M).flip p)
    ((HochschildSakai.abstract_multiplication_normal e).2 p)
  have he : (weakSpace e hp : Set (WeakDual ℂ X)) =
      {f | (WeakAlgebra.weakEquiv e).symm (p*WeakAlgebra.weakEquiv e f)=f} ∩
      {f | (WeakAlgebra.weakEquiv e).symm (WeakAlgebra.weakEquiv e f*p)=f} := by
    ext f
    change (p*WeakAlgebra.weakEquiv e f=WeakAlgebra.weakEquiv e f ∧
      WeakAlgebra.weakEquiv e f*p=WeakAlgebra.weakEquiv e f) ↔ _
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,LinearEquiv.symm_apply_eq]
  rw [he]
  exact (isClosed_eq hL continuous_id).inter (isClosed_eq hR continuous_id)

def strongEquiv : WeakSubspace.strong (weakSpace e hp) ≃ₗᵢ⋆[ℂ] algebra hp where
  toFun f := ⟨e f.val,by
    have hh := (WeakSubspace.mem_strong (weakSpace e hp) f.val).mp f.property
    exact hh⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ algebra hp
    simp⟩
  left_inv f := by apply Subtype.ext; exact e.symm_apply_apply f.val
  right_inv a := by apply Subtype.ext; exact e.apply_symm_apply a.val
  map_add' f g := by apply Subtype.ext; exact map_add e f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smulₛₗ c f.val
  norm_map' f := e.norm_map f.val

def predualEquiv : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (weakSpace e hp)) ≃ₗᵢ⋆[ℂ] algebra hp :=
  (WeakSubspace.quotientDualEquiv (weakSpace e hp) (weakSpace_closed e hp)).trans
    (strongEquiv e hp)

omit [PartialOrder M] [StarOrderedRing M] in
lemma predualEquiv_symm_apply_mk (a : algebra hp) (z : X) :
    (predualEquiv e hp).symm a (Submodule.Quotient.mk z)=e.symm (a:M) z := by
  have hs : ∀ F : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (weakSpace e hp)),
      e.symm ((predualEquiv e hp F : algebra hp):M) z = F (Submodule.Quotient.mk z) := by
    intro F
    change e.symm (e (F.comp (WeakSubspace.preannihilator (weakSpace e hp)).mkQL)) z=_
    rw [e.symm_apply_apply]
    rfl
  have hh := hs ((predualEquiv e hp).symm a)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  exact hh.symm
end PopaCorner
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_star {a : M} (ha : Central a) : Central (star a) := by
  intro x
  change star a*x=x*star a
  have h := congrArg star (ha (star x)).eq
  simpa only [star_mul,star_star] using h.symm
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_sub {a b : M} (ha : Central a) (hb : Central b) : Central (a-b) :=
  fun x => (ha x).sub_left (hb x)
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_mul {a b : M} (ha : Central a) (hb : Central b) : Central (a*b) :=
  fun x => (ha x).mul_left (hb x)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma average_norm (a : M) : ‖average e τ hτ htr hfaith a‖ ≤ ‖a‖ :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.1
lemma average_central (a : M) : Central (average e τ hτ htr hfaith a) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.1
lemma average_orbit (a : M) :
    gnsVector τ (average e τ hτ htr hfaith a) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.2

variable (h1 : τ 1=1)
include htr in
omit [StarOrderedRing M] in
lemma central_pair_hull {z : M} (hz : Central z) (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      {b | τ (z*b)=τ (z*a)} := by
  apply convexHull_min
  · rintro _ ⟨v,rfl⟩
    change τ (z*conjugate v a)=τ (z*a)
    rw [conjugate_apply]
    have he : z*((v:M)*a*star (v:M))=(v:M)*(z*a)*star (v:M) := by
      calc
        _=(z*(v:M))*a*star (v:M) := by simp only [mul_assoc]
        _=((v:M)*z)*a*star (v:M) := by rw [(hz (v:M)).eq]
        _=_ := by simp only [mul_assoc]
    rw [he]
    exact trace_conjugate τ htr v (z*a)
  · intro x hx y hy r s _hr _hs hrs
    change τ (z*(r • x+s • y))=τ (z*a)
    rw [mul_add,mul_smul_comm,mul_smul_comm,map_add,τ.map_smul_of_tower,
      τ.map_smul_of_tower,hx,hy,←add_smul,hrs,one_smul]

include htr h1 in
lemma central_pair_closure {z : M} (hz : Central z) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) : τ (z*b)=τ (z*a) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have htc : ∀ n, τ (z*c n)=τ (z*a) := fun n => central_pair_hull τ htr hz a (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n-b)‖) atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [←hcy,←map_sub,gnsVector_norm] using hh
  have htt : Tendsto (fun n => ‖τ (z*(c n-b))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (HochschildUltrapower.norm_trace_le τ h1 _).trans
        (preGNS_norm_mul_le τ z _))
    simpa only [mul_zero] using ht.const_mul ‖z‖
  have he : ‖τ (z*a)-τ (z*b)‖=0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [mul_sub,map_sub,htc] using htt)
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

include h1
lemma average_pair {z : M} (hz : Central z) (a : M) :
    τ (z*average e τ hτ htr hfaith a)=τ (z*a) :=
  central_pair_closure τ htr h1 hz a _ (average_orbit e τ hτ htr hfaith a)

omit h1 in
include hfaith in
omit [StarOrderedRing M] in
lemma central_unique {b c : M} (hb : Central b) (hc : Central c)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*c)) : b=c := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,h _ (central_star (central_sub hb hc)),sub_self]

lemma average_eq (a b : M) (hb : Central b)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*a)) : average e τ hτ htr hfaith a=b := by
  apply central_unique τ hfaith (average_central e τ hτ htr hfaith a) hb
  intro z hz
  rw [average_pair e τ hτ htr hfaith h1 hz,h z hz]

lemma average_id {a : M} (ha : Central a) : average e τ hτ htr hfaith a=a :=
  average_eq e τ hτ htr hfaith h1 a a ha (fun _ _ => rfl)
lemma average_add (a b : M) : average e τ hτ htr hfaith (a+b)=
    average e τ hτ htr hfaith a+average e τ hτ htr hfaith b := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x
    exact (average_central e τ hτ htr hfaith a x).add_left
      (average_central e τ hτ htr hfaith b x)
  · intro z hz
    rw [mul_add,map_add,mul_add,map_add,average_pair e τ hτ htr hfaith h1 hz,
      average_pair e τ hτ htr hfaith h1 hz]
lemma average_smul (r : ℂ) (a : M) : average e τ hτ htr hfaith (r • a)=
    r • average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x; exact (average_central e τ hτ htr hfaith a x).smul_left r
  · intro z hz
    rw [mul_smul_comm,mul_smul_comm,map_smul,map_smul,average_pair e τ hτ htr hfaith h1 hz]

def expectation : M →L[ℂ] M := LinearMap.mkContinuous
  { toFun := average e τ hτ htr hfaith
    map_add' := average_add e τ hτ htr hfaith h1
    map_smul' := average_smul e τ hτ htr hfaith h1 }
  1 (by intro a; simpa using average_norm e τ hτ htr hfaith a)
@[simp] lemma expectation_apply (a : M) :
    expectation e τ hτ htr hfaith h1 a=average e τ hτ htr hfaith a := rfl

lemma average_bimodule {z : M} (hz : Central z) (a : M) :
    average e τ hτ htr hfaith (z*a)=z*average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · exact central_mul hz (average_central e τ hτ htr hfaith a)
  · intro w hw
    simpa only [←mul_assoc] using average_pair e τ hτ htr hfaith h1 (central_mul hw hz) a
lemma average_trace (a b : M) : average e τ hτ htr hfaith (a*b)=
    average e τ hτ htr hfaith (b*a) := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith _
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz,←mul_assoc,htr,←mul_assoc,
      ←(hz a).eq,mul_assoc]
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}
namespace System
variable (s : System n (1:M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_projection (i : Fin n) : IsStarProjection (s.entry i i) := by
  exact ⟨by simp only [IsIdempotentElem,s.mul_entry,↓reduceIte],
    by exact s.star_entry i i⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma entry_absorb_right (i j : Fin n) : s.entry i j*s.entry j j=s.entry i j := by
  simp only [s.mul_entry,↓reduceIte]

def commutant : StarSubalgebra ℂ M where
  carrier := {a | ∀ i j, Commute a (s.entry i j)}
  zero_mem' := fun _ _ => Commute.zero_left _
  one_mem' := fun _ _ => Commute.one_left _
  add_mem' := fun ha hb i j => (ha i j).add_left (hb i j)
  mul_mem' := fun ha hb i j => (ha i j).mul_left (hb i j)
  algebraMap_mem' := fun c i j => Algebra.commutes c (s.entry i j)
  star_mem' := by
    intro a ha i j
    change star a*s.entry i j=s.entry i j*star a
    have h := congrArg star (ha j i).eq
    simpa only [star_mul,s.star_entry] using h.symm

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mem_commutant (a : M) : a ∈ s.commutant ↔ ∀ i j, Commute a (s.entry i j) := Iff.rfl

def coordinate (x : M) (i j : Fin n) : M := ∑ k, s.entry k i*x*s.entry j k

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_commutes (x : M) (i j a b : Fin n) :
    Commute (s.coordinate x i j) (s.entry a b) := by
  classical
  change (∑ k, s.entry k i*x*s.entry j k)*s.entry a b =
    s.entry a b*(∑ k, s.entry k i*x*s.entry j k)
  simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc,s.mul_entry,mul_ite,mul_zero]
  simp only [← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_mem (x : M) (i j : Fin n) : s.coordinate x i j ∈ s.commutant :=
  s.coordinate_commutes x i j

omit [PartialOrder M] [StarOrderedRing M] in
lemma reconstruct (x : M) : ∑ i, ∑ j, s.entry i j*s.coordinate x i j=x := by
  classical
  have hh (i j : Fin n) : s.entry i j*s.coordinate x i j = s.entry i i*x*s.entry j j := by
    simp [coordinate,Finset.mul_sum,← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp_rw [hh]
  calc
    (∑ i, ∑ j, s.entry i i*x*s.entry j j) =
        (∑ i, s.entry i i)*x*(∑ j, s.entry j j) := by
          simp only [Finset.sum_mul,Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = x := by rw [s.sum_diag,one_mul,mul_one]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_in_commutant_is_central (b : M) (hb : b ∈ s.commutant)
    (hc : ∀ a ∈ s.commutant, Commute b a) (x : M) : Commute b x := by
  rw [← s.reconstruct x]
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (hb i j).mul_right (hc _ (s.coordinate_mem x i j))

omit [PartialOrder M] [StarOrderedRing M] in
lemma sumExpect_commutes (x : M) (a b : Fin n) : Commute (s.sumExpect x) (s.entry a b) := by
  classical
  change (∑ i, ∑ j, s.entry i j*x*s.entry j i)*s.entry a b =
    s.entry a b*(∑ i, ∑ j, s.entry i j*x*s.entry j i)
  simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc,s.mul_entry,mul_ite,mul_zero]
  simp only [← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_mem (x : M) : s.expect x ∈ s.commutant := by
  intro a b
  exact (s.sumExpect_commutes x a b).smul_left _

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_bimodule (a b x : M) (ha : a ∈ s.commutant) (hb : b ∈ s.commutant) :
    s.expect (a*x*b)=a*s.expect x*b := by
  simp only [expect,mul_smul_comm,smul_mul_assoc]
  congr 1
  simp only [sumExpect,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  calc
    s.entry i j*(a*x*b)*s.entry j i = a*s.entry i j*x*(b*s.entry j i) := by
      simp only [← mul_assoc]
      rw [← (ha i j).eq]
    _ = a*(s.entry i j*x*s.entry j i)*b := by rw [(hb j i).eq]; simp only [mul_assoc]

omit [StarOrderedRing M] in
lemma trace_sumExpect (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (x : M) :
    τ (s.sumExpect x)=(n : ℕ) • τ x := by
  classical
  calc
    τ (s.sumExpect x) = ∑ i : Fin n, ∑ j, τ (s.entry j j*x) := by
      simp only [sumExpect,map_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [htr,← mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = (n : ℕ) • τ x := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← map_sum,← Finset.sum_mul,s.sum_diag,one_mul]

omit [StarOrderedRing M] in
lemma trace_expect (hn : 0 < n) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (x : M) : τ (s.expect x)=τ x := by
  rw [expect,← Complex.coe_smul,map_smul,s.trace_sumExpect τ htr x,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hn0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,inv_mul_cancel₀ hn0,one_smul]

end System
end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include htr
omit [StarOrderedRing M] in
lemma expect_pairing (hn : 0 < n) (x a : M) (ha : a ∈ s.commutant) :
    τ (star a*s.expect x)=τ (star a*x) := by
  have he := s.expect_bimodule (star a) 1 x (s.commutant.star_mem' ha) s.commutant.one_mem
  simp only [mul_one] at he
  rw [← he,s.trace_expect hn τ htr]

lemma expect_orthogonal (hn : 0 < n) (x : M) :
    inner ℂ (τ.toPreGNS (s.expect x)) (τ.toPreGNS (x-s.expect x))=0 := by
  rw [PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,mul_sub,map_sub]
  rw [s.expect_pairing τ htr hn x _ (s.expect_mem x),sub_self]

lemma expect_pythagoras (hn : 0 < n) (x : M) :
    ‖τ.toPreGNS x‖^2 = ‖τ.toPreGNS (s.expect x)‖^2 + ‖τ.toPreGNS (x-s.expect x)‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (τ.toPreGNS (s.expect x)) (τ.toPreGNS (x-s.expect x)) (s.expect_orthogonal τ htr hn x)
  simpa only [← map_add,add_sub_cancel,pow_two] using h

lemma expect_norm_le (hn : 0 < n) (x : M) : ‖τ.toPreGNS (s.expect x)‖ ≤ ‖τ.toPreGNS x‖ := by
  have h := s.expect_pythagoras τ htr hn x
  nlinarith [sq_nonneg ‖τ.toPreGNS (x-s.expect x)‖,norm_nonneg (τ.toPreGNS x),
    norm_nonneg (τ.toPreGNS (s.expect x))]
end PopaMatrices.System
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

lemma norm_sq_eq_trace (a : M) : ‖τ.toPreGNS a‖^2=(τ (star a*a)).re := by
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re]
    using congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS a))

include htr in
omit [StarOrderedRing M] in
lemma trace_diagonal_mul (i j : Fin n) (a : M) (ha : a ∈ s.commutant) :
    τ (s.entry i i*a)=τ (s.entry j j*a) := by
  calc
    τ (s.entry i i*a) = τ (s.entry i j*(s.entry j i*a)) := by rw [← mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = τ ((s.entry j i*a)*s.entry i j) := htr _ _
    _ = τ (s.entry j j*a) := by rw [mul_assoc,(ha i j).eq,← mul_assoc,s.mul_entry,ite_eq_left rfl]

include htr in
omit [StarOrderedRing M] in
lemma trace_diagonal (i : Fin n) (a : M) (ha : a ∈ s.commutant) :
    (n:ℂ)*τ (s.entry i i*a)=τ a := by
  calc
    (n:ℂ)*τ (s.entry i i*a) = ∑ j : Fin n, τ (s.entry j j*a) := by
      simp only [← s.trace_diagonal_mul τ htr i _ a ha,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = τ a := by rw [← map_sum,← Finset.sum_mul,s.sum_diag,one_mul]

include htr in
lemma blocks_norm_sum (i0 : Fin n) (x : M) :
    (∑ i, ∑ j, ‖τ.toPreGNS (s.entry i0 i*x*s.entry j i0)‖^2)=‖τ.toPreGNS x‖^2 := by
  have hs : (∑ j, s.entry j i0*star (s.entry j i0))=1 := by
    simp only [s.star_entry,s.mul_entry,↓reduceIte,s.sum_diag]
  simp_rw [sum_preGNS_norm_mul_sq τ htr (fun j => s.entry j i0) hs]
  have hh := sum_preGNS_norm_mul_sq τ htr (fun i => s.entry i i0) hs (star x)
  simpa only [← preGNS_norm_star τ htr (star x*s.entry _ i0),star_mul,
    s.star_entry,star_star,preGNS_norm_star τ htr] using hh

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_sum_eq (i0 : Fin n) (x : M) :
    (∑ i, s.entry i0 i*x*s.entry i i0) = (n:ℝ) • (s.entry i0 i0*s.expect x) := by
  classical
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  simp only [expect,mul_smul_comm,smul_smul,mul_inv_cancel₀ hn,one_smul,sumExpect,Finset.mul_sum]
  simp only [← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp

include htr in
lemma diagonal_sum_norm (i0 : Fin n) (x : M) :
    ‖τ.toPreGNS (∑ i, s.entry i0 i*x*s.entry i i0)‖^2=
      (n:ℝ)*‖τ.toPreGNS (s.expect x)‖^2 := by
  let b := s.expect x
  have hb : b ∈ s.commutant := s.expect_mem x
  have htrace := congrArg Complex.re (s.trace_diagonal τ htr i0 (star b*b)
    (s.commutant.mul_mem (s.commutant.star_mem' hb) hb))
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at htrace
  rw [s.diagonal_sum_eq]
  rw [← Complex.coe_smul,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg n),mul_pow,norm_sq_eq_trace]
  have he : star (s.entry i0 i0*b)*(s.entry i0 i0*b)=s.entry i0 i0*(star b*b) := by
    rw [star_mul,s.star_entry,mul_assoc,← mul_assoc (s.entry i0 i0),s.mul_entry,ite_eq_left rfl]
    rw [← mul_assoc,(s.commutant.star_mem' hb i0 i0).eq,mul_assoc]
  change (n:ℝ)^2*(τ (star (s.entry i0 i0*b)*(s.entry i0 i0*b))).re = _
  rw [he,norm_sq_eq_trace]
  change (n:ℝ)^2*(τ (s.entry i0 i0*(star b*b))).re=(n:ℝ)*(τ (star b*b)).re
  rw [← htrace]
  ring
end PopaMatrices.System

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma average_diagonal_mul {n : ℕ} (s : System n (1:M)) (i j : Fin n)
    (a : M) (ha : a ∈ s.commutant) :
    average e τ hτ htr hfaith (s.entry i i*a)=average e τ hτ htr hfaith (s.entry j j*a) := by
  calc
    _ = average e τ hτ htr hfaith (s.entry i j*(s.entry j i*a)) := by
      rw [←mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = average e τ hτ htr hfaith ((s.entry j i*a)*s.entry i j) := average_trace e τ hτ htr hfaith h1 _ _
    _ = _ := by rw [mul_assoc,(ha i j).eq,←mul_assoc,s.mul_entry,ite_eq_left rfl]

include h1 in
lemma average_diagonal {n : ℕ} (s : System n (1:M)) (i : Fin n)
    (a : M) (ha : a ∈ s.commutant) :
    (n:ℝ) • average e τ hτ htr hfaith (s.entry i i*a)=average e τ hτ htr hfaith a := by
  calc
    _ = ∑ j : Fin n, average e τ hτ htr hfaith (s.entry j j*a) := by
      simp only [←average_diagonal_mul e τ hτ htr hfaith h1 s i _ a ha,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
    _ = _ := by
      change (∑ j, expectation e τ hτ htr hfaith h1 (s.entry j j*a))=expectation e τ hτ htr hfaith h1 a
      rw [←map_sum,←Finset.sum_mul,s.sum_diag,one_mul]

include h1 in
lemma average_diagonal_one {n : ℕ} (s : System n (1:M)) (i : Fin n) :
    (n:ℝ) • average e τ hτ htr hfaith (s.entry i i)=1 := by
  simpa only [mul_one,average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x)] using
    average_diagonal e τ hτ htr hfaith h1 s i 1 s.commutant.one_mem
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {p : M} (hp : IsStarProjection p) (τ : M →ₚ[ℂ] ℂ)

lemma trace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    ∀ a : algebra hp, trace hp τ (star a*a)=0 → a=0 := by
  intro a ha
  by_cases hp0 : p=0
  · apply Subtype.ext
    change (a:M)=0
    have hh := a.property.1
    simpa only [hp0,zero_mul] using hh.symm
  · have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
    apply Subtype.ext
    apply hfaith
    change (((τ p).re⁻¹ : ℝ) : ℂ)*τ (star (a:M)*(a:M))=0 at ha
    exact (mul_eq_zero.mp ha).resolve_left (by exact_mod_cast inv_ne_zero ht.ne')

lemma trace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a)) :
    ∀ a b : algebra hp, trace hp τ (a*b)=trace hp τ (b*a) := by
  intro a b
  exact congrArg (fun z => (((τ p).re⁻¹ : ℝ) : ℂ)*z) (htr a.val b.val)

lemma trace_one (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0) :
    trace hp τ 1=1 := by
  rw [trace_apply,coe_one]
  have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
  have hi := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2
  have he : τ p=((τ p).re : ℂ) := by apply Complex.ext <;> simp [hi]
  conv_lhs => rhs; rw [he]
  rw [←Complex.ofReal_mul,inv_mul_cancel₀ ht.ne',Complex.ofReal_one]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
lemma trace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (predualEquiv e hp) (trace hp τ) := by
  obtain ⟨z,hz⟩ := hτ
  refine ⟨(((τ p).re⁻¹ : ℝ) : ℂ) • (Submodule.Quotient.mk z),fun a => ?_⟩
  rw [map_smul,predualEquiv_symm_apply_mk,trace_apply,hz a.val]
  simp [smul_eq_mul]

end PopaCorner

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

section Dual
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end Dual
end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII PopaMatrices PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma corner_typeII (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p) :
    NoAbelianCorners (algebra hp) := by
  intro q hq hq0
  have hqM : IsStarProjection (q:M) := hq.map (incl hp)
  obtain ⟨x,y,hxy⟩ := hII (q:M) hqM (fun he => hq0 (Subtype.ext he))
  let L (z : algebra hqM) : algebra hp := ⟨z,by
    calc p*(z:M)=p*((q:M)*(z:M)) := by rw [z.property.1]
         _=(p*(q:M))*(z:M) := (mul_assoc _ _ _).symm
         _=(z:M) := by rw [q.property.1,z.property.1],by
    calc (z:M)*p=((z:M)*(q:M))*p := by rw [z.property.2]
         _=(z:M)*((q:M)*p) := mul_assoc _ _ _
         _=(z:M) := by rw [q.property.2,z.property.2]⟩
  let K (z : algebra hqM) : algebra hq := ⟨L z,Subtype.ext z.property.1,Subtype.ext z.property.2⟩
  refine ⟨K x,K y,fun hh => hxy ?_⟩
  apply Subtype.ext
  exact congrArg (fun z : algebra hq => ((z:algebra hp):M)) hh.eq

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def centerAlgebra : StarSubalgebra ℂ M where
  carrier := {a | Central a}
  zero_mem' := fun x => Commute.zero_left x
  one_mem' := fun x => Commute.one_left x
  add_mem' ha hb := fun x => (ha x).add_left (hb x)
  mul_mem' ha hb := central_mul ha hb
  algebraMap_mem' r := fun x => Algebra.commutes r x
  star_mem' ha := central_star ha

instance centerAlgebra_closed : IsClosed (centerAlgebra (M:=M) : Set M) := by
  change IsClosed {a : M | ∀ x : M, a*x=x*a}
  simpa only [Set.ofPred_forall,id_eq,Pi.mul_apply] using isClosed_iInter (fun x : M => isClosed_eq
    ((continuous_id : Continuous (fun a : M => a)).mul_const x)
    ((continuous_const : Continuous (fun _ : M => x)).mul continuous_id))

def centerCompression {p : M} (hp : IsStarProjection p) :
    centerAlgebra (M:=M) →⋆ₐ[ℂ] algebra hp where
  toFun a := ⟨(a:M)*p,by
    constructor
    · rw [←mul_assoc,←(a.property p).eq,mul_assoc,hp.isIdempotentElem.eq]
    · rw [mul_assoc,hp.isIdempotentElem.eq]⟩
  map_one' := Subtype.ext (one_mul p)
  map_mul' a b := Subtype.ext (by
    change ((a:M)*(b:M))*p=((a:M)*p)*((b:M)*p)
    rw [mul_assoc (a:M) p,←mul_assoc p,←(b.property p).eq,mul_assoc (b:M),hp.isIdempotentElem.eq,mul_assoc])
  map_zero' := Subtype.ext (zero_mul p)
  map_add' a b := Subtype.ext (add_mul (a:M) (b:M) p)
  commutes' r := Subtype.ext (by change (algebraMap ℂ M r)*p=r • p; simp [Algebra.algebraMap_eq_smul_one])
  map_star' a := Subtype.ext (by
    change star (a:M)*p=star ((a:M)*p)
    rw [star_mul,hp.isSelfAdjoint.star_eq]
    exact (central_star a.property p).eq)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def cornerAverage {p : M} (hp : IsStarProjection p) (a : algebra hp) : algebra hp :=
  average (predualEquiv e hp) (trace hp τ) (trace_normal hp τ e hτ)
    (trace_tracial hp τ htr) (trace_faithful hp τ hfaith) a

lemma cornerAverage_central {p : M} (hp : IsStarProjection p) (a : algebra hp) :
    Central (cornerAverage e τ hτ htr hfaith hp a) :=
  average_central _ _ _ _ _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_corner {p : M} (hp : IsStarProjection p) {z : M} (hz : Central z) :
    Central (centerCompression hp ⟨z,hz⟩) := by
  intro x
  apply Subtype.ext
  change (z*p)*(x:M)=(x:M)*(z*p)
  calc
    (z*p)*(x:M)=z*(x:M) := by rw [mul_assoc,x.property.1]
    _=(x:M)*z := (hz (x:M)).eq
    _=(x:M)*(z*p) := by rw [(hz p).eq,←mul_assoc,x.property.2]

include h1 in
lemma average_cornerAverage {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (a : algebra hp) :
    average e τ hτ htr hfaith (cornerAverage e τ hτ htr hfaith hp a : M)=
      average e τ hτ htr hfaith (a:M) := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith _
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz]
    have hh := average_pair (predualEquiv e hp) (trace hp τ) (trace_normal hp τ e hτ)
      (trace_tracial hp τ htr) (trace_faithful hp τ hfaith) (trace_one hp τ hfaith hp0)
      (central_corner hp hz) a
    have hzmul (b : algebra hp) : ((centerCompression hp ⟨z,hz⟩*b : algebra hp):M)=z*(b:M) := by
      change (z*p)*(b:M)=z*(b:M)
      rw [mul_assoc,b.property.1]
    simp only [trace_apply,hzmul] at hh
    have ht : (((τ p).re⁻¹:ℝ):ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'
    exact (mul_left_cancel₀ ht hh).symm

include h1 in
lemma cornerAverage_lift (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) {t : ℝ} (ht : 0<t)
    (hEp : average e τ hτ htr hfaith p=t • (1:M)) (a : algebra hp) :
    ∃ c : M, Central c ∧ c*p=(cornerAverage e τ hτ htr hfaith hp a:M) ∧
      ‖c‖≤‖a‖ ∧ average e τ hτ htr hfaith (a:M)=t • c := by
  obtain ⟨c,hc,hcp,hcn⟩ := full_center_lift_norm e τ hτ htr hfaith h1 hII hp ht hEp
    (cornerAverage e τ hτ htr hfaith hp a) (cornerAverage_central e τ hτ htr hfaith hp a)
  refine ⟨c,hc,hcp,?_,?_⟩
  · rw [hcn]
    exact average_norm _ _ _ _ _ a
  · rw [←average_cornerAverage e τ hτ htr hfaith h1 hp hp0 a,←hcp,
      average_bimodule e τ hτ htr hfaith h1 hc,hEp,mul_smul_comm,mul_one]

include h1 in
lemma average_corner_rank {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (q : algebra hp) {r : ℝ} (hq : cornerAverage e τ hτ htr hfaith hp q=r • (1:algebra hp)) :
    average e τ hτ htr hfaith (q:M)=r • average e τ hτ htr hfaith p := by
  rw [←average_cornerAverage e τ hτ htr hfaith h1 hp hp0 q,hq]
  change expectation e τ hτ htr hfaith h1 (r • p)=r • expectation e τ hτ htr hfaith h1 p
  exact (expectation e τ hτ htr hfaith h1).map_smul_of_tower r p
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators
namespace PopaQuantization

def sign (b : Bool) : ℝ := if b then -1 else 1
@[simp] lemma sign_sq (b : Bool) : sign b * sign b=1 := by cases b <;> norm_num [sign]
@[simp] lemma sign_sum : ∑ b : Bool, sign b=0 := by norm_num [sign]

variable {n : ℕ}
def character (s : Finset (Fin n)) (a : Fin n → Bool) : ℝ :=
  ∏ i, if i∈s then sign (a i) else 1

lemma character_empty (a : Fin n → Bool) : character ∅ a=1 := by simp [character]

lemma character_eq_prod (s : Finset (Fin n)) (a : Fin n → Bool) :
    character s a=∏ i∈s, sign (a i) := by
  classical
  calc
    character s a = ∏ i∈s, if i∈s then sign (a i) else 1 := by
      apply (Finset.prod_subset (Finset.subset_univ s) ?_).symm
      intro i _ hi
      exact ite_eq_right hi
    _ = _ := Finset.prod_congr rfl (fun i hi => ite_eq_left hi)
lemma character_pair (i j : Fin n) (hij : i ≠ j) (a : Fin n → Bool) :
    character {i,j} a=sign (a i)*sign (a j) := by
  classical
  rw [character_eq_prod,Finset.prod_pair hij]

lemma character_orthogonal (s t : Finset (Fin n)) :
    (∑ a : Fin n → Bool, character s a*character t a)=
      if s=t then (2:ℝ)^n else 0 := by
  classical
  have he : (∑ a : Fin n → Bool, character s a*character t a)=
      ∏ i : Fin n, (∑ b : Bool, (if i∈s then sign b else 1)*(if i∈t then sign b else 1)) := by
    simp only [character,← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i (b : Bool) =>
      (if i∈s then sign b else 1)*(if i∈t then sign b else 1))).symm
  rw [he]
  by_cases h : s=t
  · subst t
    simp only [ite_true]
    have hi (i : Fin n) : (∑ b : Bool, (if i∈s then sign b else 1)*(if i∈s then sign b else 1))=2 := by
      by_cases h : i∈s <;> norm_num [h,sign]
    simp only [hi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp (Finset.ext_iff.not.mp h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i∈s <;> by_cases ht : i∈t <;> simp_all [sign]

variable {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

lemma signed_norm_sq (l : ι → Finset (Fin n)) (v : ι → E) (a : Fin n → Bool) :
    ‖∑ i, character (l i) a • v i‖^2=
      ∑ i, ∑ j, (character (l i) a*character (l j) a)*inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [sum_inner]
  simp only [inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma character_mean_square (l : ι → Finset (Fin n)) (hl : Function.Injective l) (v : ι → E) :
    (∑ a : Fin n → Bool, ‖∑ i, character (l i) a • v i‖^2)=
      (2:ℝ)^n*∑ i, ‖v i‖^2 := by
  classical
  simp_rw [signed_norm_sq]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Bool)))]
  simp_rw [← Finset.sum_mul,character_orthogonal,hl.eq_iff]
  simp [ite_mul,← Finset.mul_sum]
end PopaQuantization

open scoped BigOperators
namespace PopaQuantization

abbrev UpperPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def pairLabel {n : ℕ} (p : Option (UpperPair n)) : Finset (Fin n) :=
  match p with
  | none => ∅
  | some p => {p.val.1,p.val.2}

lemma pairLabel_injective {n : ℕ} : Function.Injective (@pairLabel n) := by
  classical
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hh : b.val.1 ∈ pairLabel none := by rw [h]; simp [pairLabel]
      simp [pairLabel] at hh
  | some a =>
    cases b with
    | none => simp [pairLabel] at h
    | some b =>
      have hs := congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
      simp only [pairLabel,Finset.coe_pair,Set.pair_eq_pair_iff] at hs
      rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact congrArg some (Subtype.ext (Prod.ext h1 h2))
      · have ha := a.property
        have hb := b.property
        omega

lemma sum_diagonal_upper {n : ℕ} {E : Type*} [AddCommMonoid E] (x : Fin n → Fin n → E) :
    (∑ i, ∑ j, x i j)=(∑ i, x i i)+∑ p : UpperPair n, (x p.val.1 p.val.2+x p.val.2 p.val.1) := by
  classical
  have hsub (f : Fin n → Fin n → E) :
      (∑ p : UpperPair n, f p.val.1 p.val.2)=
        ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by
    rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => if p.1 < p.2 then f p.1 p.2 else 0)]
    simpa [Finset.sum_filter] using (Finset.sum_subtype
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (by intro p; simp) (fun p => f p.1 p.2)).symm
  have he (i j : Fin n) : x i j=(if i=j then x i j else 0)+
      (if i < j then x i j else 0)+(if j < i then x i j else 0) := by
    rcases lt_trichotomy i j with h | h | h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]
  calc
    (∑ i, ∑ j, x i j) = ∑ i, ∑ j,
        ((if i=j then x i j else 0)+(if i < j then x i j else 0)+(if j < i then x i j else 0)) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact he i j
    _ = (∑ i, x i i)+(∑ i, ∑ j, if i < j then x i j else 0)+
        (∑ i, ∑ j, if i < j then x j i else 0) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then x i j else 0)]
      simp
    _ = _ := by
      rw [Finset.sum_add_distrib, hsub (fun i j => x i j), hsub (fun i j => x j i)]
      abel

variable {n : ℕ} {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairCoefficients (x : Fin n → Fin n → E) (p : Option (UpperPair n)) : E :=
  match p with
  | none => ∑ i, x i i
  | some p => x p.val.1 p.val.2+x p.val.2 p.val.1

lemma quadratic_expansion (x : Fin n → Fin n → E) (a : Fin n → Bool) :
    (∑ i, ∑ j, (sign (a i)*sign (a j)) • x i j)=
      ∑ p : Option (UpperPair n), character (pairLabel p) a • pairCoefficients x p := by
  classical
  rw [sum_diagonal_upper,Fintype.sum_option]
  simp only [pairLabel,pairCoefficients,character_empty,one_smul,sign_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [character_pair _ _ (ne_of_lt p.property),smul_add]
  rw [mul_comm (sign (a p.val.2))]

theorem quadratic_mean_square_bound (x : Fin n → Fin n → E) :
    (∑ a : Fin n → Bool, ‖∑ i, ∑ j, (sign (a i)*sign (a j)) • x i j‖^2) ≤
      (2:ℝ)^n*(‖∑ i, x i i‖^2+2*∑ i, ∑ j, ‖x i j‖^2) := by
  classical
  simp_rw [quadratic_expansion]
  rw [character_mean_square _ pairLabel_injective,Fintype.sum_option]
  simp only [pairCoefficients]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  have hpair (p : UpperPair n) : ‖x p.val.1 p.val.2+x p.val.2 p.val.1‖^2 ≤
      2*(‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) := by
    have hh := norm_add_le (x p.val.1 p.val.2) (x p.val.2 p.val.1)
    nlinarith [norm_nonneg (x p.val.1 p.val.2+x p.val.2 p.val.1),
      norm_nonneg (x p.val.1 p.val.2),norm_nonneg (x p.val.2 p.val.1),
      sq_nonneg (‖x p.val.1 p.val.2‖-‖x p.val.2 p.val.1‖)]
  calc
    (∑ p : UpperPair n, ‖x p.val.1 p.val.2+x p.val.2 p.val.1‖^2) ≤
      ∑ p : UpperPair n, 2*(‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) :=
        Finset.sum_le_sum (fun p _ => hpair p)
    _ = 2*∑ p : UpperPair n, (‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      rw [sum_diagonal_upper (fun i j => ‖x i j‖^2)]
      have hh : 0 ≤ ∑ i : Fin n, ‖x i i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
end PopaQuantization
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity PopaQuantization
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))

def flatColumn (i0 : Fin n) (a : Fin n → Bool) : M :=
  (Real.sqrt (n:ℝ))⁻¹ • ∑ i, sign (a i) • s.entry i i0

def flatProjection (i0 : Fin n) (a : Fin n → Bool) : M :=
  s.flatColumn i0 a*star (s.flatColumn i0 a)

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatColumn_source (i0 : Fin n) (a : Fin n → Bool) :
    s.flatColumn i0 a*s.entry i0 i0=s.flatColumn i0 a := by
  simp only [flatColumn,smul_mul_assoc,Finset.sum_mul,s.mul_entry,↓reduceIte]

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatColumn_star_mul (i0 : Fin n) (a : Fin n → Bool) :
    star (s.flatColumn i0 a)*s.flatColumn i0 a=s.entry i0 i0 := by
  classical
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  have hs : (Real.sqrt (n:ℝ))⁻¹*(Real.sqrt (n:ℝ))⁻¹*(n:ℝ)=1 := by
    rw [← mul_inv,Real.mul_self_sqrt (Nat.cast_nonneg n),inv_mul_cancel₀ hn]
  have hw : star (∑ i, sign (a i) • s.entry i i0)*(∑ i, sign (a i) • s.entry i i0)=
      (n:ℝ) • s.entry i0 i0 := by
    simp only [star_sum,star_smul,star_trivial,s.star_entry,Finset.sum_mul,
      Finset.mul_sum,smul_mul_assoc,mul_smul_comm,s.mul_entry]
    simp only [smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,smul_smul,sign_sq,one_smul]
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
  rw [flatColumn,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,hw,
    smul_smul,smul_smul,hs,one_smul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatProjection_projection (i0 : Fin n) (a : Fin n → Bool) :
    IsStarProjection (s.flatProjection i0 a) := by
  refine ⟨?_,?_⟩
  · change (s.flatColumn i0 a*star (s.flatColumn i0 a))*(s.flatColumn i0 a*star (s.flatColumn i0 a))=_
    rw [mul_assoc,← mul_assoc (star _),s.flatColumn_star_mul,← mul_assoc,s.flatColumn_source]
    rfl
  · change star (s.flatColumn i0 a*star (s.flatColumn i0 a))=_
    simp only [star_mul,star_star]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatColumn_compression (i0 : Fin n) (a : Fin n → Bool) (x : M) :
    star (s.flatColumn i0 a)*x*s.flatColumn i0 a=
      (n:ℝ)⁻¹ • ∑ i, ∑ j, (sign (a i)*sign (a j)) • (s.entry i0 i*x*s.entry j i0) := by
  have hw : star (∑ i, sign (a i) • s.entry i i0)*x*(∑ i, sign (a i) • s.entry i i0)=
      ∑ i, ∑ j, (sign (a i)*sign (a j)) • (s.entry i0 i*x*s.entry j i0) := by
    simp only [star_sum,star_smul,star_trivial,s.star_entry]
    rw [Finset.sum_mul,Finset.sum_mul]
    simp only [Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm]
  rw [flatColumn,star_smul,star_trivial,smul_mul_assoc,smul_mul_assoc,
    mul_smul_comm,hw,smul_smul,← mul_inv,Real.mul_self_sqrt (Nat.cast_nonneg n)]

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr
omit [StarOrderedRing M] in
lemma flatProjection_trace (h1 : τ 1=1) (i0 : Fin n) (a : Fin n → Bool) :
    τ (s.flatProjection i0 a)=(n:ℂ)⁻¹ := by
  rw [flatProjection,htr,s.flatColumn_star_mul]
  have hh := s.trace_diagonal τ htr i0 1 s.commutant.one_mem
  simp only [mul_one,h1] at hh
  have hn : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  apply mul_left_cancel₀ hn
  rw [hh,mul_inv_cancel₀ hn]

lemma flatProjection_compression_norm (i0 : Fin n) (a : Fin n → Bool) (x : M) :
    ‖τ.toPreGNS (s.flatProjection i0 a*x*s.flatProjection i0 a)‖=
      ‖τ.toPreGNS (star (s.flatColumn i0 a)*x*s.flatColumn i0 a)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_trace,norm_sq_eq_trace]
  congr 1
  let v := s.flatColumn i0 a
  let p := s.entry i0 i0
  have hv : star v*v=p := s.flatColumn_star_mul i0 a
  have hvp : v*p=v := s.flatColumn_source i0 a
  have hpv : p*star v=star v := by
    have hh := congrArg star hvp
    have hp : star p=p := s.star_entry i0 i0
    simpa only [star_mul,hp] using hh
  change τ (star ((v*star v)*x*(v*star v))*((v*star v)*x*(v*star v)))=
    τ (star (star v*x*v)*(star v*x*v))
  simp only [star_mul,star_star,mul_assoc]
  calc
    _ = τ (v*(star v*(star x*(v*(star v*(v*(star v*(x*(v*star v))))))))) := rfl
    _ = τ (v*(star v*(star x*(v*(p*(star v*(x*(v*star v)))))))) := by rw [← mul_assoc (star v) v,hv]
    _ = τ (v*(star v*(star x*(v*(star v*(x*(v*star v))))))) := by rw [← mul_assoc p (star v),hpv]
    _ = τ (star v*(v*(star v*(star x*(v*(star v*(x*v))))))) := by
      simpa only [mul_assoc] using htr (v*(star v*(star x*(v*(star v*(x*v)))))) (star v)
    _ = τ (star v*(star x*(v*(star v*(x*v))))) := by rw [← mul_assoc (star v) v,hv,← mul_assoc p (star v),hpv]
    _ = _ := rfl
end PopaMatrices.System
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaQuantization
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaQuantization

open scoped ComplexOrder
namespace PopaMatrices.System
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n m : ℕ} (s : PopaMatrices.System n (1:M)) (t : PopaMatrices.System m (1:M))
variable (hc : ∀ i j a b, Commute (s.entry i j) (t.entry a b))

lemma sum_product_index {E : Type*} [AddCommMonoid E] (f : Fin (n*m) → E) :
    ∑ i, f i=∑ i : Fin n, ∑ a : Fin m, f (finProdFinEquiv (i,a)) := by
  exact (Fintype.sum_equiv finProdFinEquiv.symm f (fun z => f (finProdFinEquiv z))
    (fun i => (congrArg f (finProdFinEquiv.apply_symm_apply i)).symm)).trans (Fintype.sum_prod_type _)

def tensor : PopaMatrices.System (n*m) (1:M) where
  entry i j := s.entry (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
    t.entry (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
  star_entry i j := by
    simp only [star_mul,s.star_entry,t.star_entry]
    exact (hc _ _ _ _).eq.symm
  mul_entry i j k l := by
    classical
    let a := finProdFinEquiv.symm j
    let b := finProdFinEquiv.symm k
    have he : (j=k) ↔ (a.1=b.1 ∧ a.2=b.2) := by
      rw [← Prod.ext_iff]
      exact finProdFinEquiv.symm.injective.eq_iff.symm
    have hh : (s.entry (finProdFinEquiv.symm i).1 a.1 *
        t.entry (finProdFinEquiv.symm i).2 a.2) *
        (s.entry b.1 (finProdFinEquiv.symm l).1 * t.entry b.2 (finProdFinEquiv.symm l).2) =
        (s.entry (finProdFinEquiv.symm i).1 a.1 * s.entry b.1 (finProdFinEquiv.symm l).1)*
        (t.entry (finProdFinEquiv.symm i).2 a.2 * t.entry b.2 (finProdFinEquiv.symm l).2) := by
      simp only [mul_assoc]
      rw [← mul_assoc (t.entry _ _),← (hc _ _ _ _).eq,mul_assoc]
    rw [hh,s.mul_entry,t.mul_entry]
    by_cases ha : a.1=b.1 <;> by_cases hb : a.2=b.2 <;> simp [ha,hb,he]
  sum_diag := by
    rw [sum_product_index]
    simp only [Equiv.symm_apply_apply]
    simp_rw [← Finset.mul_sum,t.sum_diag,mul_one]
    exact s.sum_diag

omit [PartialOrder M] [StarOrderedRing M] in
lemma tensor_entry (i j : Fin n) (a b : Fin m) :
    (s.tensor t hc).entry (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) =
      s.entry i j*t.entry a b := by
  change s.entry (finProdFinEquiv.symm (finProdFinEquiv (i,a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (j,b))).1 *
    t.entry (finProdFinEquiv.symm (finProdFinEquiv (i,a))).2
    (finProdFinEquiv.symm (finProdFinEquiv (j,b))).2 = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma tensor_sumExpect (x : M) : (s.tensor t hc).sumExpect x=s.sumExpect (t.sumExpect x) := by
  rw [sumExpect,sum_product_index]
  simp_rw [sum_product_index,(s.tensor_entry t hc)]
  simp only [sumExpect,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_assoc]
  rw [(hc j i b a).eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma tensor_expect (x : M) : (s.tensor t hc).expect x=s.expect (t.expect x) := by
  unfold expect
  rw [tensor_sumExpect]
  simp only [sumExpect,mul_smul_comm,smul_mul_assoc,
    ← Finset.smul_sum,smul_smul,Nat.cast_mul,mul_inv_rev]
  rw [mul_comm]
end PopaMatrices.System

open scoped ComplexOrder
namespace PopaMatrices
open HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}
namespace System
variable (s : System n (1:M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma left_mul_coordinate (x : M) (i j a b : Fin n) :
    s.entry a b*s.coordinate x i j = s.entry a i*x*s.entry j b := by
  classical
  simp [coordinate,Finset.mul_sum,← mul_assoc,s.mul_entry,ite_mul,zero_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_zero (i : Fin n) : s.coordinate 0 i i=0 := by
  simp only [coordinate,mul_zero,zero_mul,Finset.sum_const_zero]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_mul {x y : M} (i : Fin n) (hxi : x*s.entry i i=x) :
    s.coordinate (x*y) i i=s.coordinate x i i*s.coordinate y i i := by
  classical
  have hterm (k l : Fin n) : (s.entry k i*x*s.entry i k)*(s.entry l i*y*s.entry i l)=
      if k=l then s.entry k i*(x*y)*s.entry i k else 0 := by
    calc
      _ = s.entry k i*(x*(s.entry i k*s.entry l i))*y*s.entry i l := by
        simp only [mul_assoc]
      _ = _ := by
        by_cases h : k=l
        · subst l
          simp only [s.mul_entry,↓reduceIte,hxi,mul_assoc]
        · simp only [s.mul_entry,ite_eq_right h,mul_zero,zero_mul]
  simp only [coordinate,Finset.sum_mul,Finset.mul_sum,hterm]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma extract_coordinate {x : M} (i : Fin n)
    (hix : s.entry i i*x=x) (hxi : x*s.entry i i=x) :
    s.entry i i*s.coordinate x i i=x := by
  rw [s.left_mul_coordinate,hix,hxi]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_of_commutes (x : M) (hx : x ∈ s.commutant) (i : Fin n) :
    s.coordinate (s.entry i i*x) i i=x := by
  have hterm (k : Fin n) : s.entry k i*(s.entry i i*x)*s.entry i k=s.entry k k*x := by
    calc
      _ = (s.entry k i*s.entry i i)*(x*s.entry i k) := by simp only [mul_assoc]
      _ = s.entry k k*x := by
        rw [s.entry_absorb_right,(hx i k).eq]
        rw [← mul_assoc,s.mul_entry,ite_eq_left rfl]
  simp only [coordinate,hterm,← Finset.sum_mul,s.sum_diag,one_mul]

end System
end PopaMatrices

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {n : ℕ} (s : System n (1:M))

section Closed
variable (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

def closedCommutant : StarSubalgebra ℂ M := WeakAlgebra.closure e s.commutant
  (HochschildSakai.abstract_multiplication_normal e).1
  (HochschildSakai.abstract_multiplication_normal e).2 P hP

instance closedCommutant_closed : IsClosed (closedCommutant e s P hP : Set M) :=
  WeakAlgebra.closure_closed e s.commutant
    (HochschildSakai.abstract_multiplication_normal e).1
    (HochschildSakai.abstract_multiplication_normal e).2 P hP

omit [PartialOrder M] [StarOrderedRing M] in
lemma mem_closedCommutant {a : M} (ha : a ∈ s.commutant) : a ∈ closedCommutant e s P hP :=
  WeakAlgebra.mem_linearClosure e s.commutant ha

omit [PartialOrder M] [StarOrderedRing M] in
lemma closedCommutant_subset : closedCommutant e s P hP ≤ s.commutant := by
  intro a ha i j
  let R := ((ContinuousLinearMap.mul ℂ M).flip (s.entry i j))
  let L := ContinuousLinearMap.mul ℂ M (s.entry i j)
  have hR := WeakAlgebra.normal_continuous e R
    ((HochschildSakai.abstract_multiplication_normal e).2 (s.entry i j))
  have hL := WeakAlgebra.normal_continuous e L
    ((HochschildSakai.abstract_multiplication_normal e).1 (s.entry i j))
  have hclosed := isClosed_eq hR hL
  have hm : (WeakAlgebra.weakEquiv e).symm a ∈
      closure ((s.commutant.toSubalgebra.toSubmodule.map
        (WeakAlgebra.weakEquiv e).symm.toLinearMap : Submodule ℂ (WeakDual ℂ X)) :
          Set (WeakDual ℂ X)) := ha
  have he : (WeakAlgebra.weakEquiv e).symm (R a)=
      (WeakAlgebra.weakEquiv e).symm (L a) := by
    have hz := closure_minimal (s := ((s.commutant.toSubalgebra.toSubmodule.map
        (WeakAlgebra.weakEquiv e).symm.toLinearMap : Submodule ℂ (WeakDual ℂ X)) :
          Set (WeakDual ℂ X))) (t := {f : WeakDual ℂ X |
        (WeakAlgebra.weakEquiv e).symm (R (WeakAlgebra.weakEquiv e f)) =
        (WeakAlgebra.weakEquiv e).symm (L (WeakAlgebra.weakEquiv e f))})
      (by
        rintro f ⟨b,hb,rfl⟩
        change (WeakAlgebra.weakEquiv e).symm (R ((WeakAlgebra.weakEquiv e)
          ((WeakAlgebra.weakEquiv e).symm b))) =
          (WeakAlgebra.weakEquiv e).symm (L ((WeakAlgebra.weakEquiv e)
          ((WeakAlgebra.weakEquiv e).symm b)))
        simpa [R,L] using congrArg (WeakAlgebra.weakEquiv e).symm (hb i j).eq) hclosed hm
    change (WeakAlgebra.weakEquiv e).symm (R ((WeakAlgebra.weakEquiv e)
      ((WeakAlgebra.weakEquiv e).symm a))) =
      (WeakAlgebra.weakEquiv e).symm (L ((WeakAlgebra.weakEquiv e)
      ((WeakAlgebra.weakEquiv e).symm a))) at hz
    simpa using hz
  exact (WeakAlgebra.weakEquiv e).symm.injective he

end Closed
end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u v
namespace System
variable {M : Type u} {N : Type v} [CStarAlgebra M] [CStarAlgebra N]
variable {n : ℕ} (s : System n (1:M))

def map (f : M →⋆ₐ[ℂ] N) : System n (1:N) where
  entry i j := f (s.entry i j)
  star_entry i j := by rw [← map_star,s.star_entry]
  mul_entry i j k l := by
    rw [← map_mul,s.mul_entry]
    split_ifs <;> simp only [map_zero]
  sum_diag := by rw [← map_sum,s.sum_diag,map_one]

@[simp] lemma map_entry (f : M →⋆ₐ[ℂ] N) (i j : Fin n) :
    (s.map f).entry i j=f (s.entry i j) := rfl

lemma map_expect (f : M →⋆ₐ[ℂ] N) (x : M) :
    (s.map f).expect (f x)=f (s.expect x) := by
  simp only [expect,sumExpect,map_entry,← map_mul,← map_sum,← Complex.coe_smul,map_smul]

end System

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

lemma preGNS_norm_eq_of_trace {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (σ : A →ₚ[ℂ] ℂ) (f : A →⋆ₐ[ℂ] M) (hf : ∀ a, σ a=τ (f a)) (a : A) :
    ‖σ.toPreGNS a‖=‖τ.toPreGNS (f a)‖ := by
  have ha := congrArg Complex.re (σ.preGNS_norm_sq (σ.toPreGNS a))
  have hb := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS (f a)))
  simp only [← Complex.ofReal_pow,Complex.ofReal_re,PositiveLinearMap.ofPreGNS_toPreGNS] at ha hb
  rw [hf,map_mul,map_star] at ha
  nlinarith [norm_nonneg (σ.toPreGNS a),norm_nonneg (τ.toPreGNS (f a))]
end PopaMatrices
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

def trivialSystem : System 1 (1:M) where
  entry _ _ := 1
  star_entry _ _ := star_one _
  mul_entry i j k l := by simp [Subsingleton.elim j k]
  sum_diag := by simp

def energy {r n : ℕ} (F : Fin r → M) (s : System n (1:M)) : ℝ :=
  ∑ i, ‖τ.toPreGNS (s.expect (F i))‖^2

lemma energy_nonneg {r n : ℕ} (F : Fin r → M) (s : System n (1:M)) :
    0 ≤ energy τ F s := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity PopaQuantization
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include htr in
lemma flatProjection_energy (i0 : Fin n) (a : Fin n → Bool) (x : M) :
    (n:ℝ)*‖τ.toPreGNS (s.flatProjection i0 a*x*s.flatProjection i0 a)‖^2=
      (n:ℝ)⁻¹*‖∑ i, ∑ j, (sign (a i)*sign (a j)) • τ.toPreGNS (s.entry i0 i*x*s.entry j i0)‖^2 := by
  rw [s.flatProjection_compression_norm τ htr,s.flatColumn_compression,
    ← Complex.coe_smul,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)),mul_pow]
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  have he : (n:ℝ)*((n:ℝ)⁻¹)^2=(n:ℝ)⁻¹ := by field_simp
  rw [← mul_assoc,he]
  congr 2

include htr in
lemma flatProjection_mean (i0 : Fin n) (x : M) :
    (∑ a : Fin n → Bool, (n:ℝ)*‖τ.toPreGNS (s.flatProjection i0 a*x*s.flatProjection i0 a)‖^2) ≤
      (2:ℝ)^n*(‖τ.toPreGNS (s.expect x)‖^2+(2/(n:ℝ))*‖τ.toPreGNS x‖^2) := by
  let : InnerProductSpace ℝ τ.PreGNS := InnerProductSpace.rclikeToReal ℂ _
  simp_rw [s.flatProjection_energy τ htr]
  rw [← Finset.mul_sum]
  have hh := quadratic_mean_square_bound (fun i j => τ.toPreGNS (s.entry i0 i*x*s.entry j i0))
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Nat.cast_nonneg n))
  apply hh'.trans_eq
  rw [← map_sum,s.diagonal_sum_norm τ htr,s.blocks_norm_sum τ htr]
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  field_simp

include htr in

lemma exists_flat_projection {r : ℕ} (i0 : Fin n) (F : Fin r → M) :
    ∃ a : Fin n → Bool,
      (∑ j, (n:ℝ)*‖τ.toPreGNS (s.flatProjection i0 a*F j*s.flatProjection i0 a)‖^2) ≤
        PopaMatrices.energy τ F s+(2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2) := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => s.flatProjection_mean τ htr i0 (F j))
  rw [Finset.sum_comm] at hh
  simp only [mul_add,Finset.sum_add_distrib,← Finset.mul_sum] at hh
  have he : ((2:ℝ)^n*PopaMatrices.energy τ F s+(2:ℝ)^n*((2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2)))=
      ∑ _a : Fin n → Bool, (PopaMatrices.energy τ F s+(2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2)) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  change _ ≤ (2:ℝ)^n*PopaMatrices.energy τ F s+(2:ℝ)^n*((2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2)) at hh
  rw [he,Finset.mul_sum] at hh
  obtain ⟨a,_,ha⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    ⟨(fun _ => false),Finset.mem_univ _⟩ hh
  exact ⟨a,by simpa only [Finset.mul_sum] using ha⟩
end PopaMatrices.System
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

lemma closedCommutant_typeII (hn : 0 < n) (hII : NoAbelianCorners M) :
    NoAbelianCorners (closedCommutant e s P hP) := by
  intro p hp hp0
  let Q := closedCommutant e s P hP
  let i : Fin n := ⟨0,hn⟩
  have hpM : IsStarProjection (p:M) := hp.map Q.subtype
  have hpQ := closedCommutant_subset e s P hP p.property
  let a : M := s.entry i i*(p:M)
  have ha : IsStarProjection a := (s.diagonal_projection i).mul hpM (hpQ i i).symm
  have hac : s.coordinate a i i=(p:M) := s.coordinate_of_commutes (p:M) hpQ i
  have ha0 : a ≠ 0 := by
    intro h
    exact hp0 (Subtype.ext (by change (p:M)=0; simpa only [h,s.coordinate_zero] using hac.symm))
  obtain ⟨x,y,hxy⟩ := hII a ha ha0
  have hai : a ≤ s.entry i i := (ha.le_iff_mul_eq_right (s.diagonal_projection i)).mpr (by
    dsimp [a]; rw [←mul_assoc,(s.diagonal_projection i).isIdempotentElem.eq])
  have aL := (ha.le_iff_mul_eq_right (s.diagonal_projection i)).mp hai
  have aR := (ha.le_iff_mul_eq_left (s.diagonal_projection i)).mp hai
  have xiR (z : PopaCorner.algebra ha) : (z:M)*s.entry i i=(z:M) := by
    calc _=((z:M)*a)*s.entry i i := by rw [z.property.2]
         _=(z:M)*(a*s.entry i i) := mul_assoc _ _ _
         _=(z:M) := by rw [aR,z.property.2]
  have xiL (z : PopaCorner.algebra ha) : s.entry i i*(z:M)=(z:M) := by
    calc _=s.entry i i*(a*(z:M)) := by rw [z.property.1]
         _=(s.entry i i*a)*(z:M) := (mul_assoc _ _ _).symm
         _=(z:M) := by rw [aL,z.property.1]
  let lift (z : PopaCorner.algebra ha) : Q :=
    ⟨s.coordinate (z:M) i i,mem_closedCommutant e s P hP (s.coordinate_mem _ i i)⟩
  have hLp (z : PopaCorner.algebra ha) : p*lift z=lift z := by
    apply Subtype.ext
    change (p:M)*s.coordinate (z:M) i i=s.coordinate (z:M) i i
    rw [←hac,←s.coordinate_mul i aR,z.property.1]
  have hRp (z : PopaCorner.algebra ha) : lift z*p=lift z := by
    apply Subtype.ext
    change s.coordinate (z:M) i i*(p:M)=s.coordinate (z:M) i i
    rw [←hac,←s.coordinate_mul i (xiR z),z.property.2]
  let L (z : PopaCorner.algebra ha) : PopaCorner.algebra hp := ⟨lift z,hLp z,hRp z⟩
  refine ⟨L x,L y,?_⟩
  intro hcomm
  apply hxy
  apply Subtype.ext
  change (x:M)*(y:M)=(y:M)*(x:M)
  have hh := congrArg (fun z : PopaCorner.algebra hp => ((z:Q):M)) hcomm.eq
  change s.coordinate (x:M) i i*s.coordinate (y:M) i i=
    s.coordinate (y:M) i i*s.coordinate (x:M) i i at hh
  rw [←s.coordinate_mul i (xiR x),←s.coordinate_mul i (xiR y)] at hh
  have hxyL : s.entry i i*((x:M)*(y:M))=(x:M)*(y:M) := by rw [←mul_assoc,xiL x]
  have hxyR : ((x:M)*(y:M))*s.entry i i=(x:M)*(y:M) := by rw [mul_assoc,xiR y]
  have hyxL : s.entry i i*((y:M)*(x:M))=(y:M)*(x:M) := by rw [←mul_assoc,xiL y]
  have hyxR : ((y:M)*(x:M))*s.entry i i=(y:M)*(x:M) := by rw [mul_assoc,xiR x]
  simpa only [s.extract_coordinate i hxyL hxyR,s.extract_coordinate i hyxL hyxR]
    using congrArg (fun z => s.entry i i*z) hh

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

namespace System
variable {n : ℕ} (s : PopaMatrices.System n (1:M))

end System
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices PopaTypeII PopaCorners PopaCorners.CornerIso
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier PopaQuantization PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma average_expect {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) (a : M) :
    average e τ hτ htr hfaith (s.expect a)=average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith a
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz]
    have he : s.expect (z*a)=z*s.expect a := by
      simpa only [mul_one] using s.expect_bimodule z 1 a
        (fun i j => hz (s.entry i j)) s.commutant.one_mem
    rw [←he,s.trace_expect hn τ htr]

include e hτ htr hfaith h1 in
lemma extend_energy_decrease_center (hII : NoAbelianCorners M)
    {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) (a : M)
    (haE : average e τ hτ htr hfaith a=0) (ha : 0<‖τ.toPreGNS (s.expect a)‖) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : PopaMatrices.System m (1:M),
      (∀ x : M, ‖τ.toPreGNS (t.expect x)‖ ≤ ‖τ.toPreGNS (s.expect x)‖) ∧
      ‖τ.toPreGNS (t.expect a)‖^2 < (1-1/1024:ℝ)*‖τ.toPreGNS (s.expect a)‖^2 := by
  obtain ⟨P,_hPn,hP⟩ := HochschildSakai.exists_abstract_star_preadjoint e
  let hL := (HochschildSakai.abstract_multiplication_normal e).1
  let hR := (HochschildSakai.abstract_multiplication_normal e).2
  let Q := closedCommutant e s P hP
  let eQ : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator
      (WeakAlgebra.linearClosure e s.commutant)) ≃ₗᵢ⋆[ℂ] Q := WeakAlgebra.predualEquiv e s.commutant hL hR P hP
  let τQ : Q →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ s.commutant hL hR P hP
  let b : Q := ⟨s.expect a,mem_closedCommutant e s P hP (s.expect_mem a)⟩
  let htQ := WeakAlgebra.inheritedTrace_normal e τ s.commutant hL hR P hP hτ
  let htrQ := WeakAlgebra.inheritedTrace_tracial e τ s.commutant hL hR P hP htr
  let hfQ := WeakAlgebra.inheritedTrace_faithful e τ s.commutant hL hR P hP hfaith
  let h1Q := WeakAlgebra.inheritedTrace_one e τ s.commutant hL hR P hP h1
  have hcen (z : Q) (hz : Central z) : Central (z:M) :=
    s.central_in_commutant_is_central (z:M) (closedCommutant_subset e s P hP z.property)
      (fun x hx => congrArg Subtype.val (hz ⟨x,mem_closedCommutant e s P hP hx⟩).eq)
  have hbE : average eQ τQ htQ htrQ hfQ b=0 := by
    apply average_eq eQ τQ htQ htrQ hfQ h1Q
    · exact fun x => Commute.zero_left x
    · intro z hz
      change τ ( (z:M)*0)=τ ((z:M)*s.expect a)
      rw [←average_pair e τ hτ htr hfaith h1 (hcen z hz) (s.expect a),
        average_expect e τ hτ htr hfaith h1 s hn,haE]
  have hnorm (x : Q) : ‖τQ.toPreGNS x‖=‖τ.toPreGNS (x:M)‖ :=
    preGNS_norm_eq_of_trace τ τQ Q.subtype (fun _ => rfl) x
  have hb : 0 < ‖τQ.toPreGNS b‖ := by rw [hnorm]; exact ha
  obtain ⟨k,hk,r,hr⟩ := exists_matrix_energy_decrease_center eQ τQ htQ htrQ hfQ h1Q
    (closedCommutant_typeII e s P hP hn hII) b hbE hb
  let rM := r.map Q.subtype
  have hc : ∀ i j a b, Commute (rM.entry i j) (s.entry a b) := by
    intro i j a b
    exact closedCommutant_subset e s P hP (r.entry i j).property a b
  let t := rM.tensor s hc
  refine ⟨k*n,Nat.mul_pos hk hn,t,?_,?_⟩
  · intro x
    rw [show t.expect x=rM.expect (s.expect x) from rM.tensor_expect s hc x]
    exact rM.expect_norm_le τ htr hk _
  · simp only [hnorm] at hr
    rw [show t.expect a=rM.expect (s.expect a) from rM.tensor_expect s hc a]
    change ‖τ.toPreGNS ((r.map Q.subtype).expect (Q.subtype b))‖^2 <
      (1-1/1024:ℝ)*‖τ.toPreGNS (Q.subtype b)‖^2
    rw [r.map_expect]
    exact hr
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)

include e hτ htr hfaith h1 in
lemma energy_contract_center (hdiff : NoAbelianCorners M)
    {r : ℕ} (hr : 0 < r) (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0)
    {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : PopaMatrices.System m (1:M),
      energy τ F t ≤ (1-1/(1024*(r:ℝ)))*energy τ F s := by
  classical
  have hrR : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  by_cases hz : energy τ F s=0
  · exact ⟨n,hn,s,by rw [hz]; simp⟩
  have hE : 0 < energy τ F s := lt_of_le_of_ne (energy_nonneg τ F s) (Ne.symm hz)
  have hsum : (∑ _i : Fin r, energy τ F s/(r:ℝ)) = energy τ F s := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _i : Fin r => energy τ F s/(r:ℝ))
    (g := fun i : Fin r => ‖τ.toPreGNS (s.expect (F i))‖^2)
    ⟨⟨0,hr⟩,Finset.mem_univ _⟩ (by rw [hsum]; rfl)
  have hi : 0 < ‖τ.toPreGNS (s.expect (F i))‖ := by
    have hh := (div_pos hE hrR).trans_le hmax
    nlinarith [norm_nonneg (τ.toPreGNS (s.expect (F i)))]
  obtain ⟨m,hm,t,hle,hlt⟩ := extend_energy_decrease_center e τ hτ htr hfaith h1
    hdiff s hn (F i) (hF i) hi
  have hdiffs (j : Fin r) : 0 ≤ ‖τ.toPreGNS (s.expect (F j))‖^2-
      ‖τ.toPreGNS (t.expect (F j))‖^2 := by
    have hj := hle (F j)
    nlinarith [norm_nonneg (τ.toPreGNS (t.expect (F j)))]
  have hdrop := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin r =>
    ‖τ.toPreGNS (s.expect (F j))‖^2-‖τ.toPreGNS (t.expect (F j))‖^2)
    (fun j _ => hdiffs j) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib] at hdrop
  change _ ≤ energy τ F s-energy τ F t at hdrop
  have hmax' : energy τ F s ≤ (r:ℝ)*‖τ.toPreGNS (s.expect (F i))‖^2 := by
    exact (div_le_iff₀ hrR).mp hmax |>.trans_eq (mul_comm _ _)
  refine ⟨m,hm,t,?_⟩
  apply (le_of_mul_le_mul_left ?_ (show 0 < 1024*(r:ℝ) by positivity))
  have hh : (1024*(r:ℝ))*((1-1/(1024*(r:ℝ)))*energy τ F s)=
      (1024*(r:ℝ)-1)*energy τ F s := by field_simp
  rw [hh]
  have hlow : ‖τ.toPreGNS (s.expect (F i))‖^2/1024 < energy τ F s-energy τ F t := by linarith
  have hmul := mul_lt_mul_of_pos_left hlow hrR
  nlinarith

include e hτ htr hfaith h1 in

theorem exists_small_expectation_center (hdiff : NoAbelianCorners M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : PopaMatrices.System n (1:M), energy τ F s < ε := by
  by_cases hr : r=0
  · subst r
    exact ⟨1,by omega,trivialSystem,by simpa [energy] using hε⟩
  have hrp : 0 < r := Nat.pos_of_ne_zero hr
  let q : ℝ := 1-1/(1024*(r:ℝ))
  have hrR : 1 ≤ (r:ℝ) := by exact_mod_cast hrp
  have hq0 : 0 ≤ q := by
    have hh : 1/(1024*(r:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; exact sub_lt_self _ (by positivity)
  have hi : ∀ k : ℕ, ∃ n : ℕ, 0 < n ∧ ∃ s : PopaMatrices.System n (1:M),
      energy τ F s ≤ q^k*energy τ F (trivialSystem (M:=M)) := by
    intro k
    induction k with
    | zero => exact ⟨1,by omega,trivialSystem,by simp⟩
    | succ k ih =>
      obtain ⟨n,hn,s,hs⟩ := ih
      obtain ⟨m,hm,t,ht⟩ := energy_contract_center e τ hτ htr hfaith h1 hdiff hrp F hF s hn
      refine ⟨m,hm,t,ht.trans ?_⟩
      have hh := mul_le_mul_of_nonneg_left hs hq0
      change q*energy τ F s ≤ _
      simpa only [pow_succ,mul_assoc,mul_comm q,mul_left_comm q] using hh
  have ht : Tendsto (fun k : ℕ => q^k*energy τ F (trivialSystem (M:=M))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (energy τ F (trivialSystem (M:=M)))
  obtain ⟨k,hk⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  obtain ⟨n,hn,s,hs⟩ := hi k
  exact ⟨n,hn,s,hs.trans_lt hk⟩
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem exists_large_refinement_center (hdiff : NoAbelianCorners M)
    {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ ∃ t : PopaMatrices.System m (1:M),
      ∀ x : M, ‖τ.toPreGNS (t.expect x)‖ ≤ ‖τ.toPreGNS (s.expect x)‖ := by
  obtain ⟨P,_hPn,hP⟩ := HochschildSakai.exists_abstract_star_preadjoint e
  let hL := (HochschildSakai.abstract_multiplication_normal e).1
  let hR := (HochschildSakai.abstract_multiplication_normal e).2
  let Q := closedCommutant e s P hP
  let eQ : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator
      (WeakAlgebra.linearClosure e s.commutant)) ≃ₗᵢ⋆[ℂ] Q := WeakAlgebra.predualEquiv e s.commutant hL hR P hP
  let τQ : Q →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ s.commutant hL hR P hP
  obtain ⟨r⟩ := exists_dyadic_system eQ τQ
    (WeakAlgebra.inheritedTrace_normal e τ s.commutant hL hR P hP hτ)
    (WeakAlgebra.inheritedTrace_tracial e τ s.commutant hL hR P hP htr)
    (WeakAlgebra.inheritedTrace_faithful e τ s.commutant hL hR P hP hfaith)
    (WeakAlgebra.inheritedTrace_one e τ s.commutant hL hR P hP h1)
    (closedCommutant_typeII e s P hP hn hdiff) (N+1)
  let rM := r.map Q.subtype
  have hc : ∀ i j a b, Commute (rM.entry i j) (s.entry a b) := by
    intro i j a b
    exact closedCommutant_subset e s P hP (r.entry i j).property a b
  let t := rM.tensor s hc
  have hpow : N < 2^(N+1) := lt_trans (Nat.lt_succ_self N) (Nat.lt_two_pow_self)
  have hpowpos : 0 < 2^(N+1) := pow_pos (by omega) _
  refine ⟨2^(N+1)*n,by nlinarith,t,?_⟩
  intro x
  rw [show t.expect x=rM.expect (s.expect x) from rM.tensor_expect s hc x]
  exact rM.expect_norm_le τ htr (by omega) _

include e hτ htr hfaith h1 in
lemma exists_large_small_expectation_center (hdiff : NoAbelianCorners M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∃ s : PopaMatrices.System n (1:M), energy τ F s < ε := by
  obtain ⟨n,hn,s,hs⟩ := exists_small_expectation_center e τ hτ htr hfaith h1 hdiff F hF ε hε
  obtain ⟨m,hm,t,ht⟩ := exists_large_refinement_center e τ hτ htr hfaith h1 hdiff s hn N
  refine ⟨m,hm,t,(Finset.sum_le_sum (fun i _ => ?_)).trans_lt hs⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (ht (F i)) 2
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem local_quantization_center_valued (hdiff : NoAbelianCorners M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ (τ q).re < δ ∧
      average e τ hτ htr hfaith q=(τ q).re • (1:M) ∧
      (∑ i, ‖τ.toPreGNS (q*F i*q)‖^2) < η*(τ q).re := by
  let C : ℝ := ∑ j, ‖τ.toPreGNS (F j)‖^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨N,hN⟩ := exists_nat_gt (max (4*C/η) (1/δ))
  obtain ⟨n,hn,s,hs⟩ := exists_large_small_expectation_center e τ hτ htr hfaith h1
    hdiff F hF (η/2) (by positivity) N
  have hnpos : 0<n := Nat.zero_lt_of_lt hn
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hnpos
  have hb : 4*C/η < (n:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hN).trans (Nat.cast_lt.mpr hn)
  have hd : 1/δ < (n:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hN).trans (Nat.cast_lt.mpr hn)
  obtain ⟨a,ha⟩ := s.exists_flat_projection τ htr ⟨0,hnpos⟩ F
  let q := s.flatProjection ⟨0,hnpos⟩ a
  have hq : IsStarProjection q := s.flatProjection_projection _ _
  have ht : (τ q).re=(n:ℝ)⁻¹ := by
    rw [show τ q=(n:ℂ)⁻¹ from s.flatProjection_trace τ htr h1 _ _]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_inv,Complex.ofReal_re]
  have htpos : 0 < (τ q).re := by rw [ht]; positivity
  refine ⟨q,hq,fun h => by simp only [h,map_zero,Complex.zero_re,lt_self_iff_false] at htpos,?_,?_,?_⟩
  · rw [ht]
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ hnR).mpr (by
      have hh := (div_lt_iff₀ hδ).mp hd
      nlinarith)
  · rw [ht]
    change average e τ hτ htr hfaith (s.flatColumn ⟨0,hnpos⟩ a*star (s.flatColumn ⟨0,hnpos⟩ a))=_
    rw [average_trace e τ hτ htr hfaith h1,s.flatColumn_star_mul]
    have hd := average_diagonal_one e τ hτ htr hfaith h1 s ⟨0,hnpos⟩
    have hh := congrArg (fun z : M => (n:ℝ)⁻¹ • z) hd
    simpa only [smul_smul,inv_mul_cancel₀ hnR.ne',one_smul] using hh
  · have hterm : (2/(n:ℝ))*C < η/2 := by
      have hh := (div_lt_iff₀ hη).mp hb
      apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      have hn0 := hnR.ne'
      field_simp
      nlinarith
    have hh : (n:ℝ)*(∑ i, ‖τ.toPreGNS (q*F i*q)‖^2) < η := by
      rw [Finset.mul_sum]
      exact ha.trans_lt (by change energy τ F s+2/(n:ℝ)*C<η; linarith)
    rw [ht,←div_eq_mul_inv]
    exact (lt_div_iff₀ hnR).mpr (by nlinarith)
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

lemma norm_sq_trace_corner {p : M} (hp : IsStarProjection p) (a : algebra hp) :
    ‖(trace hp τ).toPreGNS a‖^2=(τ p).re⁻¹*‖τ.toPreGNS (a:M)‖^2 := by
  rw [PopaMatrices.System.norm_sq_eq_trace,PopaMatrices.System.norm_sq_eq_trace,trace_apply]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

lemma cornerCoefficient_central {p : M} (hp : IsStarProjection p) (a : M) :
    Central (cornerCoefficient e τ hτ htr hfaith hp a) := fun x =>
  (average_central e τ hτ htr hfaith _ x).smul_left _

include h1 in
lemma cornerCoefficient_spec (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hEp : average e τ hτ htr hfaith p=(τ p).re • (1:M)) (a : M) :
    cornerCoefficient e τ hτ htr hfaith hp a*p=
        (cornerAverage e τ hτ htr hfaith hp (compress hp a):M) ∧
      ‖cornerCoefficient e τ hτ htr hfaith hp a‖≤‖a‖ := by
  have ht := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  obtain ⟨c,hc,hcp,hcn,hce⟩ := cornerAverage_lift e τ hτ htr hfaith h1 hII hp hp0 ht hEp (compress hp a)
  have he : cornerCoefficient e τ hτ htr hfaith hp a=c := by
    change (τ p).re⁻¹ • average e τ hτ htr hfaith ((compress hp a):M)=c
    rw [hce,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  rw [he]
  exact ⟨hcp,hcn.trans (compress_norm_le hp a)⟩

include h1 in
theorem local_quantization_corner (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hEp : average e τ hτ htr hfaith p=(τ p).re • (1:M))
    {r : ℕ} (F : Fin r → M) (η δ : ℝ) (hη : 0<η) (hδ : 0<δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧ (τ q).re < δ*(τ p).re ∧
      average e τ hτ htr hfaith q=(τ q).re • (1:M) ∧
      (∑ i, ‖τ.toPreGNS (q*F i*q-cornerCoefficient e τ hτ htr hfaith hp (F i)*q)‖^2) < η*(τ q).re := by
  let t := trace hp τ
  let ec := predualEquiv e hp
  let htc := trace_normal hp τ e hτ
  let httr := trace_tracial hp τ htr
  let htf := trace_faithful hp τ hfaith
  have ht1 : t 1=1 := trace_one hp τ hfaith hp0
  let G : Fin r → algebra hp := fun i => compress hp (F i)-cornerAverage e τ hτ htr hfaith hp (compress hp (F i))
  have hG (i : Fin r) : average ec t htc httr htf (G i)=0 := by
    change expectation ec t htc httr htf ht1 (_-_)=0
    rw [map_sub]
    change average ec t htc httr htf (compress hp (F i))-
      average ec t htc httr htf (average ec t htc httr htf (compress hp (F i)))=0
    rw [average_id ec t htc httr htf ht1 (average_central ec t htc httr htf _),sub_self]
  obtain ⟨q,hq,hq0,hqt,hqE,hqe⟩ := local_quantization_center_valued ec t htc httr htf ht1
    (corner_typeII hII hp) G hG η δ hη hδ
  have ht : 0 < (τ p).re := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  have hqM : IsStarProjection (q:M) := hq.map (incl hp)
  have hqp : (q:M) ≤ p := (hqM.le_iff_mul_eq_left hp).mpr q.property.2
  have hqtval : (t q).re=(τ p).re⁻¹*(τ (q:M)).re := by
    simp only [t,trace_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have he (i : Fin r) : ((q*G i*q : algebra hp):M)=
      (q:M)*F i*(q:M)-cornerCoefficient e τ hτ htr hfaith hp (F i)*(q:M) := by
    let c := cornerCoefficient e τ hτ htr hfaith hp (F i)
    have hc : Central c := cornerCoefficient_central e τ hτ htr hfaith hp (F i)
    have hcp := (cornerCoefficient_spec e τ hτ htr hfaith h1 hII hp hp0 hEp (F i)).1
    change (q:M)*(p*F i*p-(cornerAverage e τ hτ htr hfaith hp (compress hp (F i)):M))*(q:M)=_
    rw [←hcp,mul_sub,sub_mul,←mul_assoc (q:M),←mul_assoc (q:M),q.property.2,
      mul_assoc _ p,q.property.1]
    change _-(q:M)*(c*p)*(q:M)=_
    have hec : (q:M)*(c*p)*(q:M)=c*(q:M) := by
      rw [mul_assoc (q:M) (c*p), mul_assoc c p, q.property.1,
        ←mul_assoc, ←(hc (q:M)).eq, mul_assoc, hqM.isIdempotentElem.eq]
    rw [hec]
  refine ⟨q.val,hqM,fun hh => hq0 (Subtype.ext hh),hqp,?_,?_,?_⟩
  · rw [hqtval] at hqt
    calc
      (τ (q:M)).re = ((τ p).re⁻¹*(τ (q:M)).re)*(τ p).re := by field_simp
      _ < δ*(τ p).re := mul_lt_mul_of_pos_right hqt ht
  · have hh := average_corner_rank e τ hτ htr hfaith h1 hp hp0 q hqE
    rw [hEp,hqtval,smul_smul] at hh
    have hmul : ((τ p).re⁻¹*(τ (q:M)).re)*(τ p).re=(τ (q:M)).re := by field_simp
    simpa only [hmul] using hh
  · have hh : (τ p).re⁻¹*(∑ i, ‖τ.toPreGNS ((q:M)*F i*(q:M)-cornerCoefficient e τ hτ htr hfaith hp (F i)*(q:M))‖^2)
        < η*((τ p).re⁻¹*(τ (q:M)).re) := by
      simpa only [t,norm_sq_trace_corner,he,trace_apply,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero,←Finset.mul_sum] using hqe
    have hm := mul_lt_mul_of_pos_left hh ht
    simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_one,mul_left_comm (τ p).re η] using hm
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
open BoundedHochschild HochschildRigidity
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace Rep

end Rep

variable {K : Type*}

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner PopaPatching
variable {G M K : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_central {q : M} (hq : IsStarProjection q) {c : M} (hc : Central c) :
    ((compress hq c):M)=c*q := by
  change q*c*q=c*q
  rw [←(hc q).eq,mul_assoc,hq.isIdempotentElem.eq]
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
universe u v
variable {A : Type u} [Fintype A]

def shortWords (A : Type u) [Fintype A] : ℕ → Finset (List A)
  | 0 => {[]}
  | n+1 => by
    classical
    exact insert [] (Finset.univ.biUnion (fun a => (shortWords A n).image (List.cons a)))

@[simp] theorem mem_shortWords (l : List A) (n : ℕ) : l ∈ shortWords A n ↔ l.length ≤ n := by
  classical
  induction n generalizing l with
  | zero => simp [shortWords]
  | succ n ih =>
    cases l with
    | nil => simp [shortWords]
    | cons a l => simp [shortWords,ih]

variable {C B : Type u} [Fintype C] [Fintype B]
variable {G : Type u} [Group G]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching
universe u v
variable {C B : Type u} [Fintype C] [Fintype B]
variable {G : Type u} [Group G]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in

theorem quantize_words (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hEp : Homogeneous e τ hτ htr hfaith p)
    (a : C → M) (γ : B → G) (v : Rep G M) (L : ℕ)
    (θ d : ℝ) (hθ : 0<θ) (hd : 0<d) :
    ∃ q : M, ∃ hq : IsStarProjection q, q ≠ 0 ∧ q ≤ p ∧ (τ q).re < d*(τ p).re ∧ Homogeneous e τ hτ htr hfaith q ∧
      ∀ l : List (Letter C B), l.length ≤ L →
        ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
          PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ := by
  classical
  let W := {l : List (Letter C B) // l ∈ shortWords (Letter C B) L}
  let E := Fintype.equivFin W
  let F : Fin (Fintype.card W) → M := fun i => evaluate a γ v (E.symm i).val
  obtain ⟨q,hq,hq0,hqp,hqd,hEq,hqe⟩ := local_quantization_corner e τ hτ htr hfaith h1
    hII hp hp0 hEp F (θ^2) d (sq_pos_of_pos hθ) hd
  refine ⟨q,hq,hq0,hqp,hqd,hEq,fun l hl => ?_⟩
  let j : Fin (Fintype.card W) := E ⟨l,(mem_shortWords l L).mpr hl⟩
  have hj : F j=evaluate a γ v l := by simp [F,j]
  have hb : ‖τ.toPreGNS (q*evaluate a γ v l*q-
      cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)*q)‖^2 < θ^2*(τ q).re := by
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖τ.toPreGNS (q*F i*q-
        cornerCoefficient e τ hτ htr hfaith hp (F i)*q)‖) (Finset.mem_univ j)
    have hhh := hh.trans_lt hqe
    simpa only [hj] using hhh
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  let z : PopaCorner.algebra hq := PopaCorner.compress hq (evaluate a γ v l)-
      PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l))
  have hz := PopaCorner.norm_sq_trace_corner τ hq z
  have hzb : ((τ q).re)*‖(PopaCorner.trace hq τ).toPreGNS z‖^2 < (τ q).re*θ^2 := by
    rw [hz,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_comm]
    change ‖τ.toPreGNS (q*evaluate a γ v l*q-
      ((PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l))):M))‖^2 < _
    rw [compress_central hq (cornerCoefficient_central e τ hτ htr hfaith hp (evaluate a γ v l))]
    exact hb
  have hh : ‖(PopaCorner.trace hq τ).toPreGNS z‖^2 < θ^2 := by nlinarith
  nlinarith [norm_nonneg ((PopaCorner.trace hq τ).toPreGNS z)]
end PopaCenter
end
end OAI
end

theorem solution.{u,v} : type_of% @OAI.PopaCenter.quantize_words.{u,v} := @OAI.PopaCenter.quantize_words.{u,v}
