-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.finite_homogeneous_typeI_primitive_of_abelian_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:04:12.224363+00:00
-- url     : https://prove2.me/submissions/8d9ee306-af83-4cbe-bf97-26f8ecaaf45e

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace BoundedHochschild

section AlgebraicAveraging
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

@[simp] theorem differentialValue_add {n : ℕ} (f g : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (f + g) v = differentialValue f v + differentialValue g v := by
  simp only [differentialValue, add_apply, mul_add, add_mul,
    smul_add, Finset.sum_add_distrib]
  abel

@[simp] theorem differentialValue_smul {n : ℕ} (c : ℂ) (f : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (c • f) v = c • differentialValue f v := by
  simp only [differentialValue, smul_apply, smul_mul_assoc,
    mul_smul_comm, smul_add, Finset.smul_sum, smul_smul]
  congr 2
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm c]
  · rw [mul_comm c]

end AlgebraicAveraging

section TupleIdentities
variable {M : Type*}

@[simp] theorem mergeInputs_snoc_castSucc [Mul M] {n : ℕ} (v : Fin (n + 1) → M)
    (u : M) (j : Fin n) :
    mergeInputs (Fin.snoc v u) j.castSucc = Fin.snoc (mergeInputs v j) u := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have hlt : ¬ Fin.last n < j.castSucc := by
      simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
      omega
    have heq : Fin.last n ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [mergeInputs, hlt, heq]
  · simp [mergeInputs, ← Fin.castSucc_succ]

@[simp] theorem mergeInputs_snoc_last [Mul M] {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    mergeInputs (Fin.snoc v u) (Fin.last n) =
      Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs]
end TupleIdentities
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
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem bounded_cochain_ultralimit {n : ℕ} (u : Ultrafilter I)
    (F : I → Cochain M n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i, ‖F i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧
      ∀ x, PredualTendsto e (fun i => F i x) u (G x) := by
  classical
  have hex (x : Fin n → M) : ∃ b : M, ‖b‖ ≤ C * ∏ k, ‖x k‖ ∧
      PredualTendsto e (fun i => F i x) u b :=
    exists_predual_ultralimit e u (fun i => F i x) _ (fun i =>
      (F i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hF i)
        (Finset.prod_nonneg (fun k _ => norm_nonneg (x k)))))
  choose b hb ht using hex
  let G₀ : MultilinearMap ℂ (fun _ : Fin n => M) M :=
    { toFun := b
      map_update_add' := fun x k a c => by
        apply predual_tendsto_unique e (ht (Function.update x k (a+c)))
        simpa only [ContinuousMultilinearMap.map_update_add] using
          predual_tendsto_add e (ht (Function.update x k a)) (ht (Function.update x k c))
      map_update_smul' := fun x k c a => by
        apply predual_tendsto_unique e (ht (Function.update x k (c • a)))
        simpa only [ContinuousMultilinearMap.map_update_smul] using
          predual_tendsto_smul e (ht (Function.update x k a)) c }
  exact ⟨G₀.mkContinuous C hb, G₀.mkContinuous_norm_le hC hb, ht⟩

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_sum {a : I → J → M} {b : J → M} (l : Filter I) (s : Finset J)
    (h : ∀ j ∈ s, PredualTendsto e (fun i => a i j) l (b j)) :
    PredualTendsto e (fun i => ∑ j ∈ s, a i j) l (∑ j ∈ s, b j) := by
  intro z
  simpa only [map_sum,sum_apply] using
    tendsto_finsetSum s (fun j hj => h j hj z)
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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include h1 htr

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]

end HochschildWalk

namespace BoundedHochschild
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_differential
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    {n : ℕ} {F : I → Cochain M n} {G : Cochain M n} {l : Filter I}
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x))
    (x : Fin (n+1) → M) :
    PredualTendsto e (fun i => differentialValue (F i) x) l (differentialValue G x) := by
  simp only [differentialValue]
  apply predual_tendsto_add e
  · apply predual_tendsto_add e
    · exact (hL (x 0)).tendsto e (ht _)
    · apply predual_tendsto_sum e l Finset.univ
      intro j _
      exact predual_tendsto_smul e (ht _) _
  · exact predual_tendsto_smul e ((hR (x (Fin.last n))).tendsto e (ht _)) _
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
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def centralOutput {n : ℕ} (p : M) (f : Cochain M n) : Cochain M n :=
  (ContinuousLinearMap.mul ℂ M p).compContinuousMultilinearMap f

@[simp] lemma centralOutput_apply {n : ℕ} (p : M) (f : Cochain M n) (x : Fin n → M) :
    centralOutput p f x=p*f x := rfl

lemma norm_centralOutput_le {n : ℕ} (p : M) (hp : ‖p‖ ≤ 1) (f : Cochain M n) :
    ‖centralOutput p f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (norm_mul_le p (f x)).trans ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
    (by simpa only [one_mul] using f.le_opNorm x))
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
end WeakAlgebra
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
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

def commutant : StarSubalgebra ℂ M where
  carrier := {x | ∀ i j, Commute x (E.entry i j)}
  zero_mem' := fun i j => Commute.zero_left _
  one_mem' := fun i j => Commute.one_left _
  add_mem' := fun hx hy i j => (hx i j).add_left (hy i j)
  mul_mem' := fun hx hy i j => (hx i j).mul_left (hy i j)
  algebraMap_mem' c := fun i j => Algebra.commutes c (E.entry i j)
  star_mem' := fun hx i j => by
    have hh := congrArg star (hx j i).eq
    change _ * _ = _ * _
    simpa only [star_mul,E.star_entry] using hh.symm

instance commutant_closed : IsClosed (E.commutant : Set M) := by
  change IsClosed {x : M | ∀ i j, x*E.entry i j = E.entry i j*x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

def coefficient (i j : Fin n) (x : M) : M := ∑ k, E.entry k i*x*E.entry j k

lemma entry_mul_coefficient (a b i j : Fin n) (x : M) :
    E.entry a b*E.coefficient i j x=E.entry a i*x*E.entry j b := by
  classical
  simp only [coefficient,Finset.mul_sum,← mul_assoc,E.entry_mul,ite_mul,zero_mul]
  simp

lemma coefficient_mul_entry (a b i j : Fin n) (x : M) :
    E.coefficient i j x*E.entry a b=E.entry a i*x*E.entry j b := by
  classical
  simp only [coefficient,Finset.sum_mul,mul_assoc,E.entry_mul,mul_ite,mul_zero]
  simp [← mul_assoc]

lemma coefficient_mem (i j : Fin n) (x : M) : E.coefficient i j x ∈ E.commutant := by
  intro a b
  exact (E.coefficient_mul_entry a b i j x).trans (E.entry_mul_coefficient a b i j x).symm

lemma reconstruct (x : M) : ∑ i, ∑ j, E.entry i j*E.coefficient i j x=x := by
  simp only [E.entry_mul_coefficient,← Finset.mul_sum,← Finset.sum_mul,E.sum_diagonal,one_mul,mul_one]

lemma diagonal_proj (i : Fin n) : IsStarProjection (E.entry i i) := by
  exact ⟨by change E.entry i i*E.entry i i=E.entry i i; rw [E.entry_mul,ite_eq_left rfl],
    by change star (E.entry i i)=E.entry i i; exact E.star_entry i i⟩

variable [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coefficient_of_commutant (i : Fin n) {x : M} (hx : x ∈ E.commutant) :
    E.coefficient i i (E.entry i i*x)=x := by
  classical
  calc
    E.coefficient i i (E.entry i i*x) = ∑ k, (E.entry k k)*x := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        E.entry k i*(E.entry i i*x)*E.entry i k = (E.entry k i*E.entry i i)*(x*E.entry i k) := by
          noncomm_ring
        _ = (E.entry k i*E.entry i i)*(E.entry i k*x) := by rw [(hx i k).eq]
        _ = E.entry k k*x := by rw [E.entry_mul,ite_eq_left rfl,← mul_assoc,E.entry_mul,ite_eq_left rfl]
    _ = x := by rw [← Finset.sum_mul,E.sum_diagonal,one_mul]

end MatrixSystem
end HochschildMatrixSystems

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (E : MatrixSystem M n)

end MatrixSystem

universe u
namespace MatrixSystem
open BoundedHochschild BoundedHochschild.WeakAlgebra
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {n : ℕ} (E : MatrixSystem M n)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

lemma commutantClosure_eq : WeakAlgebra.closure e E.commutant hL hR P hP=E.commutant := by
  apply le_antisymm
  · intro x hx i j
    have hclosed : IsClosed {f : WeakDual ℂ X |
        (weakEquiv e).symm (E.entry i j*weakEquiv e f)=
        (weakEquiv e).symm (weakEquiv e f*E.entry i j)} :=
      isClosed_eq (normal_continuous e _ (hL _)) (normal_continuous e _ (hR _))
    have hs : (linearClosure e E.commutant : Set (WeakDual ℂ X)) ⊆
        {f | (weakEquiv e).symm (E.entry i j*weakEquiv e f)=
             (weakEquiv e).symm (weakEquiv e f*E.entry i j)} := by
      apply closure_minimal _ hclosed
      rintro f ⟨a,ha,rfl⟩
      change (weakEquiv e).symm (E.entry i j*weakEquiv e ((weakEquiv e).symm a)) =
        (weakEquiv e).symm (weakEquiv e ((weakEquiv e).symm a)*E.entry i j)
      simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e).symm (ha i j).eq.symm
    have hh := (weakEquiv e).symm.injective (hs hx)
    change x*E.entry i j=E.entry i j*x
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  · intro x hx
    exact mem_linearClosure e E.commutant hx

def commutantPredual := X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)
instance : NormedAddCommGroup (E.commutantPredual e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)))
instance : NormedSpace ℂ (E.commutantPredual e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)))
instance [CompleteSpace X] : CompleteSpace (E.commutantPredual e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)))

def subalgebraIsoOfEq (A B : StarSubalgebra ℂ M) (h : A=B) : A ≃ₗᵢ[ℂ] B := by
  subst B
  exact LinearIsometryEquiv.refl ℂ A

def commutantPredualEquiv : StrongDual ℂ (E.commutantPredual e) ≃ₗᵢ⋆[ℂ] E.commutant :=
  (predualEquiv e E.commutant hL hR P hP).trans
    (subalgebraIsoOfEq _ _ (E.commutantClosure_eq e hL hR P hP))
end MatrixSystem
end HochschildMatrixSystems
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
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def reverseArguments {n : ℕ} (f : Cochain M n) : Cochain M n :=
  ContinuousMultilinearMap.domDomCongr Fin.revPerm f

lemma reverseArguments_apply {n : ℕ} (f : Cochain M n) (v : Fin n → M) :
    reverseArguments f v=f (v ∘ Fin.rev) := rfl

@[simp] lemma reverseArguments_norm {n : ℕ} (f : Cochain M n) : ‖reverseArguments f‖=‖f‖ :=
  ContinuousMultilinearMap.norm_domDomCongr ℂ M M _ _

def firstSliceN {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) : M →L[ℂ] M :=
  (reverseArguments f).curryRight (v ∘ Fin.rev)

@[simp] lemma firstSliceN_apply {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) (a : M) :
    firstSliceN f v a=f (Fin.cons a v) := by
  change reverseArguments f (Fin.snoc (v ∘ Fin.rev) a)=_
  rw [reverseArguments_apply,Fin.snoc_comp_rev]
  have hv : (v ∘ Fin.rev) ∘ Fin.rev=v := by
    ext i
    simp
  rw [hv]
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild

variable (M : Type*) [CStarAlgebra M]

def differentialLinearMap (k : ℕ) : Cochain M k →ₗ[ℂ] Cochain M (k+1) where
  toFun := differential
  map_add' f g := by
    ext v
    simp only [differential_apply, differentialValue_add, add_apply]
  map_smul' c f := by
    ext v
    simp only [differential_apply, differentialValue_smul, smul_apply, RingHom.id_apply]
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

def signScalar (b : Bool) : ℂ := if b then -1 else 1

lemma signScalar_xor (a b : Bool) : signScalar (a ^^ b) = signScalar a * signScalar b := by
  cases a <;> cases b <;> norm_num [signScalar]

@[simp] lemma signScalar_star (a : Bool) : star (signScalar a) = signScalar a := by
  cases a <;> simp [signScalar]

def signedPermutation (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : M :=
  ∑ i, signScalar (s i) • E.entry (σ i) i

lemma signedPermutation_one : E.signedPermutation 1 (fun _ => false) = 1 := by
  simpa only [signedPermutation, signScalar, Bool.false_eq_true, ↓reduceIte,
    one_smul, Equiv.Perm.one_apply] using E.sum_diagonal

lemma signedPermutation_mul (σ τ : Equiv.Perm (Fin n)) (s t : Fin n → Bool) :
    E.signedPermutation σ s * E.signedPermutation τ t =
      E.signedPermutation (σ * τ) (fun i => s (τ i) ^^ t i) := by
  classical
  simp only [signedPermutation, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    E.entry_mul, smul_ite, smul_zero]
  simp [signScalar_xor, Equiv.Perm.mul_apply]

lemma signedPermutation_star (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    star (E.signedPermutation σ s) =
      E.signedPermutation σ⁻¹ (fun i => s (σ⁻¹ i)) := by
  classical
  simp only [signedPermutation, star_sum, star_smul, signScalar_star, E.star_entry]
  apply Fintype.sum_equiv σ _ _
  intro i
  simp

lemma signedPermutation_mem_unitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    E.signedPermutation σ s ∈ unitary M := by
  constructor
  · rw [E.signedPermutation_star, E.signedPermutation_mul, inv_mul_cancel]
    simpa using E.signedPermutation_one
  · rw [E.signedPermutation_star, E.signedPermutation_mul, mul_inv_cancel]
    simpa only [Bool.xor_self] using E.signedPermutation_one

def signedPermutationUnitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : unitary M :=
  ⟨E.signedPermutation σ s, E.signedPermutation_mem_unitary σ s⟩

def signedPermutationGroup : Subgroup (unitary M) where
  carrier := Set.range (fun p : Equiv.Perm (Fin n) × (Fin n → Bool) =>
    E.signedPermutationUnitary p.1 p.2)
  one_mem' := ⟨(1, fun _ => false), Subtype.ext E.signedPermutation_one⟩
  mul_mem' := by
    rintro _ _ ⟨⟨σ, s⟩, rfl⟩ ⟨⟨τ, t⟩, rfl⟩
    exact ⟨(σ * τ, fun i => s (τ i) ^^ t i), Subtype.ext (E.signedPermutation_mul σ τ s t).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨σ, s⟩, rfl⟩
    exact ⟨(σ⁻¹, fun i => s (σ⁻¹ i)), Subtype.ext (E.signedPermutation_star σ s).symm⟩

instance signedPermutationGroup_finite : Finite E.signedPermutationGroup :=
  (Set.finite_range _).to_subtype

lemma signedPermutation_flip (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    E.signedPermutation σ (fun _ => false) -
      E.signedPermutation σ (fun k => decide (k = j)) = (2 : ℂ) • E.entry (σ j) j := by
  classical
  simp only [signedPermutation, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp [signScalar, two_smul]
  · intro k _ hkj
    simp [signScalar, hkj]
  · simp

lemma entry_mem_signedPermutation_span (i j : Fin n) :
    E.entry i j ∈ Submodule.span ℂ
      (Set.range (fun u : E.signedPermutationGroup => ((u : unitary M) : M))) := by
  classical
  let S := Submodule.span ℂ
    (Set.range (fun u : E.signedPermutationGroup => ((u : unitary M) : M)))
  have hmem (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : E.signedPermutation σ s ∈ S :=
    Submodule.subset_span ⟨⟨E.signedPermutationUnitary σ s, ⟨(σ, s), rfl⟩⟩, rfl⟩
  have hh := S.sub_mem (hmem (Equiv.swap j i) (fun _ => false))
    (hmem (Equiv.swap j i) (fun k => decide (k = j)))
  rw [E.signedPermutation_flip, Equiv.swap_apply_left] at hh
  have h := S.smul_mem (2⁻¹ : ℂ) hh
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using h

lemma neg_one_mem_signedPermutationGroup : (-1 : unitary M) ∈ E.signedPermutationGroup := by
  refine ⟨(1, fun _ => true), Subtype.ext ?_⟩
  change E.signedPermutation 1 (fun _ => true) = -1
  simp only [signedPermutation, signScalar, ↓reduceIte, neg_smul, one_smul,
    Equiv.Perm.one_apply, Finset.sum_neg_distrib, E.sum_diagonal]
end MatrixSystem
end HochschildMatrixSystems
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open scoped BigOperators

variable {M : Type*} [CommCStarAlgebra M]

private lemma split_same (a b q : M) (hq : IsStarProjection q) :
    (a * q) * (b * q) = (a * b) * q := by
  calc
    (a * q) * (b * q) = (a * b) * (q * q) := by ring
    _ = (a * b) * q := by rw [hq.isIdempotentElem.eq]

private lemma split_cross (a b q : M) (hq : IsStarProjection q) :
    (a * q) * (b * (1 - q)) = 0 := by
  have hzero : q * (1 - q) = 0 := by
    rw [mul_sub, mul_one, hq.isIdempotentElem.eq, sub_self]
  calc
    (a * q) * (b * (1 - q)) = (a * b) * (q * (1 - q)) := by ring
    _ = 0 := by rw [hzero, mul_zero]

private lemma decides_mul {r a : M} (h : r * a = 0 ∨ r * a = a) (b : M) :
    r * (a * b) = 0 ∨ r * (a * b) = a * b := by
  rcases h with h | h
  · exact Or.inl (by rw [← mul_assoc, h, zero_mul])
  · exact Or.inr (by rw [← mul_assoc, h])

theorem exists_refining_partition (S : Finset {q : M // IsStarProjection q}) :
    ∃ (n : ℕ) (p : Fin n → M),
      (∀ i, IsStarProjection (p i)) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧
      (∑ i, p i) = 1 ∧
      (∀ q ∈ S, ∀ i, q.val * p i = 0 ∨ q.val * p i = p i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 1, fun _ => IsStarProjection.one M, ?_, by simp, ?_⟩
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · simp
  | @insert q S _ ih =>
    obtain ⟨n, p, hp, ho, hsum, hdec⟩ := ih
    let parts : Fin (n + n) → M :=
      Fin.append (fun i => p i * q.val) (fun i => p i * (1 - q.val))
    refine ⟨n + n, parts, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [parts, Fin.append_left] using (hp j).mul q.property (Commute.all _ _)
      · simpa only [parts, Fin.append_right] using
          (hp j).mul q.property.one_sub (Commute.all _ _)
    · intro i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij
      · have hij' : i ≠ j := fun h => hij (congrArg (Fin.castAdd n) h)
        simp only [parts, Fin.append_left]
        change (p i * q.val) * (p j * q.val) = 0
        rw [split_same _ _ _ q.property, ho i j hij', zero_mul]
      · simp only [parts, Fin.append_left, Fin.append_right]
        exact split_cross _ _ _ q.property
      · simp only [parts, Fin.append_left, Fin.append_right]
        rw [mul_comm]
        exact split_cross _ _ _ q.property
      · have hij' : i ≠ j := fun h => hij (congrArg (Fin.natAdd n) h)
        simp only [parts, Fin.append_right]
        change (p i * (1 - q.val)) * (p j * (1 - q.val)) = 0
        rw [split_same _ _ _ q.property.one_sub, ho i j hij', zero_mul]
    · simp only [parts, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      ring
    · intro r hr i
      rcases Finset.mem_insert.mp hr with hrq | hr
      · subst r
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [parts, Fin.append_left]
          right
          calc
            q.val * (p j * q.val) = p j * (q.val * q.val) := by ring
            _ = p j * q.val := by rw [q.property.isIdempotentElem.eq]
        · simp only [parts, Fin.append_right]
          left
          calc
            q.val * (p j * (1 - q.val)) = p j * (q.val * (1 - q.val)) := by ring
            _ = 0 := by rw [mul_sub, mul_one, q.property.isIdempotentElem.eq, sub_self, mul_zero]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [parts, Fin.append_left] using decides_mul (hdec r hr j) q.val
        · simpa only [parts, Fin.append_right] using decides_mul (hdec r hr j) (1 - q.val)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild

variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem predual_tendsto_differential_of_predual
    {n : ℕ} {F : I → Cochain M n} {G : Cochain M n} {l : Filter I}
    (h : ∀ x, PredualTendsto e (fun i => F i x) l (G x))
    (x : Fin (n + 1) → M) :
    PredualTendsto e (fun i => differentialValue (F i) x) l (differentialValue G x) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact predual_tendsto_differential e (HochschildSakai.mul_hasPreadjoint e)
    (HochschildSakai.mul_right_hasPreadjoint e) h x
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

section FirstIdentity

variable {M : Type*} [CStarAlgebra M]

lemma mergeInputs_cons_zero {n : ℕ} (p : M) (v : Fin (n + 1) → M) :
    mergeInputs (Fin.cons p v) (0 : Fin (n + 1)) =
      Fin.cons (p * v 0) (fun i : Fin n => v i.succ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs]

lemma mergeInputs_cons_succ {n : ℕ} (p : M) (v : Fin (n + 1) → M)
    (j : Fin n) :
    mergeInputs (Fin.cons p v) j.succ = Fin.cons p (mergeInputs v j) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs, Fin.succ_lt_succ_iff]

lemma differentialValue_cons {n : ℕ} (f : Cochain M (n + 1))
    (p : M) (v : Fin (n + 1) → M) :
    differentialValue f (Fin.cons p v) =
      p * f v - f (Fin.cons (p * v 0) (fun i : Fin n => v i.succ)) -
        differentialValue (f.curryLeft p) v +
        v 0 * f (Fin.cons p (fun i : Fin n => v i.succ)) := by
  rw [differentialValue, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mergeInputs_cons_zero,
    mergeInputs_cons_succ, Fin.val_zero, zero_add, pow_one, neg_smul, one_smul,
    Fin.val_succ]
  have hi : (fun i : Fin (n + 1) => (Fin.cons p v : Fin (n + 2) → M) i.castSucc) =
      Fin.cons p (fun i : Fin n => v i.castSucc) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [hi]
  simp only [differentialValue, ContinuousMultilinearMap.curryLeft_apply]
  have hs (j : Fin n) : (-1 : ℂ) ^ (j.val + 1 + 1) = -((-1 : ℂ) ^ (j.val + 1)) := by
    rw [pow_succ]
    ring
  have hn : (-1 : ℂ) ^ (n + 2) = -((-1 : ℂ) ^ (n + 1)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  simp only [hs, hn, neg_smul, Finset.sum_neg_distrib]
  abel

lemma first_homotopy_identity {n : ℕ} (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) (p : M) (v : Fin (n + 1) → M) :
    differentialValue (f.curryLeft p) v =
      p * f v - f (Fin.cons (p * v 0) (fun i : Fin n => v i.succ)) +
        v 0 * f (Fin.cons p (fun i : Fin n => v i.succ)) := by
  have h := hf (Fin.cons p v)
  rw [differentialValue_cons] at h
  symm
  apply sub_eq_zero.mp
  convert h using 1
  abel
end FirstIdentity
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma differentialValue_leftOutput {n : ℕ} (b : M) (f : Cochain M n)
    (x : Fin (n + 1) → M) :
    differentialValue (centralOutput b f) x =
      b * differentialValue f x +
        (x 0 * b - b * x 0) * f (fun i => x i.succ) := by
  simp only [differentialValue, centralOutput_apply, mul_add,
    Finset.mul_sum, mul_smul_comm, mul_assoc]
  noncomm_ring

lemma first_separability_identity {n : ℕ} (a b : M) (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) (x : Fin (n + 1) → M) :
    differentialValue (centralOutput a (f.curryLeft b)) x =
      a * b * f x - a * f (Fin.cons (b * x 0) (fun i => x i.succ)) +
        x 0 * a * f (Fin.cons b (fun i => x i.succ)) := by
  rw [differentialValue_leftOutput, first_homotopy_identity f hf]
  simp only [ContinuousMultilinearMap.curryLeft_apply]
  noncomm_ring

variable {G : Type*} [Group G] [Fintype G]

private lemma unitary_norm_le (u : unitary M) : ‖(u : M)‖ ≤ 1 := by
  nontriviality M
  exact (CStarRing.norm_coe_unitary u).le

def finiteUnitaryHomotopy (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) : Cochain M n :=
  (Fintype.card G : ℂ)⁻¹ •
    ∑ u : G, centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))

lemma finiteUnitaryHomotopy_norm (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) : ‖finiteUnitaryHomotopy ρ f‖ ≤ ‖f‖ := by
  have hterm (u : G) :
      ‖centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))‖ ≤ ‖f‖ := by
    apply (norm_centralOutput_le _ (unitary_norm_le _) _).trans
    calc
      ‖f.curryLeft (ρ u⁻¹ : M)‖ ≤ ‖f.curryLeft‖ * ‖(ρ u⁻¹ : M)‖ :=
        f.curryLeft.le_opNorm _
      _ ≤ ‖f‖ := by
        rw [ContinuousMultilinearMap.curryLeft_norm]
        exact (mul_le_mul_of_nonneg_left (unitary_norm_le _) (norm_nonneg _)).trans_eq
          (mul_one _)
  have hc : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  calc
    ‖finiteUnitaryHomotopy ρ f‖ =
        (Fintype.card G : ℝ)⁻¹ *
          ‖∑ u : G, centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))‖ := by
      simp only [finiteUnitaryHomotopy, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ((Fintype.card G : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun u _ => hterm u))
    _ = ‖f‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

lemma finiteUnitaryHomotopy_exact_unitary (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0)
    (v : G) (x : Fin n → M) :
    differentialValue (finiteUnitaryHomotopy ρ f) (Fin.cons (ρ v : M) x) =
      f (Fin.cons (ρ v : M) x) := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hu (u : G) : (ρ u : M) * (ρ u⁻¹ : M) = 1 := by
    rw [← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one, Submonoid.coe_one]
  have hsum :
      (∑ u : G, (ρ u : M) * f (Fin.cons ((ρ u⁻¹ : M) * (ρ v : M)) x)) =
      ∑ u : G, (ρ v : M) * (ρ u : M) * f (Fin.cons (ρ u⁻¹ : M) x) := by
    apply Fintype.sum_equiv (Equiv.mulLeft v⁻¹) _ _
    intro u
    change (ρ u : M) * f (Fin.cons ((ρ u⁻¹ : M) * (ρ v : M)) x) =
      (ρ v : M) * (ρ (v⁻¹ * u) : M) * f (Fin.cons (ρ (v⁻¹ * u)⁻¹ : M) x)
    have hcancel : (ρ v : M) * (ρ (v⁻¹ * u) : M) = (ρ u : M) := by
      change ((ρ v * ρ (v⁻¹ * u) : unitary M) : M) = _
      rw [← map_mul, mul_inv_cancel_left]
    rw [hcancel, mul_inv_rev, inv_inv, map_mul, Submonoid.coe_mul]
  rw [finiteUnitaryHomotopy, differentialValue_smul]
  have hd : differentialValue
      (∑ u : G, centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M)))
      (Fin.cons (ρ v : M) x) =
      ∑ u : G, differentialValue
        (centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))) (Fin.cons (ρ v : M) x) := by
    have hh := map_sum (differentialLinearMap M n)
      (fun u : G => centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))) Finset.univ
    have he := congrArg (fun g : Cochain M (n + 1) => g (Fin.cons (ρ v : M) x)) hh
    change (differential _) _ = (∑ u : G, differential _) _ at he
    simpa only [sum_apply, differential_apply] using he
  rw [hd]
  simp only [first_separability_identity _ _ f hf, hu, one_mul, Fin.cons_zero,
    Fin.cons_succ, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, sub_add_cancel,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma finiteUnitaryHomotopy_exact_span (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0)
    {a : M} (ha : a ∈ Submodule.span ℂ (Set.range (fun u : G => (ρ u : M))))
    (x : Fin n → M) :
    differentialValue (finiteUnitaryHomotopy ρ f) (Fin.cons a x) = f (Fin.cons a x) := by
  let L := firstSliceN (differential (finiteUnitaryHomotopy ρ f) - f) x
  have hker : Submodule.span ℂ (Set.range (fun u : G => (ρ u : M))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    change L (ρ u : M) = 0
    simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using
      sub_eq_zero.mpr (finiteUnitaryHomotopy_exact_unitary ρ f hf u x)
  have h := hker ha
  change L a = 0 at h
  exact sub_eq_zero.mp (by
    simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using h)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

variable {M I G : Type*} [CStarAlgebra M] [Fintype I]
  [Group G]
  (p : I → M) (hp : ∀ i, IsStarProjection (p i))
  (hc : ∀ i a, p i * a = a * p i)
  (ho : ∀ i j, i ≠ j → p i * p j = 0)
  (hs : ∑ i, p i = 1)

def centralBlock (a : I → M) : M := ∑ i, p i * a i

include hp hc ho in
lemma centralBlock_mul (a b : I → M) :
    centralBlock p a * centralBlock p b = centralBlock p (fun i => a i * b i) := by
  classical
  have ht (i j : I) : (p i * a i) * (p j * b j) =
      if i = j then p i * (a i * b i) else 0 := by
    have he : (p i * a i) * (p j * b j) = (p i * p j) * (a i * b j) := by
      calc
        _ = p i * (a i * p j) * b j := by noncomm_ring
        _ = p i * (p j * a i) * b j := by rw [hc j (a i)]
        _ = _ := by noncomm_ring
    rw [he]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, (hp i).isIdempotentElem.eq]
    · rw [ite_eq_right hij, ho i j hij, zero_mul]
  simp [centralBlock, Finset.sum_mul, Finset.mul_sum, ht]

include hp hc in
lemma centralBlock_star (a : I → M) :
    star (centralBlock p a) = centralBlock p (fun i => star (a i)) := by
  simp only [centralBlock, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hp i).isSelfAdjoint.star_eq, hc]

include hs in
lemma centralBlock_one : centralBlock p (fun _ => 1) = 1 := by
  simpa only [centralBlock, mul_one] using hs

variable (ρ : G →* unitary M)

include hp hc ho hs in
lemma centralBlock_mem_unitary (a : I → G) :
    centralBlock p (fun i => (ρ (a i) : M)) ∈ unitary M := by
  constructor
  · rw [centralBlock_star p hp hc, centralBlock_mul p hp hc ho]
    simpa only [Unitary.coe_star_mul_self] using centralBlock_one p hs
  · rw [centralBlock_star p hp hc, centralBlock_mul p hp hc ho]
    have hm (i : I) : (ρ (a i) : M) * star (ρ (a i) : M) = 1 :=
      Unitary.mul_star_self_of_mem (ρ (a i)).property
    simpa only [hm] using centralBlock_one p hs

def centralBlockHom : (I → G) →* unitary M where
  toFun a := ⟨centralBlock p (fun i => (ρ (a i) : M)),
    centralBlock_mem_unitary p hp hc ho hs ρ a⟩
  map_one' := Subtype.ext (by
    simpa only [Pi.one_apply, map_one, Submonoid.coe_one] using centralBlock_one p hs)
  map_mul' a b := Subtype.ext (by
    simpa only [Pi.mul_apply, map_mul, Submonoid.coe_mul] using
      (centralBlock_mul p hp hc ho (fun i => (ρ (a i) : M))
        (fun i => (ρ (b i) : M))).symm)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

variable {M I G : Type*} [CStarAlgebra M] [Fintype I] [Group G]
  (p : I → M) (hp : ∀ i, IsStarProjection (p i))
  (hc : ∀ i a, p i * a = a * p i)
  (ho : ∀ i j, i ≠ j → p i * p j = 0)
  (hs : ∑ i, p i = 1) (ρ : G →* unitary M)

def centralBlockSpan : Submodule ℂ M := Submodule.span ℂ
  (Set.range (fun a : I → G => (centralBlockHom p hp hc ho hs ρ a : M)))

lemma centralBlock_unitary_mem_span (a : I → G) :
    centralBlock p (fun i => (ρ (a i) : M)) ∈ centralBlockSpan p hp hc ho hs ρ :=
  Submodule.subset_span ⟨a, rfl⟩

lemma centralBlock_component_mem_span (j : I) (g z : G) (hz : (ρ z : M) = -1) :
    p j * (ρ g : M) ∈ centralBlockSpan p hp hc ho hs ρ := by
  classical
  let a : I → G := fun _ => g
  let b : I → G := Function.update a j (z * g)
  have hdiff : centralBlock p (fun i => (ρ (a i) : M)) -
      centralBlock p (fun i => (ρ (b i) : M)) = (2 : ℂ) • (p j * (ρ g : M)) := by
    rw [centralBlock, centralBlock, ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp only [a, b, Function.update_self, map_mul, Submonoid.coe_mul, hz,
        neg_one_mul, mul_neg, sub_neg_eq_add, two_smul]
    · intro k _ hkj
      simp only [b, Function.update_of_ne hkj, sub_self]
    · simp
  have h := (centralBlockSpan p hp hc ho hs ρ).sub_mem
    (centralBlock_unitary_mem_span p hp hc ho hs ρ a)
    (centralBlock_unitary_mem_span p hp hc ho hs ρ b)
  rw [hdiff] at h
  have h' := (centralBlockSpan p hp hc ho hs ρ).smul_mem (2⁻¹ : ℂ) h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using h'

lemma centralBlock_mul_mem_span (j : I) (z : G) (hz : (ρ z : M) = -1)
    {a : M} (ha : a ∈ Submodule.span ℂ (Set.range (fun g : G => (ρ g : M)))) :
    p j * a ∈ centralBlockSpan p hp hc ho hs ρ := by
  let S := (centralBlockSpan p hp hc ho hs ρ).comap
    (ContinuousLinearMap.mul ℂ M (p j)).toLinearMap
  have hle : Submodule.span ℂ (Set.range (fun g : G => (ρ g : M))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact centralBlock_component_mem_span p hp hc ho hs ρ j g z hz
  exact hle ha
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

lemma commutant_central (hcomm : ∀ a b : E.commutant, Commute a b)
    (a : E.commutant) (x : M) : (a : M) * x = x * (a : M) := by
  have hc : Commute (a : M) x := by
    rw [← E.reconstruct x]
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro j _
    exact (a.property i j).mul_right (show Commute (a : M) (E.coefficient i j x) from
      congrArg (fun z : E.commutant => (z : M))
        (hcomm a ⟨_, E.coefficient_mem i j x⟩).eq)
  exact hc.eq

lemma commutant_commutative_of_abelian_diagonal (i : Fin n)
    (hi : FinitePathMain.AbelianProjection (E.entry i i)) :
    ∀ a b : E.commutant, Commute a b := by
  intro a b
  have hcut (a : E.commutant) : E.entry i i * (a : M) * E.entry i i =
      E.entry i i * (a : M) := by
    rw [mul_assoc, (a.property i i).eq, ← mul_assoc, (E.diagonal_proj i).isIdempotentElem.eq]
  have hprod (a b : E.commutant) :
      (E.entry i i * (a : M)) * (E.entry i i * (b : M)) =
        E.entry i i * ((a : M) * (b : M)) := by
    calc
      _ = (E.entry i i * (a : M) * E.entry i i) * (b : M) := by noncomm_ring
      _ = _ := by rw [hcut]; noncomm_ring
  have h := hi.2 (a : M) (b : M)
  change (E.entry i i * (a : M) * E.entry i i) *
      (E.entry i i * (b : M) * E.entry i i) =
    (E.entry i i * (b : M) * E.entry i i) *
      (E.entry i i * (a : M) * E.entry i i) at h
  simp only [hcut, hprod] at h
  have he := congrArg (E.coefficient i i) h
  change E.coefficient i i (E.entry i i * ((a * b : E.commutant) : M)) =
    E.coefficient i i (E.entry i i * ((b * a : E.commutant) : M)) at he
  rw [E.coefficient_of_commutant i (a * b).property,
    E.coefficient_of_commutant i (b * a).property] at he
  exact Subtype.ext he
end MatrixSystem
end HochschildMatrixSystems
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

open BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] {n r : ℕ} (E : MatrixSystem M n)
  (hcomm : ∀ a b : E.commutant, Commute a b)
  (p : Fin r → E.commutant) (hp : ∀ j, IsStarProjection (p j))
  (ho : ∀ i j, i ≠ j → p i * p j = 0) (hs : ∑ j, p j = 1)

include hp in
lemma partition_coe_projection (j : Fin r) : IsStarProjection (p j : M) := by
  constructor
  · exact congrArg Subtype.val (hp j).isIdempotentElem.eq
  · exact congrArg Subtype.val (hp j).isSelfAdjoint.star_eq

include ho in
lemma partition_coe_orthogonal (i j : Fin r) (hij : i ≠ j) :
    (p i : M) * (p j : M) = 0 := congrArg Subtype.val (ho i j hij)

include hs in
lemma partition_coe_sum : ∑ j, (p j : M) = 1 := by
  simpa using congrArg (fun a : E.commutant => (a : M)) hs

def matrixBlockHom : (Fin r → E.signedPermutationGroup) →* unitary M :=
  centralBlockHom (fun j => (p j : M)) (E.partition_coe_projection p hp)
    (fun j => E.commutant_central hcomm (p j)) (E.partition_coe_orthogonal p ho)
    (E.partition_coe_sum p hs) E.signedPermutationGroup.subtype

def matrixBlockSpan : Submodule ℂ M := Submodule.span ℂ
  (Set.range (fun a : Fin r → E.signedPermutationGroup =>
    (E.matrixBlockHom hcomm p hp ho hs a : M)))

lemma matrixBlock_entry_mem_span (j : Fin r) (a b : Fin n) :
    (p j : M) * E.entry a b ∈ E.matrixBlockSpan hcomm p hp ho hs := by
  exact centralBlock_mul_mem_span (fun j => (p j : M)) (E.partition_coe_projection p hp)
    (fun j => E.commutant_central hcomm (p j)) (E.partition_coe_orthogonal p ho)
    (E.partition_coe_sum p hs) E.signedPermutationGroup.subtype j
    ⟨-1, E.neg_one_mem_signedPermutationGroup⟩ rfl (E.entry_mem_signedPermutation_span a b)

lemma matrixBlock_refined_entry_mem_span (q : E.commutant)
    (hq : ∀ j, q * p j = 0 ∨ q * p j = p j) (a b : Fin n) :
    (q : M) * E.entry a b ∈ E.matrixBlockSpan hcomm p hp ho hs := by
  have he : (q : M) * E.entry a b =
      ∑ j, ((q : M) * (p j : M)) * E.entry a b := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, E.partition_coe_sum p hs, mul_one]
  rw [he]
  apply Submodule.sum_mem
  intro j _
  rcases hq j with hj | hj
  · have he := congrArg Subtype.val hj
    change (q : M) * (p j : M) = 0 at he
    rw [he, zero_mul]
    exact Submodule.zero_mem _
  · have he := congrArg Subtype.val hj
    change (q : M) * (p j : M) = (p j : M) at he
    rw [he]
    exact E.matrixBlock_entry_mem_span hcomm p hp ho hs j a b
end MatrixSystem
end HochschildMatrixSystems
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildMatrixSystems HochschildSakai

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_homogeneous_typeI_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {d : ℕ} (E : MatrixSystem M d) (hcomm : ∀ a b : E.commutant, Commute a b)
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  classical
  let : CommCStarAlgebra E.commutant := { mul_comm := fun a b => (hcomm a b).eq }
  obtain ⟨P, _, hP⟩ := exists_abstract_star_preadjoint e
  let eC := E.commutantPredualEquiv e (mul_hasPreadjoint e)
    (mul_right_hasPreadjoint e) P hP
  let Q := {q : E.commutant // IsStarProjection q}
  choose r p hp ho hs href using fun S : Finset Q => exists_refining_partition S
  let := Fintype.ofFinite E.signedPermutationGroup
  let F (S : Finset Q) : Cochain M n := finiteUnitaryHomotopy
    (E.matrixBlockHom hcomm (p S) (hp S) (ho S) (hs S)) f
  have hFn (S : Finset Q) : ‖F S‖ ≤ ‖f‖ := finiteUnitaryHomotopy_norm _ f
  let U : Ultrafilter (Finset Q) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset Q)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨g, hgn, ht⟩ := bounded_cochain_ultralimit e U F ‖f‖ (norm_nonneg _) hFn
  have hproj (q : Q) (a b : Fin d) (x : Fin n → M) :
      differentialValue g (Fin.cons ((q.val : M) * E.entry a b) x) =
        f (Fin.cons ((q.val : M) * E.entry a b) x) := by
    have he : (fun S => differentialValue (F S)
        (Fin.cons ((q.val : M) * E.entry a b) x)) =ᶠ[U]
        (fun _ => f (Fin.cons ((q.val : M) * E.entry a b) x)) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({q} : Finset Q)] with S hS
      exact finiteUnitaryHomotopy_exact_span _ f hf
        (E.matrixBlock_refined_entry_mem_span hcomm (p S) (hp S) (ho S) (hs S) q.val
          (href S q (hS (Finset.mem_singleton_self q))) a b) x
    apply predual_tendsto_unique e (predual_tendsto_differential_of_predual e ht _)
    intro z
    exact tendsto_const_nhds.congr' (he.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  refine ⟨g, hgn, fun x => ?_⟩
  let L := firstSliceN (differential g - f) (Fin.tail x)
  have hcoord (a b : Fin d) (c : E.commutant) : L ((c : M) * E.entry a b) = 0 := by
    let T : E.commutant →L[ℂ] M := L.comp
      (((ContinuousLinearMap.mul ℂ M).flip (E.entry a b)).comp
        E.commutant.toSubalgebra.toSubmodule.subtypeL)
    have hspan : Submodule.span ℂ {q : E.commutant | IsStarProjection q} ≤ T.ker := by
      apply Submodule.span_le.mpr
      intro q hq
      change L ((q : M) * E.entry a b) = 0
      simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using
        sub_eq_zero.mpr (hproj ⟨q, hq⟩ a b (Fin.tail x))
    have hclosed := Submodule.topologicalClosure_minimal _ hspan T.isClosed_ker
    rw [projection_span_dense eC] at hclosed
    exact hclosed (Submodule.mem_top : c ∈ (⊤ : Submodule ℂ E.commutant))
  have hzero : L (x 0) = 0 := by
    rw [← E.reconstruct (x 0), map_sum]
    apply Finset.sum_eq_zero
    intro a _
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro b _
    have h := hcoord a b ⟨_, E.coefficient_mem a b (x 0)⟩
    simpa only [(E.coefficient_mem a b (x 0) a b).eq] using h
  apply sub_eq_zero.mp
  simpa only [L, firstSliceN_apply, sub_apply, differential_apply, Fin.cons_self_tail] using hzero

theorem finite_homogeneous_typeI_primitive_of_abelian_diagonal
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {d : ℕ} (E : MatrixSystem M d) (i : Fin d)
    (hi : FinitePathMain.AbelianProjection (E.entry i i))
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  finite_homogeneous_typeI_primitive e E (E.commutant_commutative_of_abelian_diagonal i hi) f hf
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.finite_homogeneous_typeI_primitive_of_abelian_diagonal.{u} := @OAI.BoundedHochschild.KadisonRingrose.finite_homogeneous_typeI_primitive_of_abelian_diagonal.{u}
