-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.primitive_of_algebraic_matrix_multimodular
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:21:41.940736+00:00
-- url     : https://prove2.me/submissions/bed85e07-0713-4219-9105-e92076d6393e

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_weakRightAverageOrbit_subset_ball
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_finite_right_module_average
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normal_reduction_multimodular

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

theorem snoc_succ_tuple {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    (fun i : Fin (n + 1) => (Fin.snoc v u : Fin (n + 2) → M) i.succ) =
      Fin.snoc (fun i : Fin n => v i.succ) u := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [← Fin.castSucc_succ, Fin.snoc_castSucc]

theorem snoc_castSucc_tuple {n : ℕ} (v : Fin n → M) (u : M) :
    (fun i : Fin n => (Fin.snoc v u : Fin (n + 1) → M) i.castSucc) = v := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ => M) u v i

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

section CocycleIdentity
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

theorem differentialValue_snoc {n : ℕ} (f : Cochain M (n + 1))
    (v : Fin (n + 1) → M) (u : M) :
    differentialValue f (Fin.snoc v u) =
      v 0 * f (Fin.snoc (fun i : Fin n => v i.succ) u) +
      (∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (Fin.snoc (mergeInputs v j) u)) +
      ((-1 : ℂ) ^ (n + 1)) •
        f (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u)) +
      ((-1 : ℂ) ^ (n + 2)) • (f v * u) := by
  rw [differentialValue, snoc_succ_tuple, snoc_castSucc_tuple, Fin.sum_univ_castSucc]
  simp only [mergeInputs_snoc_castSucc, Fin.val_castSucc, mergeInputs_snoc_last,
    Fin.val_last, Fin.snoc_last]
  have hzero : (Fin.snoc v u : Fin (n + 2) → M) 0 = v 0 := by
    exact Fin.snoc_castSucc (α := fun _ => M) u v 0
  rw [hzero]
  abel
end CocycleIdentity
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

theorem predual_tendsto_mul_left (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => a*b i) l (a*c) :=
  HasPreadjoint.tendsto e (mul_hasPreadjoint e a) hb

theorem predual_tendsto_mul_right (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => b i*a) l (c*a) :=
  HasPreadjoint.tendsto e (mul_right_hasPreadjoint e a) hb

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

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (S : Set M) (hne : S.Nonempty)
    (hchain : IsChain (· ≤ ·) S) (hproj : ∀ q ∈ S, IsStarProjection q) :
    ∃ p : M, IsStarProjection p ∧ (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) ∧
      ∃ U : Ultrafilter S, (U : Filter S) ≤ atTop ∧
        PredualTendsto e (fun q : S => (q : M)) (U : Filter S) p := by
  classical
  let : Nonempty S := hne.to_subtype
  let : IsDirectedOrder S := ⟨fun a b => by
    rcases hchain.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter S := Ultrafilter.of atTop
  have hU : (U : Filter S) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨p, _, ht⟩ := exists_predual_ultralimit e U (fun q : S => (q : M)) 1
    (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  have hp : IsStarProjection p := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e p ht
      have heq : (fun q : S => (q : M) * p) = (fun q : S => (q : M)) :=
        funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun q : S => star (q : M)) = (fun q : S => (q : M)) := by
        funext q
        exact (hproj q q.property).isSelfAdjoint.star_eq
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨p, hp, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hu
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hu q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) :=
      funext fun q => ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))
end KadisonRingrose
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
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

namespace PartialIso

lemma final_mul (v : PartialIso M) : v.final * (v : M) = v := v.mul_star_mul

lemma final_proj (v : PartialIso M) : IsStarProjection v.final := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self _⟩
  change ((v : M) * star (v : M)) * ((v : M) * star (v : M)) = (v : M) * star (v : M)
  calc
    _ = ((v : M) * star (v : M) * v) * star (v : M) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]
lemma norm_le_one (v : PartialIso M) : ‖(v : M)‖ ≤ 1 := by
  have hi := v.initial_proj.norm_le _
  have he : ‖(v : M)‖ * ‖(v : M)‖ = ‖v.initial‖ := by
    exact CStarRing.norm_star_mul_self.symm
  nlinarith [norm_nonneg (v : M)]

variable [PartialOrder M]

variable [StarOrderedRing M]

omit [StarOrderedRing M] in
lemma initial_mono {v w : PartialIso M} (h : v ≤ w) : v.initial ≤ w.initial := h.1

lemma star_mul_of_le {v w : PartialIso M} (h : v ≤ w) : star (v : M) * w = v.initial := by
  have hv := congrArg star h.2
  simp only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] at hv
  calc
    star (v : M) * w = (v.initial * star (w : M)) * w := by rw [hv]
    _ = v.initial * w.initial := by simp only [initial,mul_assoc]
    _ = v.initial := (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp h.1
lemma star_mul_of_ge {v w : PartialIso M} (h : v ≤ w) : star (w : M) * v = v.initial := by
  simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
    using congrArg star (star_mul_of_le h)
lemma final_mono {v w : PartialIso M} (h : v ≤ w) : v.final ≤ w.final := by
  apply (v.final_proj.le_iff_mul_eq_right w.final_proj).mpr
  calc
    w.final * v.final = (w : M) * (star (w : M) * v) * star (v : M) := by
      simp only [final,mul_assoc]
    _ = (w : M) * v.initial * star (v : M) := by rw [star_mul_of_ge h]
    _ = v.final := by rw [h.2]; rfl

section
omit [PartialOrder M] [StarOrderedRing M]

lemma star_mul_eq_zero_of_final_orthogonal {v w : PartialIso M}
    (h : v.final*w.final=0) : star (v : M)*w=0 := by
  have hv : star (v : M)*v.final=star (v : M) := by
    simpa only [star_mul,star_star,v.final_proj.isSelfAdjoint.star_eq]
      using congrArg star v.final_mul
  calc
    star (v : M)*w = (star (v : M)*v.final)*(w.final*(w : M)) := by
      rw [hv,w.final_mul]
    _ = star (v : M)*(v.final*w.final)*(w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma mul_star_eq_zero_of_initial_orthogonal {v w : PartialIso M}
    (h : v.initial*w.initial=0) : (v : M)*star (w : M)=0 := by
  have hw : w.initial*star (w : M)=star (w : M) := by
    simpa only [star_mul,star_star,w.initial_proj.isSelfAdjoint.star_eq]
      using congrArg star w.mul_initial
  calc
    (v : M)*star (w : M) = ((v : M)*v.initial)*(w.initial*star (w : M)) := by
      rw [v.mul_initial,hw]
    _ = (v : M)*(v.initial*w.initial)*star (w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma orthogonal_initial_symm {v w : PartialIso M} (h : v.initial*w.initial=0) :
    w.initial*v.initial=0 := by
  simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
    w.initial_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h
lemma orthogonal_final_symm {v w : PartialIso M} (h : v.final*w.final=0) :
    w.final*v.final=0 := by
  simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : PartialIso M where
  val := (v : M)+w
  mul_star_mul := by
    have hab := mul_star_eq_zero_of_initial_orthogonal hi
    have hba := mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi)
    have hab' := star_mul_eq_zero_of_final_orthogonal hf
    have hba' := star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf)
    simp only [star_add,mul_add,add_mul,hab,hba,zero_add,add_zero]
    rw [v.mul_star_mul,w.mul_star_mul,mul_assoc,mul_assoc,hab',hba',mul_zero,mul_zero]
    abel

lemma orthogonalSum_initial (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).initial=v.initial+w.initial := by
  change star ((v : M)+w)*((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,star_mul_eq_zero_of_final_orthogonal hf,
    star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf),zero_add,add_zero,initial]
lemma orthogonalSum_final (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).final=v.final+w.final := by
  change ((v : M)+w)*star ((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,mul_star_eq_zero_of_initial_orthogonal hi,
    mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi),zero_add,add_zero,final]
end
end PartialIso
end HochschildComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_partialIso_chain_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ w : PartialIso M, (∀ v ∈ c, v ≤ w) ∧
      (∀ z : PartialIso M, (∀ v ∈ c, v ≤ z) → w ≤ z) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.initial ≤ r) → w.initial ≤ r) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.final ≤ r) → w.final ≤ r) := by
  classical
  let S : Set M := PartialIso.initial '' c
  have hSne : S.Nonempty := hne.image _
  have hSchain : IsChain (· ≤ ·) S := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ _
    exact (hc.total hv hw).imp PartialIso.initial_mono PartialIso.initial_mono
  have hSproj : ∀ r ∈ S, IsStarProjection r := by
    rintro _ ⟨v, _, rfl⟩
    exact v.initial_proj
  obtain ⟨p, hp, hupper, hleast, hann, _⟩ :=
    exists_projection_chain_supremum_with_limit e S hSne hSchain hSproj
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := ⟨fun a b => by
    rcases hc.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter c := Ultrafilter.of atTop
  have hU : (U : Filter c) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨V, _, ht⟩ := exists_predual_ultralimit e U
    (fun v : c => ((v : PartialIso M) : M)) 1 (fun v => v.val.norm_le_one)
  have hVi (v : c) : V * v.val.initial = (v.val : M) := by
    have hm := HochschildSakai.predual_tendsto_mul_right e v.val.initial ht
    have heq : (fun w : c => (w.val : M) * v.val.initial) =ᶠ[U]
        (fun _ => (v.val : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact hvw.2
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hstarVi (v : c) : star V * (v.val : M) = v.val.initial := by
    have hm := HochschildSakai.predual_tendsto_mul_right e (v.val : M)
      (HochschildSakai.predual_tendsto_star e ht)
    have heq : (fun w : c => star (w.val : M) * (v.val : M)) =ᶠ[U]
        (fun _ => v.val.initial) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact PartialIso.star_mul_of_ge hvw
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hVp : V * p = V := by
    have hm := HochschildSakai.predual_tendsto_mul_right e p ht
    have heq : (fun v : c => (v.val : M) * p) =
        (fun v : c => (v.val : M)) := by
      funext v
      calc
        (v.val : M) * p = ((v.val : M) * v.val.initial) * p := by
          rw [v.val.mul_initial]
        _ = (v.val : M) := by
          rw [mul_assoc, (v.val.initial_proj.le_iff_mul_eq_left hp).mp
            (hupper _ ⟨v.val, v.property, rfl⟩), v.val.mul_initial]
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  have hpstar : p * star V = star V := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hVp
  have hVV : star V * V = p := by
    have hann' : p * (star V * V - p) = 0 := by
      apply hann
      rintro _ ⟨v, hv, rfl⟩
      have hfixed : v.initial * (star V * V) = v.initial := by
        have hs : v.initial * star V = star (v : M) := by
          simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] using
            congrArg star (hVi ⟨v, hv⟩)
        calc
          v.initial * (star V * V) = star (v : M) * V := by rw [← mul_assoc, hs]
          _ = v.initial := by
            simpa only [star_mul, star_star, v.initial_proj.isSelfAdjoint.star_eq]
              using congrArg star (hstarVi ⟨v, hv⟩)
      rw [mul_sub, hfixed, (v.initial_proj.le_iff_mul_eq_left hp).mp
        (hupper _ ⟨v, hv, rfl⟩), sub_self]
    rw [mul_sub, ← mul_assoc, hpstar, hp.isIdempotentElem.eq] at hann'
    exact sub_eq_zero.mp hann'
  let w : PartialIso M := ⟨V, by rw [mul_assoc, hVV, hVp]⟩
  have hwi : w.initial = p := hVV
  have hwupper : ∀ v ∈ c, v ≤ w := by
    intro v hv
    exact ⟨by rw [hwi]; exact hupper _ ⟨v, hv, rfl⟩, hVi ⟨v, hv⟩⟩
  refine ⟨w, hwupper, ?_, ?_, ?_⟩
  · intro z hz
    have hpz : p ≤ z.initial := by
      apply hleast z.initial z.initial_proj
      rintro _ ⟨v, hv, rfl⟩
      exact (hz v hv).1
    have hzp : (z : M) * p = V := by
      have ha : p * star ((z : M) - V) = 0 := by
        apply hann
        rintro _ ⟨v, hv, rfl⟩
        have heq : ((z : M) - V) * v.initial = 0 := by
          rw [sub_mul, (hz v hv).2, hVi ⟨v, hv⟩, sub_self]
        simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq, star_zero]
          using congrArg star heq
      have ha' : ((z : M) - V) * p = 0 := by
        simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq, star_zero]
          using congrArg star ha
      rwa [sub_mul, hVp, sub_eq_zero] at ha'
    exact ⟨by rw [hwi]; exact hpz, by change (z : M) * w.initial = V; rw [hwi, hzp]⟩
  · intro r hr hb
    rw [hwi]
    apply hleast r hr
    rintro _ ⟨v, hv, rfl⟩
    exact hb v hv
  · intro r hr hb
    have hrV : r * V = V := by
      have hm := HochschildSakai.predual_tendsto_mul_left e r ht
      have heq : (fun v : c => r * (v.val : M)) =
          (fun v : c => (v.val : M)) := by
        funext v
        calc
          r * (v.val : M) = r * (v.val.final * (v.val : M)) := by rw [v.val.final_mul]
          _ = (v.val : M) := by
            rw [← mul_assoc, (v.val.final_proj.le_iff_mul_eq_right hr).mp
              (hb v.val v.property), v.val.final_mul]
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    apply (w.final_proj.le_iff_mul_eq_right hr).mpr
    change r * (V * star V) = V * star V
    rw [← mul_assoc, hrV]
end KadisonRingrose
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
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma HasPreadjoint.comp {S T : M →L[ℂ] M}
    (hS : HasPreadjoint e S) (hT : HasPreadjoint e T) : HasPreadjoint e (S.comp T) := by
  intro z
  obtain ⟨w,hw⟩ := hS z
  obtain ⟨y,hy⟩ := hT w
  exact ⟨y,fun a => (hw (T a)).trans (hy a)⟩
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildRigidity HochschildDiffuse HochschildComparison
open FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_orthogonal_of_le_complement {s c : M}
    (hs : IsStarProjection s) (hc : IsStarProjection c) (hcs : c ≤ 1-s) : s*c=0 := by
  have h := (hc.le_iff_mul_eq_right hs.one_sub).mp hcs
  rw [sub_mul,one_mul] at h
  exact sub_eq_self.mp h
end HochschildTypeII
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v}

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_finset_sum (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (s : Finset I) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply (hp i).add ih
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j (fun hij => his (hij ▸ hj))

lemma orthogonal_projection_sum_annihilator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (a P : M)
    (ht : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, p i) atTop P)
    (hpa : ∀ i, p i * a = 0) : P * a = 0 := by
  classical
  have hm := HochschildSakai.predual_tendsto_mul_right e a ht
  have heq : (fun s : Finset I => (∑ i ∈ s, p i) * a) = fun _ => (0 : M) := by
    funext s
    rw [Finset.sum_mul]
    simp only [hpa, Finset.sum_const_zero]
  rw [heq] at hm
  exact predual_tendsto_unique e hm (predual_tendsto_const e 0 atTop)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*}

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIso_finset_sum_data (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) :
    ∃ w : PartialIso M, (w : M) = ∑ i ∈ s, (v i : M) ∧
      w.initial = ∑ i ∈ s, (v i).initial ∧ w.final = ∑ i ∈ s, (v i).final := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | @insert i s his ih =>
      obtain ⟨w, hw, hwi, hwf⟩ := ih
      have hI : (v i).initial * w.initial = 0 := by
        rw [hwi, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hi i j (fun h => his (h ▸ hj)))
      have hF : (v i).final * w.final = 0 := by
        rw [hwf, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hf i j (fun h => his (h ▸ hj)))
      refine ⟨(v i).orthogonalSum w hI hF, ?_, ?_, ?_⟩
      · change (v i : M) + (w : M) = _
        rw [hw, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_initial, hwi, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_final, hwf, Finset.sum_insert his]

def partialIsoFinsetSum (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) : PartialIso M :=
  (partialIso_finset_sum_data v hi hf s).choose

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_coe (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s : M) = ∑ i ∈ s, (v i : M) :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_initial (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).initial = ∑ i ∈ s, (v i).initial :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_final (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).final = ∑ i ∈ s, (v i).final :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.2

lemma partialIsoFinsetSum_mono (v : I → PartialIso M) (hi hf)
    {s t : Finset I} (hst : s ⊆ t) :
    partialIsoFinsetSum v hi hf s ≤ partialIsoFinsetSum v hi hf t := by
  classical
  constructor
  · rw [partialIsoFinsetSum_initial, partialIsoFinsetSum_initial]
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (v i).initial_proj.nonneg)
  · rw [partialIsoFinsetSum_coe, partialIsoFinsetSum_initial, Finset.mul_sum,
      partialIsoFinsetSum_coe]
    apply Finset.sum_congr rfl
    intro i his
    rw [Finset.sum_mul]
    calc
      _ = (v i : M) * (v i).initial := Finset.sum_eq_single i (fun j _ hji => ?_)
        (fun hit => (hit (hst his)).elim)
      _ = (v i : M) := (v i).mul_initial
    calc
        (v j : M) * (v i).initial = ((v j : M) * (v j).initial) * (v i).initial := by
          rw [(v j).mul_initial]
        _ = 0 := by rw [mul_assoc, hi j i hji, mul_zero]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_countable_partialIso_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (v : ℕ → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    ∃ w : PartialIso M, (∀ i, (v i).initial ≤ w.initial) ∧
      (∀ i, (v i).final ≤ w.final) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).initial ≤ p) → w.initial ≤ p) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).final ≤ p) → w.final ≤ p) := by
  classical
  let V (n : ℕ) := partialIsoFinsetSum v hi hf (Finset.range n)
  have hm : Monotone V := fun _ _ h => partialIsoFinsetSum_mono v hi hf (Finset.range_mono h)
  have hc : IsChain (· ≤ ·) (Set.range V) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact (le_total i j).imp (fun h => hm h) (fun h => hm h)
  obtain ⟨w, hw, _, hwi, hwf⟩ := exists_partialIso_chain_supremum e (Set.range V) hc
    ⟨V 0, Set.mem_range_self 0⟩
  have hsumI (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).initial ≤ p) (n : ℕ) :
      (V n).initial ≤ p := by
    apply ((V n).initial_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_initial, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).initial_proj.le_iff_mul_eq_right hp).mp (h i))
  have hsumF (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).final ≤ p) (n : ℕ) :
      (V n).final ≤ p := by
    apply ((V n).final_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_final, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).final_proj.le_iff_mul_eq_right hp).mp (h i))
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i
    apply le_trans _ (hw (V (i + 1)) (Set.mem_range_self _)).1
    rw [partialIsoFinsetSum_initial]
    exact Finset.single_le_sum (fun j _ => (v j).initial_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro i
    apply le_trans _ (PartialIso.final_mono (hw (V (i + 1)) (Set.mem_range_self _)))
    rw [partialIsoFinsetSum_final]
    exact Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro p hp h
    apply hwi p hp
    rintro _ ⟨n, rfl⟩
    exact hsumI p hp h n
  · intro p hp h
    apply hwf p hp
    rintro _ ⟨n, rfl⟩
    exact hsumF p hp h n
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_transition_initial (v w : PartialIso M) (h : v.initial = w.initial) :
    star ((v : M) * star (w : M)) * ((v : M) * star (w : M)) = w.final := by
  calc
    _ = (w : M) * v.initial * star (w : M) := by
      simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
    _ = w.final := by rw [h, w.mul_initial]; rfl

def columnTransition (v w : PartialIso M) (h : v.initial = w.initial) : PartialIso M :=
  ⟨(v : M) * star (w : M), by
    rw [mul_assoc, column_transition_initial v w h]
    have hw : star (w : M) * w.final = star (w : M) := by
      simpa only [star_mul, star_star, w.final_proj.isSelfAdjoint.star_eq] using
        congrArg star w.final_mul
    rw [mul_assoc, hw]⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_initial (v w : PartialIso M) (h) :
    (columnTransition v w h).initial = w.final := column_transition_initial v w h

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_final (v w : PartialIso M) (h) :
    (columnTransition v w h).final = v.final := by
  change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = _
  rw [star_mul, star_star]
  calc
    _ = (v : M) * w.initial * star (v : M) := by simp only [PartialIso.initial, mul_assoc]
    _ = v.final := by rw [← h, v.mul_initial]; rfl

lemma projection_le_complement_of_mul_zero {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) : p ≤ 1 - q := by
  apply (hp.le_iff_mul_eq_left hq.one_sub).mpr
  rw [mul_sub, mul_one, hpq, sub_zero]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_eq_one_of_column_bounds (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    {p : M} (hp : IsStarProjection p) (h : ∀ i, (c i).final ≤ p) : p = 1 := by
  have hh := orthogonal_projection_sum_annihilator e (fun i => (c i).final) (1 - p) 1 ht
    (fun i => by
      rw [mul_sub, mul_one, ((c i).final_proj.le_iff_mul_eq_left hp).mp (h i), sub_self])
  rw [one_mul, sub_eq_zero] at hh
  exact hh.symm
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X Y : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

theorem finite_columns_in_subalgebra (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (R : StarSubalgebra ℂ M) [IsClosed (R : Set M)] (eR : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] R)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    (hc : ∀ i j, (c i : M) * star (c j : M) ∈ R) (n : ℕ) [NeZero n] :
    ∃ v : Fin n → PartialIso M, (∀ j, (v j).initial = 1) ∧
      (∀ j k, j ≠ k → (v j).final * (v k).final = 0) ∧
      (∑ j, (v j).final = 1) ∧ ∀ j, (v j : M) ∈ R := by
  classical
  let σ := (Nat.divModEquiv n).symm
  let aM (j : Fin n) (i : ℕ) := columnTransition (c (σ (i, j))) (c i)
    ((hi _).trans (hi _).symm)
  let a (j : Fin n) (i : ℕ) : PartialIso R :=
    ⟨⟨(aM j i : M), hc _ _⟩, Subtype.ext (aM j i).mul_star_mul⟩
  have hai (j i) : ((a j i).initial : M) = (c i).final :=
    columnTransition_initial (c (σ (i, j))) (c i) ((hi _).trans (hi _).symm)
  have haf (j i) : ((a j i).final : M) = (c (σ (i, j))).final :=
    columnTransition_final (c (σ (i, j))) (c i) ((hi _).trans (hi _).symm)
  have haI (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).initial * (a j k).initial = 0 := by
    apply Subtype.ext
    change ((a j i).initial : M) * ((a j k).initial : M) = 0
    rw [hai, hai]
    exact ho i k hik
  have haF (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).final * (a j k).final = 0 := by
    apply Subtype.ext
    change ((a j i).final : M) * ((a j k).final : M) = 0
    rw [haf, haf]
    exact ho _ _ (fun h => hik (congrArg Prod.fst (σ.injective h)))
  choose v hvi hvf hvi_min hvf_min using fun j =>
    exists_countable_partialIso_sum eR (a j) (haI j) (haF j)
  have hinit (j : Fin n) : (v j).initial = 1 := by
    apply Subtype.ext
    apply projection_eq_one_of_column_bounds e c ht
      ((v j).initial_proj.map R.subtype)
    intro i
    have h := hvi j i
    change ((a j i).initial : M) ≤ ((v j).initial : M) at h
    rwa [hai] at h
  have hcross (j k : Fin n) (hjk : j ≠ k) (i l : ℕ) :
      (a j i).final * (a k l).final = 0 := by
    apply Subtype.ext
    change ((a j i).final : M) * ((a k l).final : M) = 0
    rw [haf, haf]
    exact ho _ _ (fun h => hjk (congrArg Prod.snd (σ.injective h)))
  have horth (j k : Fin n) (hjk : j ≠ k) : (v j).final * (v k).final = 0 := by
    have hfirst (i : ℕ) : (a j i).final * (v k).final = 0 := by
      have hb : (v k).final ≤ 1 - (a j i).final := by
        apply hvf_min k _ (a j i).final_proj.one_sub
        intro l
        apply projection_le_complement_of_mul_zero (a k l).final_proj (a j i).final_proj
        simpa only [star_mul, (a j i).final_proj.isSelfAdjoint.star_eq,
          (a k l).final_proj.isSelfAdjoint.star_eq, star_zero] using
          congrArg star (hcross j k hjk i l)
      exact HochschildTypeII.projection_orthogonal_of_le_complement (a j i).final_proj
        (v k).final_proj hb
    have hb : (v j).final ≤ 1 - (v k).final := hvf_min j _ (v k).final_proj.one_sub
      (fun i => projection_le_complement_of_mul_zero (a j i).final_proj (v k).final_proj (hfirst i))
    have h := ((v j).final_proj.le_iff_mul_eq_left (v k).final_proj.one_sub).mp hb
    rw [mul_sub, mul_one] at h
    exact sub_eq_self.mp h
  have hproj : IsStarProjection (∑ j, (v j).final) :=
    orthogonal_projection_finset_sum (fun j => (v j).final) (fun j => (v j).final_proj)
      horth Finset.univ
  have hsum : (∑ j, (v j).final) = 1 := by
    apply Subtype.ext
    apply projection_eq_one_of_column_bounds e c ht (hproj.map R.subtype)
    intro i
    let t := Nat.divModEquiv n i
    have hti : σ t = i := (Nat.divModEquiv n).symm_apply_apply i
    have hh : (c i).final ≤ ((v t.2).final : M) := by
      have h := hvf t.2 t.1
      change ((a t.2 t.1).final : M) ≤ ((v t.2).final : M) at h
      rw [haf] at h
      simpa only [hti] using h
    apply hh.trans
    exact show (v t.2).final ≤ ∑ j, (v j).final from
      Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg) (Finset.mem_univ t.2)
  let w (j : Fin n) : PartialIso M :=
    ⟨((v j : R) : M), congrArg Subtype.val (v j).mul_star_mul⟩
  refine ⟨w, fun j => congrArg Subtype.val (hinit j), ?_, ?_, fun j => (v j : R).property⟩
  · intro j k hjk
    exact congrArg Subtype.val (horth j k hjk)
  · change (∑ j, ((v j).final : M)) = 1
    simpa using congrArg (fun z : R => (z : M)) hsum
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def matrixClosureStarPreadjoint (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : X →L⋆[ℂ] X :=
  (HochschildSakai.exists_abstract_star_preadjoint e).choose

omit [PartialOrder M] [StarOrderedRing M] in
lemma matrixClosureStarPreadjoint_spec (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) (z : X) :
    e.symm (star a) z = star (e.symm a (matrixClosureStarPreadjoint e z)) :=
  (HochschildSakai.exists_abstract_star_preadjoint e).choose_spec.2 a z

def countableMatrixClosure (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (c : ℕ → PartialIso M) :
    StarSubalgebra ℂ M :=
  WeakAlgebra.closure e (countableMatrixAlgebra c)
    (HochschildSakai.abstract_multiplication_normal e).1
    (HochschildSakai.abstract_multiplication_normal e).2
    (matrixClosureStarPreadjoint e) (matrixClosureStarPreadjoint_spec e)

instance countableMatrixClosure_closed (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) : IsClosed (countableMatrixClosure e c : Set M) := by
  unfold countableMatrixClosure
  infer_instance

instance countableMatrixClosure_wstar (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) : WStarAlgebra (countableMatrixClosure e c) := by
  unfold countableMatrixClosure
  infer_instance

omit [PartialOrder M] [StarOrderedRing M] in
lemma countableMatrixClosure_transition (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (i j : ℕ) :
    (c i : M) * star (c j : M) ∈ countableMatrixClosure e c := by
  apply WeakAlgebra.mem_linearClosure e (countableMatrixAlgebra c)
  exact StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩

theorem countableMatrixClosure_columns (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    (n : ℕ) [NeZero n] :
    ∃ v : Fin n → PartialIso M, (∀ j, (v j).initial = 1) ∧
      (∀ j k, j ≠ k → (v j).final * (v k).final = 0) ∧
      (∑ j, (v j).final = 1) ∧ ∀ j, (v j : M) ∈ countableMatrixClosure e c := by
  obtain ⟨Y, hY, hYS, hYC, ⟨eR⟩⟩ :=
    WStarAlgebra.exists_predual (M := countableMatrixClosure e c)
  let := hY
  let := hYS
  let := hYC
  exact finite_columns_in_subalgebra e (countableMatrixClosure e c) eR c hi ho ht
    (countableMatrixClosure_transition e c) n
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] {n : ℕ}
variable (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
  (hs : ∑ i, (c i).final = 1)

include hi ho in
lemma column_star_mul (i j : Fin n) :
    star (c i : M) * (c j : M) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j
    exact hi i
  · exact PartialIso.star_mul_eq_zero_of_final_orthogonal (ho i j h)

def columnCompression (a : M) : CStarMatrix (Fin n) (Fin n) M :=
  CStarMatrix.ofMatrix (fun i j => star (c i : M) * a * (c j : M))

def columnReconstruction (A : CStarMatrix (Fin n) (Fin n) M) : M :=
  ∑ i, ∑ j, (c i : M) * A i j * star (c j : M)

include hs in
lemma columnReconstruction_compression (a : M) :
    columnReconstruction c (columnCompression c a) = a := by
  calc
    _ = ∑ i, ((c i : M) * star (c i : M)) * a * (∑ j, (c j : M) * star (c j : M)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (c i : M) * (star (c i : M) * a * (c j : M)) * star (c j : M) = _
      simp only [mul_assoc]
    _ = a := by
      change (∑ i, (c i).final * a * (∑ j, (c j).final)) = a
      rw [hs]
      simp only [mul_one]
      rw [← Finset.sum_mul, hs, one_mul]

include hi ho in
lemma columnCompression_reconstruction (A : CStarMatrix (Fin n) (Fin n) M) :
    columnCompression c (columnReconstruction c A) = A := by
  classical
  ext i j
  change star (c i : M) * (∑ k, ∑ l, (c k : M) * A k l * star (c l : M)) * (c j : M) = A i j
  calc
    _ = ∑ k, ∑ l, (star (c i : M) * (c k : M)) * A k l *
        (star (c l : M) * (c j : M)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [mul_assoc]
    _ = A i j := by simp [column_star_mul c hi ho]

include hs in
lemma columnCompression_mul (a b : M) :
    columnCompression c (a * b) = columnCompression c a * columnCompression c b := by
  ext i j
  change star (c i : M) * (a * b) * (c j : M) =
    ∑ k, (star (c i : M) * a * (c k : M)) * (star (c k : M) * b * (c j : M))
  calc
    _ = star (c i : M) * a * (∑ k, (c k : M) * star (c k : M)) * b * (c j : M) := by
      change _ = star (c i : M) * a * (∑ k, (c k).final) * b * (c j : M)
      rw [hs, mul_one]
      simp only [mul_assoc]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mul_assoc]

def columnMatrixEquiv : M ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) M where
  toFun := columnCompression c
  invFun := columnReconstruction c
  left_inv := columnReconstruction_compression c hs
  right_inv := columnCompression_reconstruction c hi ho
  map_mul' := columnCompression_mul c hs
  map_add' a b := by
    ext i j
    change star (c i : M) * (a + b) * (c j : M) =
      star (c i : M) * a * (c j : M) + star (c i : M) * b * (c j : M)
    rw [mul_add, add_mul]
  map_smul' z a := by
    ext i j
    change star (c i : M) * (z • a) * (c j : M) = z • (star (c i : M) * a * (c j : M))
    rw [mul_smul_comm, smul_mul_assoc]
  map_star' a := by
    ext i j
    change star (c i : M) * star a * (c j : M) = star (star (c j : M) * a * (c i : M))
    simp only [star_mul, star_star, mul_assoc]

variable [PartialOrder M] [StarOrderedRing M]

include hi ho hs in
lemma columnCompression_norm (a : M) : ‖columnCompression c a‖ = ‖a‖ := by
  change ‖columnMatrixEquiv c hi ho hs a‖ = ‖a‖
  exact StarAlgEquiv.norm_map (columnMatrixEquiv c hi ho hs) a
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

variable {I : Type*} [Fintype I]

lemma finiteRightAverage_add (m : I → M) (S T : M →L[ℂ] M) :
    finiteRightAverage m (S + T) = finiteRightAverage m S + finiteRightAverage m T := by
  ext a
  simp only [finiteRightAverage_apply, add_apply, add_mul, Finset.sum_add_distrib]

lemma finiteRightAverage_smul (m : I → M) (z : ℂ) (T : M →L[ℂ] M) :
    finiteRightAverage m (z • T) = z • finiteRightAverage m T := by
  ext a
  simp only [finiteRightAverage_apply, smul_apply, smul_mul_assoc,
    Finset.smul_sum]

lemma finiteRightAverage_mul_left (m : I → M) (hm : ∑ i, m i * star (m i) = 1) (b : M) :
    finiteRightAverage m (ContinuousLinearMap.mul ℂ M b) = ContinuousLinearMap.mul ℂ M b := by
  ext a
  simp only [finiteRightAverage_apply, ContinuousLinearMap.mul_apply']
  calc
    _ = b * a * (∑ i, m i * star (m i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_assoc]
    _ = b * a := by rw [hm, mul_one]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def matrixScalarHom (k : ℕ) : M →⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) M where
  toFun a := CStarMatrix.ofMatrix (Matrix.scalar (Fin k) a)
  map_zero' := (Matrix.scalar (Fin k)).map_zero
  map_one' := (Matrix.scalar (Fin k)).map_one
  map_add' a b := (Matrix.scalar (Fin k)).map_add a b
  map_mul' a b := (Matrix.scalar (Fin k)).map_mul a b
  commutes' _ := rfl
  map_star' a := by
    ext i j
    change (if i = j then star a else 0) = star (if j = i then a else 0)
    by_cases h : i = j
    · simp only [h, ite_true]
    · simp only [h, Ne.symm h, ite_false, star_zero]

@[simp] lemma matrixScalarHom_apply (k : ℕ) (a : M) (i j : Fin k) :
    matrixScalarHom k a i j = if i = j then a else 0 := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma completelyBounded_add {T U : M →L[ℂ] M} {C D : ℝ}
    (hT : CompletelyBoundedEstimate T C) (hU : CompletelyBoundedEstimate U D) :
    CompletelyBoundedEstimate (T + U) (C + D) := by
  refine ⟨add_nonneg hT.1 hU.1, fun n A => ?_⟩
  have he : A.map (T + U) = A.map T + A.map U := by ext i j; rfl
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [hT.2 n A, hU.2 n A])

def leftSandwichMap (a b : M) (T : M →L[ℂ] M) : M →L[ℂ] M :=
  (ContinuousLinearMap.mul ℂ M a).comp (T.comp (ContinuousLinearMap.mul ℂ M b))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma leftSandwichMap_apply (a b : M) (T : M →L[ℂ] M) (x : M) :
    leftSandwichMap a b T x = a * T (b * x) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma matrix_scalar_mul_apply {n : ℕ} (a : M) (A : CStarMatrix (Fin n) (Fin n) M)
    (i j : Fin n) : (matrixScalarHom n a * A) i j = a * A i j := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, ite_mul, zero_mul]
  simp

lemma completelyBounded_leftSandwich (a b : M) {T : M →L[ℂ] M} {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) :
    CompletelyBoundedEstimate (leftSandwichMap a b T) (‖a‖ * C * ‖b‖) := by
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) hT.1) (norm_nonneg _), fun n A => ?_⟩
  have he : A.map (leftSandwichMap a b T) =
      matrixScalarHom n a * ((matrixScalarHom n b * A).map T) := by
    ext i j
    simp only [CStarMatrix.map_apply, leftSandwichMap_apply, matrix_scalar_mul_apply]
  rw [he]
  have ha : ‖matrixScalarHom n a‖ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le _ _
  have hb : ‖matrixScalarHom n b‖ ≤ ‖b‖ := NonUnitalStarAlgHom.norm_apply_le _ _
  calc
    _ ≤ ‖matrixScalarHom n a‖ * ‖(matrixScalarHom n b * A).map T‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * (C * (‖b‖ * ‖A‖)) := by
      apply mul_le_mul ha _ (norm_nonneg _) (norm_nonneg _)
      exact (hT.2 n _).trans (mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) hT.1)
    _ = _ := by ring
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma finiteRightAverage_reindex (e : I ≃ J) (m : J → M) (T : M →L[ℂ] M) :
    finiteRightAverage (m ∘ e) T = finiteRightAverage m T := by
  ext a
  simpa only [finiteRightAverage_apply, Function.comp_apply] using
    e.sum_comp (fun j => T (a * m j) * star (m j))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M X : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma weakOperatorImage_injective (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Function.Injective (weakOperatorImage e) := by
  intro S T h
  ext a
  apply e.symm.injective
  exact congrArg WeakDual.toStrongDual (congrFun h a)

lemma weakOperatorImage_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (S T : M →L[ℂ] M) :
    weakOperatorImage e (S + T) = weakOperatorImage e S + weakOperatorImage e T := by
  funext a
  change StrongDual.toWeakDual (e.symm (S a + T a)) = _
  simp only [map_add]
  rfl

lemma weakOperatorBall_realize (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {C : ℝ} (hC : 0 ≤ C) {F : M → WeakDual ℂ X}
    (hF : F ∈ weakOperatorBall C) :
    ∃ T : M →L[ℂ] M, ‖T‖ ≤ C ∧ weakOperatorImage e T = F := by
  let L : M →ₗ[ℂ] M :=
    { toFun := fun a => e (WeakDual.toStrongDual (F a))
      map_add' := fun a b => by
        rw [hF.1 a b]
        exact map_add e _ _
      map_smul' := fun z a => by
        rw [hF.2.1 z a]
        change e (star z • WeakDual.toStrongDual (F a)) = _
        simp only [LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply, star_star,
          RingHom.id_apply] }
  have hb (a : M) : ‖L a‖ ≤ C * ‖a‖ := by
    change ‖e (WeakDual.toStrongDual (F a))‖ ≤ _
    rw [e.norm_map]
    exact hF.2.2 a
  refine ⟨L.mkContinuous C hb, L.mkContinuous_norm_le hC hb, ?_⟩
  funext a
  change StrongDual.toWeakDual (e.symm (e (WeakDual.toStrongDual (F a)))) = F a
  rw [e.symm_apply_apply]
  rfl

lemma weakOperatorBall_isClosed (C : ℝ) :
    IsClosed (weakOperatorBall (M := M) (X := X) C) := by
  have hadd : IsClosed {F : M → WeakDual ℂ X | ∀ a b, F (a + b) = F a + F b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
  have hsmul : IsClosed {F : M → WeakDual ℂ X |
      ∀ (z : ℂ) a, F (z • a) = star z • F a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun z => isClosed_iInter fun a =>
      isClosed_eq (continuous_apply (z • a)) ((continuous_apply a).const_smul (star z))
  have hbound : IsClosed {F : M → WeakDual ℂ X |
      ∀ a, ‖WeakDual.toStrongDual (F a)‖ ≤ C * ‖a‖} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    have h := (WeakDual.isClosed_closedBall (0 : StrongDual ℂ X) (C * ‖a‖)).preimage
      (continuous_apply a : Continuous (fun F : M → WeakDual ℂ X => F a))
    convert h using 1
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact hadd.inter (hsmul.inter hbound)

theorem weakOperatorBall_isCompact (C : ℝ) :
    IsCompact (weakOperatorBall (M := M) (X := X) C) := by
  have hprod := isCompact_pi_infinite (fun a : M =>
    WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) (C * ‖a‖))
  apply hprod.of_isClosed_subset (weakOperatorBall_isClosed C)
  intro F hF a
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hF.2.2 a
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def weakDualOperator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (L : M →L[ℂ] M)
    (F : WeakDual ℂ X) : WeakDual ℂ X :=
  StrongDual.toWeakDual (e.symm (L (e (WeakDual.toStrongDual F))))

lemma weakDualOperator_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (L : M →L[ℂ] M) (a : M) :
    weakDualOperator e L (StrongDual.toWeakDual (e.symm a)) =
      StrongDual.toWeakDual (e.symm (L a)) := by
  change StrongDual.toWeakDual (e.symm (L (e (e.symm a)))) = _
  rw [e.apply_symm_apply]

lemma weakDualOperator_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (L : M →L[ℂ] M) (hL : HasPreadjoint e L) : Continuous (weakDualOperator e L) := by
  apply WeakDual.continuous_of_continuous_eval
  intro x
  obtain ⟨y, hy⟩ := hL x
  have h : (fun F : WeakDual ℂ X => weakDualOperator e L F x) = fun F => F y := by
    funext F
    simp only [weakDualOperator, StrongDual.toWeakDual_apply, hy, e.symm_apply_apply,
      WeakDual.toStrongDual_apply]
  rw [h]
  exact WeakDual.eval_continuous y

def weakRightAverage {I : Type*} [Fintype I] (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (m : I → M) (F : M → WeakDual ℂ X) : M → WeakDual ℂ X := fun a =>
  ∑ i, weakDualOperator e ((ContinuousLinearMap.mul ℂ M).flip (star (m i))) (F (a * m i))

lemma weakRightAverage_image {I : Type*} [Fintype I]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (m : I → M) (T : M →L[ℂ] M) :
    weakRightAverage e m (weakOperatorImage e T) =
      weakOperatorImage e (finiteRightAverage m T) := by
  funext a
  simp only [weakRightAverage, weakOperatorImage, weakDualOperator_image,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    finiteRightAverage_apply, map_sum]

variable [CompleteSpace X]

lemma weakRightAverage_continuous {I : Type*} [Fintype I]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (m : I → M) : Continuous (weakRightAverage e m) := by
  apply continuous_pi
  intro a
  apply continuous_finsetSum
  intro i _
  exact (weakDualOperator_continuous e _
    ((HochschildSakai.abstract_multiplication_normal e).2 (star (m i)))).comp
      (continuous_apply (a * m i))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma finiteRightAverage_mem_orbit {I : Type*} [Fintype I]
    (m : I → M) (hm : ∑ i, m i * star (m i) = 1) (T : M →L[ℂ] M) :
    finiteRightAverage m T ∈ rightAverageOrbit T := by
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, m ∘ e.symm, ?_, ?_⟩
  · exact (e.symm.sum_comp (fun i => m i * star (m i))).trans hm
  · exact (finiteRightAverage_reindex e.symm m T).symm

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem weakRightAverageOrbit_isCompact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : IsCompact (weakRightAverageOrbit e T) :=
  (weakOperatorBall_isCompact C).of_isClosed_subset isClosed_closure
    (weakRightAverageOrbit_subset_ball e hno T hT)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma leftSandwichMap_rightAverage {I : Type*} [Fintype I]
    (a b : M) (m : I → M) (T : M →L[ℂ] M) :
    leftSandwichMap a b (finiteRightAverage m T) =
      finiteRightAverage m (leftSandwichMap a b T) := by
  ext x
  simp only [leftSandwichMap_apply, finiteRightAverage_apply, Finset.mul_sum, mul_assoc]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakLeftSandwich (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M)
    (F : M → WeakDual ℂ X) : M → WeakDual ℂ X :=
  fun x => weakDualOperator e (ContinuousLinearMap.mul ℂ M a) (F (b * x))

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakLeftSandwich_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a b : M) (T : M →L[ℂ] M) :
    weakLeftSandwich e a b (weakOperatorImage e T) =
      weakOperatorImage e (leftSandwichMap a b T) := by
  funext x
  exact weakDualOperator_image e _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakLeftSandwich_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    Continuous (weakLeftSandwich e a b) := by
  apply continuous_pi
  intro x
  exact (weakDualOperator_continuous e _
    ((HochschildSakai.abstract_multiplication_normal e).1 a)).comp (continuous_apply (b*x))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma right_module_of_unitary_averages (T : M →L[ℂ] M)
    (hT : ∀ u : unitary M, finiteRightAverage (fun _ : Fin 1 => (u : M)) T = T) :
    ∀ a b : M, T (a * b) = T a * b := by
  have hu (a : M) (u : unitary M) : T (a * (u : M)) = T a * (u : M) := by
    have h := congrArg (fun S : M →L[ℂ] M => S a * (u : M)) (hT u)
    simpa only [finiteRightAverage_apply, Fin.sum_univ_one, mul_assoc,
      Unitary.star_mul_self_of_mem u.property, mul_one] using h
  intro a b
  obtain ⟨u, c, hb, _⟩ := CStarAlgebra.exists_sum_four_unitary b
  rw [hb]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hu]

lemma right_module_eq_left_multiplication (T : M →L[ℂ] M)
    (hT : ∀ a b : M, T (a * b) = T a * b) :
    T = ContinuousLinearMap.mul ℂ M (T 1) := by
  ext a
  simpa only [one_mul, ContinuousLinearMap.mul_apply'] using hT 1 a

theorem fixed_right_averages_iff (T : M →L[ℂ] M) :
    (∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
      finiteRightAverage m T = T) ↔ T = ContinuousLinearMap.mul ℂ M (T 1) := by
  constructor
  · intro hT
    apply right_module_eq_left_multiplication T
    apply right_module_of_unitary_averages T
    intro u
    exact hT 1 (fun _ => (u : M)) (by
      simp only [Fin.sum_univ_one, Unitary.mul_star_self_of_mem u.property])
  · intro hT n m hm
    conv_lhs => rw [hT]
    rw [finiteRightAverage_mul_left m hm, ← hT]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem weak_fixed_right_averages_realize (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : M → WeakDual ℂ X} {C : ℝ} (hC : 0 ≤ C) (hF : F ∈ weakOperatorBall C)
    (hfix : ∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
      weakRightAverage e m F = F) :
    ∃ b : M, ‖ContinuousLinearMap.mul ℂ M b‖ ≤ C ∧
      weakOperatorImage e (ContinuousLinearMap.mul ℂ M b) = F := by
  obtain ⟨T, hT, hTF⟩ := weakOperatorBall_realize e hC hF
  have hfixed : ∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
      finiteRightAverage m T = T := by
    intro n m hm
    apply weakOperatorImage_injective e
    rw [← weakRightAverage_image, hTF, hfix n m hm]
  have heq := (fixed_right_averages_iff T).mp hfixed
  exact ⟨T 1, heq ▸ hT, heq ▸ hTF⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I J : Type*}

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakFamilyAverageOrbit_component (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) (i : I) {F : I → M → WeakDual ℂ X}
    (hF : F ∈ weakFamilyAverageOrbit e T) : F i ∈ weakRightAverageOrbit e (T i) := by
  have hc : IsClosed {G : I → M → WeakDual ℂ X | G i ∈ weakRightAverageOrbit e (T i)} :=
    isClosed_closure.preimage (continuous_apply i)
  apply closure_minimal _ hc hF
  rintro G ⟨k, m, hm, rfl⟩
  exact subset_closure ⟨_, finiteRightAverage_mem_orbit m hm _, rfl⟩

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakFamilyAverageOrbit_nonempty (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) : (weakFamilyAverageOrbit e T).Nonempty := by
  refine ⟨_, subset_closure ⟨1, (fun _ : Fin 1 => (1 : M)), by simp, rfl⟩⟩

theorem weakFamilyAverageOrbit_isCompact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : I → M →L[ℂ] M) (C : I → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    IsCompact (weakFamilyAverageOrbit e T) :=
  (isCompact_pi_infinite (fun i => weakRightAverageOrbit_isCompact e hno (T i) (hT i))).of_isClosed_subset
    isClosed_closure (fun _ hF i => weakFamilyAverageOrbit_component e T i hF)

theorem weakFamilyAverageOrbit_restriction_lift (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : I → M →L[ℂ] M) (C : I → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) (f : J → I)
    {F : J → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e (T ∘ f)) :
    ∃ G ∈ weakFamilyAverageOrbit e T, G ∘ f = F := by
  let r (G : I → M → WeakDual ℂ X) : J → M → WeakDual ℂ X := G ∘ f
  have hc : Continuous r := continuous_pi (fun j => continuous_apply (f j))
  have hclosed : IsClosed (r '' weakFamilyAverageOrbit e T) :=
    ((weakFamilyAverageOrbit_isCompact e hno T C hT).image hc).isClosed
  have hsub : finiteFamilyAverageOrbit e (T ∘ f) ⊆ r '' weakFamilyAverageOrbit e T := by
    rintro G ⟨k, m, hm, rfl⟩
    refine ⟨fun i => weakOperatorImage e (finiteRightAverage m (T i)),
      subset_closure ⟨k, m, hm, rfl⟩, rfl⟩
  exact closure_minimal hsub hclosed hF
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I : Type*}

def WeakRightAverageFixed (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : M → WeakDual ℂ X) : Prop :=
  ∀ (n : ℕ) (m : Fin n → M), (∑ j, m j * star (m j) = 1) → weakRightAverage e m F = F

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakRightAverageFixed_isClosed (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    IsClosed {F : M → WeakDual ℂ X | WeakRightAverageFixed e F} := by
  simp only [WeakRightAverageFixed, Set.ofPred_forall]
  exact isClosed_iInter (fun n => isClosed_iInter (fun m => isClosed_iInter
    (fun _ => isClosed_eq (weakRightAverage_continuous e m) continuous_id)))

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakRightAverageFixed_of_module (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) (hT : ∀ a b, T (a*b) = T a * b) :
    WeakRightAverageFixed e (weakOperatorImage e T) := by
  have hf := (fixed_right_averages_iff T).mpr (right_module_eq_left_multiplication T hT)
  intro n m hm
  rw [weakRightAverage_image, hf n m hm]

theorem exists_simultaneous_right_module_average [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (T : I → M →L[ℂ] M) (C : I → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    ∃ S : I → M →L[ℂ] M,
      (∀ i, ‖S i‖ ≤ C i ∧ ∀ a b, S i (a*b) = S i a * b) ∧
      (fun i => weakOperatorImage e (S i)) ∈ weakFamilyAverageOrbit e T := by
  classical
  let B := weakFamilyAverageOrbit e T
  let A (s : Finset I) := B ∩ {F : I → M → WeakDual ℂ X |
    ∀ i ∈ s, WeakRightAverageFixed e (F i)}
  have hfixclosed (i : I) : IsClosed {F : I → M → WeakDual ℂ X |
      WeakRightAverageFixed e (F i)} := by
    have hc : Continuous (fun F : I → M → WeakDual ℂ X => F i) := continuous_apply i
    exact (weakRightAverageFixed_isClosed e).preimage hc
  have hclosed (s : Finset I) : IsClosed (A s) := by
    apply isClosed_closure.inter
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ => hfixclosed i))
  have hne (s : Finset I) : (A s).Nonempty := by
    by_cases hs : s.Nonempty
    · let : Nonempty s := hs.to_subtype
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := s))
      let q : s ≃ Fin (n+1) := Fintype.equivFinOfCardEq hn
      let f : Fin (n+1) → I := fun j => (q.symm j).val
      obtain ⟨U, hU, hUorb⟩ := exists_finite_right_module_average e hno
        (T ∘ f) (C ∘ f) (fun j => hT (f j))
      obtain ⟨F, hF, hEq⟩ := weakFamilyAverageOrbit_restriction_lift e hno T C hT f hUorb
      refine ⟨F, hF, ?_⟩
      intro i hi
      have he := congrFun hEq (q ⟨i, hi⟩)
      have hf : f (q ⟨i, hi⟩) = i := by simp [f]
      change F (f (q ⟨i, hi⟩)) = weakOperatorImage e (U (q ⟨i, hi⟩)) at he
      rw [hf] at he
      rw [he]
      exact weakRightAverageFixed_of_module e _ (hU _).2
    · obtain ⟨F, hF⟩ := weakFamilyAverageOrbit_nonempty e T
      exact ⟨F, hF, fun i hi => (hs ⟨i, hi⟩).elim⟩
  have hcompact (s : Finset I) : IsCompact (A s) :=
    (weakFamilyAverageOrbit_isCompact e hno T C hT).of_isClosed_subset
      (hclosed s) (fun _ h => h.1)
  obtain ⟨F, hF⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed A
    (fun s t => ⟨s ∪ t,
      fun G hG => ⟨hG.1, fun i hi => hG.2 i (Finset.mem_union_left t hi)⟩,
      fun G hG => ⟨hG.1, fun i hi => hG.2 i (Finset.mem_union_right s hi)⟩⟩)
    hne hcompact hclosed
  have hFB : F ∈ B := (Set.mem_iInter.mp hF ∅).1
  have hfix (i : I) : WeakRightAverageFixed e (F i) :=
    (Set.mem_iInter.mp hF {i}).2 i (Finset.mem_singleton_self i)
  have hb (i : I) : F i ∈ weakOperatorBall (C i) :=
    weakRightAverageOrbit_subset_ball e hno (T i) (hT i)
      (weakFamilyAverageOrbit_component e T i hFB)
  choose b hn he using fun i => weak_fixed_right_averages_realize e (hT i).1 (hb i) (hfix i)
  refine ⟨fun i => ContinuousLinearMap.mul ℂ M (b i), fun i => ⟨hn i, ?_⟩, ?_⟩
  · intro a c
    exact (mul_assoc (b i) a c).symm
  · have hEq : (fun i => weakOperatorImage e (ContinuousLinearMap.mul ℂ M (b i))) = F := funext he
    rwa [hEq]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I : Type*}

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma joint_orbit_closed_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) (R : Set (I → M → WeakDual ℂ X)) (hR : IsClosed R)
    (hfin : ∀ (n : ℕ) (m : Fin n → M), (∑ j, m j * star (m j) = 1) →
      (fun i => weakOperatorImage e (finiteRightAverage m (T i))) ∈ R) :
    weakFamilyAverageOrbit e T ⊆ R := by
  apply closure_minimal _ hR
  rintro F ⟨n, m, hm, rfl⟩
  exact hfin n m hm

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakOperatorImage_complex_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (z : ℂ) (T : M →L[ℂ] M) :
    weakOperatorImage e (z • T) = star z • weakOperatorImage e T := by
  funext a
  change StrongDual.toWeakDual (e.symm (z • T a)) = _
  rw [e.symm.map_smulₛₗ]
  rfl

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma joint_orbit_add_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) {i j k : I} (hT : T k = T i + T j)
    {F : I → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e T) :
    F k = F i + F j := by
  apply joint_orbit_closed_relation e T {F | F k = F i + F j} _ _ hF
  · exact isClosed_eq (continuous_apply k) ((continuous_apply i).add (continuous_apply j))
  · intro n m _
    change weakOperatorImage e (finiteRightAverage m (T k)) =
      weakOperatorImage e (finiteRightAverage m (T i)) + weakOperatorImage e (finiteRightAverage m (T j))
    rw [hT, finiteRightAverage_add, weakOperatorImage_add]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma joint_orbit_smul_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) {i j : I} (z : ℂ) (hT : T j = z • T i)
    {F : I → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e T) :
    F j = star z • F i := by
  apply joint_orbit_closed_relation e T {F | F j = star z • F i} _ _ hF
  · exact isClosed_eq (continuous_apply j) ((continuous_apply i).const_smul (star z))
  · intro n m _
    change weakOperatorImage e (finiteRightAverage m (T j)) =
      star z • weakOperatorImage e (finiteRightAverage m (T i))
    rw [hT, finiteRightAverage_smul, weakOperatorImage_complex_smul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma joint_orbit_sandwich_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) {i j : I} (a b : M) (hT : T j = leftSandwichMap a b (T i))
    {F : I → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e T) :
    F j = weakLeftSandwich e a b (F i) := by
  apply joint_orbit_closed_relation e T {F | F j = weakLeftSandwich e a b (F i)} _ _ hF
  · exact isClosed_eq (continuous_apply j)
      ((weakLeftSandwich_continuous e a b).comp (continuous_apply i))
  · intro n m _
    change weakOperatorImage e (finiteRightAverage m (T j)) =
      weakLeftSandwich e a b (weakOperatorImage e (finiteRightAverage m (T i)))
    rw [hT, ← leftSandwichMap_rightAverage, weakLeftSandwich_image]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma completelyBounded_zero : CompletelyBoundedEstimate (0 : M →L[ℂ] M) 0 := by
  refine ⟨le_rfl, fun n A => ?_⟩
  have he : A.map (0 : M →L[ℂ] M) = 0 := by ext i j; rfl
  rw [he, norm_zero, zero_mul]

lemma completelyBounded_smul (z : ℂ) {T : M →L[ℂ] M} {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) :
    CompletelyBoundedEstimate (z • T) (‖z‖ * C) := by
  refine ⟨mul_nonneg (norm_nonneg z) hT.1, fun n A => ?_⟩
  have he : A.map (z • T) = z • A.map T := by ext i j; rfl
  rw [he, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hT.2 n A) (norm_nonneg z)

def completelyBoundedSubmodule : Submodule ℂ (M →L[ℂ] M) where
  carrier := {T | ∃ C, CompletelyBoundedEstimate T C}
  zero_mem' := ⟨0, completelyBounded_zero⟩
  add_mem' := by
    rintro T U ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C+D, completelyBounded_add hC hD⟩
  smul_mem' := by
    rintro z T ⟨C, hC⟩
    exact ⟨‖z‖*C, completelyBounded_smul z hC⟩

abbrev CompletelyBoundedMap (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] :=
  completelyBoundedSubmodule (M := M)

def completelyBoundedBound (T : CompletelyBoundedMap M) : ℝ := Classical.choose T.property

lemma completelyBoundedBound_spec (T : CompletelyBoundedMap M) :
    CompletelyBoundedEstimate T.val (completelyBoundedBound T) := Classical.choose_spec T.property

def cbLeftSandwich (a b : M) (T : CompletelyBoundedMap M) : CompletelyBoundedMap M :=
  ⟨leftSandwichMap a b T.val, _, completelyBounded_leftSandwich a b (completelyBoundedBound_spec T)⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma norm_le_of_weakRightAverageOrbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T S : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C)
    (hS : weakOperatorImage e S ∈ weakRightAverageOrbit e T) : ‖S‖ ≤ C := by
  obtain ⟨U, hU, hUS⟩ := weakOperatorBall_realize e hT.1
    (weakRightAverageOrbit_subset_ball e hno T hT hS)
  exact (weakOperatorImage_injective e hUS) ▸ hU

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma module_map_weakRightAverageOrbit_singleton (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) (hT : ∀ a b, T (a*b) = T a * b) :
    weakRightAverageOrbit e T ⊆ {weakOperatorImage e T} := by
  have hfix := (fixed_right_averages_iff T).mpr (right_module_eq_left_multiplication T hT)
  apply closure_minimal _ isClosed_singleton
  rintro F ⟨S, ⟨n, m, hm, rfl⟩, rfl⟩
  rw [hfix n m hm]
  rfl

structure RightModuleAveragingProjection where
  map : CompletelyBoundedMap M →ₗ[ℂ] (M →L[ℂ] M)
  bound : ∀ T C, CompletelyBoundedEstimate T.val C → ‖map T‖ ≤ C
  module : ∀ T a b, map T (a*b) = map T a * b
  covariance : ∀ a b T, map (cbLeftSandwich a b T) = leftSandwichMap a b (map T)
  fixes : ∀ T, (∀ a b, T.val (a*b) = T.val a * b) → map T = T.val

theorem exists_rightModuleAveragingProjection [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M) :
    Nonempty (RightModuleAveragingProjection (M := M)) := by
  obtain ⟨S, hS, hSorb⟩ := exists_simultaneous_right_module_average e hno
    (fun T : CompletelyBoundedMap M => T.val) completelyBoundedBound completelyBoundedBound_spec
  let P : CompletelyBoundedMap M →ₗ[ℂ] (M →L[ℂ] M) :=
    { toFun := S
      map_add' := by
        intro T U
        apply weakOperatorImage_injective e
        rw [weakOperatorImage_add]
        exact joint_orbit_add_relation e (fun T : CompletelyBoundedMap M => T.val) rfl hSorb
      map_smul' := by
        intro z T
        apply weakOperatorImage_injective e
        rw [weakOperatorImage_complex_smul]
        exact joint_orbit_smul_relation e (fun T : CompletelyBoundedMap M => T.val) z rfl hSorb }
  refine ⟨{ map := P, bound := ?_, module := ?_, covariance := ?_, fixes := ?_ }⟩
  · intro T C hTC
    exact norm_le_of_weakRightAverageOrbit e hno T.val (S T) hTC
      (weakFamilyAverageOrbit_component e (fun T : CompletelyBoundedMap M => T.val) T hSorb)
  · exact fun T => (hS T).2
  · intro a b T
    apply weakOperatorImage_injective e
    rw [← weakLeftSandwich_image]
    exact joint_orbit_sandwich_relation e (fun T : CompletelyBoundedMap M => T.val) a b rfl hSorb
  · intro T hT
    apply weakOperatorImage_injective e
    exact module_map_weakRightAverageOrbit_singleton e T.val hT
      (weakFamilyAverageOrbit_component e (fun T : CompletelyBoundedMap M => T.val) T hSorb)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def LastSliceEstimate {n : ℕ} (f : Cochain M (n + 1)) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ v : Fin n → M,
    CompletelyBoundedEstimate (f.curryRight v) (C * ∏ i, ‖v i‖)

def cbCurryRight {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hf : LastSliceEstimate f C) :
    MultilinearMap ℂ (fun _ : Fin n => M) (CompletelyBoundedMap M) :=
  f.curryRight.toMultilinearMap.codRestrict completelyBoundedSubmodule
    (fun v => ⟨C * ∏ i, ‖v i‖, hf.2 v⟩)

@[simp] lemma cbCurryRight_val {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hf : LastSliceEstimate f C) (v : Fin n → M) :
    (cbCurryRight f hf v).val = f.curryRight v := rfl

@[simp] lemma cbCurryRight_apply {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hf : LastSliceEstimate f C) (v : Fin n → M) (u : M) :
    (cbCurryRight f hf v).val u = f (Fin.snoc v u) := rfl

@[simp] lemma cbLeftSandwich_apply (a b : M) (T : CompletelyBoundedMap M) (u : M) :
    (cbLeftSandwich a b T).val u = a * T.val (b * u) := rfl

def averagedLastMultilinear (P : RightModuleAveragingProjection (M := M))
    {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) :
    MultilinearMap ℂ (fun _ : Fin n => M) M :=
  ((ContinuousLinearMap.apply ℂ M (1 : M)).toLinearMap.comp P.map).compMultilinearMap
    (cbCurryRight f hf)

@[simp] lemma averagedLastMultilinear_apply
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) (v : Fin n → M) :
    averagedLastMultilinear P f hf v = P.map (cbCurryRight f hf v) 1 := rfl

lemma averagedLastMultilinear_bound [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) (v : Fin n → M) :
    ‖averagedLastMultilinear P f hf v‖ ≤ C * ∏ i, ‖v i‖ := by
  rw [averagedLastMultilinear_apply]
  calc
    _ ≤ ‖P.map (cbCurryRight f hf v)‖ * ‖(1 : M)‖ := (P.map _).le_opNorm _
    _ = ‖P.map (cbCurryRight f hf v)‖ := by rw [norm_one, mul_one]
    _ ≤ _ := P.bound _ _ (hf.2 v)

def averagedLastCochain [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) : Cochain M n :=
  (averagedLastMultilinear P f hf).mkContinuous C (averagedLastMultilinear_bound P f hf)

@[simp] lemma averagedLastCochain_apply [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) (v : Fin n → M) :
    averagedLastCochain P f hf v = P.map (cbCurryRight f hf v) 1 := rfl

lemma averagedLastCochain_norm [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) :
    ‖averagedLastCochain P f hf‖ ≤ C :=
  MultilinearMap.mkContinuous_norm_le _ hf.1 _

lemma completelyBounded_id :
    CompletelyBoundedEstimate (ContinuousLinearMap.id ℂ M) 1 := by
  refine ⟨zero_le_one, fun n A => ?_⟩
  have h : A.map (ContinuousLinearMap.id ℂ M) = A := by ext i j; rfl
  rw [h, one_mul]

def cbIdentity : CompletelyBoundedMap M :=
  ⟨ContinuousLinearMap.id ℂ M, 1, completelyBounded_id⟩

def cbLeftMul (a : M) : CompletelyBoundedMap M := cbLeftSandwich a 1 cbIdentity

@[simp] lemma cbLeftMul_apply (a x : M) : (cbLeftMul a).val x = a * x := by
  simp [cbLeftMul, cbLeftSandwich, cbIdentity, leftSandwichMap]

lemma moduleProjection_leftMul (P : RightModuleAveragingProjection (M := M))
    (a : M) : P.map (cbLeftMul a) = (cbLeftMul a).val := by
  apply P.fixes
  intro x y
  simp only [cbLeftMul_apply, mul_assoc]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def shiftedColumnTuple {n : ℕ} (a b : Fin (n + 1) → M) (r : M)
    (k : Fin (n + 1)) : Fin (n + 1) → M :=
  fun j => if j < k then b j else if j = k then r * a j else a j

lemma shiftedColumnTuple_zero {n : ℕ} (a b : Fin (n + 1) → M) (r : M) :
    shiftedColumnTuple a b r 0 = Function.update a 0 (r * a 0) := by
  ext j
  by_cases hj : j = 0
  · subst j; simp [shiftedColumnTuple]
  · simp [shiftedColumnTuple, hj]

lemma multimodular_slide_column {R : StarSubalgebra ℂ M} {n : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (r : M) (hr : r ∈ R) (a b : Fin (n + 1) → M)
    (hb : ∀ j : Fin n, b j.castSucc * r = r * a j.castSucc)
    (k : Fin (n + 1)) : f (shiftedColumnTuple a b r k) = r * f a := by
  induction k using Fin.induction with
  | zero => rw [shiftedColumnTuple_zero]; exact hf.left r hr a
  | succ k ih =>
      let x : Fin (n + 1) → M := fun j => if j ≤ k.castSucc then b j else a j
      have h₀ : shiftedColumnTuple a b r k.castSucc =
          Function.update x k.castSucc (x k.castSucc * r) := by
        ext j
        by_cases he : j = k.castSucc
        · subst j
          simp [shiftedColumnTuple, x, hb k]
        · by_cases hj : j < k.castSucc
          · simp [shiftedColumnTuple, x, he, hj, le_of_lt hj]
          · have hle : ¬j ≤ k.castSucc := fun h => he (le_antisymm h (le_of_not_gt hj))
            simp [shiftedColumnTuple, x, he, hj, hle]
      have h₁ : shiftedColumnTuple a b r k.succ =
          Function.update x k.succ (r * x k.succ) := by
        ext j
        by_cases he : j = k.succ
        · subst j
          have hnot : ¬ k.succ ≤ k.castSucc := by simp [Fin.le_def]
          simp [shiftedColumnTuple, x, hnot]
        · have he' : j < k.succ ↔ j ≤ k.castSucc := by
            simp only [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
            omega
          simp [shiftedColumnTuple, x, he, he']
      rw [h₁, ← hf.balance r hr x k, ← h₀]
      exact ih

def columnDiagonal {m : ℕ} (c : Fin m → PartialIso M) (a : M) : M :=
  ∑ i, (c i : M) * a * star (c i : M)

lemma columnDiagonal_mul_column {m : ℕ} (c : Fin m → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (a : M) (j : Fin m) : columnDiagonal c a * (c j : M) = (c j : M) * a := by
  classical
  simp only [columnDiagonal, Finset.sum_mul, mul_assoc]
  simp [column_star_mul c hi ho]

lemma multimodular_column_term {R : StarSubalgebra ℂ M} {n m : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (c : Fin m → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hc : ∀ i, (c i : M) ∈ R) (a : Fin n → M) (y : M) (i j : Fin m) :
    f (Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y * star (c j : M))) =
      (c i : M) * f (Fin.snoc a y) * star (c j : M) := by
  have he : Function.update (Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y) :
      Fin (n + 1) → M) (Fin.last n) (((c i : M) * y) * star (c j : M)) =
      Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y * star (c j : M)) := by
    ext k
    refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
  have hright := hf.right (star (c j : M)) (star_mem (hc j))
    (Fin.snoc (fun k => columnDiagonal c (a k)) ((c i : M) * y))
  rw [Fin.snoc_last, he] at hright
  rw [hright]
  congr 1
  have h := multimodular_slide_column f hf (c i : M) (hc i)
    (Fin.snoc a y) (Fin.snoc (fun k => columnDiagonal c (a k)) y)
    (fun k => by simpa using columnDiagonal_mul_column c hi ho (a k) i) (Fin.last n)
  convert h using 2
  ext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [shiftedColumnTuple]
  · have hlt : k.castSucc < Fin.last n := by simp [Fin.lt_def]
    simp [shiftedColumnTuple, hlt]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma cb_cocycle_last_relation {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hs : LastSliceEstimate f C)
    (hf : ∀ x, differentialValue f x = 0) (v : Fin (n + 1) → M) :
    cbLeftSandwich (v 0) 1 (cbCurryRight f hs (fun i => v i.succ)) +
      (∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • cbCurryRight f hs (mergeInputs v j)) +
      ((-1 : ℂ) ^ (n + 1)) •
        cbLeftSandwich 1 (v (Fin.last n)) (cbCurryRight f hs (fun i => v i.castSucc)) +
      ((-1 : ℂ) ^ (n + 2)) • cbLeftMul (f v) = 0 := by
  apply Subtype.ext
  ext u
  have h := hf (Fin.snoc v u)
  rw [differentialValue_snoc] at h
  simpa [cbLeftSandwich, leftSandwichMap, cbCurryRight_val] using h

lemma averagedLastCochain_differential [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hs : LastSliceEstimate f C)
    (hf : ∀ x, differentialValue f x = 0) (v : Fin (n + 1) → M) :
    differentialValue (averagedLastCochain P f hs) v =
      ((-1 : ℂ) ^ (n + 1)) • f v := by
  have h := congrArg (fun T : CompletelyBoundedMap M => P.map T 1)
    (cb_cocycle_last_relation f hs hf v)
  simp only [map_add, map_sum, map_smul, add_apply,
    sum_apply, smul_apply,
    P.covariance, leftSandwichMap_apply, one_mul, mul_one,
    moduleProjection_leftMul, cbLeftMul_apply, map_zero, zero_apply] at h
  have hm := P.module (cbCurryRight f hs (fun i => v i.castSucc)) 1 (v (Fin.last n))
  rw [one_mul] at hm
  rw [hm] at h
  have hp : (-1 : ℂ) ^ (n + 2) = -((-1 : ℂ) ^ (n + 1)) := by
    rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
    ring
  rw [hp, neg_smul] at h
  apply eq_of_sub_eq_zero
  simpa only [differentialValue, averagedLastCochain_apply, sub_eq_add_neg] using h

theorem primitive_of_lastSliceEstimate [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hs : LastSliceEstimate f C)
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ C ∧ ∀ x, differentialValue g x = f x := by
  let g := ((-1 : ℂ) ^ (n + 1)) • averagedLastCochain P f hs
  refine ⟨g, ?_, fun x => ?_⟩
  · simpa only [g, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
      averagedLastCochain_norm P f hs
  · change differentialValue (((-1 : ℂ) ^ (n + 1)) • averagedLastCochain P f hs) x = f x
    rw [differentialValue_smul, averagedLastCochain_differential P f hs hf,
      smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma columnDiagonal_eq_reconstruction {m : ℕ} (c : Fin m → PartialIso M) (a : M) :
    columnDiagonal c a = columnReconstruction c (matrixScalarHom m a) := by
  classical
  simp [columnDiagonal, columnReconstruction, matrixScalarHom_apply]

lemma columnReconstruction_norm_for_multimodular {m : ℕ} (c : Fin m → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (A : CStarMatrix (Fin m) (Fin m) M) :
    ‖columnReconstruction c A‖ = ‖A‖ := by
  rw [← columnCompression_norm c hi ho hs (columnReconstruction c A),
    columnCompression_reconstruction c hi ho]

lemma columnDiagonal_norm_le {m : ℕ} (c : Fin m → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (a : M) : ‖columnDiagonal c a‖ ≤ ‖a‖ := by
  rw [columnDiagonal_eq_reconstruction, columnReconstruction_norm_for_multimodular c hi ho hs]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma multimodular_matrix_identity {R : StarSubalgebra ℂ M} {n m : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (c : Fin m → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hc : ∀ i, (c i : M) ∈ R) (a : Fin n → M) (A : CStarMatrix (Fin m) (Fin m) M) :
    f (Fin.snoc (fun k => columnDiagonal c (a k)) (columnReconstruction c A)) =
      columnReconstruction c (A.map (f.curryRight a)) := by
  classical
  calc
    _ = (f.curryRight (fun k => columnDiagonal c (a k)))
        (∑ i, ∑ j, (c i : M) * A i j * star (c j : M)) := rfl
    _ = ∑ i, ∑ j, f (Fin.snoc (fun k => columnDiagonal c (a k))
        ((c i : M) * A i j * star (c j : M))) := by
      simp only [map_sum, ContinuousMultilinearMap.curryRight_apply]
    _ = ∑ i, ∑ j, (c i : M) * f (Fin.snoc a (A i j)) * star (c j : M) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact multimodular_column_term f hf c hi ho hc a (A i j) i j
    _ = _ := rfl

lemma multimodular_last_matrix_bound {R : StarSubalgebra ℂ M} {n m : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (c : Fin m → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (hc : ∀ i, (c i : M) ∈ R)
    (a : Fin n → M) (A : CStarMatrix (Fin m) (Fin m) M) :
    ‖A.map (f.curryRight a)‖ ≤ (‖f‖ * ∏ k, ‖a k‖) * ‖A‖ := by
  rw [← columnReconstruction_norm_for_multimodular c hi ho hs (A.map (f.curryRight a)),
    ← multimodular_matrix_identity f hf c hi ho hc a A]
  calc
    _ ≤ (‖f‖ * ∏ k, ‖columnDiagonal c (a k)‖) * ‖columnReconstruction c A‖ :=
      f.norm_map_snoc_le _ _
    _ ≤ (‖f‖ * ∏ k, ‖a k‖) * ‖A‖ := by
      rw [columnReconstruction_norm_for_multimodular c hi ho hs]
      gcongr with k
      exact columnDiagonal_norm_le c hi ho hs (a k)

theorem lastSliceEstimate_of_multimodular_columns {R : StarSubalgebra ℂ M} {n : ℕ}
    (f : Cochain M (n + 1)) (hf : MultimodularOver R f)
    (hcols : ∀ m : ℕ, ∃ c : Fin (m + 1) → PartialIso M,
      (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      (∑ i, (c i).final = 1) ∧ ∀ i, (c i : M) ∈ R) :
    LastSliceEstimate f ‖f‖ := by
  refine ⟨norm_nonneg _, fun a => ⟨by positivity, fun m A => ?_⟩⟩
  cases m with
  | zero =>
      have hA : A = 0 := by ext i; exact Fin.elim0 i
      have hB : A.map (f.curryRight a) = 0 := by ext i; exact Fin.elim0 i
      rw [hB, hA, norm_zero, mul_zero]
  | succ m =>
      obtain ⟨c, hi, ho, hs, hc⟩ := hcols m
      exact multimodular_last_matrix_bound f hf c hi ho hs hc a A

theorem primitive_of_multimodular_columns [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M))
    {R : StarSubalgebra ℂ M} {n : ℕ} (f : Cochain M (n + 1))
    (hf : MultimodularOver R f)
    (hcols : ∀ m : ℕ, ∃ c : Fin (m + 1) → PartialIso M,
      (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      (∑ i, (c i).final = 1) ∧ ∀ i, (c i : M) ∈ R)
    (hcocycle : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  primitive_of_lastSliceEstimate P f (lastSliceEstimate_of_multimodular_columns f hf hcols)
    hcocycle
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem primitive_of_countableMatrix_multimodular [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain M (n + 1))
    (hf : MultimodularOver (countableMatrixClosure e c) f)
    (hcocycle : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  obtain ⟨P⟩ := exists_rightModuleAveragingProjection e hno
  apply primitive_of_multimodular_columns P f hf _ hcocycle
  intro m
  exact countableMatrixClosure_columns e c hi ho ht (m + 1)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma normal_maps_eq_on_linearClosure (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (A : StarSubalgebra ℂ M) (T U : M →L[ℂ] M)
    (hT : HasPreadjoint e T) (hU : HasPreadjoint e U)
    (h : ∀ a ∈ A, T a = U a) {a : M}
    (ha : (WeakAlgebra.weakEquiv e).symm a ∈ WeakAlgebra.linearClosure e A) : T a = U a := by
  have hclosed : IsClosed {F : WeakDual ℂ X |
      (WeakAlgebra.weakEquiv e).symm (T (WeakAlgebra.weakEquiv e F)) =
      (WeakAlgebra.weakEquiv e).symm (U (WeakAlgebra.weakEquiv e F))} :=
    isClosed_eq (WeakAlgebra.normal_continuous e T hT) (WeakAlgebra.normal_continuous e U hU)
  have hs : (WeakAlgebra.linearClosure e A : Set (WeakDual ℂ X)) ⊆
      {F | (WeakAlgebra.weakEquiv e).symm (T (WeakAlgebra.weakEquiv e F)) =
      (WeakAlgebra.weakEquiv e).symm (U (WeakAlgebra.weakEquiv e F))} := by
    apply closure_minimal _ hclosed
    rintro F ⟨b, hb, rfl⟩
    change (WeakAlgebra.weakEquiv e).symm
        (T (WeakAlgebra.weakEquiv e ((WeakAlgebra.weakEquiv e).symm b))) =
      (WeakAlgebra.weakEquiv e).symm
        (U (WeakAlgebra.weakEquiv e ((WeakAlgebra.weakEquiv e).symm b)))
    rw [LinearEquiv.apply_symm_apply, h b hb]
  simpa only [LinearEquiv.apply_symm_apply] using (WeakAlgebra.weakEquiv e).symm.injective (hs ha)

def updateSlice {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) : M →L[ℂ] M := sliceAt f i (i.removeNth v)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma updateSlice_apply {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) (a : M) : updateSlice f i v a = f (Function.update v i a) := by
  simp only [updateSlice, sliceAt_apply, Fin.insertNth_removeNth]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma updateSlice_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1)) (hn : SeparatelyNormal e f) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) : HasPreadjoint e (updateSlice f i v) := by
  intro z
  obtain ⟨w, hw⟩ := hn i v z
  exact ⟨w, fun a => by simpa only [updateSlice_apply] using hw a⟩

omit [PartialOrder M] [StarOrderedRing M] in
theorem normal_multimodular_countable_closure (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → HochschildComparison.PartialIso M) {n : ℕ} (f : Cochain M (n + 1))
    (hn : SeparatelyNormal e f) (hf : MultimodularOver (countableMatrixAlgebra c) f) :
    MultimodularOver (countableMatrixClosure e c) f := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hR := (HochschildSakai.abstract_multiplication_normal e).2
  constructor
  · intro r hr x
    have h := normal_maps_eq_on_linearClosure e (countableMatrixAlgebra c)
      ((updateSlice f 0 x).comp ((ContinuousLinearMap.mul ℂ M).flip (x 0)))
      ((ContinuousLinearMap.mul ℂ M).flip (f x))
      ((updateSlice_normal e f hn 0 x).comp e (hR (x 0))) (hR (f x))
      (fun a ha => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hf.left a ha x) hr
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h
  · intro r hr x
    have h := normal_maps_eq_on_linearClosure e (countableMatrixAlgebra c)
      ((updateSlice f (Fin.last n) x).comp (ContinuousLinearMap.mul ℂ M (x (Fin.last n))))
      (ContinuousLinearMap.mul ℂ M (f x))
      ((updateSlice_normal e f hn (Fin.last n) x).comp e (hL (x (Fin.last n)))) (hL (f x))
      (fun a ha => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.mul_apply'] using hf.right a ha x) hr
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.mul_apply'] using h
  · intro r hr x j
    have h := normal_maps_eq_on_linearClosure e (countableMatrixAlgebra c)
      ((updateSlice f j.castSucc x).comp (ContinuousLinearMap.mul ℂ M (x j.castSucc)))
      ((updateSlice f j.succ x).comp ((ContinuousLinearMap.mul ℂ M).flip (x j.succ)))
      ((updateSlice_normal e f hn j.castSucc x).comp e (hL (x j.castSucc)))
      ((updateSlice_normal e f hn j.succ x).comp e (hR (x j.succ)))
      (fun a ha => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hf.balance a ha x j) hr
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h

theorem primitive_of_normal_matrix_multimodular [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → HochschildComparison.PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain M (n + 1)) (hn : SeparatelyNormal e f)
    (hf : MultimodularOver (countableMatrixAlgebra c) f)
    (hcocycle : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  primitive_of_countableMatrix_multimodular e hno c hi ho ht f
    (normal_multimodular_countable_closure e c f hn hf) hcocycle
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem primitive_of_algebraic_matrix_multimodular [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain M (n + 2))
    (hM : MultimodularOver (countableMatrixAlgebra c) f)
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  obtain ⟨F, b, hFN, hFM, hFc, hid⟩ :=
    normal_reduction_multimodular e (countableMatrixAlgebra c) f hf hM
  obtain ⟨g, _, hg⟩ := primitive_of_normal_matrix_multimodular e hno c hi ho ht F hFN hFM hFc
  refine ⟨g + b, fun x => ?_⟩
  rw [differentialValue_add, hg]
  exact (hid x).symm
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.primitive_of_algebraic_matrix_multimodular.{u} := @OAI.BoundedHochschild.KadisonRingrose.primitive_of_algebraic_matrix_multimodular.{u}
