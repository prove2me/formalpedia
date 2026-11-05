-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.finite_noTypeII1_primitive
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:12:20.200563+00:00
-- url     : https://prove2.me/submissions/216c63e6-24e9-4062-9568-a2ed81c4e43a

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_fixes_normal
import Theorems.Thm_OAI_HochschildNormalPart_functionalModel_nonempty
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_finite_homogeneous_typeI_primitive_of_abelian_diagonal
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_faithful_normal_trace_of_center_state
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_homogeneous_piece_of_abelian_trace

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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

end BoundedHochschild

open scoped NNReal
namespace BoundedHochschild
variable {M I : Type*} [CStarAlgebra M]

lemma mul_eq_zero_of_supports (x y p q : M) (hxp : x*p=x) (hqy : q*y=y) (hpq : p*q=0) :
    x*y=0 := by
  calc
    x*y=(x*p)*(q*y) := by rw [hxp,hqy]
    _=x*(p*q)*y := by simp only [mul_assoc]
    _=0 := by rw [hpq,mul_zero,zero_mul]

lemma orthogonal_blocks_norm_sum_le (t : I → M)
    (hleft : ∀ i j, i ≠ j → star (t i)*t j=0)
    (hright : ∀ i j, i ≠ j → t i*star (t j)=0)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, t i‖ ≤ R := by
  classical
  have hdiag : star (∑ i ∈ s, t i)*(∑ i ∈ s, t i) = ∑ i ∈ s, star (t i)*t i := by
    simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_eq_single i (fun j _hj hji => hleft j i hji) (fun h => (h hi).elim)
  have horth : Pairwise (fun i j => (star (t i)*t i)*(star (t j)*t j)=0) := by
    intro i j hij
    calc
      (star (t i)*t i)*(star (t j)*t j) = star (t i)*(t i*star (t j))*t j := by simp only [mul_assoc]
      _ = 0 := by rw [hright i j hij,mul_zero,zero_mul]
  have hs := IsSelfAdjoint.nnnorm_sum_eq_sup s (fun i _hi => IsSelfAdjoint.star_mul_self (t i)) horth
  have hbound : ‖∑ i ∈ s, star (t i)*t i‖₊ ≤ (⟨R^2,sq_nonneg R⟩ : ℝ≥0) := by
    rw [hs]
    apply Finset.sup_le
    intro i hi
    change ‖star (t i)*t i‖ ≤ R^2
    rw [CStarRing.norm_star_mul_self]
    nlinarith [ht i hi,norm_nonneg (t i)]
  change ‖∑ i ∈ s, star (t i)*t i‖ ≤ R^2 at hbound
  rw [← hdiag,CStarRing.norm_star_mul_self] at hbound
  nlinarith [norm_nonneg (∑ i ∈ s, t i)]

lemma supported_sum_norm_le (p t : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (hpt : ∀ i, p i*t i=t i) (htp : ∀ i, t i*p i=t i)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, t i‖ ≤ R := by
  apply orthogonal_blocks_norm_sum_le t _ _ s R hR ht
  · intro i j hij
    apply mul_eq_zero_of_supports _ _ (p i) (p j) _ (hpt j) (horth i j hij)
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg Star.star (hpt i)
  · intro i j hij
    apply mul_eq_zero_of_supports _ _ (p i) (p j) (htp i) _ (horth i j hij)
    simpa only [star_mul,(hp j).isSelfAdjoint.star_eq] using congrArg Star.star (htp j)
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
variable {M : Type*} [CStarAlgebra M]

def centralCut {n : ℕ} (z : M) (f : Cochain M n) : Cochain M n :=
  f.compContinuousLinearMap (fun _ => ContinuousLinearMap.mul ℂ M z)

@[simp] lemma centralCut_apply {n : ℕ} (z : M) (f : Cochain M n) (v : Fin n → M) :
    centralCut z f v = f (fun i => z*v i) := rfl

lemma central_mul_assoc (z : M) (hz : ∀ a, z*a=a*z) (a b : M) :
    a*(z*b) = z*(a*b) := by rw [← mul_assoc, ← hz, mul_assoc]

lemma central_idempotent_mul (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z) (a b : M) :
    (z*a)*(z*b) = z*(a*b) := by
  rw [mul_assoc, central_mul_assoc z hz, ← mul_assoc z z, hi]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*}

def tupleInsert {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) (i : Fin (n+1)) : M :=
  if h : i.val < p.val then v ⟨i.val, by omega⟩
  else if h : i = p then a else v ⟨i.val-1, by have := i.isLt; have := p.isLt; omega⟩

lemma tupleInsert_eq {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) :
    tupleInsert p a v = p.insertNth a v := by
  apply (Fin.eq_insertNth_iff).mpr
  constructor
  · simp [tupleInsert]
  · funext i
    change tupleInsert p a v (p.succAbove i) = v i
    by_cases h : i.castSucc < p
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      dsimp [tupleInsert]
      rw [dite_eq_left (show i.val < p.val from h)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
      dsimp [tupleInsert]
      rw [dite_eq_right (by change ¬i.val < p.val at h; omega),
        ite_eq_right (by intro he; have hv := congrArg Fin.val he; dsimp at hv; change ¬i.val < p.val at h; omega)]

lemma tupleInsert_lt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : i.val < p.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val, by omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_left h]

lemma tupleInsert_gt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : p.val < i.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val-1, by have := i.isLt; omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_right (by omega : ¬i.val < p.val),
    dite_eq_right (by intro he; have := congrArg Fin.val he; omega : i ≠ p)]

lemma merge_insert_same [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hq : q*v r=v r) : mergeInputs (r.castSucc.insertNth q v) r = v := by
  funext i
  simp only [mergeInputs]
  split_ifs with h h
  · rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc, Fin.lt_def] using h)]
    rfl
  · subst i
    rw [Fin.insertNth_apply_same, tupleInsert_gt _ _ _ _ (by simp)]
    simpa using hq
  · rw [tupleInsert_gt _ _ _ _ (by simpa only [Fin.val_castSucc,Fin.val_succ] using
        (show r.val < i.val+1 by omega))]
    rfl

lemma merge_insert_before [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : j.val+1 < r.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.castSucc := by
    exact Fin.succAbove_of_castSucc_lt _ _ (by simpa only [Fin.lt_def, Fin.val_castSucc] using (show j.val < r.val by omega))
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)

lemma merge_insert_after [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : r.val ≤ j.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.succ := by
    exact Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def, Fin.val_castSucc] using hjr)
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals first | rfl | (apply Fin.ext; dsimp; omega) |
    (apply congrArg v; apply Fin.ext; dsimp; omega)

lemma tail_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hr : 0 < r.val) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.succ) =
    (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth (α := fun _ => M) q (fun i => v i.succ) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)

lemma init_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.castSucc) =
    r.insertNth (α := fun _ => M) q (fun i => v i.castSucc) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> rfl

lemma last_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (r.castSucc.insertNth (α := fun _ => M) q v) (Fin.last (n+1)) = v (Fin.last n) := by
  rw [tupleInsert_gt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.val_last]; omega)]
  rfl

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

def centralJTerm {n : ℕ} (z q : M) (f : Cochain M (n+1)) (i : Fin n) : Cochain M n :=
  (f.curryMid i.castSucc q).compContinuousLinearMap (fun j =>
    if j < i then ContinuousLinearMap.mul ℂ M z
    else if j = i then ContinuousLinearMap.mul ℂ M q
    else ContinuousLinearMap.id ℂ M)

@[simp] lemma centralJTerm_apply {n : ℕ} (z q : M) (f : Cochain M (n+1))
    (i : Fin n) (v : Fin n → M) :
    centralJTerm z q f i v = f (i.castSucc.insertNth q (fun j =>
      if j < i then z*v j else if j = i then q*v j else v j)) := by
  change f (i.castSucc.insertNth q (fun j => (if j < i then ContinuousLinearMap.mul ℂ M z
    else if j = i then ContinuousLinearMap.mul ℂ M q else ContinuousLinearMap.id ℂ M) (v j))) = _
  apply congrArg (fun w => f (i.castSucc.insertNth q w))
  funext j
  split_ifs <;> rfl

def centralJ {n : ℕ} (z q : M) (f : Cochain M (n+1)) : Cochain M n :=
  ∑ i : Fin n, ((-1:ℂ)^(i.val+1)) • centralJTerm z q f i

lemma norm_centralJTerm_le {n : ℕ} (z q : M) (hz : ‖z‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (f : Cochain M (n+1)) (i : Fin n) : ‖centralJTerm z q f i‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  rw [centralJTerm_apply]
  apply (f.norm_map_insertNth_le _ _).trans
  calc
    ‖f‖ * ‖q‖ * (∏ j, ‖if j < i then z*v j else if j = i then q*v j else v j‖) ≤
        ‖f‖ * 1 * (∏ j, ‖v j‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      · apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro j _
        split_ifs
        · exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (v j)])
        · exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (v j)])
        · rfl
      · positivity
      · positivity
    _ = _ := by ring

lemma norm_centralJ_le {n : ℕ} (z q : M) (hz : ‖z‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (f : Cochain M (n+1)) : ‖centralJ z q f‖ ≤ n*‖f‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i : Fin n, ‖((-1:ℂ)^(i.val+1)) • centralJTerm z q f i‖ ≤
        ∑ _ : Fin n, ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        using norm_centralJTerm_le z q hz hq f i
    _ = _ := by simp

lemma centralJ_range {n : ℕ} (z q : M) (f : Cochain M (n+1))
    (hr : ∀ v, z*f v=f v) (v : Fin n → M) : z*centralJ z q f v=centralJ z q f v := by
  simp only [centralJ, sum_apply, smul_apply, centralJTerm_apply, Finset.mul_sum,
    mul_smul_comm, hr]

lemma centralJTerm_eq_zero_lt {n : ℕ} (z q : M) (hzq : q*z=0)
    (f : Cochain M (n+1)) (i r : Fin n) (hir : i < r) (v : Fin n → M)
    (hv : ∀ j, j < r → z*v j=v j) : centralJTerm z q f i v=0 := by
  have hqi : q*v i=0 := by rw [← hv i hir, ← mul_assoc, hzq, zero_mul]
  rw [centralJTerm_apply]
  apply f.map_coord_zero ((i.castSucc).succAbove i)
  simp only [Fin.insertNth_apply_succAbove, lt_self_iff_false, ite_false, ite_true, hqi]

lemma centralJTerm_eq_zero_gt {n : ℕ} (z q : M) (hzq : z*q=0)
    (f : Cochain M (n+1)) (i r : Fin n) (hri : r < i) (v : Fin n → M)
    (hv : q*v r=v r) : centralJTerm z q f i v=0 := by
  have hzr : z*v r=0 := by rw [← hv, ← mul_assoc, hzq, zero_mul]
  rw [centralJTerm_apply]
  apply f.map_coord_zero ((i.castSucc).succAbove r)
  simp only [Fin.insertNth_apply_succAbove, hri, ite_true, hzr]

lemma centralJ_first_q {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (r : Fin n) (v : Fin n → M)
    (hv : ∀ j, j < r → z*v j=v j) (hvr : q*v r=v r) :
    centralJ z q f v = ((-1:ℂ)^(r.val+1)) • f (r.castSucc.insertNth q v) := by
  classical
  rw [centralJ, sum_apply, Finset.sum_eq_single r]
  · simp only [smul_apply, centralJTerm_apply]
    apply congrArg (fun w => ((-1:ℂ)^(r.val+1)) • f (r.castSucc.insertNth q w))
    funext j
    split_ifs with h h
    · exact hv j h
    · subst j; exact hvr
    · rfl
  · intro i _ hir
    rw [smul_apply]
    have hi : centralJTerm z q f i v=0 := by
      rcases lt_or_gt_of_ne hir with h | h
      · exact centralJTerm_eq_zero_lt z q hqz f i r h v hv
      · exact centralJTerm_eq_zero_gt z q hzq f i r h v hvr
    rw [hi, smul_zero]
  · simp

lemma centralJ_all_z {n : ℕ} (z q : M) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin n → M) (hv : ∀ j, z*v j=v j) :
    centralJ z q f v=0 := by
  rw [centralJ, sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [smul_apply]
  have hi : centralJTerm z q f i v=0 := by
    have hqi : q*v i=0 := by rw [← hv i, ← mul_assoc, hqz, zero_mul]
    rw [centralJTerm_apply]
    apply f.map_coord_zero ((i.castSucc).succAbove i)
    simp only [Fin.insertNth_apply_succAbove, lt_self_iff_false, ite_false, ite_true, hqi]
  rw [hi, smul_zero]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

lemma centralJ_merge_before {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : j.val+1 < r.val) :
    centralJ z q f (mergeInputs v j) = ((-1:ℂ)^r.val) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j)) := by
  rw [merge_insert_before v r q j hjr]
  let r' : Fin n := ⟨r.val-1, by omega⟩
  have hh : ∀ i, i < r' → z*mergeInputs v j i=mergeInputs v j i := by
    intro i hi
    simp only [mergeInputs]
    split_ifs with h h
    · exact hv i.castSucc (by simp only [Fin.lt_def, Fin.val_castSucc] at *; omega)
    · subst i
      rw [← mul_assoc, hv j.castSucc (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]
    · exact hv i.succ (by simp only [r', Fin.lt_def,Fin.val_succ] at *; omega)
  have hq : q*mergeInputs v j r'=mergeInputs v j r' := by
    have hlo : ¬r' < j := by simp only [r', Fin.lt_def]; omega
    have hne : r' ≠ j := by intro h; have hh := congrArg Fin.val h; dsimp [r'] at hh; omega
    have he : r'.succ=r := Fin.ext (by dsimp [r']; omega)
    simp only [mergeInputs, hlo, hne, ite_false, he]
    exact hvr
  rw [centralJ_first_q z q hzq hqz f r' _ hh hq]
  have he : r'.val+1=r.val := by dsimp [r']; omega
  rw [he]
  rfl

lemma centralJ_merge_after {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : r.val ≤ j.val) :
    centralJ z q f (mergeInputs v j) = ((-1:ℂ)^(r.val+1)) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j)) := by
  rw [merge_insert_after v r q j hjr]
  let r' : Fin n := ⟨r.val, by omega⟩
  have hh : ∀ i, i < r' → z*mergeInputs v j i=mergeInputs v j i := by
    intro i hi
    have hh : i<j := by simp only [r', Fin.lt_def] at *; omega
    simp only [mergeInputs, hh, ite_true]
    exact hv i.castSucc (by simpa only [r', Fin.lt_def,Fin.val_castSucc] using hi)
  have hq : q*mergeInputs v j r'=mergeInputs v j r' := by
    have he : r'.castSucc=r := rfl
    simp only [mergeInputs]
    split_ifs with hlt heq
    · simpa only [he] using hvr
    · rw [he, ← mul_assoc, hvr]
    · exfalso
      apply heq
      apply Fin.ext
      change r.val = j.val
      change ¬r.val < j.val at hlt
      omega
  exact centralJ_first_q z q hzq hqz f r' _ hh hq

lemma centralJ_merge_boundary {n : ℕ} (z q : M) (hzq : z*q=0) (hz : ∀ a, z*a=a*z)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : j.val+1 = r.val) :
    centralJ z q f (mergeInputs v j)=0 ∧
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))=0 := by
  have hjr' : j.succ=r := Fin.ext hjr
  have hlt : j.castSucc<r := by simp only [Fin.lt_def, Fin.val_castSucc]; omega
  have hvj : v j.castSucc*q=0 := by
    rw [← hv _ hlt, mul_assoc, ← central_mul_assoc z hz, hzq, mul_zero]
  constructor
  · apply (centralJ z q f).map_coord_zero j
    simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true, hjr']
    rw [← hvr, ← mul_assoc, hvj, zero_mul]
  · apply f.map_coord_zero j.castSucc
    have hes : r.succAbove j=j.castSucc := Fin.succAbove_of_castSucc_lt _ _ hlt
    rw [hes]
    simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true]
    rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc] using (show j.val<r.val by omega))]
    have he : j.castSucc.succ=r.castSucc := Fin.ext (by simp only [Fin.val_succ,Fin.val_castSucc]; omega)
    rw [he, Fin.insertNth_apply_same]
    exact hvj

lemma centralJ_inner_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n) :
    ((-1:ℂ)^(r.val+1)) • (((-1:ℂ)^((r.succAbove j).val+1)) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))) =
        - (((-1:ℂ)^(j.val+1)) • centralJ z q f (mergeInputs v j)) := by
  rcases lt_trichotomy (j.val+1) r.val with h | h | h
  · rw [centralJ_merge_before z q hzq hqz f v r hv hvr j h]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)]
    simp only [Fin.val_castSucc, smul_smul, ← neg_smul]
    congr 1
    rw [pow_succ]
    ring
  · obtain ⟨h₁,h₂⟩ := centralJ_merge_boundary z q hzq hz f v r hv hvr j h
    rw [h₁,h₂,smul_zero,smul_zero,smul_zero,neg_zero]
  · have hrj : r.val ≤ j.val := by omega
    rw [centralJ_merge_after z q hzq hqz f v r hv hvr j hrj]
    rw [Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hrj)]
    simp only [Fin.val_succ, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

lemma centralJ_left_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) :
    ((-1:ℂ)^(r.val+1)) • ((r.castSucc.insertNth (α := fun _ => M) q v) 0 *
      f (fun i => (r.castSucc.insertNth (α := fun _ => M) q v) i.succ)) =
        -(v 0 * centralJ z q f (fun i => v i.succ)) := by
  by_cases hro : r.val=0
  · have hre : r=0 := Fin.ext hro
    subst r
    have hqf : ∀ w, q*f w=0 := by intro w; rw [← hr w, ← mul_assoc, hqz, zero_mul]
    have hvrz : v 0*z=0 := by
      rw [← hvr, mul_assoc, ← hz (v 0), ← mul_assoc, hqz, zero_mul]
    have hrj := centralJ_range z q f hr (fun i => v i.succ)
    have hh : v 0*centralJ z q f (fun i => v i.succ)=0 := by
      rw [← hrj, ← mul_assoc, hvrz, zero_mul]
    simp only [Fin.castSucc_zero, Fin.insertNth_apply_same, hqf, smul_zero, hh, neg_zero]
  · have hro : 0<r.val := by omega
    let r' : Fin n := ⟨r.val-1, by omega⟩
    have hv' : ∀ i, i<r' → z*v i.succ=v i.succ := by
      intro i hi
      exact hv _ (by simp only [r', Fin.lt_def,Fin.val_succ] at *; omega)
    have he : r'.succ=r := Fin.ext (by dsimp [r']; omega)
    have hq' : q*v r'.succ=v r'.succ := by simpa only [he] using hvr
    rw [centralJ_first_q z q hzq hqz f r' _ hv' hq', tail_insert v r q hro,
      tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_zero,Fin.val_castSucc] using hro)]
    have he' : r'.val+1=r.val := by dsimp [r']; omega
    rw [he', mul_smul_comm, ← neg_smul, pow_succ]
    congr 1
    ring

lemma centralJ_right_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) :
    ((-1:ℂ)^(r.val+1)) • (((-1:ℂ)^(n+2)) •
      (f (fun i => (r.castSucc.insertNth (α := fun _ => M) q v) i.castSucc) *
        (r.castSucc.insertNth (α := fun _ => M) q v) (Fin.last (n+1)))) =
        - (((-1:ℂ)^(n+1)) • (centralJ z q f (fun i => v i.castSucc)*v (Fin.last n))) := by
  rw [init_insert, last_insert]
  by_cases hrl : r.val=n
  · have hre : r=Fin.last n := Fin.ext hrl
    subst r
    have hv' : ∀ i : Fin n, z*v i.castSucc=v i.castSucc := by
      intro i; exact hv _ (by simpa only [Fin.lt_def,Fin.val_last,Fin.val_castSucc] using i.isLt)
    rw [centralJ_all_z z q hqz f _ hv', zero_mul, smul_zero, neg_zero]
    have hh : z*v (Fin.last n)=0 := by rw [← hvr, ← mul_assoc, hzq, zero_mul]
    have he : f ((Fin.last n).insertNth q (fun i => v i.castSucc))*v (Fin.last n)=0 := by
      rw [← hr, hz, mul_assoc, hh, mul_zero]
    rw [he, smul_zero, smul_zero]
  · let r' : Fin n := ⟨r.val, by omega⟩
    have hv' : ∀ i, i<r' → z*v i.castSucc=v i.castSucc := by
      intro i hi; exact hv _ (by simpa only [r', Fin.lt_def,Fin.val_castSucc] using hi)
    have he : r'.castSucc=r := rfl
    have hq' : q*v r'.castSucc=v r'.castSucc := by simpa only [he] using hvr
    rw [centralJ_first_q z q hzq hqz f r' _ hv' hq', he]
    simp only [r', smul_mul_assoc, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

lemma differential_centralJ_first_q {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i<r → z*v i=v i) (hvr : q*v r=v r) :
    differentialValue (centralJ z q f) v=f v := by
  have h := congrArg (fun a => ((-1:ℂ)^(r.val+1)) • a)
    (hf (r.castSucc.insertNth (α := fun _ => M) q v))
  simp only [smul_zero, differentialValue, smul_add] at h
  rw [centralJ_left_cancellation z q hzq hqz hz f hr v r hv hvr,
    centralJ_right_cancellation z q hzq hqz hz f hr v r hv hvr,
    Fin.sum_univ_succAbove _ r, smul_add, merge_insert_same v r q hvr,
    smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul, Finset.smul_sum] at h
  have hi : ∑ j : Fin n, ((-1:ℂ)^(r.val+1)) •
      (((-1:ℂ)^((r.succAbove j).val+1)) •
        f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))) =
      -(∑ j : Fin n, ((-1:ℂ)^(j.val+1)) • centralJ z q f (mergeInputs v j)) := by
    simp only [centralJ_inner_cancellation z q hzq hqz hz f v r hv hvr, Finset.sum_neg_distrib]
  rw [hi] at h
  have h' : f v - differentialValue (centralJ z q f) v = 0 := by
    convert h using 1
    simp only [differentialValue]
    abel
  exact (sub_eq_zero.mp h').symm

lemma differential_centralJ_all_z {n : ℕ} (z q : M) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (hv : ∀ i, z*v i=v i) :
    differentialValue (centralJ z q f) v=0 := by
  have hl : centralJ z q f (fun i : Fin n => v i.succ)=0 := centralJ_all_z z q hqz f _ (fun _ => hv _)
  have hr : centralJ z q f (fun i : Fin n => v i.castSucc)=0 := centralJ_all_z z q hqz f _ (fun _ => hv _)
  have hm (j : Fin n) : centralJ z q f (mergeInputs v j)=0 := by
    apply centralJ_all_z z q hqz f
    intro i
    simp only [mergeInputs]
    split_ifs
    · exact hv _
    · rw [← mul_assoc, hv]
    · exact hv _
  simp only [differentialValue, hl,hr,hm,mul_zero,zero_mul,smul_zero,Finset.sum_const_zero,add_zero]

theorem differential_centralJ {n : ℕ} (z : M) (hzz : z*z=z) (hz : ∀ a, z*a=a*z)
    (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) (v : Fin (n+1) → M) :
    differentialValue (centralJ z (1-z) f) v = f v - centralCut z f v := by
  classical
  let q := 1-z
  have hzq : z*q=0 := by dsimp [q]; rw [mul_sub,mul_one,hzz,sub_self]
  have hqz : q*z=0 := by dsimp [q]; rw [sub_mul,one_mul,hzz,sub_self]
  have hqq : q*q=q := by dsimp [q]; rw [mul_sub,sub_mul,sub_mul,one_mul,mul_one,one_mul,hzz]; abel
  let D := differential (centralJ z q f) - f + centralCut z f
  have hall (w : Fin (n+1) → M) (hw : ∀ i, z*w i=w i ∨ q*w i=w i) : D w=0 := by
    by_cases hzall : ∀ i, z*w i=w i
    · have he : (fun i => z*w i)=w := funext hzall
      simp only [D,add_apply,sub_apply,differential_apply,
        differential_centralJ_all_z z q hqz f w hzall, centralCut_apply, he]
      abel
    · let bad : Finset (Fin (n+1)) := Finset.univ.filter (fun i => z*w i≠w i)
      have hb : bad.Nonempty := by
        push Not at hzall
        obtain ⟨i,hi⟩ := hzall
        exact ⟨i, by simp [bad,hi]⟩
      let r := bad.min' hb
      have hrb : r∈bad := Finset.min'_mem bad hb
      have hzr : z*w r≠w r := (Finset.mem_filter.mp hrb).2
      have hqr : q*w r=w r := (hw r).resolve_left hzr
      have hprefix : ∀ i, i<r → z*w i=w i := by
        intro i hi
        by_contra h
        have him : i∈bad := by simp [bad,h]
        have hil : r ≤ i := Finset.min'_le bad i him
        exact (not_le_of_gt hi) hil
      have hc : centralCut z f w=0 := by
        apply f.map_coord_zero r
        change z*w r=0
        rw [← hqr, ← mul_assoc, hzq, zero_mul]
      simp only [D,add_apply,sub_apply,differential_apply,
        differential_centralJ_first_q z q hzq hqz hz f hr hf w r hprefix hqr,
        hc,sub_self,add_zero]
  have hvsum : (fun i => z*v i) + (fun i => q*v i)=v := by
    funext i
    change z*v i+(1-z)*v i=v i
    rw [sub_mul,one_mul]
    abel
  have hd : D v=0 := by
    rw [← hvsum, D.map_add_univ]
    apply Finset.sum_eq_zero
    intro s _
    apply hall
    intro i
    by_cases his : i∈s
    · left
      simp only [Finset.piecewise,his,ite_true,← mul_assoc,hzz]
    · right
      simp only [Finset.piecewise,his,ite_false,← mul_assoc,hqq]
  change differentialValue (centralJ z q f) v = _
  simp only [D,add_apply,sub_apply,differential_apply] at hd
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = (differentialValue (centralJ z q f) v - f v + centralCut z f v) + f v := by abel
    _ = f v := by rw [hd,zero_add]

theorem central_cocycle_correction {n : ℕ} (z : M) (hp : IsStarProjection z)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) :
    ∃ g : Cochain M n, ‖g‖ ≤ n*‖f‖ ∧ (∀ w, z*g w=g w) ∧
      ∀ w, differentialValue g w = f w-centralCut z f w := by
  have hq : IsStarProjection (1-z) := hp.one_sub
  exact ⟨centralJ z (1-z) f, norm_centralJ_le z (1-z) (IsStarProjection.norm_le z hp)
    (IsStarProjection.norm_le (1-z) hq) f, centralJ_range z (1-z) f hr,
    differential_centralJ z hp.isIdempotentElem.eq hz f hr hf⟩
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

lemma central_differential_values {n : ℕ} (p : M) (hp : ∀ a, p*a=a*p)
    (f g : Cochain M n) (hfg : ∀ x, p*f x=g x) (x : Fin (n+1) → M) :
    p*differentialValue f x=differentialValue g x := by
  simp only [differentialValue,mul_add,Finset.mul_sum,mul_smul_comm]
  congr 2
  · rw [← mul_assoc,hp (x 0),mul_assoc,hfg]
  · apply Finset.sum_congr rfl
    intro j _
    rw [hfg]
  · rw [← mul_assoc,hfg]

lemma norm_sum_supported_cochains {n : ℕ} (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0) (g : I → Cochain M n)
    (hleft : ∀ i x, p i*g i x=g i x) (hright : ∀ i x, g i x*p i=g i x)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ i, ‖g i‖ ≤ C) (s : Finset I) :
    ‖∑ i ∈ s, g i‖ ≤ C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro x
  rw [sum_apply]
  apply supported_sum_norm_le p (fun i => g i x) hp horth
    (fun i => hleft i x) (fun i => hright i x) s (C*∏ j,‖x j‖)
    (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  intro i _
  exact (g i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hg i)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem primitive_of_central_pieces
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hcentral : ∀ i a, p i*a=a*p i)
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (htotal : ∀ x : M, (∀ i, p i*x=0) → x=0)
    {n : ℕ} (f : Cochain M (n+1)) (g : I → Cochain M n)
    (hleft : ∀ i x, p i*g i x=g i x)
    (hdf : ∀ i x, differentialValue (g i) x=p i*f x)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ i, ‖g i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧ ∀ x, differentialValue G x=f x := by
  classical
  let F : Finset I → Cochain M n := fun s => ∑ i ∈ s, g i
  have hF (s : Finset I) : ‖F s‖ ≤ C :=
    norm_sum_supported_cochains p hp horth g hleft
      (fun i x => by rw [← hcentral,hleft]) C hC hg s
  let U : Ultrafilter (Finset I) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset I)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U F C hC hF
  have hproj (i : I) (x : Fin n → M) : p i*G x=g i x := by
    have hlim := (hL (p i)).tendsto e (ht x)
    have hex : (fun s => p i*F s x) =ᶠ[U] (fun _ => g i x) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({i} : Finset I)] with s hs
      have hi : i ∈ s := hs (Finset.mem_singleton_self i)
      change p i*(∑ j ∈ s,g j) x=g i x
      rw [sum_apply,Finset.mul_sum]
      rw [Finset.sum_eq_single i]
      · exact hleft i x
      · intro j _ hji
        calc
          p i*g j x=p i*(p j*g j x) := by rw [hleft]
          _=0 := by rw [← mul_assoc,horth i j hji.symm,zero_mul]
      · exact fun hh => (hh hi).elim
    apply predual_tendsto_unique e hlim
    intro z
    exact tendsto_const_nhds.congr' (hex.mono fun _ h => congrArg (fun a : M => e.symm a z) h.symm)
  refine ⟨G,hG,fun x => sub_eq_zero.mp (htotal _ fun i => ?_)⟩
  rw [mul_sub,central_differential_values (p i) (hcentral i) G (g i) (hproj i),hdf,sub_self]

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

theorem primitive_of_central_cut_primitives
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hcentral : ∀ i a, p i*a=a*p i)
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (htotal : ∀ x : M, (∀ i, p i*x=0) → x=0)
    {n : ℕ} (f : Cochain M (n+1)) (hf : ∀ x, differentialValue f x=0)
    (b : I → Cochain M n) (hb : ∀ i x, p i*b i x=b i x)
    (hdb : ∀ i x, differentialValue (b i) x=centralCut (p i) (centralOutput (p i) f) x)
    (C : ℝ) (hC : 0 ≤ C) (hbn : ∀ i, ‖b i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C+n*‖f‖ ∧ ∀ x, differentialValue G x=f x := by
  have hsupport (i : I) (x : Fin (n+1) → M) :
      p i*centralOutput (p i) f x=centralOutput (p i) f x := by
    simp only [centralOutput_apply,← mul_assoc,(hp i).isIdempotentElem.eq]
  have hcoc (i : I) (x : Fin (n+2) → M) : differentialValue (centralOutput (p i) f) x=0 := by
    rw [← central_differential_values (p i) (hcentral i) f (centralOutput (p i) f)
      (fun _ => rfl),hf,mul_zero]
  choose a han has had using fun i =>
    central_cocycle_correction (p i) (hp i) (hcentral i) (centralOutput (p i) f)
      (hsupport i) (hcoc i)
  let g : I → Cochain M n := fun i => b i+a i
  have hgn (i : I) : ‖g i‖ ≤ C+n*‖f‖ := by
    calc
      ‖g i‖ ≤ ‖b i‖+‖a i‖ := norm_add_le _ _
      _ ≤ C+n*‖centralOutput (p i) f‖ := add_le_add (hbn i) (han i)
      _ ≤ C+n*‖f‖ := add_le_add_right
        (mul_le_mul_of_nonneg_left (norm_centralOutput_le (p i) ((hp i).norm_le) f)
          (Nat.cast_nonneg _)) C
  apply primitive_of_central_pieces e hL p hp hcentral horth htotal f g
    (fun i x => by simp only [g,add_apply,mul_add,hb,has]) _ _ (by positivity) hgn
  intro i x
  simp only [g,differentialValue_add,hdb,had]
  rw [add_sub_cancel,centralOutput_apply]
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

theorem exists_central_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
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
  obtain ⟨p, _hpnorm, ht⟩ := exists_predual_ultralimit e U
    (fun q : S => (q : M)) 1 (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ hr => congrArg (fun a : M => e.symm a z) hr.symm)
  have hpcentral (a : M) : p * a = a * p := by
    have hl := HochschildSakai.predual_tendsto_mul_left e a ht
    have hr := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => a * (q : M)) = (fun q : S => (q : M) * a) := by
      funext q
      exact (hcentral q q.property a).symm
    rw [heq] at hl
    exact predual_tendsto_unique e hr hl
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
  refine ⟨p, hp, hpcentral, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hub
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hub q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) := by
      funext q
      exact ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))

theorem exists_central_projection_chain_supremum
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) := by
  obtain ⟨p, hp, hc, hu, hl, ha, _⟩ :=
    exists_central_projection_chain_supremum_with_limit e S hne hchain hproj hcentral
  exact ⟨p, hp, hc, hu, hl, ha⟩
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

lemma normal_continuous (A : M →L[ℂ] M) (hA : HasPreadjoint e A) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (A (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  obtain ⟨w,hw⟩ := hA z
  change Continuous (fun f : WeakDual ℂ X => e.symm (A (weakEquiv e f)) z)
  simp_rw [hw]
  simpa [weakEquiv] using WeakDual.eval_continuous (𝕜 := ℂ) w

variable (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_mem_corner {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) : q ∈ corner p hp :=
  ⟨(hq.le_iff_mul_eq_right hp).mp hqp,(hq.le_iff_mul_eq_left hp).mp hqp⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_mem_corner {p : M} (hp : IsStarProjection p) (a : M) :
    p*a*p ∈ corner p hp := by
  exact ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],
    by rw [mul_assoc,hp.isIdempotentElem.eq]⟩

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end HochschildCorners

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

section Predual
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakCorner : Submodule ℂ (WeakDual ℂ X) where
  carrier := {f | weakEquiv e f ∈ corner p hp}
  zero_mem' := by
    change weakEquiv e 0 ∈ corner p hp
    rw [map_zero]
    exact (corner p hp).zero_mem
  add_mem' := by
    intro a b ha hb
    change weakEquiv e (a+b) ∈ corner p hp
    rw [map_add]
    exact (corner p hp).add_mem ha hb
  smul_mem' := by
    intro c a ha
    change weakEquiv e (c • a) ∈ corner p hp
    rw [LinearEquiv.map_smulₛₗ]
    exact (corner p hp).smul_mem (star c) ha

lemma weakCorner_closed : IsClosed (weakCorner p hp e : Set (WeakDual ℂ X)) := by
  have hL := mul_hasPreadjoint e p
  have hR := mul_right_hasPreadjoint e p
  have hLeft := isClosed_eq (normal_continuous e _ hL) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  have hRight := isClosed_eq (normal_continuous e _ hR) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  change IsClosed {f | (weakEquiv e).symm (p*weakEquiv e f)=f} at hLeft
  change IsClosed {f | (weakEquiv e).symm (weakEquiv e f*p)=f} at hRight
  convert hLeft.inter hRight using 1
  ext f
  change (p*weakEquiv e f=weakEquiv e f ∧ weakEquiv e f*p=weakEquiv e f) ↔
    ((weakEquiv e).symm (p*weakEquiv e f)=f ∧ (weakEquiv e).symm (weakEquiv e f*p)=f)
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨by rw [h,LinearEquiv.symm_apply_apply],by rw [h',LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨h,h'⟩
    exact ⟨by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h,
      by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h'⟩

def CornerPredual := X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)
instance : NormedAddCommGroup (CornerPredual p hp e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : NormedSpace ℂ (CornerPredual p hp e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : CompleteSpace (CornerPredual p hp e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))

def cornerStrongEquiv : WeakSubspace.strong (weakCorner p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp where
  toFun f := ⟨e f.val,by
    have hf := (WeakSubspace.mem_strong (weakCorner p hp e) f.val).mp f.property
    exact hf⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ corner p hp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using a.property⟩
  left_inv f := Subtype.ext (e.symm_apply_apply f.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)
  map_add' f g := Subtype.ext (map_add e f.val g.val)
  map_smul' c f := Subtype.ext (e.map_smulₛₗ c f.val)
  norm_map' f := e.norm_map f.val

def cornerPredualEquiv : StrongDual ℂ (CornerPredual p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp :=
  (WeakSubspace.quotientDualEquiv (weakCorner p hp e) (weakCorner_closed p hp e)).trans
    (cornerStrongEquiv p hp e)

lemma cornerPredualEquiv_apply (F : StrongDual ℂ (CornerPredual p hp e)) (z : X) :
    e.symm ((cornerPredualEquiv p hp e F : Corner p hp):M) z=F (Submodule.Quotient.mk z) := by
  change e.symm (e (F.comp (WeakSubspace.preannihilator (weakCorner p hp e)).mkQL)) z=_
  rw [e.symm_apply_apply]
  rfl

lemma cornerPredualEquiv_symm_mk (a : Corner p hp) (z : X) :
    (cornerPredualEquiv p hp e).symm a (Submodule.Quotient.mk z)=e.symm (a:M) z := by
  have h := (cornerPredualEquiv p hp e).apply_symm_apply a
  have hh := congrArg (fun b : Corner p hp => e.symm (b:M) z) h
  rw [cornerPredualEquiv_apply] at hh
  exact hh

end Predual
end HochschildCorners

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_projection_coe {q : Corner p hp} (hq : IsStarProjection q) :
    IsStarProjection (q:M) := ⟨congrArg (fun a : Corner p hp => (a:M)) hq.isIdempotentElem.eq,
      congrArg (fun a : Corner p hp => (a:M)) hq.isSelfAdjoint.star_eq⟩

lemma corner_projection_le {q : Corner p hp} (hq : IsStarProjection q) : (q:M) ≤ p :=
  ((corner_projection_coe p hp hq).le_iff_mul_eq_left hp).mpr q.property.2

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def cornerTrace : Corner p hp →ₚ[ℂ] ℂ where
  toLinearMap := ((τ p).re : ℂ)⁻¹ • (τ.toLinearMap.comp (corner p hp).subtype)
  monotone' := fun _ _ h => mul_le_mul_of_nonneg_left (τ.monotone h)
    (inv_nonneg.mpr (Complex.zero_le_real.mpr
      (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1))

@[simp] lemma cornerTrace_apply (a : Corner p hp) :
    cornerTrace p hp τ a = ((τ p).re : ℂ)⁻¹ * τ (a:M) := rfl

lemma cornerTrace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (cornerPredualEquiv p hp e) (cornerTrace p hp τ) := by
  obtain ⟨z,hz⟩ := hτ
  let zq : CornerPredual p hp e := Submodule.Quotient.mk z
  refine ⟨((τ p).re : ℂ)⁻¹ • zq,fun a => ?_⟩
  rw [map_smul]
  change _ = star (((τ p).re : ℂ)⁻¹ * (cornerPredualEquiv p hp e).symm a (Submodule.Quotient.mk z))
  rw [cornerPredualEquiv_symm_mk]
  rw [cornerTrace_apply,hz a.val,star_mul,star_inv₀]
  simp only [Complex.star_def,Complex.conj_ofReal]
  exact mul_comm _ _
end HochschildCorners
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace CentralCorner

open HochschildCorners

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)

def includeMap : Corner p hp →L[ℂ] M :=
  (corner p hp).toNonUnitalSubalgebra.toSubmodule.subtypeL

def compressMap : M →L[ℂ] Corner p hp :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨p * a, by
        constructor
        · rw [← mul_assoc, hp.isIdempotentElem.eq]
        · calc
            (p * a) * p = p * (a * p) := mul_assoc _ _ _
            _ = p * (p * a) := by rw [← hc a]
            _ = p * a := by rw [← mul_assoc, hp.isIdempotentElem.eq]⟩
      map_add' := fun a b => Subtype.ext (mul_add p a b)
      map_smul' := fun c a => Subtype.ext (by
        change p * (c • a) = c • (p * a)
        rw [mul_smul_comm]) }
    1 (fun a => by
      change ‖p * a‖ ≤ 1 * ‖a‖
      exact (norm_mul_le p a).trans (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma includeMap_apply (a : Corner p hp) : includeMap p hp a = (a : M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_coe (a : M) :
    (compressMap p hp hc a : M) = p * a := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_includeMap (a : Corner p hp) :
    compressMap p hp hc (includeMap p hp a) = a := Subtype.ext a.property.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_mul (a b : M) :
    compressMap p hp hc (a * b) = compressMap p hp hc a * compressMap p hp hc b := by
  apply Subtype.ext
  exact (central_idempotent_mul p hp.isIdempotentElem.eq hc a b).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_left_module (a : Corner p hp) (b : M) :
    compressMap p hp hc ((a : M) * b) = a * compressMap p hp hc b := by
  apply Subtype.ext
  change p * ((a : M) * b) = (a : M) * (p * b)
  rw [← mul_assoc, a.property.1, ← mul_assoc, a.property.2]

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_right_module (a : M) (b : Corner p hp) :
    compressMap p hp hc (a * (b : M)) = compressMap p hp hc a * b := by
  apply Subtype.ext
  exact (mul_assoc p a (b : M)).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_norm (a : M) : ‖compressMap p hp hc a‖ ≤ ‖a‖ := by
  exact (norm_mul_le p a).trans
    ((mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)).trans_eq (one_mul _))

def restrict {n : ℕ} (f : Cochain M n) : Cochain (Corner p hp) n :=
  (compressMap p hp hc).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun _ => includeMap p hp))

def extend {n : ℕ} (g : Cochain (Corner p hp) n) : Cochain M n :=
  (includeMap p hp).compContinuousMultilinearMap
    (g.compContinuousLinearMap (fun _ => compressMap p hp hc))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma restrict_apply {n : ℕ} (f : Cochain M n) (x : Fin n → Corner p hp) :
    restrict p hp hc f x = compressMap p hp hc (f (fun i => (x i : M))) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma extend_apply {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    extend p hp hc g x = (g (fun i => compressMap p hp hc (x i)) : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma restrict_norm {n : ℕ} (f : Cochain M n) : ‖restrict p hp hc f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (compressMap_norm p hp hc _).trans (f.le_opNorm (fun i => (x i : M)))

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_norm {n : ℕ} (g : Cochain (Corner p hp) n) :
    ‖extend p hp hc g‖ ≤ ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => compressMap_norm p hp hc (x i)))
    (norm_nonneg _))

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_supported {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    p * extend p hp hc g x = extend p hp hc g x :=
  (g (fun i => compressMap p hp hc (x i))).property.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma merge_include {n : ℕ} (x : Fin (n + 1) → Corner p hp) (j : Fin n) :
    mergeInputs (fun i => (x i : M)) j = fun i => (mergeInputs (M := Corner p hp) x j i : M) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma merge_compress {n : ℕ} (x : Fin (n + 1) → M) (j : Fin n) :
    mergeInputs (fun i => compressMap p hp hc (x i)) j =
      fun i => compressMap p hp hc (mergeInputs x j i) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> first | rfl | exact (compressMap_mul p hp hc _ _).symm

omit [PartialOrder M] [StarOrderedRing M] in

lemma differential_restrict {n : ℕ} (f : Cochain M n)
    (x : Fin (n + 1) → Corner p hp) :
    differentialValue (restrict p hp hc f) x =
      compressMap p hp hc (differentialValue f (fun i => (x i : M))) := by
  simp only [differentialValue, restrict_apply, map_add, map_sum, map_smul,
    merge_include, compressMap_left_module, compressMap_right_module]

omit [PartialOrder M] [StarOrderedRing M] in
lemma restrict_cocycle {n : ℕ} (f : Cochain M n)
    (hf : ∀ x, differentialValue f x = 0) :
    ∀ x, differentialValue (restrict p hp hc f) x = 0 := by
  intro x
  rw [differential_restrict, hf, map_zero]

omit [PartialOrder M] [StarOrderedRing M] in

lemma differential_extend {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin (n + 1) → M) :
    differentialValue (extend p hp hc g) x =
      (differentialValue (M := Corner p hp) g (fun i => compressMap p hp hc (x i)) : M) := by
  change differentialValue (extend p hp hc g) x =
    includeMap p hp (differentialValue (M := Corner p hp) g (fun i => compressMap p hp hc (x i)))
  simp only [differentialValue, map_add, map_sum, map_smul, extend_apply,
    includeMap_apply, merge_compress]
  congr 2
  · change x 0 * (g _ : M) = (p * x 0) * (g _ : M)
    rw [hc (x 0), mul_assoc, (g _).property.1]
  · change (g _ : M) * x (Fin.last n) = (g _ : M) * (p * x (Fin.last n))
    rw [← mul_assoc, (g _).property.2]

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_primitive {n : ℕ} (f : Cochain M (n + 1))
    (g : Cochain (Corner p hp) n)
    (hg : ∀ x, differentialValue g x = restrict p hp hc f x)
    (x : Fin (n + 1) → M) :
    differentialValue (extend p hp hc g) x =
      centralCut p (centralOutput p f) x := by
  rw [differential_extend, hg]
  rfl
end CentralCorner
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
namespace HochschildNormalPart
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

end HochschildNormalPart

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def functionalModel (φ : StrongDual ℂ M) : FunctionalModel φ := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact Classical.choice (functionalModel_nonempty φ)
end HochschildNormalPart
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def FiniteCorner (p : M) : Prop :=
  ∀ a : M, p * a = a → a * p = a → star a * a = p → a * star a = p

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_iff (p : M) (hp : IsStarProjection p) :
    FiniteCorner p ↔ FiniteAlgebra (HochschildCorners.Corner p hp) := by
  constructor
  · intro h a ha
    apply Subtype.ext
    exact h a a.property.1 a.property.2 (congrArg Subtype.val ha)
  · intro h a hL hR ha
    let b : HochschildCorners.Corner p hp := ⟨a, hL, hR⟩
    exact congrArg Subtype.val (h b (Subtype.ext ha))

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_of_finiteAlgebra (hfinite : FiniteAlgebra M)
    (p : M) (hp : IsStarProjection p) : FiniteCorner p := by
  intro a hL hR haa
  have hsL : star a * p = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hL
  have hsR : p * star a = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hR
  have hca : (1 - p) * a = 0 := by rw [sub_mul, one_mul, hL, sub_self]
  have hac : a * (1 - p) = 0 := by rw [mul_sub, mul_one, hR, sub_self]
  have hcsa : (1 - p) * star a = 0 := by rw [sub_mul, one_mul, hsR, sub_self]
  have hsac : star a * (1 - p) = 0 := by rw [mul_sub, mul_one, hsL, sub_self]
  have hin : star (a + (1 - p)) * (a + (1 - p)) = 1 := by
    simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      add_mul, mul_add, hsac, hca, zero_add, add_zero, haa,
      hp.one_sub.isIdempotentElem.eq]
    abel
  have hout := hfinite (a + (1 - p)) hin
  simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
    add_mul, mul_add, hac, hcsa, zero_add, add_zero,
    hp.one_sub.isIdempotentElem.eq] at hout
  have hp1 : p + (1 - p) = 1 := by abel
  exact add_right_cancel (hout.trans hp1.symm)

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralCorner_central {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : HochschildCorners.Corner p hp)
    (hqc : ∀ b : HochschildCorners.Corner p hp, q * b = b * q) :
    ∀ a : M, (q : M) * a = a * (q : M) := by
  intro a
  have h := congrArg Subtype.val (hqc (CentralCorner.compressMap p hp hc a))
  change (q : M) * (p * a) = (p * a) * (q : M) at h
  calc
    (q : M) * a = ((q : M) * p) * a := by rw [q.property.2]
    _ = (q : M) * (p * a) := mul_assoc _ _ _
    _ = (p * a) * (q : M) := h
    _ = a * (p * (q : M)) := by rw [hc a, mul_assoc]
    _ = a * (q : M) := by rw [q.property.1]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def TypeICentralSummand (z : M) : Prop :=
  CentralProjection z ∧ ∀ c : M, CentralProjection c → c ≤ z → c ≠ 0 →
    ∃ p : M, AbelianProjection p ∧ p ≤ c ∧ p ≠ 0
end FinitePathMain
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

lemma abelian_of_le {p q : M} (hp : AbelianProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p) : AbelianProjection q := by
  refine ⟨hq,?_⟩
  intro a b
  have he (x : M) : p*(q*x*q)*p=q*x*q := by
    rw [← mul_assoc,← mul_assoc,(hq.le_iff_mul_eq_right hp.1).mp hqp,
      mul_assoc,mul_assoc,(hq.le_iff_mul_eq_left hp.1).mp hqp,← mul_assoc]
  simpa only [he] using hp.2 (q*a*q) (q*b*q)

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

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma central_annihilator_chain (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : M) (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, CentralProjection q ∧ q * p = 0) :
    ∃ s : M, CentralProjection s ∧ s * p = 0 ∧ ∀ q ∈ c, q ≤ s := by
  obtain ⟨s, hsp, hsc, hub, _hleast, hann⟩ :=
    exists_central_projection_chain_supremum e c hne hc
      (fun q hq => (hs q hq).1.1) (fun q hq a => ((hs q hq).1.2 a).eq)
  exact ⟨s, ⟨hsp, fun a => hsc a⟩, hann p (fun q hq => (hs q hq).2), hub⟩

theorem exists_typeI_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) :
    ∃ z : M, TypeICentralSummand z ∧ p ≤ z ∧ z ≠ 0 := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hz : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _hs0, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨t, ht, htp, hupper⟩ :=
      central_annihilator_chain e p c hchain ⟨y, hy⟩ (fun q hq => hc hq)
    exact ⟨t, ⟨ht, htp⟩, hupper⟩) 0 hz
  have hs : CentralProjection s := hmax.1.1
  have hsp : s * p = 0 := hmax.1.2
  have hzc : CentralProjection (1 - s) :=
    ⟨hs.1.one_sub, fun a => (Commute.one_left a).sub_left (hs.2 a)⟩
  have hpz : p ≤ 1 - s := (hp.1.le_iff_mul_eq_right hs.1.one_sub).mpr
    (by rw [sub_mul, one_mul, hsp, sub_zero])
  refine ⟨1 - s, ⟨hzc, ?_⟩, hpz, ?_⟩
  · intro c hc hcz hc0
    have hcp : IsStarProjection (c * p) := hc.1.mul hp.1 (hc.2 p)
    have hcpp : c * p ≤ p := (hcp.le_iff_mul_eq_left hp.1).mpr
      (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
    have hcpc : c * p ≤ c := (hcp.le_iff_mul_eq_right hc.1).mpr
      (by rw [← mul_assoc, hc.1.isIdempotentElem.eq])
    refine ⟨c * p, HochschildTypeII.abelian_of_le hp hcp hcpp, hcpc, ?_⟩
    intro hzero
    have hsc := HochschildTypeII.projection_orthogonal_of_le_complement hs.1 hc.1 hcz
    have hnew : s + c ∈ S := ⟨⟨hs.1.add hc.1 hsc,
      fun a => (hs.2 a).add_left (hc.2 a)⟩,
      by rw [add_mul, hsp, hzero, zero_add]⟩
    have hle : s ≤ s + c := le_add_of_nonneg_right hc.1.nonneg
    have he := le_antisymm (hmax.2 hnew hle) hle
    exact hc0 (add_eq_left.mp he)
  · intro he
    exact hp0 (le_antisymm (he ▸ hpz) hp.1.nonneg)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma typeICentral_witness {p c : M} (hp : TypeICentralSummand p)
    (hc : CentralProjection c) (hzero : c * p ≠ 0) :
    ∃ a : M, AbelianProjection a ∧ a ≤ c ∧ a ≠ 0 := by
  have hcp : CentralProjection (c * p) :=
    ⟨hc.1.mul hp.1.1 (hc.2 p), fun a => (hc.2 a).mul_left (hp.1.2 a)⟩
  have hcpp : c * p ≤ p := (hcp.1.le_iff_mul_eq_left hp.1.1).mpr
    (by rw [mul_assoc, hp.1.1.isIdempotentElem.eq])
  have hcpc : c * p ≤ c := (hcp.1.le_iff_mul_eq_right hc.1).mpr
    (by rw [← mul_assoc, hc.1.isIdempotentElem.eq])
  obtain ⟨a, ha, hap, ha0⟩ := hp.2 (c * p) hcp hcpp hzero
  exact ⟨a, ha, hap.trans hcpc, ha0⟩

lemma typeICentral_chain_sup (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hS : ∀ q ∈ S, TypeICentralSummand q) :
    ∃ p : M, TypeICentralSummand p ∧ ∀ q ∈ S, q ≤ p := by
  obtain ⟨p, hp, hpc, hub, _, hann⟩ := exists_central_projection_chain_supremum
    e S hne hchain (fun q hq => (hS q hq).1.1)
      (fun q hq a => ((hS q hq).1.2 a).eq)
  refine ⟨p, ⟨⟨hp, fun a => hpc a⟩, ?_⟩, hub⟩
  intro c hc hcp hc0
  have hex : ∃ q ∈ S, c * q ≠ 0 := by
    by_contra hn
    push Not at hn
    have hpc0 := hann c (fun q hq => by rw [← (hc.2 q).eq]; exact hn q hq)
    exact hc0 (by rwa [(hc.1.le_iff_mul_eq_right hp).mp hcp] at hpc0)
  obtain ⟨q, hq, hcq⟩ := hex
  exact typeICentral_witness (hS q hq) hc hcq

lemma typeICentral_orthogonal_sum {p q : M}
    (hp : TypeICentralSummand p) (hq : TypeICentralSummand q) (hpq : p * q = 0) :
    TypeICentralSummand (p + q) := by
  have hsum : CentralProjection (p + q) :=
    ⟨hp.1.1.add hq.1.1 hpq, fun a => (hp.1.2 a).add_left (hq.1.2 a)⟩
  refine ⟨hsum, ?_⟩
  intro c hc hcle hc0
  by_cases hcp : c * p = 0
  · have hcq : c * q ≠ 0 := by
      intro hzero
      have h := (hc.1.le_iff_mul_eq_left hsum.1).mp hcle
      rw [mul_add, hcp, hzero, zero_add] at h
      exact hc0 h.symm
    exact typeICentral_witness hq hc hcq
  · exact typeICentral_witness hp hc hcp

theorem exists_maximal_typeI_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ p : M, TypeICentralSummand p ∧
      ∀ q : M, TypeICentralSummand q → q ≤ 1 - p → q = 0 := by
  classical
  let S : Set M := {p | TypeICentralSummand p}
  have hz : (0 : M) ∈ S := by
    refine ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, ?_⟩
    intro c hc hc0 hcn
    exact (hcn (le_antisymm hc0 hc.1.nonneg)).elim
  obtain ⟨p, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨s, hs, hupper⟩ := typeICentral_chain_sup e c ⟨a, ha⟩ hchain
      (fun q hq => hc hq)
    exact ⟨s, hs, hupper⟩) 0 hz
  refine ⟨p, hmax.1, ?_⟩
  intro q hq hqp
  have hpq := HochschildTypeII.projection_orthogonal_of_le_complement
    hmax.1.1.1 hq.1.1 hqp
  have hs : p + q ∈ S := typeICentral_orthogonal_sum hmax.1 hq hpq
  have hle : p ≤ p + q := le_add_of_nonneg_right hq.1.1.nonneg
  have he : p + q = p := le_antisymm (hmax.2 hs hle) hle
  exact add_eq_left.mp he

omit [PartialOrder M] [StarOrderedRing M] in

lemma finitePath_abelian_of_popa {p : M} (hp : IsStarProjection p)
    (h : PopaTypeII.AbelianProjection hp) : AbelianProjection p := by
  refine ⟨hp, fun a b => ?_⟩
  let A : PopaCorner.algebra hp := ⟨p * a * p, compress_mem_corner hp a⟩
  let B : PopaCorner.algebra hp := ⟨p * b * p, compress_mem_corner hp b⟩
  exact congrArg Subtype.val (h A B).eq

omit [PartialOrder M] [StarOrderedRing M] in

lemma centralCorner_abelian_to_ambient {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : Corner p hp)
    (hq : AbelianProjection q) : AbelianProjection (q : M) := by
  have hqp : IsStarProjection (q : M) :=
    ⟨congrArg Subtype.val hq.1.isIdempotentElem.eq,
      congrArg Subtype.val hq.1.isSelfAdjoint.star_eq⟩
  refine ⟨hqp, fun a b => ?_⟩
  have h := congrArg Subtype.val
    (hq.2 (CentralCorner.compressMap p hp hc a) (CentralCorner.compressMap p hp hc b)).eq
  change ((q : M) * (p * a) * (q : M)) * ((q : M) * (p * b) * (q : M)) =
    ((q : M) * (p * b) * (q : M)) * ((q : M) * (p * a) * (q : M)) at h
  have hcut (x : M) : (q : M) * (p * x) * (q : M) = (q : M) * x * (q : M) := by
    rw [← mul_assoc, q.property.2]
  change ((q : M) * a * (q : M)) * ((q : M) * b * (q : M)) =
    ((q : M) * b * (q : M)) * ((q : M) * a * (q : M))
  simpa only [hcut] using h

lemma centralCorner_typeI_to_ambient {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : Corner p hp)
    (hq : TypeICentralSummand q) : TypeICentralSummand (q : M) := by
  have hqp : IsStarProjection (q : M) :=
    ⟨congrArg Subtype.val hq.1.1.isIdempotentElem.eq,
      congrArg Subtype.val hq.1.1.isSelfAdjoint.star_eq⟩
  refine ⟨⟨hqp, fun a => centralCorner_central hp hc q
    (fun b => (hq.1.2 b).eq) a⟩, ?_⟩
  intro c hcp hcle hc0
  have hqp_le : (q : M) ≤ p := (hqp.le_iff_mul_eq_right hp).mpr q.property.1
  have hclep := hcle.trans hqp_le
  let cC : Corner p hp := ⟨c,
    (hcp.1.le_iff_mul_eq_right hp).mp hclep,
    (hcp.1.le_iff_mul_eq_left hp).mp hclep⟩
  have hcC : CentralProjection cC := by
    refine ⟨⟨Subtype.ext hcp.1.isIdempotentElem.eq,
      Subtype.ext hcp.1.isSelfAdjoint.star_eq⟩, ?_⟩
    intro a
    exact Subtype.ext (hcp.2 (a : M)).eq
  have hcC0 : cC ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  obtain ⟨a, ha, hac, ha0⟩ := hq.2 cC hcC hcle hcC0
  refine ⟨(a : M), centralCorner_abelian_to_ambient hp hc a ha, hac, ?_⟩
  intro h
  exact ha0 (Subtype.ext h)

theorem exists_typeI_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) ∧
      TypeICentralSummand p ∧
      PopaTypeII.NoAbelianCorners (Corner (1 - p) hp.one_sub) ∧
      PopaTypeII.NoTypeICentralPart (Corner (1 - p) hp.one_sub) := by
  obtain ⟨p, hp, hmax⟩ := exists_maximal_typeI_central_cut e
  have hpc : ∀ a : M, p * a = a * p := fun a => (hp.1.2 a).eq
  have hcomp : ∀ a : M, (1 - p) * a = a * (1 - p) := by
    intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpc]
  let N := Corner (1 - p) hp.1.1.one_sub
  have hnoAb : PopaTypeII.NoAbelianCorners N := by
    intro r hr hr0
    by_contra hn
    push Not at hn
    have hab : PopaTypeII.AbelianProjection hr := fun a b => hn a b
    obtain ⟨z, hz, _, hz0⟩ := exists_typeI_support
      (cornerPredualEquiv (1 - p) hp.1.1.one_sub e) (finitePath_abelian_of_popa hr hab) hr0
    have hzM := centralCorner_typeI_to_ambient hp.1.1.one_sub hcomp z hz
    have hzle : (z : M) ≤ 1 - p := (hzM.1.1.le_iff_mul_eq_right hp.1.1.one_sub).mpr
      z.property.1
    exact hz0 (Subtype.ext (hmax (z : M) hzM hzle))
  refine ⟨p, hp.1.1, hpc, hp, hnoAb, ?_⟩
  intro z hz _hzc hz0 hI
  obtain ⟨q, hq, _, hq0, hqa⟩ := hI z hz le_rfl hz0
  obtain ⟨a, b, hab⟩ := hnoAb q hq hq0
  exact hab (hqa a b)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

section Nested
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def nestedCornerEquiv {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) :
    Corner q hq ≃⋆ₐ[ℂ] Corner (q : M) (corner_projection_coe p hp hq) where
  toFun a := ⟨((a : Corner p hp) : M),
    congrArg Subtype.val a.property.1, congrArg Subtype.val a.property.2⟩
  invFun b := ⟨⟨(b : M), by
      constructor
      · calc
          p * (b : M) = p * ((q : M) * (b : M)) := by rw [b.property.1]
          _ = (b : M) := by rw [← mul_assoc, q.property.1, b.property.1]
      · calc
          (b : M) * p = ((b : M) * (q : M)) * p := by rw [b.property.2]
          _ = (b : M) := by rw [mul_assoc, q.property.2, b.property.2]⟩,
    Subtype.ext b.property.1, Subtype.ext b.property.2⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma nestedCornerEquiv_apply {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) (a : Corner q hq) :
    ((nestedCornerEquiv hp q hq a : Corner (q : M) (corner_projection_coe p hp hq)) : M) =
      ((a : Corner p hp) : M) := rfl

end Nested

section Transport
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]
  [PartialOrder M] [StarOrderedRing M] [PartialOrder N] [StarOrderedRing N]

def popaCornerEquiv (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : IsStarProjection p) :
    PopaCorner.algebra hp ≃⋆ₐ[ℂ] PopaCorner.algebra (hp.map φ) where
  toFun a := ⟨φ (a : M), by
    constructor
    · change φ p * φ (a : M) = φ (a : M)
      rw [← map_mul, a.property.1]
    · change φ (a : M) * φ p = φ (a : M)
      rw [← map_mul, a.property.2]⟩
  invFun b := ⟨φ.symm (b : N), by
    constructor
    · apply φ.injective
      change φ (p * φ.symm (b : N)) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.1
    · apply φ.injective
      change φ (φ.symm (b : N) * p) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.2⟩
  left_inv a := Subtype.ext (φ.symm_apply_apply (a : M))
  right_inv b := Subtype.ext (φ.apply_symm_apply (b : N))
  map_add' a b := Subtype.ext (map_add φ (a : M) (b : M))
  map_mul' a b := Subtype.ext (map_mul φ (a : M) (b : M))
  map_smul' c a := Subtype.ext (map_smul φ c (a : M))
  map_star' a := Subtype.ext (map_star φ (a : M))

lemma abelianProjection_map_equiv (φ : M ≃⋆ₐ[ℂ] N) {p : M}
    (hp : IsStarProjection p) (hab : PopaTypeII.AbelianProjection hp) :
    PopaTypeII.AbelianProjection (hp.map φ) := by
  let E := popaCornerEquiv φ hp
  intro a b
  simpa only [E.apply_symm_apply] using (hab (E.symm a) (E.symm b)).map E
end Transport
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma popa_abelian_of_finitePath {p : M} (hp : AbelianProjection p) :
    PopaTypeII.AbelianProjection hp.1 := by
  have hc (a : PopaCorner.algebra hp.1) : p * (a : M) * p = (a : M) := by
    rw [a.property.1, a.property.2]
  intro a b
  apply Subtype.ext
  change (a : M) * (b : M) = (b : M) * (a : M)
  simpa only [hc] using (hp.2 (a : M) (b : M)).eq
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace HochschildMatrixSystems.MatrixSystem

variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N] {n : ℕ}

def mapEquiv (E : HochschildMatrixSystems.MatrixSystem M n) (φ : M ≃⋆ₐ[ℂ] N) :
    HochschildMatrixSystems.MatrixSystem N n where
  entry i j := φ (E.entry i j)
  star_entry i j := by rw [← map_star, E.star_entry]
  entry_mul i j k l := by rw [← map_mul, E.entry_mul]; split_ifs <;> simp
  sum_diagonal := by rw [← map_sum, E.sum_diagonal, map_one]

end HochschildMatrixSystems.MatrixSystem

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners HochschildMatrixSystems FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma abelian_map_equiv {N : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
    (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : AbelianProjection p) : AbelianProjection (φ p) :=
  finitePath_abelian_of_popa (hp.1.map φ)
    (abelianProjection_map_equiv φ hp.1 (popa_abelian_of_finitePath hp))

def projectionInCorner {z p : M} (hz : IsStarProjection z) (hp : IsStarProjection p)
    (hpz : p ≤ z) : Corner z hz := ⟨p, projection_mem_corner hz hp hpz⟩

lemma projectionInCorner_abelian {z p : M} (hz : IsStarProjection z)
    (hp : AbelianProjection p) (hpz : p ≤ z) :
    AbelianProjection (projectionInCorner hz hp.1 hpz) := by
  refine ⟨⟨Subtype.ext hp.1.isIdempotentElem.eq, Subtype.ext hp.1.isSelfAdjoint.star_eq⟩, ?_⟩
  intro a b
  exact Subtype.ext (hp.2 (a : M) (b : M)).eq

lemma homogeneousCorner_to_ambient {z : M} (hz : IsStarProjection z)
    (q : Corner z hz) (hq : HomogeneousTypeICorner q) :
    HomogeneousTypeICorner (q : M) := by
  obtain ⟨hqp, n, E, i, hi⟩ := hq
  let φ := nestedCornerEquiv hz q hqp
  exact ⟨corner_projection_coe z hz hqp, n, E.mapEquiv φ, i, abelian_map_equiv φ hi⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorPositiveFunctional (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : M →ₚ[ℂ] ℂ where
  toLinearMap := (coefficient π ξ ξ).toLinearMap
  monotone' := by
    change Monotone (coefficient π ξ ξ)
    apply (monotone_iff_map_nonneg _).mpr
    intro a ha
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (map_nonneg π ha)).inner_nonneg_right ξ

@[simp] lemma vectorPositiveFunctional_apply (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (a : M) : vectorPositiveFunctional π ξ a = inner ℂ ξ (π a ξ) := rfl

omit [CompleteSpace X] in
lemma vectorPositiveFunctional_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {ξ : H} (hξ : ξ ∈ normalVectors e π) :
    TraceInPredual e (vectorPositiveFunctional π ξ) := by
  exact (mem_normalDual e _).mp ((mem_normalVectors e π ξ).mp hξ ξ)

theorem exists_normal_state_on_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ ψ : M →ₚ[ℂ] ℂ, TraceInPredual e ψ ∧ ψ 1 = 1 ∧ ψ p = 1 ∧
      ∀ a : M, ψ (p * a * p) = ψ a := by
  classical
  have hex : ∃ z : X, e.symm p z ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hp0
    apply e.symm.injective
    ext z
    simpa only [map_zero, zero_apply] using hn z
  obtain ⟨z, hz⟩ := hex
  let φ := predualEmbedding e z
  let m := functionalModel φ
  let π := m.representation
  let η := m.leftVector
  let ξ := normalProjection e π m.rightVector
  have hφ : φ ∈ normalDual e := ⟨z, rfl⟩
  have hreal : coefficient π η ξ = φ := by
    exact (normalProjection_fixes_normal e π η m.rightVector
      (m.realizes.symm ▸ hφ)).trans m.realizes
  have hξ : ξ ∈ normalVectors e π := by simp [ξ, normalProjection]
  let ζ := π p ξ
  have hζ : ζ ∈ normalVectors e π := normalVectors_mul e π hξ p
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have he := congrArg (fun f : StrongDual ℂ M => f p) hreal
    have hφp : φ p ≠ 0 := by simpa only [φ, predualEmbedding_apply, star_ne_zero] using hz
    apply hφp
    change inner ℂ η ζ = φ p at he
    rw [hzero, inner_zero_right] at he
    exact he.symm
  have hfix : π p ζ = ζ := by
    change π p (π p ξ) = π p ξ
    rw [← mul_apply_eq_comp, ← map_mul, hp.isIdempotentElem.eq]
  let w := (‖ζ‖⁻¹ : ℂ) • ζ
  have hwn : ‖w‖ = 1 := norm_smul_inv_norm hζ0
  have hw : w ∈ normalVectors e π := (normalVectors e π).smul_mem _ hζ
  have hwfix : π p w = w := by simp only [w, map_smul, hfix]
  let ψ := vectorPositiveFunctional π w
  have hψ1 : ψ 1 = 1 := by
    simp only [ψ, vectorPositiveFunctional_apply, map_one, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, hwn]
    norm_num
  refine ⟨ψ, vectorPositiveFunctional_normal e π hw, hψ1, ?_, ?_⟩
  · simpa only [ψ, vectorPositiveFunctional_apply, hwfix, map_one, one_apply_eq_self]
      using hψ1
  · intro a
    change inner ℂ w (π (p * a * p) w) = inner ℂ w (π a w)
    rw [map_mul, map_mul]
    change inner ℂ w (π p (π a (π p w))) = inner ℂ w (π a w)
    rw [hwfix, ← ContinuousLinearMap.adjoint_inner_left]
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, hp.isSelfAdjoint.star_eq, hwfix]

lemma normal_functional_central_null_chain (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hS : ∀ q ∈ S, IsStarProjection q ∧ (∀ a : M, q * a = a * q) ∧ ψ q = 0) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ ψ p = 0 ∧
      ∀ q ∈ S, q ≤ p := by
  obtain ⟨p, hp, hc, hu, _, _, U, _, ht⟩ :=
    exists_central_projection_chain_supremum_with_limit e S hne hchain
      (fun q hq => (hS q hq).1) (fun q hq => (hS q hq).2.1)
  refine ⟨p, hp, hc, ?_, hu⟩
  have heq : (fun q : S => ψ (q : M)) = (fun _ : S => (0 : ℂ)) :=
    funext fun q => (hS q q.property).2.2
  have hl := trace_predual_tendsto e ψ hψ ht
  rw [heq] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

theorem exists_normal_positive_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ ψ p = ψ 1 ∧
      ∀ q : M, IsStarProjection q → (∀ a : M, q * a = a * q) →
        q ≤ p → ψ q = 0 → q = 0 := by
  classical
  let S : Set M := {q | IsStarProjection q ∧ (∀ a : M, q * a = a * q) ∧ ψ q = 0}
  have hz : (0 : M) ∈ S := ⟨IsStarProjection.zero M, fun a => by simp, map_zero ψ⟩
  obtain ⟨r, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨s, hs, hcs, hψs, hu⟩ := normal_functional_central_null_chain e ψ hψ
      c ⟨a, ha⟩ hchain (fun q hq => hc hq)
    exact ⟨s, ⟨hs, hcs, hψs⟩, hu⟩) 0 hz
  have hr := hmax.1.1
  have hrc := hmax.1.2.1
  have hψr := hmax.1.2.2
  refine ⟨1 - r, hr.one_sub, ?_, ?_, ?_⟩
  · intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hrc]
  · rw [map_sub, hψr, sub_zero]
  · intro q hq hqc hqr hψq
    have hrq : r * q = 0 := by
      have h := (hq.le_iff_mul_eq_right hr.one_sub).mp hqr
      rw [sub_mul, one_mul] at h
      exact sub_eq_self.mp h
    have hs : r + q ∈ S := ⟨hr.add hq hrq,
      fun a => by rw [add_mul, mul_add, hrc, hqc], by rw [map_add, hψr, hψq, add_zero]⟩
    have hle : r ≤ r + q := le_add_of_nonneg_right hq.nonneg
    have he : r + q = r := le_antisymm (hmax.2 hs hle) hle
    exact add_eq_left.mp he

def HasCentralFaithfulNormalState (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (p : M) : Prop :=
  ∃ ψ : M →ₚ[ℂ] ℂ, TraceInPredual e ψ ∧ ψ 1 = 1 ∧ ψ p = 1 ∧
    ∀ q : M, IsStarProjection q → (∀ a : M, q * a = a * q) →
      q ≤ p → ψ q = 0 → q = 0

theorem exists_central_normal_state_subprojection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hqc : ∀ a : M, q * a = a * q) (hq0 : q ≠ 0) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      p ≤ q ∧ p ≠ 0 ∧ HasCentralFaithfulNormalState e p := by
  obtain ⟨ψ, hψ, hψ1, _, hsupport⟩ := exists_normal_state_on_projection e hq hq0
  obtain ⟨p, hp, hpc, hψp, hfaith⟩ := exists_normal_positive_central_support e ψ hψ
  have hψp1 : ψ p = 1 := hψp.trans hψ1
  have hcut : IsStarProjection (p * (1 - q)) := hp.mul hq.one_sub
    (show Commute p (1 - q) from hpc (1 - q))
  have hcutc : ∀ a : M, (p * (1 - q)) * a = a * (p * (1 - q)) := by
    intro a
    have hqc' : Commute (1 - q) a := (Commute.one_left a).sub_left (hqc a)
    exact ((show Commute p a from hpc a).mul_left hqc').eq
  have hcutle : p * (1 - q) ≤ p := (hcut.le_iff_mul_eq_right hp).mpr
    (by rw [← mul_assoc, hp.isIdempotentElem.eq])
  have hcutzero : ψ (p * (1 - q)) = 0 := by
    have h := hsupport (p * (1 - q))
    have hzero : q * (p * (1 - q)) = 0 := by
      rw [← mul_assoc, hqc p, mul_assoc, mul_sub, mul_one,
        hq.isIdempotentElem.eq, sub_self, mul_zero]
    rw [hzero, zero_mul, map_zero] at h
    exact h.symm
  have hpq : p ≤ q := by
    have hzero := hfaith (p * (1 - q)) hcut hcutc hcutle hcutzero
    rw [mul_sub, mul_one] at hzero
    exact (hp.le_iff_mul_eq_left hq).mpr (sub_eq_zero.mp hzero).symm
  have hp0 : p ≠ 0 := by
    intro hzero
    have h01 : (0 : ℂ) = 1 := by simpa only [hzero, map_zero] using hψp1
    exact zero_ne_one h01
  exact ⟨p, hp, hpc, hpq, hp0, ψ, hψ, hψ1, hψp1, hfaith⟩
end KadisonRingrose
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

open HochschildCorners

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem central_faithful_state_on_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)
    (hstate : HasCentralFaithfulNormalState e p) :
    ∃ ψ : Corner p hp →ₚ[ℂ] ℂ,
      TraceInPredual (cornerPredualEquiv p hp e) ψ ∧ ψ 1 = 1 ∧
      ∀ q : Corner p hp, IsStarProjection q →
        (∀ a : Corner p hp, q * a = a * q) → ψ q = 0 → q = 0 := by
  obtain ⟨ψ, hψ, _, hψp, hfaith⟩ := hstate
  let τ := cornerTrace p hp ψ
  have hτ (a : Corner p hp) : τ a = ψ (a : M) := by
    simp only [τ, cornerTrace_apply, hψp, Complex.one_re, Complex.ofReal_one, inv_one, one_mul]
  refine ⟨τ, cornerTrace_normal p hp e ψ hψ, ?_, ?_⟩
  · simpa only [hτ, corner_coe_one] using hψp
  · intro q hq hqc hzero
    apply Subtype.ext
    exact hfaith (q : M) (corner_projection_coe p hp hq)
      (centralCorner_central hp hc q hqc) (corner_projection_le p hp hq)
      (by rwa [hτ] at hzero)
end KadisonRingrose
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

universe u

variable {M X I : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_orthogonal_central_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hc : ∀ i a, p i * a = a * p i)
    (horth : ∀ i j, i ≠ j → p i * p j = 0) :
    ∃ q : M, IsStarProjection q ∧ (∀ a : M, q * a = a * q) ∧
      (∀ i, p i * q = p i) ∧
      (∀ a : M, (∀ i, p i * a = 0) → q * a = 0) := by
  classical
  let s (t : Finset I) : M := ∑ i ∈ t, p i
  let U : Ultrafilter (Finset I) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset I)) ≤ atTop := Ultrafilter.of_le atTop
  have hn (t : Finset I) : ‖s t‖ ≤ 1 :=
    supported_sum_norm_le p p hp horth
      (fun i => (hp i).isIdempotentElem.eq)
      (fun i => (hp i).isIdempotentElem.eq) t 1 (by norm_num)
      (fun i _ => (hp i).norm_le)
  obtain ⟨q, _, ht⟩ := exists_predual_ultralimit e U s 1 hn
  have hfixed (i : I) : p i * q = p i := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (p i) ht
    have heq : (fun t => p i * s t) =ᶠ[U] (fun _ => p i) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({i} : Finset I)] with t hit
      have hi : i ∈ t := hit (Finset.mem_singleton_self i)
      simp only [s, Finset.mul_sum]
      rw [Finset.sum_eq_single i]
      · exact (hp i).isIdempotentElem.eq
      · intro j _ hji
        exact horth i j hji.symm
      · exact fun h => (h hi).elim
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  have hqc (a : M) : q * a = a * q := by
    have hl := HochschildSakai.predual_tendsto_mul_left e a ht
    have hr := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun t => a * s t) = (fun t => s t * a) := by
      funext t
      simp only [s, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => (hc i a).symm)
    rw [heq] at hl
    exact predual_tendsto_unique e hr hl
  have hq : IsStarProjection q := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e q ht
      have heq : (fun t => s t * q) = s := by
        funext t
        simp only [s, Finset.sum_mul, hfixed]
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun t => star (s t)) = s := by
        funext t
        simp only [s, star_sum, fun i => (hp i).isSelfAdjoint.star_eq]
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨q, hq, hqc, hfixed, ?_⟩
  intro a ha
  have hm := HochschildSakai.predual_tendsto_mul_right e a ht
  have heq : (fun t => s t * a) = (fun _ => (0 : M)) := by
    funext t
    simp only [s, Finset.sum_mul, ha, Finset.sum_const_zero]
  rw [heq] at hm
  exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter (Finset I)))

structure MaximalCentralPartition (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] (P : M → Prop) where
  Index : Type u
  projection : Index → M
  isProjection : ∀ i, IsStarProjection (projection i)
  central : ∀ i a, projection i * a = a * projection i
  nonzero : ∀ i, projection i ≠ 0
  property : ∀ i, P (projection i)
  orthogonal : ∀ i j, i ≠ j → projection i * projection j = 0
  complement : M
  complement_isProjection : IsStarProjection complement
  complement_central : ∀ a, complement * a = a * complement
  complement_orthogonal : ∀ i, projection i * complement = 0
  total : ∀ a, complement * a = 0 → (∀ i, projection i * a = 0) → a = 0
  maximal : ∀ q : M, IsStarProjection q → (∀ a, q * a = a * q) →
    q ≤ complement → P q → q = 0

theorem exists_maximal_central_partition (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (P : M → Prop) : Nonempty (MaximalCentralPartition M P) := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧
    (∀ a : M, p * a = a * p) ∧ p ≠ 0 ∧ P p) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p * q = 0}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro p hp
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      exact (hc hs).1 p hps
    · intro p hp q hq hpq
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 p (hst hps) q hqt hpq
      · exact (hc hs).2 p hps q (hts hqt) hpq)
  let p : S → M := Subtype.val
  have hp (i : S) : IsStarProjection (p i) := (hS.1.1 i i.property).1
  have hc (i : S) (a : M) : p i * a = a * p i := (hS.1.1 i i.property).2.1 a
  have hn (i : S) : p i ≠ 0 := (hS.1.1 i i.property).2.2.1
  have hP (i : S) : P (p i) := (hS.1.1 i i.property).2.2.2
  have ho (i j : S) (hij : i ≠ j) : p i * p j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨q, hq, hqc, hfixed, hann⟩ := exists_orthogonal_central_supremum e p hp hc ho
  have hcomp (i : S) : p i * (1 - q) = 0 := by
    rw [mul_sub, mul_one, hfixed, sub_self]
  refine ⟨{
    Index := S
    projection := p
    isProjection := hp
    central := hc
    nonzero := hn
    property := hP
    orthogonal := ho
    complement := 1 - q
    complement_isProjection := hq.one_sub
    complement_central := fun a => by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hqc]
    complement_orthogonal := hcomp
    total := ?_
    maximal := ?_ }⟩
  · intro a hca hpa
    have hqa := hann a hpa
    simpa only [sub_mul, one_mul, hqa, sub_zero] using hca
  · intro r hr hrc hrq hPr
    by_contra hr0
    have hrr : ∀ i : S, p i * r = 0 := by
      have hqr : (1 - q) * r = r := (hr.le_iff_mul_eq_right hq.one_sub).mp hrq
      intro i
      calc
        p i * r = p i * ((1 - q) * r) := by rw [hqr]
        _ = 0 := by rw [← mul_assoc, hcomp, zero_mul]
    have hnew : insert r S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hr, hrc, hr0, hPr⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact (hrc b).trans (hrr ⟨b, hb⟩)
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hrr ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert r S ⊆ S := hS.2 hnew (Set.subset_insert r S)
    have hrS : r ∈ S := hsubset (Set.mem_insert r S)
    exact hr0 (by simpa only [p, hr.isIdempotentElem.eq] using hrr ⟨r, hrS⟩)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners FinitePathMain

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_typeI_homogeneous_subprojection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hI : TypeICentralSummand (1 : M))
    {z : M} (hz : IsStarProjection z) (hzc : ∀ a : M, z * a = a * z) (hz0 : z ≠ 0) :
    ∃ q : M, CentralProjection q ∧ q ≤ z ∧ q ≠ 0 ∧ HomogeneousTypeICorner q := by
  obtain ⟨c, hc, hcc, hcz, hc0, hstate⟩ :=
    exists_central_normal_state_subprojection e hz hzc hz0
  obtain ⟨p, hp, hpc, hp0⟩ := hI.2 c ⟨hc, fun a => hcc a⟩ hc.le_one hc0
  let eC := cornerPredualEquiv c hc e
  have hfinC : FiniteAlgebra (Corner c hc) :=
    (finiteCorner_iff c hc).mp (finiteCorner_of_finiteAlgebra hfinite c hc)
  obtain ⟨ψ, hψ, hψ1, hfaithψ⟩ := central_faithful_state_on_corner e hc hcc hstate
  obtain ⟨τ, _hτ, _hτ1, htr, hfaith⟩ :=
    faithful_normal_trace_of_center_state eC hfinC ψ hψ hψ1 hfaithψ
  have hpC := projectionInCorner_abelian hc hp hpc
  have hpC0 : projectionInCorner hc hp.1 hpc ≠ 0 := fun h => hp0 (congrArg Subtype.val h)
  obtain ⟨q, hq, hq0, hhom⟩ := exists_homogeneous_piece_of_abelian_trace eC τ htr hfaith hpC hpC0
  refine ⟨(q : M), ⟨corner_projection_coe c hc hq.1,
    fun a => centralCorner_central hc hcc q (fun b => (hq.2 b).eq) a⟩,
    (corner_projection_le c hc hq.1).trans hcz,
    (fun h => hq0 (Subtype.ext h)), homogeneousCorner_to_ambient hc q hhom⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open FinitePathMain HochschildCorners

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_typeI_central_partition (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hI : TypeICentralSummand (1 : M)) :
    ∃ D : MaximalCentralPartition M HomogeneousTypeICorner, D.complement = 0 := by
  obtain ⟨D⟩ := exists_maximal_central_partition e HomogeneousTypeICorner
  refine ⟨D, ?_⟩
  by_contra h0
  obtain ⟨q, hq, hqle, hq0, hhom⟩ := finite_typeI_homogeneous_subprojection e hfinite hI
    D.complement_isProjection D.complement_central h0
  exact hq0 (D.maximal q hq.1 (fun a => (hq.2 a).eq) hqle hhom)

theorem finite_typeI_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hI : TypeICentralSummand (1 : M))
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ + n * ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  classical
  obtain ⟨D, hD⟩ := finite_typeI_central_partition e hfinite hI
  have htotal (a : M) (ha : ∀ i, D.projection i * a = 0) : a = 0 :=
    D.total a (by rw [hD, zero_mul]) ha
  have hpieces (i : D.Index) :
      ∃ b : Cochain (Corner (D.projection i) (D.isProjection i)) n,
        ‖b‖ ≤ ‖f‖ ∧ ∀ x, differentialValue b x =
          CentralCorner.restrict (D.projection i) (D.isProjection i) (D.central i) f x := by
    obtain ⟨hp, d, E, j, hab⟩ := D.property i
    obtain ⟨b, hbn, hb⟩ := finite_homogeneous_typeI_primitive_of_abelian_diagonal
      (cornerPredualEquiv (D.projection i) (D.isProjection i) e) E j hab
      (CentralCorner.restrict (D.projection i) (D.isProjection i) (D.central i) f)
      (CentralCorner.restrict_cocycle _ _ _ f hf)
    exact ⟨b, hbn.trans (CentralCorner.restrict_norm _ _ _ f), hb⟩
  choose b hbn hb using hpieces
  exact primitive_of_central_cut_primitives e (HochschildSakai.mul_hasPreadjoint e)
    D.projection D.isProjection D.central D.orthogonal htotal f hf
    (fun i => CentralCorner.extend (D.projection i) (D.isProjection i) (D.central i) (b i))
    (fun i => CentralCorner.extend_supported _ _ _ _)
    (fun i => CentralCorner.extend_primitive _ _ _ f (b i) (hb i))
    ‖f‖ (norm_nonneg f) (fun i => (CentralCorner.extend_norm _ _ _ _).trans (hbn i))

theorem finite_typeI_of_noTypeII1 (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hno : NoTypeII1Summand M) :
    TypeICentralSummand (1 : M) := by
  obtain ⟨p, hp, hc, hI, _, hII⟩ := exists_typeI_central_cut e
  have hcc (a : M) : (1 - p) * a = a * (1 - p) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  have hfinC : FiniteAlgebra (Corner (1 - p) hp.one_sub) :=
    (finiteCorner_iff (1 - p) hp.one_sub).mp
      (finiteCorner_of_finiteAlgebra hfinite (1 - p) hp.one_sub)
  have hcomp := hno (1 - p) hp.one_sub hcc hfinC hII
  have hp1 : p = 1 := (sub_eq_zero.mp hcomp).symm
  simpa only [hp1] using hI

theorem finite_noTypeII1_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hno : NoTypeII1Summand M)
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ‖g‖ ≤ ‖f‖ + (n + 1) * ‖f‖ ∧
      ∀ x, differentialValue g x = f x := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    finite_typeI_primitive e hfinite (finite_typeI_of_noTypeII1 e hfinite hno) f hf
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.finite_noTypeII1_primitive.{u} := @OAI.BoundedHochschild.KadisonRingrose.finite_noTypeII1_primitive.{u}
