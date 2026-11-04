-- Prove2me | solution 1 for OAI.SignedSweeps.signed_occurrence_moment_bound_fixed
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:29:40.688532+00:00
-- url     : https://prove2.me/submissions/35c275b7-df8b-4aa4-b156-f875ac27fa00

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2
import Theorems.Thm_OAI_SignedSweeps_signed_sweep_recurrence
import Theorems.Thm_OAI_SignedSweeps_signed_occurrence_moment_bound_proved_ranges

section
-- module OAI.Probability.SignedSweeps.Model
namespace TensorProduct

open scoped TensorProduct in
@[elab_as_elim]
protected theorem inductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  refine TensorProduct.induction_on z ?_ tmul add
  simpa using tmul 0 0

end TensorProduct

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma positive_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsPositive) :
    ∀ r : ℕ, (T ^ r).IsPositive
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hT
  | r + 2 => by
    have h := (positive_pow hT r).adjoint_conj T
    rw [hT.adjoint_eq] at h
    simpa only [← Module.End.mul_eq_comp, ← pow_succ', ← pow_succ] using h

lemma adjoint_mul_positive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : (positiveSquare T).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self T

lemma sweepSquare_positive {d : ℕ} (lam : Partition (2 ^ d)) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Specht lam) (sweepSquare lam) := by
  exact adjoint_mul_positive (E := Specht lam) (sweepOperator lam)

lemma sweepSquare_pow_positive {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Specht lam) (sweepSquare lam ^ r) :=
  positive_pow (sweepSquare_positive lam) r

lemma weightedMoment_nonneg {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    0 ≤ weightedMoment lam r := by
  have h := (sweepSquare_pow_positive lam r).trace_nonneg
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.nonneg_iff.mp h).1

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

lemma logMoment_pos {x : ℝ} (hx : 0 < x) : logMoment x = (Real.log x : EReal) := by
  simp [logMoment, ne_of_gt hx]

lemma logMoment_le_iff {x y : ℝ} (hx : 0 ≤ x) :
    logMoment x ≤ (y : EReal) ↔ x ≤ Real.exp y := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    simp [logMoment, (Real.exp_pos y).le]
  · rw [logMoment_pos h, EReal.coe_le_coe_iff, Real.log_le_iff_le_exp h]

lemma row_part_le_size {n a : ℕ} (lam : Partition n) (ha : a ∈ lam.1.rowLens) : a ≤ n := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  rw [YoungDiagram.rowLen_eq_card]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2

lemma signedEntropy_nonneg {u v : ℕ} (α : Partition u) (β : Partition v) :
    0 ≤ signedEntropy α β := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have hp : 0 < a := by
    rcases List.mem_append.mp ha with ha | ha
    · exact α.1.pos_of_mem_rowLens _ ha
    · exact β.1.pos_of_mem_rowLens _ ha
  have hs : a ≤ u + v := by
    rcases List.mem_append.mp ha with ha | ha
    · exact (row_part_le_size α ha).trans (Nat.le_add_right _ _)
    · exact (row_part_le_size β ha).trans (Nat.le_add_left _ _)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  rw [le_div_iff₀ (show (0 : ℝ) < a by exact_mod_cast hp), one_mul]
  exact_mod_cast hs

lemma signedEntropy_empty (α β : Partition 0) : signedEntropy α β = 0 := by
  have hα : α.1.rowLens = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have := row_part_le_size α ha
    have := α.1.pos_of_mem_rowLens a ha
    omega
  have hβ : β.1.rowLens = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have := row_part_le_size β ha
    have := β.1.pos_of_mem_rowLens a ha
    omega
  simp [signedEntropy, hα, hβ]

lemma coefficient_bounds {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    a / 2 ≤ coefficient a d ∧ coefficient a d ≤ a := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt d := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d), Real.sqrt_nonneg (d : ℝ)]
  have hdiv : 0 ≤ 1 / (2 * Real.sqrt d) := by positivity
  have hdiv' : 1 / (2 * Real.sqrt d) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  constructor <;> unfold coefficient <;> nlinarith

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma spechtRepresentation_norm {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (x : Specht lam) : ‖spechtRepresentation lam g x‖ = ‖x‖ := by
  let x' : (spechtSubrepresentation lam).toSubmodule := x
  change ‖regularIsometry g (x' : RegularSpace n)‖ = ‖(x' : RegularSpace n)‖
  exact (regularIsometry g).norm_map _

lemma polytabloid_empty (lam : Partition 0) :
    polytabloid lam = EuclideanSpace.single (1 : SymmetricGroup 0) 1 := by
  classical
  let : Unique (rowSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  let : Unique (colSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  simp only [polytabloid, Fintype.sum_unique]
  rw [(Subsingleton.elim (default : colSubgroup lam) 1),
    (Subsingleton.elim (default : rowSubgroup lam) 1)]
  simp

lemma polytabloid_empty_ne_zero (lam : Partition 0) : polytabloid lam ≠ 0 := by
  classical
  intro he
  have h := congrArg (fun x : RegularSpace 0 => x (1 : SymmetricGroup 0)) he
  simp [polytabloid_empty lam] at h

lemma spechtSubrepresentation_empty (lam : Partition 0) :
    (spechtSubrepresentation lam).toSubmodule = Submodule.span ℂ {polytabloid lam} := by
  change Submodule.span ℂ _ = _
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g = 1 := Subsingleton.elim _ _
    simp [hg]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨1, by simp [hx]⟩

lemma spechtDimension_empty (lam : Partition 0) : spechtDimension lam = 1 := by
  change finrank ℂ (spechtSubrepresentation lam).toSubmodule = 1
  rw [spechtSubrepresentation_empty]
  exact finrank_span_singleton (polytabloid_empty_ne_zero lam)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupAverage
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def groupAverage {G E : Type*} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) : E →ₗ[ℂ] E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g

lemma groupAverage_invariant {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E) :
    ρ g (groupAverage ρ x) = groupAverage ρ x := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma groupAverage_fixed {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (x : E)
    (hx : ∀ g, ρ g x = x) : groupAverage ρ x = x := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma groupAverage_idempotent {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) :
    IsIdempotentElem (groupAverage ρ) := by
  ext x
  exact groupAverage_fixed ρ _ (fun g => groupAverage_invariant ρ g x)

lemma representation_inner_inverse {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : E) :
    inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  let e : E →ₗᵢ[ℂ] E := ⟨ρ g, hρ g⟩
  have he : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc
    inner ℂ (ρ g x) y = inner ℂ (ρ g x) (ρ g (ρ g⁻¹ y)) := congrArg _ he.symm
    _ = inner ℂ x (ρ g⁻¹ y) := e.inner_map_map x (ρ g⁻¹ y)

lemma groupAverage_symmetric {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) : (groupAverage ρ).IsSymmetric := by
  intro x y
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_left,
    inner_smul_right, inner_sum, sum_inner, map_inv₀, map_natCast]
  congr 1
  simp_rw [representation_inner_inverse ρ hρ]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SwitchGeneration
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma swap_mem_fiberSubgroup {A C : Type*} [DecidableEq A] (f : A → C)
    {x y : A} (hxy : f x = f y) : Equiv.swap x y ∈ fiberSubgroup f := by
  intro z
  by_cases hx : z = x
  · subst z; simpa using hxy.symm
  by_cases hy : z = y
  · subst z; simpa using hxy
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Invariants
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def complexSign (n : ℕ) : SymmetricGroup n →* ℂ where
  toFun g := (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ)
  map_one' := by simp
  map_mul' g h := by simp

def spechtInclusion {n : ℕ} (lam : Partition n) : Specht lam →ₗ[ℂ] RegularSpace n :=
  (spechtSubrepresentation lam).toSubmodule.subtype

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BudgetBounds
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

@[simp] lemma clippedBudget_zero (τ : ℝ) (a : ℕ) : clippedBudget τ a 0 = 0 := by
  simp [clippedBudget]

lemma remainderBudget_eq_clippedBudget (κ : ℝ) (d l : ℕ) :
    remainderBudget κ d l = clippedBudget (coefficient κ d) (2 ^ d) l := by
  by_cases hl : l = 0 <;> simp [remainderBudget, clippedBudget, hl]

lemma clippedBudget_mono {τ τ' : ℝ} (hτ : τ ≤ τ') {a h : ℕ} (ha : 1 ≤ a) :
    clippedBudget τ a h ≤ clippedBudget τ' a h := by
  apply max_le_max le_rfl
  apply sub_le_sub_right
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτ (by positivity))
    (Real.log_nonneg (by exact_mod_cast ha))

lemma clippedBudget_growth {τ : ℝ} (hτ : 0 ≤ τ) {a h H : ℕ}
    (ha : 0 < a) (hhH : h ≤ H) (hHa : H ≤ a) :
    clippedBudget τ a H ≤ clippedBudget τ a h +
      (τ * Real.log a + 1) * ((H : ℝ) - h) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hl : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have hΔ : (0 : ℝ) ≤ (H : ℝ) - h := by exact_mod_cast (sub_nonneg.mpr (show (h : ℝ) ≤ H by exact_mod_cast hhH))
  have hcost : 0 ≤ (τ * Real.log a + 1) * ((H : ℝ) - h) := by positivity
  by_cases hH0 : H = 0
  · have : h = 0 := by omega
    subst H; subst h; simp
  have hHp : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH0
  have hHle : (H : ℝ) ≤ a := by exact_mod_cast hHa
  have hLH : 0 ≤ Real.log ((a : ℝ) / H) :=
    Real.log_nonneg ((le_div_iff₀ hHp).mpr (by simpa using hHle))
  unfold clippedBudget
  apply max_le
  · exact add_nonneg (le_max_left _ _) hcost
  by_cases hh0 : h = 0
  · subst h
    simp only [Nat.cast_zero, mul_zero, zero_mul, sub_self, max_self, sub_zero, zero_add]
    nlinarith [mul_nonneg hHp.le hLH]
  have hhp : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh0
  have hentropy : (h : ℝ) * Real.log ((a : ℝ) / h) -
      (H : ℝ) * Real.log ((a : ℝ) / H) ≤ (H : ℝ) - h := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hHp hhp)
    have hm := mul_le_mul_of_nonneg_left hlog hhp.le
    have heq : (h : ℝ) * ((H : ℝ) / h - 1) = (H : ℝ) - h := by
      field_simp
    rw [heq] at hm
    have hratio : Real.log ((a : ℝ) / h) =
        Real.log ((a : ℝ) / H) + Real.log ((H : ℝ) / h) := by
      simp only [Real.log_div hap.ne' hhp.ne', Real.log_div hap.ne' hHp.ne',
        Real.log_div hHp.ne' hhp.ne']
      ring
    rw [hratio]
    nlinarith [mul_nonneg hΔ hLH]
  have hb := le_max_right 0
    (τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h))
  nlinarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PolytabloidNonzero
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma mem_row_col_eq_one {n : ℕ} (lam : Partition n) {g : SymmetricGroup n}
    (hr : g ∈ rowSubgroup lam) (hc : g ∈ colSubgroup lam) : g = 1 := by
  apply Equiv.ext
  intro x
  change g x = x
  apply lam.tableau.symm.injective
  apply Subtype.ext
  exact Prod.ext (hr x) (hc x)

lemma column_row_product_eq_one_iff {n : ℕ} (lam : Partition n)
    (c : colSubgroup lam) (a : rowSubgroup lam) :
    c.1 * a.1 = 1 ↔ c = 1 ∧ a = 1 := by
  constructor
  · intro hca
    have hc : c.1 = a.1⁻¹ := eq_inv_of_mul_eq_one_left hca
    have hc1 : c = 1 := by
      apply Subtype.ext
      apply mem_row_col_eq_one lam
      · rw [hc]
        exact (rowSubgroup lam).inv_mem a.property
      · exact c.property
    refine ⟨hc1, ?_⟩
    rw [hc1, OneMemClass.coe_one, one_mul] at hca
    exact Subtype.ext hca
  · rintro ⟨rfl, rfl⟩
    simp

lemma polytabloid_at_one {n : ℕ} (lam : Partition n) : polytabloid lam 1 = 1 := by
  classical
  have he (c : colSubgroup lam) (a : rowSubgroup lam) :
      Pi.single (M := fun _ => ℂ) (c.1 * a.1) (1 : ℂ) (1 : SymmetricGroup n) =
        if c = 1 ∧ a = 1 then 1 else 0 := by
    simp only [Pi.single_apply, ← column_row_product_eq_one_iff lam, eq_comm]
  simp [polytabloid, he, ite_and]

lemma polytabloid_ne_zero {n : ℕ} (lam : Partition n) : polytabloid lam ≠ 0 := by
  intro h
  have hh := congrArg (fun f : RegularSpace n => f 1) h
  simp only [polytabloid_at_one, PiLp.zero_apply, one_ne_zero] at hh

def spechtGenerator {n : ℕ} (lam : Partition n) : Specht lam :=
  ⟨polytabloid lam, Submodule.subset_span ⟨1, by simp⟩⟩

lemma spechtGenerator_ne_zero {n : ℕ} (lam : Partition n) : spechtGenerator lam ≠ 0 := by
  intro h
  have hh := congrArg (spechtInclusion lam) h
  exact polytabloid_ne_zero lam hh

instance spechtNontrivial {n : ℕ} (lam : Partition n) : Nontrivial (Specht lam) :=
  ⟨⟨spechtGenerator lam, 0, spechtGenerator_ne_zero lam⟩⟩

lemma spechtDimension_pos {n : ℕ} (lam : Partition n) : 0 < spechtDimension lam :=
  Module.finrank_pos

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BudgetAbsorption
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped Topology
open Filter

def childDepth (d : ℕ) : ℕ := (d + 1) / 2

lemma childDepth_bounds {d : ℕ} (hd : 4 ≤ d) :
    1 ≤ childDepth d ∧ 4 * childDepth d ≤ 3 * d := by
  unfold childDepth
  omega

lemma coefficient_gap {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 4 ≤ d) :
    a / (16 * Real.sqrt d) ≤ coefficient a d - coefficient a (childDepth d) := by
  have hcd := childDepth_bounds hd
  have hp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hcp : (0 : ℝ) < childDepth d := by exact_mod_cast hcd.1
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hp
  have hcs : 0 < Real.sqrt (childDepth d) := Real.sqrt_pos.mpr hcp
  have ht : 4 * (childDepth d : ℝ) ≤ 3 * d := by exact_mod_cast hcd.2
  have hratio : (9 / 8 : ℝ) * Real.sqrt (childDepth d) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by positivity) hs.le).mp
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hcp.le]
  have hinv : (1 : ℝ) / (16 * Real.sqrt d) ≤
      1 / (2 * Real.sqrt (childDepth d)) - 1 / (2 * Real.sqrt d) := by
    rw [le_sub_iff_add_le]
    field_simp
    nlinarith
  calc
    _ = a * (1 / (16 * Real.sqrt d)) := by ring
    _ ≤ a * (1 / (2 * Real.sqrt (childDepth d)) - 1 / (2 * Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left hinv ha
    _ = _ := by unfold coefficient; ring

lemma nat_two_pow_log (d : ℕ) : Real.log ((2 ^ d : ℕ) : ℝ) = (d : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

lemma depth_power_error_tendsto {δ ξ : ℝ} (h : δ < ξ) :
    Tendsto (fun d : ℕ => Real.sqrt d * (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ))) atTop (𝓝 0) := by
  have hb : 0 < (ξ - δ) * Real.log 2 := mul_pos (sub_pos.mpr h) (Real.log_pos (by norm_num))
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) ((ξ - δ) * Real.log 2) hb).comp
    tendsto_natCast_atTop_atTop
  convert ht using 1
  funext d
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (2 ^ d : ℕ)),
    nat_two_pow_log]
  congr 2
  ring

lemma induction_error_absorption {η κ c C δ ξ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hc : 0 < c) (_hC : 0 ≤ C) (hδξ : δ < ξ) :
    ∃ d₀ : ℕ, 4 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ F : ℝ, 0 ≤ F → ∀ l : ℕ,
      c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) ≤
          F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) →
      C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        (coefficient η d - coefficient η (childDepth d)) * F +
          (coefficient κ d - coefficient κ (childDepth d)) *
            ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
  let a := min η κ
  have ha : 0 < a := lt_min hη hκ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := (depth_power_error_tendsto hδξ).const_mul C
  have hsmall : ∀ᶠ d : ℕ in atTop,
      C * (Real.sqrt d * (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ))) ≤ a * c / 32 := by
    apply ht.eventually_le_const
    simp only [mul_zero]
    positivity
  have hlinear : ∀ᶠ d : ℕ in atTop, 32 * C / (a * Real.log 2) ≤ Real.sqrt d :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hevent : ∀ᶠ d : ℕ in atTop, ∀ F : ℝ, 0 ≤ F → ∀ l : ℕ,
      c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) ≤
          F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) →
      C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        (coefficient η d - coefficient η (childDepth d)) * F +
          (coefficient κ d - coefficient κ (childDepth d)) *
            ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (4 : ℕ), hsmall, hlinear] with d hd hs hl
    intro F hF l hsize
    have hp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hp
    have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
    have hln : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by
      rw [nat_two_pow_log]
      positivity
    have hnormal : a / (32 * Real.sqrt d) * Real.log ((2 ^ d : ℕ) : ℝ) =
        a * Real.log 2 * Real.sqrt d / 32 := by
      rw [nat_two_pow_log]
      field_simp [hroot.ne']
      exact (Real.sq_sqrt hp.le).symm
    have hlin : C ≤ a / (32 * Real.sqrt d) * Real.log ((2 ^ d : ℕ) : ℝ) := by
      rw [hnormal]
      have h := (div_le_iff₀ (mul_pos ha hlog2)).mp hl
      nlinarith
    have hlin' : C * (l : ℝ) ≤ a / (32 * Real.sqrt d) *
        ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hlin (Nat.cast_nonneg l)
    have hpows : (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ)) *
        (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) = (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ)) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    have hsub : C * (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ)) ≤
        a / (32 * Real.sqrt d) * (c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ))) := by
      apply (mul_le_mul_iff_of_pos_left hroot).mp
      calc
        _ = (C * (Real.sqrt d * (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ)))) *
            (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) := by
          rw [mul_assoc C, mul_assoc (Real.sqrt d), hpows]
          ring
        _ ≤ (a * c / 32) * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) :=
          mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hn.le _)
        _ = _ := by field_simp
    have hsub' := hsub.trans (mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ a / (32 * Real.sqrt d) by positivity))
    have hηgap : a / (16 * Real.sqrt d) ≤ coefficient η d - coefficient η (childDepth d) :=
      (div_le_div_of_nonneg_right (min_le_left η κ) (by positivity)).trans (coefficient_gap hη.le hd)
    have hκgap : a / (16 * Real.sqrt d) ≤ coefficient κ d - coefficient κ (childDepth d) :=
      (div_le_div_of_nonneg_right (min_le_right η κ) (by positivity)).trans (coefficient_gap hκ.le hd)
    calc
      _ = C * (l : ℝ) + C * (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ)) := by ring
      _ ≤ a / (32 * Real.sqrt d) * ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) +
          a / (32 * Real.sqrt d) * (F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) :=
        add_le_add hlin' hsub'
      _ ≤ a / (16 * Real.sqrt d) * (F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
        have hu : 0 ≤ a / (32 * Real.sqrt d) * F := by positivity
        have heq : a / (16 * Real.sqrt d) = 2 * (a / (32 * Real.sqrt d)) := by ring
        rw [heq]
        nlinarith
      _ = a / (16 * Real.sqrt d) * F +
          a / (16 * Real.sqrt d) * ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hηgap hF)
        (mul_le_mul_of_nonneg_right hκgap (mul_nonneg (Nat.cast_nonneg l) hln))
  obtain ⟨D, hD⟩ := eventually_atTop.mp hevent
  exact ⟨max D 4, le_max_right _ _, fun d hd => hD d ((le_max_left _ _).trans hd)⟩

lemma scalar_induction_budget {η κ c C δ ξ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hc : 0 < c) (hC : 0 ≤ C) (hδξ : δ < ξ) :
    ∃ d₀ : ℕ, 4 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ F : ℝ, 0 ≤ F → ∀ l : ℕ,
      c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) ≤
          F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) →
      coefficient η (childDepth d) * F +
          coefficient κ (childDepth d) * l * Real.log ((2 ^ d : ℕ) : ℝ) -
          (l : ℝ) * Real.log (((2 ^ d : ℕ) : ℝ) / l) +
          C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        coefficient η d * F + remainderBudget κ d l := by
  obtain ⟨d₀, hd₀, hstep⟩ := induction_error_absorption hη hκ hc hC hδξ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd F hF l hsize
  have he := hstep d hd F hF l hsize
  have hb : coefficient κ d * l * Real.log ((2 ^ d : ℕ) : ℝ) -
      (l : ℝ) * Real.log (((2 ^ d : ℕ) : ℝ) / l) ≤ remainderBudget κ d l := by
    rw [remainderBudget_eq_clippedBudget]
    exact le_max_right 0 _
  nlinarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ColumnAnnihilation
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma regularRepresentation_single {n : ℕ} (g h : SymmetricGroup n) (z : ℂ) :
    regularRepresentation n g (EuclideanSpace.single h z) =
      EuclideanSpace.single (g * h) z := by
  classical
  ext k
  simp only [regularRepresentation_apply, PiLp.single_apply, inv_mul_eq_iff_eq_mul]

lemma complexSign_mul_self {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g * complexSign n g = 1 := by
  change (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) = 1
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

lemma polytabloid_column_action {n : ℕ} (lam : Partition n) (g : colSubgroup lam) :
    regularRepresentation n g.1 (polytabloid lam) = complexSign n g.1 • polytabloid lam := by
  classical
  change regularRepresentation n g.1 (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
    complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1) = complexSign n g.1 •
    (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
      complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1)
  simp only [map_sum, map_smul, regularRepresentation_single, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft g)
  intro c
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, smul_smul, ← mul_assoc,
    complexSign_mul_self, one_mul]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PartitionGeometry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma polytabloid_right_row {n : ℕ} (lam : Partition n)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (g * a.1) = polytabloid lam g := by
  classical
  simp only [polytabloid, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_congr rfl
  intro c _
  symm
  apply Fintype.sum_equiv (Equiv.mulRight a)
  intro b
  have h : (g * a.1 = c.1 * (b * a).1) ↔ g = c.1 * b.1 := by
    simp only [Subgroup.coe_mul, ← mul_assoc, mul_left_inj]
  simp only [Equiv.coe_mulRight, PiLp.single_apply, h]

lemma specht_right_row {n : ℕ} (lam : Partition n) (x : Specht lam)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    (spechtInclusion lam x) (g * a.1) = (spechtInclusion lam x) g := by
  have haux : ∀ y ∈ (spechtSubrepresentation lam).toSubmodule,
      y (g * a.1) = y g := by
    intro y hy
    change y ∈ Submodule.span ℂ _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      simp only [regularRepresentation_apply, ← mul_assoc]
      exact polytabloid_right_row lam a _
    | zero => rfl
    | add y z _ _ hy hz => simpa only [PiLp.add_apply] using congrArg₂ (· + ·) hy hz
    | smul c y _ hy => simpa only [PiLp.smul_apply] using congrArg (c • ·) hy
  exact haux _ x.property

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RowSymmetry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma diagram_rowLens_sum (lam : YoungDiagram) : lam.rowLens.sum = lam.card := by
  have hh (c : ℕ × ℕ) (hc : c ∈ lam.cells) : c.1 ∈ Finset.range (lam.colLen 0) := by
    have hi : c.1 < lam.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hc
    exact Finset.mem_range.mpr (hi.trans_le (lam.colLen_anti 0 c.2 (Nat.zero_le _)))
  have he := Finset.sum_fiberwise_of_maps_to (g := Prod.fst) hh (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at he
  rw [YoungDiagram.rowLens, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, YoungDiagram.card]
  simp_rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  exact he

lemma partition_rowLens_sum {n : ℕ} (lam : Partition n) : lam.1.rowLens.sum = n :=
  (diagram_rowLens_sum lam.1).trans lam.2

lemma sorted_drop_term_bound (L : List ℕ) (hL : L.SortedGE) (q a : ℕ)
    (ha : a ∈ L.drop q) : q * a ≤ L.sum := by
  have hlen := List.length_pos_of_mem ha
  simp only [List.length_drop] at hlen
  have hq : q ≤ L.length := by omega
  have hsplit := List.pairwise_append.mp (show
      (L.take q ++ L.drop q).Pairwise (fun x y : ℕ => y ≤ x) by
    simpa using hL.pairwise)
  have hb : (L.take q).length * a ≤ (L.take q).sum := by
    simpa using List.sum_le_sum (l := L.take q) (f := fun _ => a) (g := id)
      (fun b hb => hsplit.2.2 b hb a ha)
  rw [List.length_take, min_eq_left hq] at hb
  have hs := List.sum_take_add_sum_drop L q
  omega

def truncatePartition {n : ℕ} (q : ℕ) (lam : Partition n) :
    Partition ((lam.1.rowLens.take q).sum) := by
  let hsort : (lam.1.rowLens.take q).SortedGE :=
    ((lam.1.rowLens_sorted).pairwise.sublist (List.take_sublist q _)).sortedGE
  refine ⟨YoungDiagram.ofRowLens _ hsort, ?_⟩
  rw [← diagram_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self]
  intro a ha
  exact lam.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha)

@[simp]
lemma truncatePartition_rowLens {n : ℕ} (q : ℕ) (lam : Partition n) :
    (truncatePartition q lam).1.rowLens = lam.1.rowLens.take q := by
  exact YoungDiagram.rowLens_ofRowLens_eq_self
    (hw := ((lam.1.rowLens_sorted).pairwise.sublist (List.take_sublist q _)).sortedGE)
    (fun a ha =>
    lam.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha))

def partsEntropy (total : ℝ) (L : List ℕ) : ℝ :=
  (L.map (fun a : ℕ => (a : ℝ) * Real.log (total / a))).sum

lemma partsEntropy_mono {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (L : List ℕ)
    (hL : ∀ a ∈ L, 0 < a) : partsEntropy A L ≤ partsEntropy B L := by
  apply List.sum_le_sum
  intro a ha
  have hp : (0 : ℝ) < a := by exact_mod_cast hL a ha
  apply mul_le_mul_of_nonneg_left _ hp.le
  apply Real.log_le_log (div_pos hA hp)
  exact div_le_div_of_nonneg_right hAB hp.le

lemma partsEntropy_mono_of_total (A B : ℕ) (hAB : A ≤ B) (L : List ℕ)
    (hL : ∀ a ∈ L, 0 < a) (hs : L.sum ≤ A) : partsEntropy A L ≤ partsEntropy B L := by
  by_cases hA : A = 0
  · subst A
    have hz : L = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro a ha
      have he : a = 0 := (List.sum_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)) a ha
      exact (Nat.ne_of_gt (hL a ha)) he)
    simp only [hz, partsEntropy, List.map_nil, List.sum_nil, le_refl]
  · apply partsEntropy_mono (by exact_mod_cast Nat.pos_of_ne_zero hA) (by exact_mod_cast hAB) L hL

lemma partsEntropy_drop_bound {total q : ℕ} (hq : 0 < q) (L : List ℕ)
    (hL : ∀ a ∈ L, 0 < a) (hterm : ∀ a ∈ L, q * a ≤ total) :
    (L.sum : ℝ) * Real.log q ≤ partsEntropy total L := by
  have hsum : (L.map (fun a : ℕ => (a : ℝ) * Real.log q)).sum = (L.sum : ℝ) * Real.log q := by
    clear hL hterm
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul, ih]
  rw [← hsum]
  apply List.sum_le_sum
  intro a ha
  have hp : (0 : ℝ) < a := by exact_mod_cast hL a ha
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply mul_le_mul_of_nonneg_left _ hp.le
  apply Real.log_le_log hq'
  rw [le_div_iff₀ hp]
  exact_mod_cast hterm a ha

lemma signedEntropy_truncate {u v : ℕ} (α : Partition u) (β : Partition v) {q : ℕ}
    (hq : 0 < q) :
    signedEntropy (truncatePartition q α) (truncatePartition q β) +
      (((α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum : ℕ) : ℝ) * Real.log q ≤
        signedEntropy α β := by
  let A := α.1.rowLens.take q ++ β.1.rowLens.take q
  let D := α.1.rowLens.drop q ++ β.1.rowLens.drop q
  have hα := List.sum_take_add_sum_drop α.1.rowLens q
  have hβ := List.sum_take_add_sum_drop β.1.rowLens q
  rw [partition_rowLens_sum] at hα hβ
  have hst : A.sum + D.sum = u + v := by simp only [A, D, List.sum_append]; omega
  have hsumle : A.sum ≤ u + v := by omega
  have hpA : ∀ a ∈ A, 0 < a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact α.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha)
    · exact β.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha)
  have hpD : ∀ a ∈ D, 0 < a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact α.1.pos_of_mem_rowLens a (List.mem_of_mem_drop ha)
    · exact β.1.pos_of_mem_rowLens a (List.mem_of_mem_drop ha)
  have ht : ∀ a ∈ D, q * a ≤ u + v := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have := sorted_drop_term_bound α.1.rowLens α.1.rowLens_sorted q a ha
      rw [partition_rowLens_sum] at this
      omega
    · have := sorted_drop_term_bound β.1.rowLens β.1.rowLens_sorted q a ha
      rw [partition_rowLens_sum] at this
      omega
  have hkeep := partsEntropy_mono_of_total A.sum (u + v) hsumle A hpA (le_refl _)
  have hdrop := partsEntropy_drop_bound hq D hpD ht
  have hfull : partsEntropy (u + v : ℕ) A + partsEntropy (u + v : ℕ) D = signedEntropy α β := by
    have hs (L : List ℕ) : partsEntropy (u + v : ℕ) (L.take q) +
        partsEntropy (u + v : ℕ) (L.drop q) = partsEntropy (u + v : ℕ) L := by
      rw [partsEntropy, partsEntropy, ← List.sum_append, ← List.map_append, List.take_append_drop]
      rfl
    simpa only [partsEntropy, A, D, List.map_append, List.sum_append, ← add_assoc,
      add_comm, add_left_comm, Nat.cast_add, signedEntropy] using congrArg₂ (· + ·) (hs α.1.rowLens) (hs β.1.rowLens)
  have htrunc : partsEntropy A.sum A = signedEntropy (truncatePartition q α) (truncatePartition q β) := by
    simp [partsEntropy, signedEntropy, A]
  have hd : (D.sum : ℝ) = ((α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum : ℕ) := by
    simp [D]
  rw [← hfull, ← htrunc, ← hd]
  exact add_le_add hkeep hdrop

lemma remainderBudget_growth {κ : ℝ} (hκ : 0 ≤ κ) {d l L : ℕ} (hd : 1 ≤ d)
    (hlL : l ≤ L) (hLn : L ≤ 2 ^ d) :
    remainderBudget κ d L ≤ remainderBudget κ d l +
      (coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1) * ((L : ℝ) - l) := by
  simp only [remainderBudget_eq_clippedBudget]
  exact clippedBudget_growth ((by positivity : (0 : ℝ) ≤ κ / 2).trans (coefficient_bounds hκ hd).1) (pow_pos (by norm_num) _) hlL hLn

lemma truncated_budget_le {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {d u v l : ℕ} (hd : 1 ≤ d) (hn : u + v + l = 2 ^ d)
    (α : Partition u) (β : Partition v) {q : ℕ} (hq : 0 < q)
    (hcost : coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1 ≤
      coefficient η d * Real.log q) :
    coefficient η d * signedEntropy (truncatePartition q α) (truncatePartition q β) +
      remainderBudget κ d (l + (α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum) ≤
    coefficient η d * signedEntropy α β + remainderBudget κ d l := by
  let t := (α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum
  have ht : l + t ≤ 2 ^ d := by
    have hu := List.sum_take_add_sum_drop α.1.rowLens q
    have hv := List.sum_take_add_sum_drop β.1.rowLens q
    rw [partition_rowLens_sum] at hu hv
    dsimp only [t]
    omega
  have hg := remainderBudget_growth hκ hd (Nat.le_add_right l t) ht
  have he := mul_le_mul_of_nonneg_left (signedEntropy_truncate α β hq)
    ((by positivity : (0 : ℝ) ≤ η / 2).trans (coefficient_bounds hη hd).1)
  have hc := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  simp only [Nat.cast_add, add_sub_cancel_left] at hg
  rw [Nat.add_assoc]
  change coefficient η d * signedEntropy (truncatePartition q α) (truncatePartition q β) +
    remainderBudget κ d (l + t) ≤ _
  change coefficient η d * (signedEntropy (truncatePartition q α) (truncatePartition q β) +
    (t : ℝ) * Real.log q) ≤ _ at he
  nlinarith

lemma truncation_coefficient_eventually {η κ ε : ℝ} (hη : 0 < η) (hκ : 0 ≤ κ)
    (hε : 0 < ε) (hκsmall : κ < η * ε / 2) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀,
      coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1 ≤
        coefficient η d * Real.log (⌈((2 ^ d : ℕ) : ℝ) ^ ε⌉₊ : ℕ) := by
  open Filter in
  have hlarge : ∀ᶠ d : ℕ in atTop,
      1 / (η * ε / 2 - κ) ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by
    have ht : Tendsto (fun d : ℕ => Real.log ((2 ^ d : ℕ) : ℝ)) atTop atTop := by
      simp_rw [nat_two_pow_log]
      exact tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num))
    exact ht.eventually_ge_atTop _
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max D 1, le_max_right _ _, ?_⟩
  intro d hd
  have hd1 : 1 ≤ d := (le_max_right D 1).trans hd
  have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  have hlog : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by rw [nat_two_pow_log]; positivity
  have hq : ε * Real.log ((2 ^ d : ℕ) : ℝ) ≤
      Real.log (⌈((2 ^ d : ℕ) : ℝ) ^ ε⌉₊ : ℕ) := by
    rw [← Real.log_rpow hn]
    exact Real.log_le_log (Real.rpow_pos_of_pos hn _) (Nat.le_ceil _)
  have hηlb := (coefficient_bounds hη.le hd1).1
  have hκub := (coefficient_bounds hκ hd1).2
  have hl := (div_le_iff₀ (sub_pos.mpr hκsmall)).mp (hD d ((le_max_left _ _).trans hd))
  have hc := mul_le_mul_of_nonneg_left hq ((by positivity : (0 : ℝ) ≤ η / 2).trans (coefficient_bounds hη.le hd1).1)
  have hηterm := mul_le_mul_of_nonneg_right hηlb (mul_nonneg hε.le hlog)
  have hκterm := mul_le_mul_of_nonneg_right hκub hlog
  nlinarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.YoungLemma
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma fin_strictMono_val_le {a : ℕ} (f : Fin a → ℕ) (hf : StrictMono f) (i : Fin a) :
    i.val ≤ f i := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < a := by omega
    have h := hf (show (⟨i, hi'⟩ : Fin a) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i)
    have := ih hi'
    change i + 1 ≤ f ⟨i + 1, hi⟩
    change i ≤ f ⟨i, hi'⟩ at this
    omega

lemma fin_injective_sum_lower {a : ℕ} (f : Fin a → ℕ) (hf : Function.Injective f) :
    (∑ i : Fin a, i.val) ≤ ∑ i : Fin a, f i := by
  let s : Finset ℕ := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∑ i : Fin a, s.orderEmbOfFin hs i = ∑ i : Fin a, f i := by
    have h₁ := Finset.sum_image (s := Finset.univ) (f := id) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.sum_image (s := Finset.univ) (f := id) hf.injOn
    simp only [id_eq, Finset.image_orderEmbOfFin_univ] at h₁ h₂
    exact h₁.symm.trans h₂
  rw [← he]
  exact Finset.sum_le_sum (fun i _ => fin_strictMono_val_le _ (s.orderEmbOfFin hs).strictMono i)

lemma fin_injective_minimal_sum {a : ℕ} (f : Fin a → ℕ) (hf : Function.Injective f)
    (hmin : ∑ i : Fin a, f i = ∑ i : Fin a, i.val) (i : Fin a) : f i < a := by
  let s : Finset ℕ := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∑ i : Fin a, s.orderEmbOfFin hs i = ∑ i : Fin a, i.val := by
    have h₁ := Finset.sum_image (s := Finset.univ) (f := id) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.sum_image (s := Finset.univ) (f := id) hf.injOn
    simp only [id_eq, Finset.image_orderEmbOfFin_univ] at h₁ h₂
    exact (h₁.symm.trans h₂).trans hmin
  have hp : ∀ j : Fin a, s.orderEmbOfFin hs j = j.val := by
    have hh := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset (Fin a))) =>
      fin_strictMono_val_le _ (s.orderEmbOfFin hs).strictMono j)).mp he.symm
    exact fun j => (hh j (Finset.mem_univ _)).symm
  have hi : f i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, hj⟩ := (s.orderIsoOfFin hs).surjective ⟨f i, hi⟩
  have h := congrArg Subtype.val hj
  change s.orderEmbOfFin hs j = f i at h
  rw [hp] at h
  exact h ▸ j.isLt

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma rowOf_lt {n : ℕ} (lam : Partition n) (x : Fin n) : lam.rowOf x < lam.1.colLen 0 := by
  have h := YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x).property
  exact h.trans_le (lam.1.colLen_anti 0 _ (Nat.zero_le _))

lemma colOf_lt_rowLen {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.colOf x < lam.1.rowLen (lam.rowOf x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (lam.tableau.symm x).property

def rowEquiv {n : ℕ} (lam : Partition n) :
    (Σ i : Fin (lam.1.colLen 0), Fin (lam.1.rowLen i)) ≃ Fin n where
  toFun x := lam.tableau ⟨(x.1.val, x.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  invFun x := ⟨⟨lam.rowOf x, lam.rowOf_lt x⟩, ⟨lam.colOf x, lam.colOf_lt_rowLen x⟩⟩
  left_inv x := by
    apply Sigma.ext
    · apply Fin.ext
      simp [rowOf]
    · apply (Fin.heq_ext_iff (by simp [rowOf])).mpr
      simp [colOf]
  right_inv x := by simp only; exact lam.tableau.apply_symm_apply x

@[simp] lemma rowOf_rowEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) (j : Fin (lam.1.rowLen i)) :
    lam.rowOf (lam.rowEquiv ⟨i, j⟩) = i.val := by simp [rowEquiv, rowOf]

@[simp] lemma colOf_rowEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) (j : Fin (lam.1.rowLen i)) :
    lam.colOf (lam.rowEquiv ⟨i, j⟩) = j.val := by simp [rowEquiv, colOf]

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma young_column_bound {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (x : Fin n) : lam.colOf (g x) < lam.1.rowLen (lam.rowOf x) := by
  let f := fun i : Fin (lam.1.colLen 0) => fun j : Fin (lam.1.rowLen i) =>
    lam.colOf (g (lam.rowEquiv ⟨i, j⟩))
  have hf (i : Fin (lam.1.colLen 0)) : Function.Injective (f i) := by
    intro j k h
    have he := htrans (lam.rowEquiv ⟨i, j⟩) (lam.rowEquiv ⟨i, k⟩) (by simp) h
    have hsig := lam.rowEquiv.injective he
    exact Sigma.mk.inj_iff.mp hsig |>.2 |> eq_of_heq
  have hsum : ∑ i, ∑ j, f i j = ∑ i : Fin (lam.1.colLen 0), ∑ j : Fin (lam.1.rowLen i), j.val := by
    calc
      _ = ∑ y : Fin n, lam.colOf (g y) := by
        exact (Fintype.sum_sigma (fun t : Σ i : Fin (lam.1.colLen 0),
          Fin (lam.1.rowLen i) => lam.colOf (g (lam.rowEquiv t)))).symm.trans
            (Equiv.sum_comp lam.rowEquiv (fun y : Fin n => lam.colOf (g y)))
      _ = ∑ y : Fin n, lam.colOf y := Equiv.sum_comp g _
      _ = _ := by
        rw [← Equiv.sum_comp lam.rowEquiv lam.colOf, Fintype.sum_sigma]
        simp only [Partition.colOf_rowEquiv]
  have hrow (i : Fin (lam.1.colLen 0)) : ∑ j, f i j = ∑ j : Fin (lam.1.rowLen i), j.val := by
    have h := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈
        (Finset.univ : Finset (Fin (lam.1.colLen 0)))) => fin_injective_sum_lower (f i) (hf i))).mp hsum.symm
    exact (h i (Finset.mem_univ _)).symm
  let ix := lam.rowEquiv.symm x
  have h := fin_injective_minimal_sum (f ix.1) (hf ix.1) (hrow ix.1) ix.2
  change lam.colOf (g (lam.rowEquiv ix)) < _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h

lemma young_factorization {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    ∃ c : colSubgroup lam, ∃ a : rowSubgroup lam, g = c.1 * a.1 := by
  let r : Fin n → Fin n := fun x => lam.tableau
    ⟨(lam.rowOf x, lam.colOf (g x)), YoungDiagram.mem_iff_lt_rowLen.mpr (young_column_bound lam g htrans x)⟩
  have hr (x : Fin n) : lam.rowOf (r x) = lam.rowOf x := by simp [r, Partition.rowOf]
  have hc (x : Fin n) : lam.colOf (r x) = lam.colOf (g x) := by simp [r, Partition.colOf]
  have hi : Function.Injective r := by
    intro x y h
    apply htrans x y
    · simpa only [hr] using congrArg lam.rowOf h
    · simpa only [hc] using congrArg lam.colOf h
  let a : SymmetricGroup n := Equiv.ofBijective r ((Fintype.bijective_iff_injective_and_card r).mpr ⟨hi, rfl⟩)
  have ha : a ∈ rowSubgroup lam := hr
  have hca : g * a⁻¹ ∈ colSubgroup lam := by
    intro x
    have hh := hc (a⁻¹ x)
    change lam.colOf (a (a⁻¹ x)) = lam.colOf ((g * a⁻¹) x) at hh
    simpa using hh.symm
  refine ⟨⟨g * a⁻¹, hca⟩, ⟨a, ha⟩, ?_⟩
  simp

lemma young_collision {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ¬ ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    ∃ a : rowSubgroup lam, ∃ c : colSubgroup lam,
      c.1 * g = g * a.1 ∧ complexSign n c.1 = -1 := by
  push Not at htrans
  obtain ⟨x, y, hr, hc, hxy⟩ := htrans
  refine ⟨⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩,
    ⟨Equiv.swap (g x) (g y), swap_mem_fiberSubgroup _ hc⟩, ?_, ?_⟩
  · apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  · simp [complexSign, Equiv.Perm.sign_swap (g.injective.ne hxy)]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Irreducibility
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

@[simp] lemma complexSign_inv {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g⁻¹ = complexSign n g := by
  simp [complexSign]

lemma polytabloid_left_column {n : ℕ} (lam : Partition n)
    (c : colSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (c.1 * g) = complexSign n c.1 * polytabloid lam g := by
  have h := congrArg (fun f : RegularSpace n => f g) (polytabloid_column_action lam c⁻¹)
  simpa only [regularRepresentation_apply, Subgroup.coe_inv, inv_inv, PiLp.smul_apply,
    smul_eq_mul, complexSign_inv] using h

lemma row_column_vector_eq {n : ℕ} (lam : Partition n) (f : RegularSpace n)
    (hr : ∀ (a : rowSubgroup lam) g, f (g * a.1) = f g)
    (hc : ∀ (c : colSubgroup lam) g, f (c.1 * g) = complexSign n c.1 * f g) :
    f = f 1 • polytabloid lam := by
  ext g
  change f g = f 1 * polytabloid lam g
  by_cases ht : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y
  · obtain ⟨c, a, rfl⟩ := young_factorization lam g ht
    rw [hr, polytabloid_right_row, ← mul_one c.1, hc, polytabloid_left_column,
      polytabloid_at_one]
    ring
  · obtain ⟨a, c, he, hs⟩ := young_collision lam g ht
    have hf : f g = 0 := by
      have h := hc c g
      rw [he, hr, hs, neg_one_mul] at h
      linear_combination h / 2
    have hp : polytabloid lam g = 0 := by
      have h := polytabloid_left_column lam c g
      rw [he, polytabloid_right_row, hs, neg_one_mul] at h
      linear_combination h / 2
    simp only [hf, hp, mul_zero]

lemma spechtGenerator_column_action {n : ℕ} (lam : Partition n) (c : colSubgroup lam) :
    spechtRepresentation lam c.1 (spechtGenerator lam) = complexSign n c.1 • spechtGenerator lam := by
  apply Subtype.ext
  exact polytabloid_column_action lam c

lemma specht_hom_ext {n : ℕ} (lam : Partition n)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E)
    (f g : Representation.IntertwiningMap (spechtRepresentation lam) ρ)
    (h : f (spechtGenerator lam) = g (spechtGenerator lam)) : f = g := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have haux : ∀ v (hv : v ∈ (spechtSubrepresentation lam).toSubmodule),
      f ⟨v, hv⟩ = g ⟨v, hv⟩ := by
    intro v hv
    change v ∈ Submodule.span ℂ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      change f (spechtRepresentation lam a (spechtGenerator lam)) =
        g (spechtRepresentation lam a (spechtGenerator lam))
      rw [f.isIntertwining, g.isIntertwining, h]
    | zero => exact (map_zero f).trans (map_zero g).symm
    | add x y hx hy hx' hy' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change y ∈ (spechtSubrepresentation lam).toSubmodule at hy
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      exact (map_add f (show Specht lam from ⟨x, hx⟩) (show Specht lam from ⟨y, hy⟩)).trans
        ((congrArg₂ (· + ·) hx' hy').trans (map_add g _ _).symm)
    | smul a x hx hx' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change f (a • (⟨x, hx⟩ : Specht lam)) = g (a • (⟨x, hx⟩ : Specht lam))
      exact (map_smul f a (show Specht lam from ⟨x, hx⟩)).trans
        ((congrArg (a • ·) hx').trans (map_smul g _ _).symm)
  exact haux (spechtInclusion lam x) x.property

lemma specht_endomorphism_scalar {n : ℕ} (lam : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation lam)) :
    ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap (spechtRepresentation lam)
      (spechtRepresentation lam)) := by
  let v := f (spechtGenerator lam)
  have hh : spechtInclusion lam v = (spechtInclusion lam v) 1 • polytabloid lam := by
    apply row_column_vector_eq
    · exact specht_right_row lam v
    · intro c g
      have he : spechtRepresentation lam (c⁻¹).1 v = complexSign n (c⁻¹).1 • v := by
        rw [← f.isIntertwining, spechtGenerator_column_action, map_smul]
      have h := congrArg (fun x => (spechtInclusion lam x) g) he
      change (spechtInclusion lam v) ((c⁻¹).1⁻¹ * g) =
        complexSign n (c⁻¹).1 * (spechtInclusion lam v) g at h
      simpa only [Subgroup.coe_inv, inv_inv, complexSign_inv] using h
  refine ⟨(spechtInclusion lam v) 1, specht_hom_ext lam (spechtRepresentation lam) _ _ ?_⟩
  apply Subtype.ext
  exact hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma invariant_starProjection_intertwines {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (S : Subrepresentation ρ) (g : G) (x : E) :
    S.toSubmodule.starProjection (ρ g x) = ρ g (S.toSubmodule.starProjection x) := by
  apply S.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact S.apply_mem_toSubmodule g (S.toSubmodule.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, representation_inner_inverse ρ hρ]
    exact S.toSubmodule.starProjection_inner_eq_zero x _ (S.apply_mem_toSubmodule g⁻¹ hw)

lemma irreducible_of_scalar_commutant {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (hscalar : ∀ f : Representation.IntertwiningMap ρ ρ,
      ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap ρ ρ)) :
    ρ.IsIrreducible := by
  have hb : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ E) hh
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hb⟩⟩
  refine ⟨?_⟩
  intro S
  let p : Representation.IntertwiningMap ρ ρ :=
    S.toSubmodule.starProjection.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ
      (invariant_starProjection_intertwines ρ hρ S)
  obtain ⟨z, hz⟩ := hscalar p
  have hp (x : E) : S.toSubmodule.starProjection x = z • x :=
    congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hz
  have hid (x : E) : (z * z) • x = z • x := by
    rw [mul_smul, ← hp, ← hp]
    exact S.toSubmodule.starProjection_eq_self_iff.mpr (S.toSubmodule.starProjection_apply_mem x)
  have hc : z * (z - 1) = 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have he : (z * (z - 1)) • x = 0 := by
      rw [mul_sub, mul_one, sub_smul, hid, sub_self]
    exact (smul_eq_zero.mp he).resolve_right hx
  rcases mul_eq_zero.mp hc with hz0 | hz1
  · left
    apply Subrepresentation.toSubmodule_injective
    apply eq_bot_iff.mpr
    intro x hx
    have he := S.toSubmodule.starProjection_eq_self_iff.mpr hx
    rw [hp, hz0, zero_smul] at he
    exact he.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply eq_top_iff.mpr
    intro x hx
    rw [sub_eq_zero] at hz1
    have he := S.toSubmodule.starProjection_apply_mem x
    rwa [hp, hz1, one_smul] at he

theorem specht_irreducible {n : ℕ} (lam : Partition n) :
    (spechtRepresentation lam).IsIrreducible :=
  irreducible_of_scalar_commutant _ (spechtRepresentation_norm lam)
    (specht_endomorphism_scalar lam)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OrbitDimension
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma finrank_le_translates {G E A Q : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A] [Fintype Q]
    (ρ : Representation ℂ G E) [ρ.IsIrreducible] (f : A →ₗ[ℂ] E) (hf : f ≠ 0)
    (rep : Q → G) (index : G → Q)
    (hrep : ∀ g x, ∃ y, ρ g (f x) = ρ (rep (index g)) (f y)) :
    finrank ℂ E ≤ Fintype.card Q * finrank ℂ A := by
  classical
  let L : (Q → A) →ₗ[ℂ] E :=
    { toFun := fun w => ∑ i, ρ (rep i) (f (w i))
      map_add' := by intro w z; simp [Finset.sum_add_distrib]
      map_smul' := by intro z w; simp [Finset.smul_sum] }
  have horbit (g : G) (x : A) : ρ g (f x) ∈ LinearMap.range L := by
    obtain ⟨y, hy⟩ := hrep g x
    refine ⟨Pi.single (index g) y, ?_⟩
    rw [hy]
    simp [L, Pi.single_apply, apply_ite, map_zero]
  let S : Subrepresentation ρ :=
    { toSubmodule := LinearMap.range L
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨w, rfl⟩ := hx
        change ρ g (∑ i, ρ (rep i) (f (w i))) ∈ LinearMap.range L
        rw [map_sum]
        apply Submodule.sum_mem
        intro i hi
        rw [← Module.End.mul_apply, ← map_mul]
        exact horbit (g * rep i) (w i) }
  have hS : S ≠ ⊥ := by
    intro he
    apply hf
    ext x
    have hx := horbit 1 x
    rw [map_one, Module.End.one_apply] at hx
    have hbot : LinearMap.range L = ⊥ := congrArg Subrepresentation.toSubmodule he
    rw [hbot] at hx
    exact hx
  have htop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  have hsur : Function.Surjective L := LinearMap.range_eq_top.mp
    (congrArg Subrepresentation.toSubmodule htop)
  calc
    finrank ℂ E ≤ finrank ℂ (Q → A) := LinearMap.finrank_le_finrank_of_surjective hsur
    _ = Fintype.card Q * finrank ℂ A := by simp [Module.finrank_pi_fintype]

def ColoringOrbit {n : ℕ} {I : Type*} (c : Fin n → I) : Type _ :=
  Set.range (fun g : SymmetricGroup n => c ∘ (g⁻¹ : SymmetricGroup n))

instance coloringOrbitFinite {n : ℕ} {I : Type*} (c : Fin n → I) : Finite (ColoringOrbit c) :=
  Set.finite_range _

instance coloringOrbitFintype {n : ℕ} {I : Type*} (c : Fin n → I) : Fintype (ColoringOrbit c) :=
  Fintype.ofFinite _

def coloringOrbitIndex {n : ℕ} {I : Type*} (c : Fin n → I) (g : SymmetricGroup n) :
    ColoringOrbit c := ⟨c ∘ (g⁻¹ : SymmetricGroup n), ⟨g, rfl⟩⟩

def coloringOrbitRep {n : ℕ} {I : Type*} (c : Fin n → I) (q : ColoringOrbit c) :
    SymmetricGroup n := q.property.choose

lemma coloringOrbitRep_property {n : ℕ} {I : Type*} (c : Fin n → I) (g : SymmetricGroup n) :
    (coloringOrbitRep c (coloringOrbitIndex c g))⁻¹ * g ∈ fiberSubgroup c := by
  let r := coloringOrbitRep c (coloringOrbitIndex c g)
  have he : c ∘ (r⁻¹ : SymmetricGroup n) = c ∘ (g⁻¹ : SymmetricGroup n) := (coloringOrbitIndex c g).property.choose_spec
  intro x
  have h := congrFun he (g x)
  simpa using h

lemma finrank_le_coloringOrbit {n : ℕ} {I E A : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ρ : Representation ℂ (SymmetricGroup n) E) [ρ.IsIrreducible]
    (f : A →ₗ[ℂ] E) (hf : f ≠ 0) (c : Fin n → I)
    (hstable : ∀ g : fiberSubgroup c, ∀ x : A, ∃ y, ρ g.1 (f x) = f y) :
    finrank ℂ E ≤ Fintype.card (ColoringOrbit c) * finrank ℂ A := by
  apply finrank_le_translates ρ f hf (coloringOrbitRep c) (coloringOrbitIndex c)
  intro g x
  let r := coloringOrbitRep c (coloringOrbitIndex c g)
  obtain ⟨y, hy⟩ := hstable ⟨r⁻¹ * g, coloringOrbitRep_property c g⟩ x
  refine ⟨y, ?_⟩
  rw [← hy, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ColorEntropy
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma coloringOrbit_product {n : ℕ} {I : Type*} (c : Fin n → I) (p : I → ℝ)
    (q : ColoringOrbit c) :
    (∏ x, p (q.1 x)) = ∏ x, p (c x) := by
  obtain ⟨g, hg⟩ := q.property
  rw [← hg]
  exact Equiv.prod_comp g⁻¹ (p ∘ c)

lemma coloringOrbit_card_mul_product_le_one {n : ℕ} {I : Type*} [Fintype I]
    (c : Fin n → I) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (Fintype.card (ColoringOrbit c) : ℝ) * (∏ x, p (c x)) ≤ 1 := by
  classical
  calc
    _ = ∑ q : ColoringOrbit c, ∏ x, p (q.1 x) := by
      simp only [coloringOrbit_product, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ f : Fin n → I, ∏ x, p (f x) := by
      let T := Finset.univ.image (fun q : ColoringOrbit c => q.1)
      have hi : Function.Injective (fun q : ColoringOrbit c => q.1) :=
        fun q r h => Subtype.ext h
      calc
        _ = ∑ f ∈ T, ∏ x, p (f x) := (Finset.sum_image hi.injOn).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f hf hfn => Finset.prod_nonneg (fun x hx => hp (f x)))
    _ = 1 := by rw [← Fintype.sum_pow, hsum, one_pow]

lemma coloringOrbit_card_le_exp {n : ℕ} {I : Type*} [Fintype I]
    (c : Fin n → I) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hc : ∀ x, 0 < p (c x)) :
    (Fintype.card (ColoringOrbit c) : ℝ) ≤ Real.exp (-(∑ x, Real.log (p (c x)))) := by
  have he : (∏ x, p (c x)) = Real.exp (∑ x, Real.log (p (c x))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl (fun x hx => (Real.exp_log (hc x)).symm)
  have h := coloringOrbit_card_mul_product_le_one c p hp hsum
  rw [he] at h
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (∑ x, Real.log (p (c x))))).mp
  simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h

lemma finrank_le_coloring_entropy {n : ℕ} {I E A : Type*} [Fintype I]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ρ : Representation ℂ (SymmetricGroup n) E) [ρ.IsIrreducible]
    (f : A →ₗ[ℂ] E) (hf : f ≠ 0) (c : Fin n → I)
    (hstable : ∀ g : fiberSubgroup c, ∀ x : A, ∃ y, ρ g.1 (f x) = f y)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hc : ∀ x, 0 < p (c x)) :
    (finrank ℂ E : ℝ) ≤ Real.exp (-(∑ x, Real.log (p (c x)))) * finrank ℂ A := by
  have h := finrank_le_coloringOrbit ρ f hf c hstable
  have h' : (finrank ℂ E : ℝ) ≤ (Fintype.card (ColoringOrbit c) : ℝ) * finrank ℂ A := by
    exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_right (coloringOrbit_card_le_exp c p hp hsum hc)
    (Nat.cast_nonneg _))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.InducedCarrier
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma fiberSubgroup_sum_factor {A B I J : Type*} [Finite A] [Finite B]
    (c : A → I) (d : B → J) (g : fiberSubgroup (Sum.map c d)) :
    ∃ a : fiberSubgroup c, ∃ b : fiberSubgroup d, g.1 = a.1.sumCongr b.1 := by
  have hpres : Set.MapsTo g.1 (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro x ⟨a, rfl⟩
    have h := g.property (Sum.inl a)
    cases hx : g.1 (Sum.inl a) with
    | inl a' => exact ⟨a', rfl⟩
    | inr b' => simp [hx] at h
  obtain ⟨⟨a, b⟩, he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hpres
  have hg : g.1 = a.sumCongr b := he.symm
  have ha : a ∈ fiberSubgroup c := by
    intro x
    have h := g.property (Sum.inl x)
    simpa only [hg, Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] using h
  have hb : b ∈ fiberSubgroup d := by
    intro x
    have h := g.property (Sum.inr x)
    simpa only [hg, Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq] using h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hg⟩

def blockEquiv {u v l n : ℕ} (h : u + v + l = n) :
    ((Fin u ⊕ Fin v) ⊕ Fin l) ≃ Fin n :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin l))).trans finSumFinEquiv).trans
    (finCongr h)

lemma blockEmbedding_eq {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    blockEmbedding h a b c = (blockEquiv h).permCongr ((a.sumCongr b).sumCongr c) := rfl

def blockColoring {u v l n : ℕ} {I J : Type*} (h : u + v + l = n)
    (c : Fin u → I) (d : Fin v → J) : Fin n → ((I ⊕ J) ⊕ Unit) :=
  Sum.map (Sum.map c d) (fun _ => ()) ∘ (blockEquiv h).symm

lemma blockColoring_factor {u v l n : ℕ} {I J : Type*} (h : u + v + l = n)
    (c : Fin u → I) (d : Fin v → J) (g : fiberSubgroup (blockColoring h c d)) :
    ∃ a : fiberSubgroup c, ∃ b : fiberSubgroup d, ∃ e : SymmetricGroup l,
      g.1 = blockEmbedding h a.1 b.1 e := by
  let σ := (blockEquiv h).symm.permCongr g.1
  have hσ : σ ∈ fiberSubgroup (Sum.map (Sum.map c d) (fun _ : Fin l => ())) := by
    intro x
    have he := g.property (blockEquiv h x)
    simpa only [blockColoring, Function.comp_apply, Equiv.symm_apply_apply,
      σ, Equiv.permCongr_apply, Equiv.symm_symm] using he
  obtain ⟨ab, e, he⟩ := fiberSubgroup_sum_factor (Sum.map c d) (fun _ : Fin l => ()) ⟨σ, hσ⟩
  obtain ⟨a, b, hab⟩ := fiberSubgroup_sum_factor c d ab
  refine ⟨a, b, e.1, ?_⟩
  have hx := congrArg (blockEquiv h).permCongr he
  apply Equiv.ext
  intro x
  have hh := congrArg (fun t : SymmetricGroup n => t x) hx
  simpa only [σ, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    hab, blockEmbedding_eq] using hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def rowIndex {n : ℕ} (lam : Partition n) (x : Fin n) : Fin (lam.1.colLen 0) :=
  ⟨lam.rowOf x, lam.rowOf_lt x⟩

lemma colOf_lt {n : ℕ} (lam : Partition n) (x : Fin n) : lam.colOf x < lam.1.rowLen 0 :=
  (lam.colOf_lt_rowLen x).trans_le (lam.1.rowLen_anti 0 _ (Nat.zero_le _))

def colIndex {n : ℕ} (lam : Partition n) (x : Fin n) : Fin (lam.1.rowLen 0) :=
  ⟨lam.colOf x, lam.colOf_lt x⟩

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma fiberSubgroup_rowIndex {n : ℕ} (lam : Partition n) :
    fiberSubgroup lam.rowIndex = rowSubgroup lam := by
  ext g
  constructor
  · intro hg x
    exact congrArg Fin.val (hg x)
  · intro hg x
    exact Fin.ext (hg x)

lemma fiberSubgroup_colIndex {n : ℕ} (lam : Partition n) :
    fiberSubgroup lam.colIndex = colSubgroup lam := by
  ext g
  constructor
  · intro hg x
    exact congrArg Fin.val (hg x)
  · intro hg x
    exact Fin.ext (hg x)

def spechtRowVector {n : ℕ} (lam : Partition n) : Specht lam :=
  groupAverage ((spechtRepresentation lam).comp (rowSubgroup lam).subtype) (spechtGenerator lam)

lemma spechtRowVector_invariant {n : ℕ} (lam : Partition n) (a : rowSubgroup lam) :
    spechtRepresentation lam a.1 (spechtRowVector lam) = spechtRowVector lam :=
  groupAverage_invariant ((spechtRepresentation lam).comp (rowSubgroup lam).subtype) a (spechtGenerator lam)

lemma spechtRowVector_at_one {n : ℕ} (lam : Partition n) :
    spechtInclusion lam (spechtRowVector lam) 1 = 1 := by
  classical
  have h (a : rowSubgroup lam) :
      spechtInclusion lam (spechtRepresentation lam a.1 (spechtGenerator lam)) 1 = 1 := by
    change polytabloid lam (a.1⁻¹ * 1) = 1
    calc
      _ = polytabloid lam (1 * (a⁻¹).1) := by simp
      _ = polytabloid lam 1 := polytabloid_right_row lam a⁻¹ 1
      _ = 1 := polytabloid_at_one lam
  have hn : (Fintype.card (rowSubgroup lam) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [spechtRowVector, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    smul_eq_mul, inv_mul_cancel₀ hn]

lemma spechtRowVector_ne_zero {n : ℕ} (lam : Partition n) : spechtRowVector lam ≠ 0 := by
  intro hz
  have h := spechtRowVector_at_one lam
  rw [hz, map_zero, PiLp.zero_apply] at h
  exact zero_ne_one h

lemma complex_tmul_ne_zero {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {x : A} {y : B} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h
  have he := congrArg (fun z => TensorProduct.lid ℂ ℂ (TensorProduct.map f g z)) h
  simp only [TensorProduct.map_tmul, hf, hg, TensorProduct.lid_tmul, one_smul,
    map_zero, one_ne_zero] at he

lemma signedOccurrence_colorCarrier {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (ho : SignedOccurrence h α β γ lam) :
    ∃ f : Specht γ →ₗ[ℂ] Specht lam, f ≠ 0 ∧
      ∀ g : fiberSubgroup (blockColoring h α.rowIndex β.transpose.colIndex),
        ∀ x : Specht γ, ∃ y, spechtRepresentation lam g.1 (f x) = f y := by
  obtain ⟨F, hF, hFint⟩ := ho
  let v := spechtRowVector α ⊗ₜ[ℂ] spechtGenerator β.transpose
  let f := F.comp (TensorProduct.mk ℂ (Specht α ⊗[ℂ] Specht β.transpose) (Specht γ) v)
  refine ⟨f, ?_, ?_⟩
  · intro he
    have hz : f (spechtGenerator γ) = 0 := by rw [he, LinearMap.zero_apply]
    have ht : v ⊗ₜ[ℂ] spechtGenerator γ = 0 := hF (hz.trans (map_zero F).symm)
    exact complex_tmul_ne_zero
      (complex_tmul_ne_zero (spechtRowVector_ne_zero α) (spechtGenerator_ne_zero β.transpose))
      (spechtGenerator_ne_zero γ) ht
  · intro g x
    obtain ⟨a, b, e, he⟩ := blockColoring_factor h α.rowIndex β.transpose.colIndex g
    have ha : a.1 ∈ rowSubgroup α := by rw [← fiberSubgroup_rowIndex]; exact a.property
    have hb : b.1 ∈ colSubgroup β.transpose := by rw [← fiberSubgroup_colIndex]; exact b.property
    refine ⟨complexSign _ b.1 • spechtRepresentation γ e x, ?_⟩
    dsimp only [f, LinearMap.comp_apply, TensorProduct.mk_apply]
    rw [he, ← hFint]
    simp only [TensorProduct.map_tmul,
      v, spechtRowVector_invariant α ⟨a.1, ha⟩, spechtGenerator_column_action β.transpose ⟨b.1, hb⟩,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul, map_smul]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccurrenceDimension
namespace OAI

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

lemma rowOf_lt_colLen {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.rowOf x < lam.1.colLen (lam.colOf x) :=
  YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x).property

def colEquiv {n : ℕ} (lam : Partition n) :
    (Σ j : Fin (lam.1.rowLen 0), Fin (lam.1.colLen j)) ≃ Fin n where
  toFun x := lam.tableau ⟨(x.2.val, x.1.val), YoungDiagram.mem_iff_lt_colLen.mpr x.2.isLt⟩
  invFun x := ⟨⟨lam.colOf x, lam.colOf_lt x⟩, ⟨lam.rowOf x, lam.rowOf_lt_colLen x⟩⟩
  left_inv x := by
    apply Sigma.ext
    · apply Fin.ext
      simp [colOf]
    · apply (Fin.heq_ext_iff (by simp [colOf])).mpr
      simp [rowOf]
  right_inv x := by simp only; exact lam.tableau.apply_symm_apply x

@[simp] lemma colOf_colEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.rowLen 0)) (j : Fin (lam.1.colLen i)) :
    lam.colOf (lam.colEquiv ⟨i, j⟩) = i.val := by simp [colEquiv, colOf]

lemma sum_rowLen {n : ℕ} (lam : Partition n) :
    ∑ i : Fin (lam.1.colLen 0), lam.1.rowLen i = n := by
  simpa using Fintype.card_congr lam.rowEquiv

lemma sum_colLen {n : ℕ} (lam : Partition n) :
    ∑ i : Fin (lam.1.rowLen 0), lam.1.colLen i = n := by
  simpa using Fintype.card_congr lam.colEquiv

lemma rowLen_pos {n : ℕ} (lam : Partition n) (i : Fin (lam.1.colLen 0)) :
    0 < lam.1.rowLen i :=
  YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)

lemma colLen_pos {n : ℕ} (lam : Partition n) (i : Fin (lam.1.rowLen 0)) :
    0 < lam.1.colLen i :=
  YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr i.isLt)

lemma sum_rowOf {n : ℕ} (lam : Partition n) (f : ℕ → ℝ) :
    ∑ x, f (lam.rowOf x) = ∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * f i := by
  rw [← Equiv.sum_comp lam.rowEquiv (fun x => f (lam.rowOf x)), Fintype.sum_sigma]
  simp only [rowOf_rowEquiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma sum_colOf {n : ℕ} (lam : Partition n) (f : ℕ → ℝ) :
    ∑ x, f (lam.colOf x) = ∑ i : Fin (lam.1.rowLen 0), (lam.1.colLen i : ℝ) * f i := by
  rw [← Equiv.sum_comp lam.colEquiv (fun x => f (lam.colOf x)), Fintype.sum_sigma]
  simp only [colOf_colEquiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma partsEntropy_rowLen {n : ℕ} (lam : Partition n) (N : ℝ) :
    partsEntropy N lam.1.rowLens =
      ∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i) := by
  rw [partsEntropy, YoungDiagram.rowLens, List.map_map,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  exact (Fin.sum_univ_eq_sum_range (fun i => (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i)) _).symm

def signedColorProbability {u v : ℕ} (α : Partition u) (β : Partition v) (l n : ℕ) :
    ((Fin (α.1.colLen 0) ⊕ Fin (β.transpose.1.rowLen 0)) ⊕ Unit) → ℝ :=
  Sum.elim (Sum.elim (fun i => (α.1.rowLen i : ℝ) / n)
    (fun j => (β.transpose.1.colLen j : ℝ) / n)) (fun _ => (l : ℝ) / n)

lemma signedColorProbability_nonneg {u v : ℕ} (α : Partition u) (β : Partition v) (l n : ℕ) (i) :
    0 ≤ signedColorProbability α β l n i := by
  rcases i with ((i | j) | k) <;> dsimp [signedColorProbability] <;> positivity

lemma signedColorProbability_sum {u v l n : ℕ} (h : u + v + l = n) (hn : 0 < n)
    (α : Partition u) (β : Partition v) :
    ∑ i, signedColorProbability α β l n i = 1 := by
  simp only [signedColorProbability, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique, ← Finset.sum_div, ← Nat.cast_sum, Partition.sum_rowLen, Partition.sum_colLen,
    ← add_div, ← Nat.cast_add, h]
  exact div_self (by exact_mod_cast hn.ne')

lemma signedColorProbability_used_pos {u v l n : ℕ} (h : u + v + l = n) (hn : 0 < n)
    (α : Partition u) (β : Partition v) (x : Fin n) :
    0 < signedColorProbability α β l n (blockColoring h α.rowIndex β.transpose.colIndex x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hx : (blockEquiv h).symm x with ((a | b) | c)
  · change 0 < Sum.elim _ _ (Sum.map _ _ ((blockEquiv h).symm x))
    rw [hx]
    exact div_pos (by exact_mod_cast α.rowLen_pos (α.rowIndex a)) hn'
  · change 0 < Sum.elim _ _ (Sum.map _ _ ((blockEquiv h).symm x))
    rw [hx]
    exact div_pos (by exact_mod_cast β.transpose.colLen_pos (β.transpose.colIndex b)) hn'
  · change 0 < Sum.elim _ _ (Sum.map _ _ ((blockEquiv h).symm x))
    rw [hx]
    exact div_pos (by exact_mod_cast c.pos) hn'

lemma signedColorProbability_entropy {u v l n : ℕ} (h : u + v + l = n)
    (α : Partition u) (β : Partition v) :
    -(∑ x, Real.log (signedColorProbability α β l n
      (blockColoring h α.rowIndex β.transpose.colIndex x))) =
      partsEntropy n α.1.rowLens + partsEntropy n β.1.rowLens +
        (l : ℝ) * Real.log ((n : ℝ) / l) := by
  rw [← Equiv.sum_comp (blockEquiv h)
    (fun x => Real.log (signedColorProbability α β l n (blockColoring h α.rowIndex β.transpose.colIndex x)))]
  simp only [blockColoring, Function.comp_apply, Equiv.symm_apply_apply,
    Fintype.sum_sum_type, Sum.map_inl, Sum.map_inr, signedColorProbability, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Partition.rowIndex, Partition.colIndex]
  rw [α.sum_rowOf (fun i => Real.log ((α.1.rowLen i : ℝ) / n)),
    β.transpose.sum_colOf (fun i => Real.log ((β.transpose.1.colLen i : ℝ) / n))]
  rw [partsEntropy_rowLen, partsEntropy_rowLen]
  dsimp +instances only [Partition.transpose]
  simp only [YoungDiagram.colLen_transpose]
  have hl (a : ℝ) : Real.log (a / n) = -Real.log ((n : ℝ) / a) := by
    rw [← Real.log_inv, inv_div]
  simp only [hl, mul_neg, Finset.sum_neg_distrib, neg_add, neg_neg]
  have hb := Fin.sum_univ_eq_sum_range
    (fun i => (β.1.rowLen i : ℝ) * Real.log ((n : ℝ) / β.1.rowLen i))
  rw [hb, hb, YoungDiagram.rowLen_transpose]

lemma partsEntropy_change_total {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (L : List ℕ) :
    partsEntropy B L = partsEntropy A L + (L.sum : ℝ) * Real.log (B / A) := by
  induction L with
  | nil => simp [partsEntropy]
  | cons a L ih =>
    have ht : (a : ℝ) * Real.log (B / a) =
        (a : ℝ) * Real.log (A / a) + (a : ℝ) * Real.log (B / A) := by
      by_cases ha : a = 0
      · simp [ha]
      · have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
        rw [Real.log_div hB.ne' ha', Real.log_div hA.ne' ha', Real.log_div hB.ne' hA.ne']
        ring
    simp only [partsEntropy, List.map_cons, List.sum_cons] at ih ⊢
    rw [ht, ih, Nat.cast_add]
    ring

lemma partsEntropy_partition_empty (lam : Partition 0) (A : ℝ) :
    partsEntropy A lam.1.rowLens = 0 := by
  have hz : lam.1.rowLens = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro a ha
    exact (not_lt_of_ge (row_part_le_size lam ha)) (lam.1.pos_of_mem_rowLens a ha))
  simp [partsEntropy, hz]

lemma signedEntropy_change_total {u v n : ℕ} (hn : 0 < n)
    (α : Partition u) (β : Partition v) :
    partsEntropy n α.1.rowLens + partsEntropy n β.1.rowLens =
      signedEntropy α β + ((u : ℝ) + v) * Real.log ((n : ℝ) / ((u : ℝ) + v)) := by
  by_cases hz : u + v = 0
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u; subst v
    simp only [partsEntropy_partition_empty, signedEntropy_empty, Nat.cast_zero,
      zero_mul, add_zero]
  · have hp : (0 : ℝ) < (u : ℝ) + v := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    rw [partsEntropy_change_total (B := (n : ℝ)) hp (by exact_mod_cast hn) α.1.rowLens,
      partsEntropy_change_total (B := (n : ℝ)) hp (by exact_mod_cast hn) β.1.rowLens]
    have he : signedEntropy α β =
        partsEntropy ((u : ℝ) + v) α.1.rowLens + partsEntropy ((u : ℝ) + v) β.1.rowLens := by
      simp only [signedEntropy, partsEntropy, List.map_append, List.sum_append]
    rw [he, partition_rowLens_sum, partition_rowLens_sum]
    ring

lemma split_entropy_le_remainder {N L n : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hn : 0 < n) (hs : N + L = n) :
    N * Real.log (n / N) ≤ L := by
  rcases eq_or_lt_of_le hN with hz | hp
  · simp only [← hz, zero_mul]; exact hL
  · have ht := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hn hp)) hp.le
    have hcan : N * (n / N - 1) = L := by field_simp; nlinarith
    exact ht.trans_eq hcan

lemma signedOccurrence_dimension {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (hn : 0 < n) (ho : SignedOccurrence h α β γ lam) :
    (spechtDimension lam : ℝ) ≤
      Real.exp (signedEntropy α β + (l : ℝ) * Real.log ((n : ℝ) / l) + l) *
        spechtDimension γ := by
  classical
  let _ := specht_irreducible lam
  obtain ⟨f, hf, hstable⟩ := signedOccurrence_colorCarrier ho
  have he := finrank_le_coloring_entropy (spechtRepresentation lam) f hf
    (blockColoring h α.rowIndex β.transpose.colIndex) hstable
    (signedColorProbability α β l n) (signedColorProbability_nonneg α β l n)
    (signedColorProbability_sum h hn α β) (signedColorProbability_used_pos h hn α β)
  rw [signedColorProbability_entropy h α β, signedEntropy_change_total hn α β] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (spechtDimension γ))
  apply Real.exp_le_exp.mpr
  have hs : (u : ℝ) + v + l = (n : ℝ) := by exact_mod_cast h
  have ht := split_entropy_le_remainder (N := (u : ℝ) + v) (by positivity)
    (Nat.cast_nonneg l) (by exact_mod_cast hn) hs
  linarith

lemma spechtDimension_le_factorial {n : ℕ} (lam : Partition n) :
    spechtDimension lam ≤ n.factorial := by
  classical
  have hb := Submodule.finrank_le (spechtSubrepresentation lam).toSubmodule
  change spechtDimension lam ≤ finrank ℂ (EuclideanSpace ℂ (SymmetricGroup n)) at hb
  simpa only [finrank_euclideanSpace, SymmetricGroup, Fintype.card_perm, Fintype.card_fin] using hb

lemma spechtDimension_le_exp_size_log_size {n : ℕ} (lam : Partition n) :
    (spechtDimension lam : ℝ) ≤ Real.exp ((n : ℝ) * Real.log n) := by
  by_cases hn : n = 0
  · subst n
    simp only [spechtDimension_empty, Nat.cast_one, Nat.cast_zero, zero_mul, Real.exp_zero, le_refl]
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    exact_mod_cast (spechtDimension_le_factorial lam).trans (Nat.factorial_le_pow n)

lemma signedOccurrence_log_dimension {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (hn : 0 < n) (ho : SignedOccurrence h α β γ lam) :
    Real.log (spechtDimension lam : ℝ) ≤ signedEntropy α β + (l : ℝ) * Real.log n + l := by
  have hb := signedOccurrence_dimension hn ho
  have hc := mul_le_mul_of_nonneg_left (spechtDimension_le_exp_size_log_size γ)
    (Real.exp_pos (signedEntropy α β + (l : ℝ) * Real.log ((n : ℝ) / l) + l)).le
  have he : signedEntropy α β + (l : ℝ) * Real.log ((n : ℝ) / l) + l +
      (l : ℝ) * Real.log l = signedEntropy α β + (l : ℝ) * Real.log n + l := by
    by_cases hl : l = 0
    · simp [hl]
    · rw [Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hl)]
      ring
  have ht := hb.trans hc
  rw [← Real.exp_add, he] at ht
  exact (Real.log_le_iff_le_exp (by exact_mod_cast spechtDimension_pos lam)).mpr ht

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

@[simp] lemma finiteRegularRepresentation_apply (g : G) (f : EuclideanSpace ℂ G) (h : G) :
    finiteRegularRepresentation g f h = f (g⁻¹ * h) := rfl

omit [FiniteDimensional ℂ E] in
@[simp] lemma coefficientAction_apply (ρ : Representation ℂ G E) (f : G → ℂ) (x : E) :
    coefficientAction ρ f x = ∑ g, f g • ρ g x := by
  simp [coefficientAction]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges2
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {G : Type*} [Fintype G] [Group G]

lemma finiteRegularRepresentation_norm (g : G) (x : EuclideanSpace ℂ G) :
    ‖finiteRegularRepresentation g x‖ = ‖x‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)).norm_map x

lemma finiteRegularRepresentation_single (g h : G) (z : ℂ) :
    finiteRegularRepresentation g (EuclideanSpace.single h z) =
      EuclideanSpace.single (g * h) z := by
  ext k
  simp only [finiteRegularRepresentation_apply, PiLp.single_apply]
  rw [show g⁻¹ * k = h ↔ k = g * h by exact inv_mul_eq_iff_eq_mul]

lemma invariant_projection_diagonal (S : Subrepresentation (finiteRegularRepresentation (G := G)))
    (g : G) :
    S.toSubmodule.starProjection (EuclideanSpace.single g 1) g =
      S.toSubmodule.starProjection (EuclideanSpace.single 1 1) 1 := by
  have h := congrArg (fun f : EuclideanSpace ℂ G => f g)
    (invariant_starProjection_intertwines finiteRegularRepresentation
      finiteRegularRepresentation_norm S g (EuclideanSpace.single 1 1))
  simpa only [finiteRegularRepresentation_single, mul_one,
    finiteRegularRepresentation_apply, inv_mul_cancel] using h

lemma invariant_projection_diagonal_trace
    (S : Subrepresentation (finiteRegularRepresentation (G := G))) :
    (Fintype.card G : ℂ) *
      S.toSubmodule.starProjection (EuclideanSpace.single 1 1) 1 =
        (finrank ℂ S.toSubmodule : ℂ) := by
  have htrace := (LinearMap.IsIdempotentElem.isProj_range _
    (S.toSubmodule.isSymmetricProjection_starProjection).isIdempotentElem).trace
  rw [Submodule.range_starProjection] at htrace
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)] at htrace
  simpa only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    EuclideanSpace.inner_single_left, map_one, one_mul, invariant_projection_diagonal,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using htrace

theorem invariant_evaluation_dimension_bound
    (S : Subrepresentation (finiteRegularRepresentation (G := G)))
    (f : EuclideanSpace ℂ G) (hf : f ∈ S.toSubmodule) :
    (Fintype.card G : ℝ) * ‖f 1‖ ^ 2 ≤ (finrank ℂ S.toSubmodule : ℝ) * ‖f‖ ^ 2 := by
  let p := S.toSubmodule.starProjection
  let v := p (EuclideanSpace.single 1 1)
  have hp : p f = f := S.toSubmodule.starProjection_eq_self_iff.mpr hf
  have hv : p v = v := S.toSubmodule.starProjection_eq_self_iff.mpr
    (S.toSubmodule.starProjection_apply_mem _)
  have he : inner ℂ v f = f 1 := by
    change inner ℂ (p (EuclideanSpace.single 1 1)) f = _
    rw [S.toSubmodule.inner_starProjection_left_eq_right, hp,
      EuclideanSpace.inner_single_left, map_one, one_mul]
  have hvnorm : ‖v‖ ^ 2 = (v 1).re := by
    calc
      ‖v‖ ^ 2 = (inner ℂ v v).re := by simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
      _ = (v 1).re := ?_
    · change (inner ℂ (p (EuclideanSpace.single 1 1)) v).re = _
      rw [S.toSubmodule.inner_starProjection_left_eq_right, hv,
        EuclideanSpace.inner_single_left, map_one, one_mul]
  have ht : (Fintype.card G : ℝ) * ‖v‖ ^ 2 = (finrank ℂ S.toSubmodule : ℝ) := by
    rw [hvnorm]
    have h := congrArg Complex.re (invariant_projection_diagonal_trace S)
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using h
  have hb := pow_le_pow_left₀ (norm_nonneg (inner ℂ v f))
    (norm_inner_le_norm (𝕜 := ℂ) v f) 2
  rw [he, mul_pow] at hb
  calc
    _ ≤ (Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by rw [← mul_assoc, ht]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma column_row_product_injective {n : ℕ} (lam : Partition n) :
    Function.Injective (fun p : colSubgroup lam × rowSubgroup lam => p.1.1 * p.2.1) := by
  rintro ⟨c, a⟩ ⟨c', a'⟩ h
  have he : c'.1⁻¹ * c.1 = a'.1 * a.1⁻¹ := by
    have := congrArg (fun g => c'.1⁻¹ * g * a.1⁻¹) h
    simpa [mul_assoc] using this
  have hz : c'.1⁻¹ * c.1 = 1 := mem_row_col_eq_one lam
    (he ▸ (rowSubgroup lam).mul_mem a'.property ((rowSubgroup lam).inv_mem a.property))
    ((colSubgroup lam).mul_mem ((colSubgroup lam).inv_mem c'.property) c.property)
  have hc : c = c' := Subtype.ext (inv_mul_eq_one.mp hz).symm
  subst c'
  have ha : a = a' := Subtype.ext (mul_left_cancel h)
  subst a'
  rfl

lemma polytabloid_norm_sq {n : ℕ} (lam : Partition n) :
    ‖polytabloid lam‖ ^ 2 =
      (Fintype.card (colSubgroup lam) : ℝ) * Fintype.card (rowSubgroup lam) := by
  let v := fun p : colSubgroup lam × rowSubgroup lam =>
    EuclideanSpace.single (p.1.1 * p.2.1) (1 : ℂ)
  have hv : Orthonormal ℂ v := by
    have hcomp := (EuclideanSpace.basisFun (SymmetricGroup n) ℂ).orthonormal.comp
      (fun p : colSubgroup lam × rowSubgroup lam => p.1.1 * p.2.1)
      (column_row_product_injective lam)
    have hfun : v = (⇑(EuclideanSpace.basisFun (SymmetricGroup n) ℂ)) ∘
        (fun p : colSubgroup lam × rowSubgroup lam => p.1.1 * p.2.1) := by
      funext pair
      simp [v, EuclideanSpace.basisFun_apply]
    rw [hfun]
    exact hcomp
  have he : polytabloid lam = ∑ p, complexSign n p.1.1 • v p := by
    simp only [polytabloid, Fintype.sum_prod_type, v]
    rfl
  have hh := hv.inner_sum (fun p => complexSign n p.1.1) (fun p => complexSign n p.1.1)
    Finset.univ
  rw [← he] at hh
  have hsign (p : colSubgroup lam × rowSubgroup lam) :
      starRingEnd ℂ (complexSign n p.1.1) * complexSign n p.1.1 = 1 := by
    simp only [complexSign, MonoidHom.coe_mk, OneHom.coe_mk, map_intCast]
    exact complexSign_mul_self p.1.1
  simp only [hsign, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
    mul_one, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hh
  exact_mod_cast hh

theorem spechtDimension_row_column_lower {n : ℕ} (lam : Partition n) :
    (Nat.factorial n : ℝ) ≤ (spechtDimension lam : ℝ) *
      (Fintype.card (colSubgroup lam) : ℝ) * Fintype.card (rowSubgroup lam) := by
  have hb := invariant_evaluation_dimension_bound
    (show Subrepresentation (finiteRegularRepresentation (G := SymmetricGroup n)) from
      spechtSubrepresentation lam) (polytabloid lam) (spechtGenerator lam).property
  rw [polytabloid_at_one, norm_one, one_pow, mul_one, polytabloid_norm_sq] at hb
  change (Fintype.card (SymmetricGroup n) : ℝ) ≤
    (spechtDimension lam : ℝ) *
      ((Fintype.card (colSubgroup lam) : ℝ) * (Fintype.card (rowSubgroup lam) : ℝ)) at hb
  simpa only [SymmetricGroup, Fintype.card_perm, Fintype.card_fin, mul_assoc] using hb

def fiberPermEquiv {A I : Type*} (c : A → I) :
    fiberSubgroup c ≃ (∀ i, Equiv.Perm {x : A // c x = i}) where
  toFun g i := g.1.subtypeEquiv (fun x => by rw [g.property x])
  invFun σ := ⟨(Equiv.sigmaFiberEquiv c).permCongr (Equiv.sigmaCongrRight σ), by
    intro x
    exact (σ (c x) ⟨x, rfl⟩).property⟩
  left_inv g := by
    apply Subtype.ext
    ext x
    rfl
  right_inv σ := by
    funext i
    apply Equiv.ext
    rintro ⟨x,hx⟩
    apply Subtype.ext
    subst i
    rfl

lemma card_fiberSubgroup {A I : Type*} [Fintype A] [Fintype I] (c : A → I) :
    Fintype.card (fiberSubgroup c) = ∏ i, (Fintype.card {x : A // c x = i}).factorial := by
  rw [Fintype.card_congr (fiberPermEquiv c), Fintype.card_pi]
  exact Finset.prod_congr rfl (fun i _ => Fintype.card_perm)

lemma fiber_product_injective {A I J : Type*} (c : A → I) (d : A → J)
    (h : Function.Injective (fun x => (c x, d x))) :
    Function.Injective (fun p : fiberSubgroup c × fiberSubgroup d => p.1.1 * p.2.1) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ hab
  have he : a'.1⁻¹ * a.1 = b'.1 * b.1⁻¹ := by
    have := congrArg (fun g => a'.1⁻¹ * g * b.1⁻¹) hab
    simpa [mul_assoc] using this
  have hf : a'.1⁻¹ * a.1 = 1 := by
    have hc := (fiberSubgroup c).mul_mem ((fiberSubgroup c).inv_mem a'.property) a.property
    have hd : a'.1⁻¹ * a.1 ∈ fiberSubgroup d :=
      he ▸ (fiberSubgroup d).mul_mem b'.property ((fiberSubgroup d).inv_mem b.property)
    ext x
    exact h (Prod.ext (hc x) (hd x))
  have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp hf).symm
  subst a'
  have hb : b = b' := Subtype.ext (mul_left_cancel hab)
  subst b'
  rfl

lemma card_fiber_product_le {A I J : Type*} [Fintype A]
    (c : A → I) (d : A → J) (h : Function.Injective (fun x => (c x,d x))) :
    Fintype.card (fiberSubgroup c) * Fintype.card (fiberSubgroup d) ≤
      (Fintype.card A).factorial := by
  simpa only [Fintype.card_prod, Fintype.card_perm] using
    Fintype.card_le_of_injective _ (fiber_product_injective c d h)

lemma rowIndex_fiber_card {n : ℕ} (lam : Partition n) (i : Fin (lam.1.colLen 0)) :
    Fintype.card {x : Fin n // lam.rowIndex x = i} = lam.1.rowLen i := by
  let e : {x : Fin n // lam.rowIndex x = i} ≃ Fin (lam.1.rowLen i) := {
    toFun := fun x => ⟨lam.colOf x.1, by
      have hr : lam.rowOf x.1 = i := congrArg Fin.val x.property
      rw [← hr]
      exact lam.colOf_lt_rowLen x.1⟩
    invFun := fun j => ⟨lam.tableau ⟨(i,j.1), YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩,
      by apply Fin.ext; simp [Partition.rowIndex, Partition.rowOf]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply lam.tableau.symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext (congrArg Fin.val x.property).symm rfl
    right_inv := by
      intro j
      apply Fin.ext
      simp [Partition.colOf] }
  simpa using Fintype.card_congr e

lemma colIndex_fiber_card {n : ℕ} (lam : Partition n) (j : Fin (lam.1.rowLen 0)) :
    Fintype.card {x : Fin n // lam.colIndex x = j} = lam.1.colLen j := by
  let e : {x : Fin n // lam.colIndex x = j} ≃ Fin (lam.1.colLen j) := {
    toFun := fun x => ⟨lam.rowOf x.1, by
      have hc : lam.colOf x.1 = j := congrArg Fin.val x.property
      rw [← hc]
      exact YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x.1).property⟩
    invFun := fun i => ⟨lam.tableau ⟨(i.1,j), YoungDiagram.mem_iff_lt_colLen.mpr i.2⟩,
      by apply Fin.ext; simp [Partition.colIndex, Partition.colOf]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply lam.tableau.symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext rfl (congrArg Fin.val x.property).symm
    right_inv := by
      intro i
      apply Fin.ext
      simp [Partition.rowOf] }
  simpa using Fintype.card_congr e

lemma card_rowSubgroup {n : ℕ} (lam : Partition n) :
    Fintype.card (rowSubgroup lam) = ∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial := by
  let e : rowSubgroup lam ≃ (∀ i : Fin (lam.1.colLen 0), Equiv.Perm {x : Fin n // lam.rowIndex x = i}) :=
    (Equiv.subtypeEquivRight (fun g => by rw [fiberSubgroup_rowIndex])).trans
      (fiberPermEquiv lam.rowIndex)
  calc
    _ = Fintype.card (∀ i : Fin (lam.1.colLen 0), Equiv.Perm {x : Fin n // lam.rowIndex x = i}) :=
      Fintype.card_congr e
    _ = _ := by
      rw [Fintype.card_pi]
      exact Finset.prod_congr rfl (fun i _ => (Fintype.card_perm).trans
        (congrArg Nat.factorial (rowIndex_fiber_card lam i)))

lemma card_colSubgroup {n : ℕ} (lam : Partition n) :
    Fintype.card (colSubgroup lam) = ∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial := by
  let e : colSubgroup lam ≃ (∀ j : Fin (lam.1.rowLen 0), Equiv.Perm {x : Fin n // lam.colIndex x = j}) :=
    (Equiv.subtypeEquivRight (fun g => by rw [fiberSubgroup_colIndex])).trans
      (fiberPermEquiv lam.colIndex)
  calc
    _ = Fintype.card (∀ j : Fin (lam.1.rowLen 0), Equiv.Perm {x : Fin n // lam.colIndex x = j}) :=
      Fintype.card_congr e
    _ = _ := by
      rw [Fintype.card_pi]
      exact Finset.prod_congr rfl (fun j _ => (Fintype.card_perm).trans
        (congrArg Nat.factorial (colIndex_fiber_card lam j)))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma factorial_fiber_pair_bound {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
    (c : A → I) (d : A → J) (h : Function.Injective (fun x => (c x,d x))) :
    (∏ i, (Fintype.card {x : A // c x = i}).factorial) *
      (∏ j, (Fintype.card {x : A // d x = j}).factorial) ≤ (Fintype.card A).factorial := by
  rw [← card_fiberSubgroup c, ← card_fiberSubgroup d]
  exact card_fiber_product_le c d h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
variable (c : A → I) (d : A → J) (i₀ : I)
variable (hinj : Function.Injective (fun x => (c x,d x)))
variable (hfull : ∀ j, ∃ x, c x = i₀ ∧ d x = j)

omit [Fintype I] in
lemma row_removed_same_fiber (i : I) (hi : i ≠ i₀) :
    Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i} =
      Fintype.card {x : A // c x = i} := by
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨x.1.1, x.2⟩
    invFun := fun x => ⟨⟨x.1, by simpa only [x.2] using hi⟩, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

omit [Fintype I] in
lemma row_removed_top_empty :
    Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i₀} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun x => x.1.2 x.2⟩

lemma row_removal_factorial_product :
    (∏ i, (Fintype.card {x : A // c x = i}).factorial) =
      (Fintype.card {x : A // c x = i₀}).factorial *
        (∏ i, (Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i}).factorial) := by
  classical
  rw [← Finset.mul_prod_erase (s := Finset.univ) (a := i₀) _ (Finset.mem_univ i₀)]
  congr 1
  rw [← Finset.mul_prod_erase (s := Finset.univ) (a := i₀) _ (Finset.mem_univ i₀),
    row_removed_top_empty, Nat.factorial_zero, one_mul]
  exact Finset.prod_congr rfl (fun i hi => (congrArg Nat.factorial
    (row_removed_same_fiber c i₀ i (Finset.mem_erase.mp hi).1)).symm)

include hinj hfull

omit [Fintype I] [Fintype J] in
lemma col_fiber_removal (j : J) :
    Fintype.card {x : A // d x = j} =
      Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j} + 1 := by
  let P : {x : A // d x = j} → Prop := fun x => c x.1 = i₀
  have hP : Fintype.card {x : {x : A // d x = j} // P x} = 1 := by
    obtain ⟨a, ha, hd⟩ := hfull j
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨⟨a, hd⟩, ha⟩, ?_⟩
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact hinj (Prod.ext (x.2.trans ha.symm) (x.1.2.trans hd.symm))
  have hPc : Fintype.card {x : {x : A // d x = j} // ¬ P x} =
      Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j} := by
    apply Fintype.card_congr
    exact {
      toFun := fun x => ⟨⟨x.1.1,x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1,x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have ht := Fintype.card_subtype_compl P
  rw [hP, hPc] at ht
  have hp : 0 < Fintype.card {x : A // d x = j} := by
    obtain ⟨x, _, hx⟩ := hfull j
    exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  omega

omit [Fintype I] in
lemma col_removal_factorial_product :
    (∏ j, (Fintype.card {x : A // d x = j}).factorial) =
      (∏ j, (Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j}).factorial) *
        (∏ j, Fintype.card {x : A // d x = j}) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [col_fiber_removal c d i₀ hinj hfull, Nat.factorial_succ]
  exact mul_comm _ _

theorem factorial_product_remove_full_row :
    (∏ i, (Fintype.card {x : A // c x = i}).factorial) *
      (∏ j, (Fintype.card {x : A // d x = j}).factorial) ≤
    (Fintype.card {x : A // c x = i₀}).factorial *
      (Fintype.card {x : A // c x ≠ i₀}).factorial *
        ∏ j, Fintype.card {x : A // d x = j} := by
  rw [row_removal_factorial_product c i₀, col_removal_factorial_product c d i₀ hinj hfull]
  have hb := factorial_fiber_pair_bound
    (fun x : {a : A // c a ≠ i₀} => c x.1) (fun x => d x.1)
    (fun x y h => Subtype.ext (hinj h))
  calc
    _ = (Fintype.card {x : A // c x = i₀}).factorial *
      ((∏ i, (Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i}).factorial) *
       (∏ j, (Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j}).factorial)) *
       (∏ j, Fintype.card {x : A // d x = j}) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := Real.pow_div_factorial_le_exp (n : ℝ) hn'.le n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n / n.factorial) hh
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
  linarith

lemma log_factorial_upper {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    have hnp : (0 : ℝ) < n + 1 := by positivity
    have hh := Real.log_le_sub_one_of_pos (div_pos hp hnp)
    rw [Real.log_div hp.ne' hnp.ne'] at hh
    have hmul := mul_le_mul_of_nonneg_left hh hnp.le
    have hdiv : ((n : ℝ) + 1) * ((n : ℝ) / (n + 1) - 1) = -1 := by
      field_simp
      ring
    rw [hdiv] at hmul
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

lemma log_le_quarter_add_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 4 + 1 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < x / 4)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have hp : 4 ≤ Real.exp 2 := by
      have h₁ : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h₂ : (2 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by simpa using pow_le_pow_left₀ (by norm_num) h₁ 2
      norm_num [← Real.exp_nat_mul] at h₂ ⊢; exact h₂
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr hp
  linarith

lemma Partition.rowColIndex_injective {n : ℕ} (lam : Partition n) :
    Function.Injective (fun x => (lam.rowIndex x, lam.colIndex x)) := by
  intro x y h
  apply lam.tableau.symm.injective
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)

lemma row_column_cell_sum_le {n : ℕ} (lam : Partition n) :
    (∑ x : Fin n, (lam.1.rowLen (lam.rowOf x) : ℝ) * (lam.1.colLen (lam.colOf x) : ℝ)) ≤
      (n : ℝ) ^ 2 := by
  let f : Fin (lam.1.colLen 0) × Fin (lam.1.rowLen 0) → ℝ :=
    fun x => (lam.1.rowLen x.1 : ℝ) * (lam.1.colLen x.2 : ℝ)
  calc
    _ = ∑ x ∈ Finset.univ.image (fun x => (lam.rowIndex x, lam.colIndex x)), f x := by
      rw [Finset.sum_image (fun x _ y _ h => lam.rowColIndex_injective h)]
      rfl
    _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intros; exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = (n : ℝ) ^ 2 := by
      rw [Fintype.sum_prod_type]
      simp only [f, ← Finset.mul_sum]
      rw [← Nat.cast_sum, lam.sum_colLen, ← Finset.sum_mul, ← Nat.cast_sum, lam.sum_rowLen]
      ring

lemma row_column_entropy_sum_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i)) +
    (∑ j : Fin (lam.1.rowLen 0), (lam.1.colLen j : ℝ) * Real.log (lam.1.colLen j)) ≤
      (n : ℝ) * Real.log n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hr (x : Fin n) : (0 : ℝ) < lam.1.rowLen (lam.rowOf x) := by
    exact_mod_cast lam.rowLen_pos (lam.rowIndex x)
  have hc (x : Fin n) : (0 : ℝ) < lam.1.colLen (lam.colOf x) := by
    exact_mod_cast lam.colLen_pos (lam.colIndex x)
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun x _ => Real.log_le_sub_one_of_pos (div_pos (mul_pos (hr x) (hc x)) hp))
  simp_rw [Real.log_div (mul_pos (hr _) (hc _)).ne' hp.ne',
    Real.log_mul (hr _).ne' (hc _).ne'] at hb
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, lam.sum_rowOf (fun i => Real.log (lam.1.rowLen i : ℝ)),
    lam.sum_colOf (fun j => Real.log (lam.1.colLen j : ℝ))] at hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hb
  have hsum := div_le_div_of_nonneg_right (row_column_cell_sum_le lam) hp.le
  have he : (n : ℝ) ^ 2 / n = n := by field_simp
  rw [he] at hsum
  linarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges3
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma spechtDimension_positive {n : ℕ} (lam : Partition n) : (0 : ℝ) < spechtDimension lam := by
  exact_mod_cast spechtDimension_pos lam

lemma spechtDimension_factorial_lower {n : ℕ} (lam : Partition n) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      ((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ) := by
  have hb := spechtDimension_row_column_lower lam
  rw [card_rowSubgroup, card_colSubgroup] at hb
  calc
    _ ≤ _ := hb
    _ = _ := by ring

theorem specht_log_dimension_small_axes {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (n : ℝ) / 2 - 2 * ((lam.1.rowLen 0 : ℝ) + lam.1.colLen 0) ≤
      Real.log (spechtDimension lam : ℝ) := by
  have hD := spechtDimension_positive lam
  have hdim := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial)
    (spechtDimension_factorial_lower lam)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul
    (spechtDimension_positive lam).ne' (by positivity), Nat.cast_prod, Nat.cast_prod,
    Real.log_prod (by intros; positivity), Real.log_prod (by intros; positivity)] at hdim
  have hrow := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.colLen 0))))
    (fun i _ => log_factorial_upper (lam.rowLen_pos i))
  have hcol := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.rowLen 0))))
    (fun j _ => log_factorial_upper (lam.colLen_pos j))
  have hrlog := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.colLen 0))))
    (fun i _ => log_le_quarter_add_one (x := (lam.1.rowLen i : ℝ)) (by exact_mod_cast lam.rowLen_pos i))
  have hclog := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.rowLen 0))))
    (fun j _ => log_le_quarter_add_one (x := (lam.1.colLen j : ℝ)) (by exact_mod_cast lam.colLen_pos j))
  have hrowsum : (∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ)) = n := by
    exact_mod_cast lam.sum_rowLen
  have hcolsum : (∑ j : Fin (lam.1.rowLen 0), (lam.1.colLen j : ℝ)) = n := by
    exact_mod_cast lam.sum_colLen
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hrowsum,
    hcolsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    at hrow hcol hrlog hclog
  linarith [row_column_entropy_sum_le lam hn, log_factorial_lower n]

lemma Partition.firstRow_pos {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    0 < lam.1.rowLen 0 :=
  lt_of_le_of_lt (Nat.zero_le _) (lam.colOf_lt ⟨0, hn⟩)

lemma Partition.firstCol_pos {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    0 < lam.1.colLen 0 :=
  lt_of_le_of_lt (Nat.zero_le _) (lam.rowOf_lt ⟨0, hn⟩)

lemma Partition.firstRow_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    lam.1.rowLen 0 ≤ n := by
  let i : Fin (lam.1.colLen 0) := ⟨0, lam.firstCol_pos hn⟩
  calc
    _ ≤ ∑ j : Fin (lam.1.colLen 0), lam.1.rowLen j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = _ := lam.sum_rowLen

lemma factorial_product_remove_first_row {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial) *
      (∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial) ≤
      (lam.1.rowLen 0).factorial * (n - lam.1.rowLen 0).factorial *
        ∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j := by
  let i₀ : Fin (lam.1.colLen 0) := ⟨0, lam.firstCol_pos hn⟩
  have hfull : ∀ j : Fin (lam.1.rowLen 0), ∃ x, lam.rowIndex x = i₀ ∧ lam.colIndex x = j := by
    intro j
    refine ⟨lam.tableau ⟨(0,j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, ?_, ?_⟩
    · apply Fin.ext; simp [Partition.rowIndex, Partition.rowOf, i₀]
    · apply Fin.ext; simp [Partition.colIndex, Partition.colOf]
  have hopen : Fintype.card {x : Fin n // lam.rowIndex x ≠ i₀} = n - lam.1.rowLen 0 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rowIndex_fiber_card]
  have hb := factorial_product_remove_full_row lam.rowIndex lam.colIndex i₀
    lam.rowColIndex_injective hfull
  have hrn (i : Fin (lam.1.colLen 0)) : Nat.card {x : Fin n // lam.rowIndex x = i} =
      lam.1.rowLen i := Nat.card_eq_fintype_card.trans (rowIndex_fiber_card lam i)
  have hcn (j : Fin (lam.1.rowLen 0)) : Nat.card {x : Fin n // lam.colIndex x = j} =
      lam.1.colLen j := Nat.card_eq_fintype_card.trans (colIndex_fiber_card lam j)
  have hopen' : Nat.card {x : Fin n // lam.rowIndex x ≠ i₀} = n - lam.1.rowLen 0 :=
    Nat.card_eq_fintype_card.trans hopen
  simpa only [← Nat.card_eq_fintype_card, hrn, hcn, hopen'] using hb

lemma column_log_sum_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (∑ j : Fin (lam.1.rowLen 0), Real.log (lam.1.colLen j : ℝ)) ≤
      (lam.1.rowLen 0 : ℝ) * Real.log ((n : ℝ) / lam.1.rowLen 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : (0 : ℝ) < lam.1.rowLen 0 := by exact_mod_cast lam.firstRow_pos hn
  have hp (j : Fin (lam.1.rowLen 0)) : (0 : ℝ) < lam.1.colLen j := by
    exact_mod_cast lam.colLen_pos j
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.rowLen 0))))
    (fun j _ => Real.log_le_sub_one_of_pos (div_pos (hp j) (div_pos hn' hA)))
  simp_rw [Real.log_div (hp _).ne' (div_pos hn' hA).ne'] at hb
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← Nat.cast_sum, lam.sum_colLen] at hb
  have he : (n : ℝ) / (n / lam.1.rowLen 0) = lam.1.rowLen 0 := by field_simp
  rw [he] at hb
  linarith

lemma log_degree_from_first_row {n : ℕ} (lam : Partition n) (hn : 0 < n)
    {D : ℝ} (hD : 0 < D) (hk : 0 < n - lam.1.rowLen 0)
    (hbound : (n.factorial : ℝ) ≤ D *
      ((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ)) :
    ((n - lam.1.rowLen 0 : ℕ) : ℝ) * Real.log ((n : ℝ) / (n - lam.1.rowLen 0 : ℕ)) -
      Real.log (lam.1.rowLen 0 : ℝ) - Real.log ((n - lam.1.rowLen 0 : ℕ) : ℝ) - 2 ≤
        Real.log D := by
  have hnat := factorial_product_remove_first_row lam hn
  have hreal : (((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ)) ≤
      ((lam.1.rowLen 0).factorial : ℝ) * ((n - lam.1.rowLen 0).factorial : ℝ) *
        ((∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j : ℕ) : ℝ) := by exact_mod_cast hnat
  have htot : (n.factorial : ℝ) ≤ D * (((lam.1.rowLen 0).factorial : ℝ) *
      ((n - lam.1.rowLen 0).factorial : ℝ) *
        ((∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j : ℕ) : ℝ)) :=
    hbound.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hreal hD.le)
  have hP : (0 : ℝ) < ((∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => lam.colLen_pos j)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) htot
  rw [Real.log_mul hD.ne' (by positivity), Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (by positivity), Nat.cast_prod,
    Real.log_prod (by intro j _; exact_mod_cast (lam.colLen_pos j).ne')] at hlog
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : (0 : ℝ) < lam.1.rowLen 0 := by exact_mod_cast lam.firstRow_pos hn
  have hK : (0 : ℝ) < (n - lam.1.rowLen 0 : ℕ) := by exact_mod_cast hk
  have hsum : (n : ℝ) = (lam.1.rowLen 0 : ℝ) + (n - lam.1.rowLen 0 : ℕ) := by
    rw [Nat.cast_sub (lam.firstRow_le hn)]; ring
  have hc := column_log_sum_le lam hn
  rw [Real.log_div hN.ne' hA.ne'] at hc
  rw [Real.log_div hN.ne' hK.ne']
  have hsplit := congrArg (fun x : ℝ => x * Real.log n) hsum
  nlinarith [log_factorial_upper (lam.firstRow_pos hn), log_factorial_upper hk,
    log_factorial_lower n]

lemma Partition.firstCol_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    lam.1.colLen 0 ≤ n := by
  simpa only [Partition.transpose, YoungDiagram.rowLen_transpose] using
    lam.transpose.firstRow_le hn

lemma deficit_log_ratio_lower {N A K : ℝ} (hN : 0 < N) (hK : 0 < K)
    (hsum : N = A + K) (hlong : N ≤ 100 * A) :
    (1 : ℝ) / 100 ≤ Real.log (N / K) := by
  have hp : 0 < K / N := div_pos hK hN
  have hb := Real.log_le_sub_one_of_pos hp
  rw [Real.log_div hK.ne' hN.ne'] at hb
  rw [Real.log_div hN.ne' hK.ne']
  have hratio : K / N ≤ 99 / 100 := (div_le_iff₀ hN).mpr (by linarith)
  linarith

lemma log_degree_long_first_row {n : ℕ} (lam : Partition n) (hn : 0 < n)
    {D : ℝ} (hD : 0 < D) (hk : 0 < n - lam.1.rowLen 0)
    (hlong : n ≤ 100 * lam.1.rowLen 0)
    (hbound : (n.factorial : ℝ) ≤ D *
      ((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ)) :
    ((n - lam.1.rowLen 0 : ℕ) : ℝ) / 100 - 2 * Real.log n - 2 ≤ Real.log D := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : (0 : ℝ) < (n - lam.1.rowLen 0 : ℕ) := by exact_mod_cast hk
  have hsum : (n : ℝ) = (lam.1.rowLen 0 : ℝ) + (n - lam.1.rowLen 0 : ℕ) := by
    rw [Nat.cast_sub (lam.firstRow_le hn)]; ring
  have hlong' : (n : ℝ) ≤ 100 * (lam.1.rowLen 0 : ℝ) := by exact_mod_cast hlong
  have hlog := deficit_log_ratio_lower hN hK hsum hlong'
  have hprod := mul_le_mul_of_nonneg_left hlog hK.le
  have hAlog : Real.log (lam.1.rowLen 0 : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast lam.firstRow_pos hn)
      (by exact_mod_cast lam.firstRow_le hn)
  have hKlog : Real.log ((n - lam.1.rowLen 0 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log hK (by exact_mod_cast Nat.sub_le n (lam.1.rowLen 0))
  linarith [log_degree_from_first_row lam hn hD hk hbound]

theorem specht_log_dimension_deficit {n : ℕ} (lam : Partition n) (hn : 0 < n)
    (hcol : lam.1.colLen 0 ≤ n / 2) :
    ((n - lam.1.rowLen 0 : ℕ) : ℝ) / 200 - 2 * Real.log n - 2 ≤
      Real.log (spechtDimension lam : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : ((n - lam.1.rowLen 0 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n (lam.1.rowLen 0)
  have hk0 : (0 : ℝ) ≤ (n - lam.1.rowLen 0 : ℕ) := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlogD : 0 ≤ Real.log (spechtDimension lam : ℝ) :=
    Real.log_nonneg (by exact_mod_cast spechtDimension_pos lam)
  by_cases hk : n - lam.1.rowLen 0 = 0
  · simp only [hk, Nat.cast_zero, zero_div, zero_sub]
    linarith
  have hkp : 0 < n - lam.1.rowLen 0 := Nat.pos_of_ne_zero hk
  by_cases hrow : n ≤ 100 * lam.1.rowLen 0
  · have hb := log_degree_long_first_row lam hn (spechtDimension_positive lam) hkp
      hrow (spechtDimension_factorial_lower lam)
    linarith
  by_cases hcolumn : n ≤ 100 * lam.1.colLen 0
  · have hB : 2 * lam.1.colLen 0 ≤ n := by omega
    have hB' : 2 * (lam.1.colLen 0 : ℝ) ≤ n := by exact_mod_cast hB
    have hk' : 0 < n - lam.1.colLen 0 := by omega
    have hfact : (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
        ((∏ i : Fin (lam.transpose.1.colLen 0), (lam.transpose.1.rowLen i).factorial : ℕ) : ℝ) *
        ((∏ j : Fin (lam.transpose.1.rowLen 0), (lam.transpose.1.colLen j).factorial : ℕ) : ℝ) := by
      have hb := spechtDimension_factorial_lower lam
      rw [Fin.prod_univ_eq_prod_range (fun i => (lam.1.rowLen i).factorial),
        Fin.prod_univ_eq_prod_range (fun i => (lam.1.colLen i).factorial)] at hb
      rw [Fin.prod_univ_eq_prod_range (fun i => (lam.transpose.1.rowLen i).factorial),
        Fin.prod_univ_eq_prod_range (fun i => (lam.transpose.1.colLen i).factorial)]
      simpa only [Partition.transpose, YoungDiagram.colLen_transpose,
        YoungDiagram.rowLen_transpose, mul_assoc, mul_left_comm, mul_comm] using hb
    have hs := log_degree_long_first_row lam.transpose hn (spechtDimension_positive lam)
      (by simpa only [Partition.transpose, YoungDiagram.rowLen_transpose] using hk')
      (by simpa only [Partition.transpose, YoungDiagram.rowLen_transpose] using hcolumn) hfact
    simp only [Partition.transpose, YoungDiagram.rowLen_transpose] at hs
    rw [Nat.cast_sub (lam.firstCol_le hn)] at hs
    linarith
  · have hA : 100 * (lam.1.rowLen 0 : ℝ) < n := by exact_mod_cast Nat.lt_of_not_ge hrow
    have hB : 100 * (lam.1.colLen 0 : ℝ) < n := by exact_mod_cast Nat.lt_of_not_ge hcolumn
    linarith [specht_log_dimension_small_axes lam hn]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
open Filter
open scoped Topology

lemma nonsparse_degree_error {δ : ℝ} (hδ : δ < 1) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d ≥ d₀,
      2 * Real.log ((2 ^ d : ℕ) : ℝ) + 2 ≤
        (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / 400 := by
  let b := (1 - δ) * Real.log 2
  have hb : 0 < b := mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hlin := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
    tendsto_natCast_atTop_atTop).const_mul (2 * Real.log 2)
  have hconst := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb).comp
    tendsto_natCast_atTop_atTop).const_mul 2
  have ht : Tendsto (fun d : ℕ => (2 * (d : ℝ) * Real.log 2 + 2) *
      Real.exp (-b * d)) atTop (𝓝 0) := by
    convert hlin.add hconst using 1
    · funext d
      simp only [Function.comp_apply, Real.rpow_one, Real.rpow_zero, one_mul]
      ring
    · simp
  obtain ⟨D, hD⟩ := eventually_atTop.mp
    (ht.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 400))
  refine ⟨max D 2, le_max_right _ _, ?_⟩
  intro d hd
  have hs := mul_le_mul_of_nonneg_right (hD d ((le_max_left _ _).trans hd))
    (Real.exp_nonneg (b * d))
  have he : Real.exp (-b * d) * Real.exp (b * d) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [mul_assoc, he, mul_one] at hs
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (2 ^ d : ℕ)), nat_two_pow_log]
  have hp : (d : ℝ) * Real.log 2 * (1 - δ) = b * d := by dsimp [b]; ring
  rw [hp]
  linarith

theorem nonsparse_specht_log_dimension {δ : ℝ} (hδ : δ < 1) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      lam.1.colLen 0 ≤ 2 ^ d / 2 →
      ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ≤ ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) →
      (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / 400 ≤ Real.log (spechtDimension lam : ℝ) := by
  obtain ⟨d₀, hd₀, herr⟩ := nonsparse_degree_error hδ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd lam hcol hk
  linarith [herr d hd, specht_log_dimension_deficit lam (by positivity) hcol]

theorem nonsparse_signed_entropy_size {δ : ℝ} (hδ : δ < 1) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      lam.1.colLen 0 ≤ 2 ^ d / 2 →
      ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ≤ ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) →
      ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
        (α : Partition u) (β : Partition v) (γ : Partition l),
        SignedOccurrence h α β γ lam →
        (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / 800 ≤
          signedEntropy α β + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) := by
  obtain ⟨d₀, hd₀, hh⟩ := nonsparse_specht_log_dimension hδ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd lam hcol hk u v l h α β γ ho
  have hdim := hh d hd lam hcol hk
  have hup := signedOccurrence_log_dimension (by positivity) ho
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd₀.trans hd
  have hlog : 1 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by
    rw [nat_two_pow_log]
    nlinarith [Real.log_two_gt_d9]
  have hl := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
  linarith [signedEntropy_nonneg α β]

theorem nonsparse_closing_budget {η κ C δ ξ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hC : 0 ≤ C) (hδ : δ < 1) (hδξ : δ < ξ) :
    ∃ d₀ : ℕ, 4 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      lam.1.colLen 0 ≤ 2 ^ d / 2 →
      ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ≤ ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) →
      ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
        (α : Partition u) (β : Partition v) (γ : Partition l),
        SignedOccurrence h α β γ lam →
        coefficient η (childDepth d) * signedEntropy α β +
          coefficient κ (childDepth d) * l * Real.log ((2 ^ d : ℕ) : ℝ) -
          (l : ℝ) * Real.log (((2 ^ d : ℕ) : ℝ) / l) +
          C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        coefficient η d * signedEntropy α β + remainderBudget κ d l := by
  obtain ⟨D, hD, hclose⟩ := scalar_induction_budget hη hκ
    (by norm_num : (0 : ℝ) < 1 / 800) hC hδξ
  obtain ⟨N, _, hsize⟩ := nonsparse_signed_entropy_size hδ
  refine ⟨max D N, hD.trans (le_max_left _ _), ?_⟩
  intro d hd lam hcol hk u v l h α β γ ho
  apply hclose d ((le_max_left _ _).trans hd) (signedEntropy α β)
    (signedEntropy_nonneg α β) l
  simpa only [one_div, ← div_eq_mul_inv, mul_comm] using
    hsize d ((le_max_right _ _).trans hd) lam hcol hk u v l h α β γ ho

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {Z C R 𝕜 : Type*} [Fintype Z] [Semiring 𝕜]
  {E : Z → Type*} [∀ z, Fintype (E z)]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.IrreducibleClassification
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

def columnStatistic {n : ℕ} (lam : Partition n) : ℕ :=
  ∑ x : Fin n, lam.colOf x

lemma row_column_transversal_statistic {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    columnStatistic mu ≤ columnStatistic lam := by
  unfold columnStatistic
  rw [← Equiv.sum_comp g lam.colOf,
    ← Equiv.sum_comp mu.rowEquiv (fun y => lam.colOf (g y)),
    ← Equiv.sum_comp mu.rowEquiv mu.colOf, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [Partition.colOf_rowEquiv]
  apply Finset.sum_le_sum
  intro i _
  apply fin_injective_sum_lower
  intro j k h
  have he := ht (mu.rowEquiv ⟨i, j⟩) (mu.rowEquiv ⟨i, k⟩) (by simp) h
  exact Sigma.mk.inj_iff.mp (mu.rowEquiv.injective he) |>.2 |> eq_of_heq

lemma row_column_transversal_bound_of_statistic_eq {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (hstat : columnStatistic lam = columnStatistic mu) (x : Fin n) :
    lam.colOf (g x) < mu.1.rowLen (mu.rowOf x) := by
  let f := fun i : Fin (mu.1.colLen 0) => fun j : Fin (mu.1.rowLen i) =>
    lam.colOf (g (mu.rowEquiv ⟨i, j⟩))
  have hf (i : Fin (mu.1.colLen 0)) : Function.Injective (f i) := by
    intro j k h
    have he := ht (mu.rowEquiv ⟨i, j⟩) (mu.rowEquiv ⟨i, k⟩) (by simp) h
    exact Sigma.mk.inj_iff.mp (mu.rowEquiv.injective he) |>.2 |> eq_of_heq
  have hsum : ∑ i, ∑ j, f i j = ∑ i : Fin (mu.1.colLen 0), ∑ j : Fin (mu.1.rowLen i), j.val := by
    unfold columnStatistic at hstat
    rw [← Equiv.sum_comp g lam.colOf,
      ← Equiv.sum_comp mu.rowEquiv (fun y => lam.colOf (g y)),
      ← Equiv.sum_comp mu.rowEquiv mu.colOf, Fintype.sum_sigma, Fintype.sum_sigma] at hstat
    simpa only [Partition.colOf_rowEquiv] using hstat
  have hrow (i : Fin (mu.1.colLen 0)) : ∑ j, f i j = ∑ j : Fin (mu.1.rowLen i), j.val := by
    have h := Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin (mu.1.colLen 0)))) =>
      fin_injective_sum_lower (f i) (hf i))
    exact (h.mp hsum.symm i (Finset.mem_univ _)).symm
  let ix := mu.rowEquiv.symm x
  have hh := fin_injective_minimal_sum (f ix.1) (hf ix.1) (hrow ix.1) ix.2
  change lam.colOf (g (mu.rowEquiv ix)) < _ at hh
  rw [Equiv.apply_symm_apply] at hh
  exact hh

def columnPositionsEquiv {n : ℕ} (lam : Partition n) (j : ℕ) :
    Fin (lam.1.colLen j) ≃ {x : Fin n // lam.colOf x = j} where
  toFun i := ⟨lam.tableau ⟨(i.val, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩,
    by simp [Partition.colOf]⟩
  invFun x := ⟨lam.rowOf x.1, by
    have h := YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x.1).property
    change lam.rowOf x.1 < lam.1.colLen (lam.colOf x.1) at h
    simpa only [x.2] using h⟩
  left_inv i := by ext; simp [Partition.rowOf]
  right_inv x := by
    apply Subtype.ext
    apply lam.tableau.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    exact Prod.ext rfl x.2.symm

lemma colOf_fiber_card {n : ℕ} (lam : Partition n) (j : ℕ) :
    Fintype.card {x : Fin n // lam.colOf x = j} = lam.1.colLen j := by
  simpa using (Fintype.card_congr (columnPositionsEquiv lam j)).symm

lemma row_column_transversal_eq_of_statistic_eq {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (hstat : columnStatistic lam = columnStatistic mu) : lam = mu := by
  let r : Fin n → Fin n := fun x => mu.tableau
    ⟨(mu.rowOf x, lam.colOf (g x)), YoungDiagram.mem_iff_lt_rowLen.mpr
      (row_column_transversal_bound_of_statistic_eq lam mu g ht hstat x)⟩
  have hr (x : Fin n) : mu.rowOf (r x) = mu.rowOf x := by simp [r, Partition.rowOf]
  have hc (x : Fin n) : mu.colOf (r x) = lam.colOf (g x) := by simp [r, Partition.colOf]
  have hi : Function.Injective r := by
    intro x y h
    apply ht x y
    · simpa only [hr] using congrArg mu.rowOf h
    · simpa only [hc] using congrArg mu.colOf h
  let a : SymmetricGroup n := Equiv.ofBijective r (⟨hi, Finite.surjective_of_injective hi⟩)
  let e : SymmetricGroup n := g.symm.trans a
  have he (x : Fin n) : mu.colOf (e x) = lam.colOf x := by
    change mu.colOf (r (g⁻¹ x)) = lam.colOf x
    rw [hc]
    exact congrArg lam.colOf (g.apply_symm_apply x)
  have hcol (j : ℕ) : lam.1.colLen j = mu.1.colLen j := by
    rw [← colOf_fiber_card lam j, ← colOf_fiber_card mu j]
    exact Fintype.card_congr (Equiv.subtypeEquiv e (by intro x; rw [he]))
  apply Subtype.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen, hcol]

lemma specht_hom_generator_ne_zero {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) : f (spechtGenerator lam) ≠ 0 := by
  intro h
  apply hf
  apply specht_hom_ext lam _
  simpa using h

lemma specht_hom_transversal {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) :
    ∃ g : SymmetricGroup n, ∀ x y, mu.rowOf x = mu.rowOf y →
      lam.colOf (g x) = lam.colOf (g y) → x = y := by
  let v : RegularSpace n := spechtInclusion mu (f (spechtGenerator lam))
  have hv : v ≠ 0 := by
    intro h
    apply specht_hom_generator_ne_zero lam mu f hf
    exact Subtype.ext h
  obtain ⟨g, hg⟩ : ∃ g, v g ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    ext g
    exact h g
  have hvcol (c : colSubgroup lam) (g : SymmetricGroup n) :
      v (c.1 * g) = complexSign n c.1 * v g := by
    have he := Representation.IntertwiningMap.isIntertwining _ _ f (c⁻¹).1 (spechtGenerator lam)
    rw [spechtGenerator_column_action, map_smul] at he
    have hh := congrArg (fun w => (spechtInclusion mu w) g) he
    change complexSign n (c⁻¹).1 * v g = v ((c⁻¹).1⁻¹ * g) at hh
    simpa only [Subgroup.coe_inv, inv_inv, complexSign_inv] using hh.symm
  refine ⟨g, ?_⟩
  intro x y hr hc
  by_contra hxy
  let a : rowSubgroup mu := ⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩
  let c : colSubgroup lam := ⟨Equiv.swap (g x) (g y), swap_mem_fiberSubgroup _ hc⟩
  have he : c.1 * g = g * a.1 := by
    apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  have hs : complexSign n c.1 = -1 := by
    simp [c, complexSign, Equiv.Perm.sign_swap (g.injective.ne hxy)]
  have hh := hvcol c g
  rw [he, specht_right_row mu (f (spechtGenerator lam)), hs, neg_one_mul] at hh
  apply hg
  linear_combination hh / 2

lemma specht_hom_columnStatistic {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) : columnStatistic mu ≤ columnStatistic lam := by
  obtain ⟨g, hg⟩ := specht_hom_transversal lam mu f hf
  exact row_column_transversal_statistic lam mu g hg

lemma specht_equiv_shape_eq {n : ℕ} (lam mu : Partition n)
    (f : Representation.Equiv (spechtRepresentation lam) (spechtRepresentation mu)) :
    lam = mu := by
  have hf : f.toIntertwiningMap ≠ 0 := by
    intro h
    have hh := congrArg (fun k : Representation.IntertwiningMap
      (spechtRepresentation lam) (spechtRepresentation mu) => k (spechtGenerator lam)) h
    apply spechtGenerator_ne_zero lam
    exact f.toLinearEquiv.injective (by simpa using hh)
  have hi : f.symm.toIntertwiningMap ≠ 0 := by
    intro h
    have hh := congrArg (fun k : Representation.IntertwiningMap
      (spechtRepresentation mu) (spechtRepresentation lam) => k (spechtGenerator mu)) h
    apply spechtGenerator_ne_zero mu
    exact f.symm.toLinearEquiv.injective (by simpa using hh)
  have hs := le_antisymm (specht_hom_columnStatistic _ _ f.symm.toIntertwiningMap hi)
    (specht_hom_columnStatistic _ _ f.toIntertwiningMap hf)
  obtain ⟨g, hg⟩ := specht_hom_transversal lam mu f.toIntertwiningMap hf
  exact row_column_transversal_eq_of_statistic_eq lam mu g hg hs

def natPartitionOfDiagram {n : ℕ} (lam : Partition n) : Nat.Partition n where
  parts := lam.1.rowLens
  parts_pos := by
    intro i hi
    exact lam.1.pos_of_mem_rowLens i hi
  parts_sum := partition_rowLens_sum lam

def diagramOfNatPartition {n : ℕ} (p : Nat.Partition n) : Partition n :=
  ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
      (p.parts.pairwise_sort (· ≥ ·)).sortedGE, by
    rw [← diagram_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self]
    · simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum
    · intro a ha
      exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp ha)⟩

@[simp]
lemma natPartitionOfDiagram_diagramOfNatPartition {n : ℕ} (p : Nat.Partition n) :
    natPartitionOfDiagram (diagramOfNatPartition p) = p := by
  apply Nat.Partition.ext
  dsimp [natPartitionOfDiagram, diagramOfNatPartition]
  rw [YoungDiagram.rowLens_ofRowLens_eq_self]
  · exact Multiset.sort_eq _ _
  · intro a ha
    exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp ha)

@[simp]
lemma diagramOfNatPartition_natPartitionOfDiagram {n : ℕ} (lam : Partition n) :
    diagramOfNatPartition (natPartitionOfDiagram lam) = lam := by
  apply Subtype.ext
  change YoungDiagram.ofRowLens ((↑lam.1.rowLens : Multiset ℕ).sort (· ≥ ·))
    ((↑lam.1.rowLens : Multiset ℕ).pairwise_sort (· ≥ ·)).sortedGE = lam.1
  have hs : (↑lam.1.rowLens : Multiset ℕ).sort (· ≥ ·) = lam.1.rowLens := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ lam.1.rowLens_sorted.pairwise
  simpa only [hs] using (YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := lam.1))

def conjugacyDiagram (n : ℕ) : ConjClasses (SymmetricGroup n) → Partition n :=
  Quotient.lift (fun g : SymmetricGroup n =>
    diagramOfNatPartition (show Nat.Partition n from Fintype.card_fin n ▸ g.partition)) (by
      intro g h hgh
      have he := Equiv.Perm.partition_eq_of_isConj.mp hgh
      apply congrArg diagramOfNatPartition
      exact congrArg (fun p : Nat.Partition (Fintype.card (Fin n)) =>
        show Nat.Partition n from Fintype.card_fin n ▸ p) he)

lemma conjugacyDiagram_injective (n : ℕ) : Function.Injective (conjugacyDiagram n) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      intro he
      apply Quotient.sound
      apply Equiv.Perm.partition_eq_of_isConj.mpr
      have hh := congrArg natPartitionOfDiagram he
      simp only [conjugacyDiagram, Quotient.lift_mk,
        natPartitionOfDiagram_diagramOfNatPartition] at hh
      simpa using hh

def quotientCharacter {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (ρ : Representation ℂ G E) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (by
    intro g h hgh
    obtain ⟨k, rfl⟩ := isConj_iff.mp hgh
    exact (ρ.char_conj g k).symm)

@[simp]
lemma quotientCharacter_mk {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (ρ : Representation ℂ G E) (g : G) :
    quotientCharacter ρ (ConjClasses.mk g) = ρ.character g := rfl

def classCharacterPairing {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) : (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g : G, f (ConjClasses.mk g) * ρ.character g⁻¹
  map_add' f g := by simp [Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' c f := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

lemma specht_classCharacterPairing {n : ℕ} (lam mu : Partition n) :
    classCharacterPairing (spechtRepresentation lam)
      (quotientCharacter (spechtRepresentation mu)) = if lam = mu then 1 else 0 := by
  let := specht_irreducible lam
  let := specht_irreducible mu
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  change (Nat.card (SymmetricGroup n) : ℂ)⁻¹ * ∑ g,
    (spechtRepresentation mu).character g * (spechtRepresentation lam).character g⁻¹ = _
  rw [Representation.char_orthonormal]
  congr 1
  apply propext
  constructor
  · rintro ⟨e⟩
    exact specht_equiv_shape_eq lam mu e
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

lemma specht_characters_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (fun lam : Partition n => quotientCharacter (spechtRepresentation lam)) := by
  rw [linearIndependent_iff']
  intro s c hc lam hlam
  have h := congrArg (classCharacterPairing (spechtRepresentation lam)) hc
  simpa only [map_sum, map_smul, map_zero, specht_classCharacterPairing,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hlam] using h

lemma specht_characters_span (n : ℕ) :
    Submodule.span ℂ (Set.range (fun lam : Partition n =>
      quotientCharacter (spechtRepresentation lam))) = ⊤ := by
  let := Fintype.ofFinite (Partition n)
  let := Fintype.ofFinite (ConjClasses (SymmetricGroup n))
  let : Nonempty (Partition n) := ⟨conjugacyDiagram n 1⟩
  have hle : Module.finrank ℂ (ConjClasses (SymmetricGroup n) → ℂ) ≤
      Fintype.card (Partition n) := by
    rw [Module.finrank_pi]
    exact Fintype.card_le_of_injective _ (conjugacyDiagram_injective n)
  exact (specht_characters_linearIndependent n).span_eq_top_of_card_eq_finrank
    (le_antisymm (specht_characters_linearIndependent n).fintype_card_le_finrank hle)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TraceDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

lemma class_function_expansion {n : ℕ} (f : ConjClasses (SymmetricGroup n) → ℂ) :
    f = ∑ lam : Partition n, classCharacterPairing (spechtRepresentation lam) f •
      quotientCharacter (spechtRepresentation lam) := by
  have hf : f ∈ Submodule.span ℂ (Set.range (fun lam : Partition n =>
    quotientCharacter (spechtRepresentation lam))) := by rw [specht_characters_span]; trivial
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨mu, rfl⟩ := hx
    simp only [specht_classCharacterPairing, ite_smul, one_smul, zero_smul]
    simp
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul c x _ hx =>
    simp only [map_smul, smul_assoc, ← Finset.smul_sum]
    rw [← hx]

theorem character_specht_expansion {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (g : SymmetricGroup n) :
    ρ.character g = ∑ lam : Partition n,
      (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
        (spechtRepresentation lam).character g := by
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  have he := congrFun (class_function_expansion (quotientCharacter ρ)) (ConjClasses.mk g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, quotientCharacter_mk] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro lam _
  congr 1
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank _ _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RestrictionSum
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
variable {G E F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

def outerTensorRepresentation {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) :
    Representation ℂ (G × H) (E ⊗[ℂ] F) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

@[simp]
lemma outerTensorRepresentation_apply {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (g : G) (h : H) :
    outerTensorRepresentation ρ σ (g, h) = TensorProduct.map (ρ g) (σ h) := rfl

lemma outerTensorRepresentation_norm {G H E F : Type*} [Monoid G] [Monoid H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ h y, ‖σ h y‖ = ‖y‖)
    (gh : G × H) (x : E ⊗[ℂ] F) : ‖outerTensorRepresentation ρ σ gh x‖ = ‖x‖ := by
  exact (TensorProduct.mapIsometry
    (⟨ρ gh.1, hρ gh.1⟩ : E →ₗᵢ[ℂ] E) (⟨σ gh.2, hσ gh.2⟩ : F →ₗᵢ[ℂ] F)).norm_map x

@[simp]
lemma outerTensorRepresentation_character {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (g : G) (h : H) :
    (outerTensorRepresentation ρ σ).character (g, h) = ρ.character g * σ.character h := by
  rw [outerTensorRepresentation, Representation.char_tensor]
  rfl

lemma outerTensorRepresentation_end_finrank {G H E F : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    finrank ℂ (Representation.IntertwiningMap (outerTensorRepresentation ρ σ)
      (outerTensorRepresentation ρ σ)) = 1 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  let : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := H)).ne')
  let : Invertible (Nat.card (G × H) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G × H)).ne')
  apply Nat.cast_injective (R := ℂ)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [Fintype.sum_prod_type, Prod.inv_mk, outerTensorRepresentation_character,
    Nat.card_prod, Nat.cast_mul, mul_inv_rev, Nat.cast_one]
  calc
    _ = ((Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * ρ.character g⁻¹) *
        ((Nat.card H : ℂ)⁻¹ * ∑ h, σ.character h * σ.character h⁻¹) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = 1 := by simp only [Representation.char_orthonormal,
      if_pos (show Nonempty (Representation.Equiv ρ ρ) from ⟨.refl ρ⟩),
      if_pos (show Nonempty (Representation.Equiv σ σ) from ⟨.refl σ⟩), mul_one]

theorem outerTensorRepresentation_irreducible {G H E F : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ h y, ‖σ h y‖ = ‖y‖)
    [ρ.IsIrreducible] [σ.IsIrreducible] : (outerTensorRepresentation ρ σ).IsIrreducible := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) σ.asModule
  let : Nontrivial E := ρ.asModuleEquiv.toEquiv.symm.nontrivial
  let : Nontrivial F := σ.asModuleEquiv.toEquiv.symm.nontrivial
  apply irreducible_of_scalar_commutant _ (outerTensorRepresentation_norm ρ σ hρ hσ)
  intro f
  let τ := outerTensorRepresentation ρ σ
  have h1 : (1 : Representation.IntertwiningMap τ τ) ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : E ⊗[ℂ] F)
    exact hx (congrArg (fun f : Representation.IntertwiningMap τ τ => f x) hz)
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' _ h1).mp
    (outerTensorRepresentation_end_finrank ρ σ) f
  exact ⟨z, hz.symm⟩

theorem exists_specht_intertwiner {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (τ : Representation ℂ (SymmetricGroup n) E) :
    ∃ γ : Partition n, ∃ f : Representation.IntertwiningMap (spechtRepresentation γ) τ,
      f ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz (γ : Partition n) :
      finrank ℂ (Representation.IntertwiningMap (spechtRepresentation γ) τ) = 0 :=
    finrank_zero_iff_forall_zero.mpr (hn γ)
  have he := character_specht_expansion τ 1
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero, Representation.char_one] at he
  have hc : finrank ℂ E = 0 := Nat.cast_eq_zero.mp he
  exact (Module.finrank_pos (R := ℂ) (M := E)).ne' hc

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical
variable {G H E F L : Type*} [Monoid G] [Monoid H]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup L] [Module ℂ L]

def multiplicityAction (ρ : Representation ℂ G E) (τ : Representation ℂ (G × H) L)
    (h : H) (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) :
    Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H)) :=
  (τ (1, h) ∘ₗ f.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change τ (1, h) (f (ρ g x)) = τ (g, 1) (τ (1, h) (f x))
    rw [f.isIntertwining]
    change (τ (1, h) * τ (g, 1)) (f x) = (τ (g, 1) * τ (1, h)) (f x)
    rw [← map_mul, ← map_mul]
    simp)

@[simp] lemma multiplicityAction_apply (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) (h : H)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) (x : E) :
    multiplicityAction ρ τ h f x = τ (1, h) (f x) := rfl

def multiplicityRepresentation (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) :
    Representation ℂ H (Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) where
  toFun h := {
    toFun := multiplicityAction ρ τ h
    map_add' := by intro f k; ext x; simp
    map_smul' := by intro c f; ext x; simp }
  map_one' := by
    ext f x
    change τ (1, 1) (f x) = f x
    change τ 1 (f x) = f x
    simp
  map_mul' h k := by
    ext f x
    change τ (1, h * k) (f x) = (τ (1, h) * τ (1, k)) (f x)
    rw [← map_mul]
    simp

@[simp] lemma multiplicityRepresentation_apply (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) (h : H)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) (x : E) :
    multiplicityRepresentation ρ τ h f x = τ (1, h) (f x) := rfl

def tensorMultiplicityEvaluation (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) :
    E ⊗[ℂ] F →ₗ[ℂ] L :=
  TensorProduct.lift {
    toFun x := {
      toFun y := f y x
      map_add' := by intro y z; simp
      map_smul' := by intro c y; simp }
    map_add' := by intro x z; ext y; simp
    map_smul' := by intro c x; ext y; simp }

@[simp] lemma tensorMultiplicityEvaluation_tmul
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) (x : E) (y : F) :
    tensorMultiplicityEvaluation ρ σ τ f (x ⊗ₜ[ℂ] y) = f y x := rfl

def tensorMultiplicityIntertwiner (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) :
    Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ :=
  (tensorMultiplicityEvaluation ρ σ τ f).intertwiningMap_of_isIntertwiningMap _ _ (by
    rintro ⟨g, h⟩ v
    induction v using TensorProduct.inductionOn with
    | tmul x y =>
      change tensorMultiplicityEvaluation ρ σ τ f
        (TensorProduct.map (ρ g) (σ h) (x ⊗ₜ[ℂ] y)) = _
      rw [TensorProduct.map_tmul, tensorMultiplicityEvaluation_tmul,
        f.isIntertwining, multiplicityRepresentation_apply, (f y).isIntertwining]
      change (τ (1, h) * τ (g, 1)) (f y x) = τ (g, h) (f y x)
      rw [← map_mul]
      simp
    | add x y hx hy => simp only [map_add, hx, hy])

lemma tensorMultiplicityIntertwiner_ne_zero (ρ : Representation ℂ G E)
    (σ : Representation ℂ H F) (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) (hf : f ≠ 0) :
    tensorMultiplicityIntertwiner ρ σ τ f ≠ 0 := by
  intro hz
  apply hf
  ext y x
  exact congrArg (fun k : Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ =>
    k (x ⊗ₜ[ℂ] y)) hz

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

theorem exists_external_specht_extension {G E L : Type*} {h : ℕ}
    [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L]
    (ρ : Representation ℂ G E) (τ : Representation ℂ (G × SymmetricGroup h) L)
    [ρ.IsIrreducible] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G (SymmetricGroup h))))
    (hf : f ≠ 0) :
    ∃ γ : Partition h, ∃ k : Representation.IntertwiningMap
      (outerTensorRepresentation ρ (spechtRepresentation γ)) τ, Function.Injective k := by
  let : Nontrivial (Representation.IntertwiningMap ρ
      (τ.comp (MonoidHom.inl G (SymmetricGroup h)))) := ⟨⟨f, 0, hf⟩⟩
  obtain ⟨γ, k, hk⟩ := exists_specht_intertwiner (multiplicityRepresentation ρ τ)
  let : (spechtRepresentation γ).IsIrreducible := specht_irreducible γ
  let : (outerTensorRepresentation ρ (spechtRepresentation γ)).IsIrreducible :=
    outerTensorRepresentation_irreducible _ _ hρ (spechtRepresentation_norm γ)
  exact ⟨γ, tensorMultiplicityIntertwiner ρ (spechtRepresentation γ) τ k,
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
      (tensorMultiplicityIntertwiner_ne_zero _ _ _ k hk)⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

lemma complexSign_norm {n : ℕ} (g : SymmetricGroup n) : ‖complexSign n g‖ = 1 := by
  have he := congrArg norm (complexSign_mul_self g)
  rw [norm_mul, norm_one] at he
  nlinarith [norm_nonneg (complexSign n g)]

def signTwist {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) : Representation ℂ (SymmetricGroup n) E where
  toFun g := complexSign n g • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

lemma signTwist_norm {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (g : SymmetricGroup n) (x : E) : ‖signTwist ρ g x‖ = ‖x‖ := by
  change ‖complexSign n g • ρ g x‖ = ‖x‖
  rw [norm_smul, complexSign_norm, hρ, one_mul]

def orbitEvaluation {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) : RegularSpace n →ₗ[ℂ] E where
  toFun f := ∑ g, f g • ρ g x
  map_add' := by intro f k; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c f; simp [smul_smul, Finset.smul_sum]

lemma orbitEvaluation_intertwines {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (g : SymmetricGroup n)
    (f : RegularSpace n) :
    orbitEvaluation ρ x (regularRepresentation n g f) = ρ g (orbitEvaluation ρ x f) := by
  change (∑ h, f (g⁻¹ * h) • ρ h x) = ρ g (∑ h, f h • ρ h x)
  simp only [map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
  have he := (Equiv.sum_comp (Equiv.mulLeft g) (fun h => f (g⁻¹ * h) • ρ h x)).symm
  change (∑ h, f (g⁻¹ * h) • ρ h x) = ∑ h, f (g⁻¹ * (g * h)) • ρ (g * h) x at he
  simpa only [inv_mul_cancel_left] using he

lemma orbitEvaluation_single {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (g : SymmetricGroup n) :
    orbitEvaluation ρ x (EuclideanSpace.single g 1) = ρ g x := by
  simp [orbitEvaluation, PiLp.single_apply, ite_smul]

lemma orbitEvaluation_polytabloid {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (μ : Partition n) :
    orbitEvaluation ρ x (polytabloid μ) =
      ((Fintype.card (colSubgroup μ) : ℂ) * (Fintype.card (rowSubgroup μ) : ℂ)) •
        groupAverage ((signTwist ρ).comp (colSubgroup μ).subtype)
          (groupAverage (ρ.comp (rowSubgroup μ).subtype) x) := by
  have hr : (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card (colSubgroup μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [polytabloid, map_sum, map_smul, orbitEvaluation_single]
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    MonoidHom.comp_apply, Subgroup.subtype_apply, signTwist, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [map_smul, map_sum, smul_smul, Finset.smul_sum, map_mul, Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  change complexSign n c.1 • ρ c.1 (ρ a.1 x) = _
  congr 1
  field_simp

lemma projection_product_nonzero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Q : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetric)
    (x : E) (hQx : Q x = x) (hPx : P x ≠ 0) : Q (P x) ≠ 0 := by
  intro hz
  have he := hQ x (P x)
  rw [hQx, hz, inner_zero_right] at he
  have hp := hP.isSymmetric x (P x)
  have hi : P (P x) = P x := congrArg (fun f : E →ₗ[ℂ] E => f x) hP.isIdempotentElem
  rw [hi, he] at hp
  exact hPx (inner_self_eq_zero.mp hp)

def spechtOrbitIntertwiner {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (μ : Partition n) (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) :
    Representation.IntertwiningMap (spechtRepresentation μ) ρ :=
  ((orbitEvaluation ρ x).comp (spechtInclusion μ)).intertwiningMap_of_isIntertwiningMap _ _
    (by intro g v; exact orbitEvaluation_intertwines ρ x g (spechtInclusion μ v))

theorem specht_occurs_of_row_average {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (μ : Partition n) (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (x : E)
    (hcol : ∀ c : colSubgroup μ, ρ c.1 x = complexSign n c.1 • x)
    (hrow : groupAverage (ρ.comp (rowSubgroup μ).subtype) x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ) ρ,
      Function.Injective f := by
  let P := groupAverage (ρ.comp (rowSubgroup μ).subtype)
  let Q := groupAverage ((signTwist ρ).comp (colSubgroup μ).subtype)
  have hP : P.IsSymmetricProjection := ⟨groupAverage_idempotent _,
    groupAverage_symmetric _ (fun g => hρ g.1)⟩
  have hQ : Q.IsSymmetric := groupAverage_symmetric _ (fun g => signTwist_norm ρ hρ g.1)
  have hQx : Q x = x := by
    apply groupAverage_fixed
    intro c
    change complexSign n c.1 • ρ c.1 x = x
    rw [hcol, smul_smul, complexSign_mul_self, one_smul]
  have hv : Q (P x) ≠ 0 := projection_product_nonzero P Q hP hQ x hQx hrow
  have hf : spechtOrbitIntertwiner μ ρ x ≠ 0 := by
    intro hz
    have he := congrArg (fun f : Representation.IntertwiningMap (spechtRepresentation μ) ρ =>
      f (spechtGenerator μ)) hz
    change orbitEvaluation ρ x (polytabloid μ) = 0 at he
    rw [orbitEvaluation_polytabloid] at he
    have hn : (Fintype.card (colSubgroup μ) : ℂ) * (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero) (by exact_mod_cast Fintype.card_ne_zero)
    exact hv ((smul_eq_zero.mp he).resolve_left hn)
  let : (spechtRepresentation μ).IsIrreducible := specht_irreducible μ
  exact ⟨spechtOrbitIntertwiner μ ρ x, (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right hf⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RestrictionSum2
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

def subdiagramLabels {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) : Fin m ↪ Fin n where
  toFun i := lam.tableau ⟨(μ.tableau.symm i).1, h (μ.tableau.symm i).2⟩
  inj' := by
    intro i j hij
    apply μ.tableau.symm.injective
    apply Subtype.ext
    exact congrArg (fun b : {c // c ∈ lam.1.cells} => b.1) (lam.tableau.injective hij)

@[simp] lemma subdiagramLabels_row {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (i : Fin m) : lam.rowOf (subdiagramLabels h i) = μ.rowOf i := by
  change (lam.tableau.symm (lam.tableau ⟨(μ.tableau.symm i).1, _⟩)).1.1 = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma subdiagramLabels_col {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (i : Fin m) : lam.colOf (subdiagramLabels h i) = μ.colOf i := by
  change (lam.tableau.symm (lam.tableau ⟨(μ.tableau.symm i).1, _⟩)).1.2 = _
  rw [Equiv.symm_apply_apply]
  rfl

def subdiagramEmbedding {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) : SymmetricGroup m →* SymmetricGroup n :=
  Equiv.Perm.viaEmbeddingHom (subdiagramLabels h)

lemma subdiagramEmbedding_row {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (a : rowSubgroup μ) : subdiagramEmbedding h a.1 ∈ rowSubgroup lam := by
  intro x
  by_cases hx : x ∈ Set.range (subdiagramLabels h)
  · obtain ⟨i, rfl⟩ := hx
    change lam.rowOf (a.1.viaEmbedding (subdiagramLabels h) (subdiagramLabels h i)) = _
    rw [Equiv.Perm.viaEmbedding_apply, subdiagramLabels_row, subdiagramLabels_row]
    exact a.2 i
  · change lam.rowOf (a.1.viaEmbedding _ x) = _
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]

lemma subdiagramEmbedding_col {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (a : colSubgroup μ) : subdiagramEmbedding h a.1 ∈ colSubgroup lam := by
  intro x
  by_cases hx : x ∈ Set.range (subdiagramLabels h)
  · obtain ⟨i, rfl⟩ := hx
    change lam.colOf (a.1.viaEmbedding (subdiagramLabels h) (subdiagramLabels h i)) = _
    rw [Equiv.Perm.viaEmbedding_apply, subdiagramLabels_col, subdiagramLabels_col]
    exact a.2 i
  · change lam.colOf (a.1.viaEmbedding _ x) = _
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]

lemma complexSign_viaEmbedding {m n : ℕ} (j : Fin m ↪ Fin n) (a : SymmetricGroup m) :
    complexSign n (Equiv.Perm.viaEmbeddingHom j a) = complexSign m a := by
  simp [complexSign, Equiv.Perm.viaEmbeddingHom, Equiv.Perm.extendDomainHom]

theorem subdiagram_specht_occurs {m n : ℕ} (μ : Partition m) (lam : Partition n)
    (h : μ.1 ≤ lam.1) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ)
      ((spechtRepresentation lam).comp (subdiagramEmbedding h)), Function.Injective f := by
  apply specht_occurs_of_row_average μ ((spechtRepresentation lam).comp (subdiagramEmbedding h))
    (fun g => spechtRepresentation_norm lam (subdiagramEmbedding h g)) (spechtGenerator lam)
  · intro c
    have he := spechtGenerator_column_action lam
      ⟨subdiagramEmbedding h c.1, subdiagramEmbedding_col h c⟩
    simpa only [MonoidHom.comp_apply, subdiagramEmbedding, complexSign_viaEmbedding] using he
  · let ρ := (spechtRepresentation lam).comp (subdiagramEmbedding h)
    have ha (a : rowSubgroup μ) :
        spechtInclusion lam (ρ a.1 (spechtGenerator lam)) 1 = 1 := by
      change polytabloid lam ((subdiagramEmbedding h a.1)⁻¹ * 1) = 1
      let b : rowSubgroup lam := ⟨subdiagramEmbedding h a.1, subdiagramEmbedding_row h a⟩
      calc
        _ = polytabloid lam (1 * (b⁻¹).1) := by simp [b]
        _ = polytabloid lam 1 := polytabloid_right_row lam b⁻¹ 1
        _ = 1 := polytabloid_at_one lam
    have he : spechtInclusion lam (groupAverage (ρ.comp (rowSubgroup μ).subtype)
        (spechtGenerator lam)) 1 = 1 := by
      have hn : (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
        map_smul, map_sum, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
      simp only [ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        smul_eq_mul, inv_mul_cancel₀ hn]
    intro hz
    rw [hz, map_zero, PiLp.zero_apply] at he
    exact zero_ne_one he

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

def blockEmbeddingHom {u v l n : ℕ} (h : u + v + l = n) :
    ((SymmetricGroup u × SymmetricGroup v) × SymmetricGroup l) →* SymmetricGroup n :=
  (blockEquiv h).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin u ⊕ Fin v) (Fin l)).comp
      ((Equiv.Perm.sumCongrHom (Fin u) (Fin v)).prodMap (MonoidHom.id _)))

@[simp] lemma blockEmbeddingHom_apply {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    blockEmbeddingHom h ((a,b),c) = blockEmbedding h a b c := rfl

def blockSpinInjection {u v l n : ℕ} (h : u + v + l = n) :
    (Fin u ⊕ Fin v) ↪ Fin n :=
  Function.Embedding.inl.trans (blockEquiv h).toEmbedding

lemma blockEmbedding_one_remainder {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    blockEmbedding h a b 1 = (a.sumCongr b).viaEmbedding (blockSpinInjection h) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (blockEquiv h).surjective x
  cases x with
  | inl y =>
    change (blockEquiv h).permCongr _ (blockEquiv h (Sum.inl y)) =
      (a.sumCongr b).viaEmbedding _ (blockSpinInjection h y)
    rw [Equiv.Perm.viaEmbedding_apply]
    simp [Equiv.permCongr_apply, blockSpinInjection]
  | inr z =>
    have hn : blockEquiv h (Sum.inr z) ∉ Set.range (blockSpinInjection h) := by
      rintro ⟨y, he⟩
      have he' := (blockEquiv h).injective he
      exact Sum.inl_ne_inr he'
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]
    simp [blockEmbedding_eq, Equiv.permCongr_apply]

lemma viaEmbedding_trans {A B C : Type*} (i : A ↪ B) (j : B ↪ C) (g : Equiv.Perm A) :
    g.viaEmbedding (i.trans j) = (g.viaEmbedding i).viaEmbedding j := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    by_cases hy : y ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hy
      change g.viaEmbedding (i.trans j) ((i.trans j) z) = j (g.viaEmbedding i (i z))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      rfl
    · have hn : j y ∉ Set.range (i.trans j) := by
        rintro ⟨z, he⟩
        exact hy ⟨z, j.injective he⟩
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy]
  · have hn : x ∉ Set.range (i.trans j) := by
      rintro ⟨z, rfl⟩
      exact hx ⟨i z, rfl⟩
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]

lemma sumCongr_viaEmbedding {A B C D : Type*} (i : A ↪ B) (j : C ↪ D)
    (a : Equiv.Perm A) (b : Equiv.Perm C) :
    (a.viaEmbedding i).sumCongr (b.viaEmbedding j) =
      (a.sumCongr b).viaEmbedding (i.sumMap j) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl y =>
    by_cases hy : y ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hy
      change Sum.inl (a.viaEmbedding i (i z)) =
        (a.sumCongr b).viaEmbedding _ ((i.sumMap j) (Sum.inl z))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      rfl
    · have hn : Sum.inl y ∉ Set.range (i.sumMap j) := by
        rintro ⟨z, he⟩
        cases z with
        | inl z => exact hy ⟨z, Sum.inl.inj he⟩
        | inr z => exact Sum.inr_ne_inl he
      change Sum.inl (a.viaEmbedding i y) = _
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]
  | inr y =>
    by_cases hy : y ∈ Set.range j
    · obtain ⟨z, rfl⟩ := hy
      change Sum.inr (b.viaEmbedding j (j z)) =
        (a.sumCongr b).viaEmbedding _ ((i.sumMap j) (Sum.inr z))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      rfl
    · have hn : Sum.inr y ∉ Set.range (i.sumMap j) := by
        rintro ⟨z, he⟩
        cases z with
        | inl z => exact Sum.inl_ne_inr he
        | inr z => exact hy ⟨z, Sum.inr.inj he⟩
      change Sum.inr (b.viaEmbedding j y) = _
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]

lemma viaEmbedding_conjugate {A B : Type*} (i j : A ↪ B) (σ : Equiv.Perm B)
    (hσ : ∀ x, σ (i x) = j x) (g : Equiv.Perm A) :
    σ * g.viaEmbedding i * σ⁻¹ = g.viaEmbedding j := by
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ Set.range j
  · obtain ⟨x, rfl⟩ := hy
    have he : σ⁻¹ (j x) = i x := by
      rw [← hσ]; exact σ.symm_apply_apply (i x)
    simp only [Equiv.Perm.mul_apply, he, Equiv.Perm.viaEmbedding_apply, hσ]
  · have hn : σ⁻¹ y ∉ Set.range i := by
      rintro ⟨x, hx⟩
      apply hy
      refine ⟨x, ?_⟩
      rw [← hσ, hx]
      exact Equiv.apply_symm_apply σ y
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy]
    exact σ.apply_symm_apply y

def spinRestriction {u v l n : ℕ} (h : u + v + l = n) (lam : Partition n) :
    Representation ℂ (SymmetricGroup u × SymmetricGroup v) (Specht lam) :=
  (spechtRepresentation lam).comp ((blockEmbeddingHom h).comp
    (MonoidHom.inl (SymmetricGroup u × SymmetricGroup v) (SymmetricGroup l)))

@[simp] lemma spinRestriction_apply {u v l n : ℕ} (h : u + v + l = n) (lam : Partition n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    spinRestriction h lam (a,b) = spechtRepresentation lam (blockEmbedding h a b 1) := rfl

theorem signed_occurrence_of_spin_intertwiner {u v l n : ℕ} (h : u + v + l = n)
    (α : Partition u) (β : Partition v) (lam : Partition n)
    (f : Representation.IntertwiningMap
      (outerTensorRepresentation (spechtRepresentation α) (spechtRepresentation β.transpose))
      (spinRestriction h lam)) (hf : f ≠ 0) :
    ∃ γ : Partition l, SignedOccurrence h α β γ lam := by
  let ρ := outerTensorRepresentation (spechtRepresentation α) (spechtRepresentation β.transpose)
  let τ := (spechtRepresentation lam).comp (blockEmbeddingHom h)
  let : (spechtRepresentation α).IsIrreducible := specht_irreducible α
  let : (spechtRepresentation β.transpose).IsIrreducible := specht_irreducible β.transpose
  have hρ := outerTensorRepresentation_norm _ _
    (spechtRepresentation_norm α) (spechtRepresentation_norm β.transpose)
  let : ρ.IsIrreducible := outerTensorRepresentation_irreducible _ _
    (spechtRepresentation_norm α) (spechtRepresentation_norm β.transpose)
  obtain ⟨γ, k, hk⟩ := exists_external_specht_extension ρ τ hρ f hf
  refine ⟨γ, k.toLinearMap, hk, ?_⟩
  intro a b c x
  simpa only [τ, ρ, outerTensorRepresentation_apply, MonoidHom.comp_apply, blockEmbeddingHom_apply,
    Representation.IntertwiningMap.toLinearMap_apply]
    using (Representation.IntertwiningMap.isIntertwining _ _ k ((a,b),c) x)

theorem signed_occurrence_subdiagrams {u v l n u' v' L : ℕ}
    {h : u + v + l = n} {α : Partition u} {β : Partition v}
    {γ : Partition l} {lam : Partition n} (ho : SignedOccurrence h α β γ lam)
    (α' : Partition u') (β' : Partition v') (ha : α'.1 ≤ α.1) (hb : β'.1 ≤ β.1)
    (hL : u' + v' + L = n) :
    ∃ γ' : Partition L, SignedOccurrence hL α' β' γ' lam := by
  obtain ⟨F, hF, hinter⟩ := ho
  have hbt : β'.transpose.1 ≤ β.transpose.1 := YoungDiagram.transpose_mono hb
  obtain ⟨fa, hfa⟩ := subdiagram_specht_occurs α' α ha
  obtain ⟨fb, hfb⟩ := subdiagram_specht_occurs β'.transpose β.transpose hbt
  let i := (subdiagramLabels ha).sumMap (subdiagramLabels hbt)
  let j := i.trans (blockSpinInjection h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (blockSpinInjection hL) j (blockSpinInjection hL).injective j.injective
  have hconj (a : SymmetricGroup u') (b : SymmetricGroup v') :
      σ * blockEmbedding hL a b 1 * σ⁻¹ =
        blockEmbedding h (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1 := by
    rw [blockEmbedding_one_remainder, blockEmbedding_one_remainder]
    change σ * (a.sumCongr b).viaEmbedding (blockSpinInjection hL) * σ⁻¹ =
      ((a.viaEmbedding (subdiagramLabels ha)).sumCongr
        (b.viaEmbedding (subdiagramLabels hbt))).viaEmbedding (blockSpinInjection h)
    rw [sumCongr_viaEmbedding, ← viaEmbedding_trans]
    exact viaEmbedding_conjugate _ _ σ hσ _
  let A := Specht α ⊗[ℂ] Specht β.transpose
  let k : (Specht α' ⊗[ℂ] Specht β'.transpose) →ₗ[ℂ] Specht lam :=
    F.comp (((TensorProduct.mk ℂ A (Specht γ)).flip (spechtGenerator γ)).comp
      (TensorProduct.map fa.toLinearMap fb.toLinearMap))
  have hk (a : SymmetricGroup u') (b : SymmetricGroup v')
      (x : Specht α' ⊗[ℂ] Specht β'.transpose) :
      k (TensorProduct.map (spechtRepresentation α' a) (spechtRepresentation β'.transpose b) x) =
      spechtRepresentation lam
        (blockEmbedding h (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1) (k x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change F ((TensorProduct.map fa.toLinearMap fb.toLinearMap
        (TensorProduct.map _ _ (x ⊗ₜ[ℂ] y))) ⊗ₜ[ℂ] spechtGenerator γ) = _
      simp only [TensorProduct.map_tmul, Representation.IntertwiningMap.toLinearMap_apply]
      rw [fa.isIntertwining, fb.isIntertwining]
      have he := hinter (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1
        ((fa x ⊗ₜ[ℂ] fb y) ⊗ₜ[ℂ] spechtGenerator γ)
      dsimp [k, A] at *
      simpa only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        TensorProduct.map_tmul, Representation.IntertwiningMap.toLinearMap_apply,
        MonoidHom.comp_apply, map_one, Module.End.one_apply] using he
    | add x y hx hy => simp only [map_add, hx, hy]
  have hk0 : k ≠ 0 := by
    intro hz
    have hax : fa (spechtGenerator α') ≠ 0 := by
      intro he
      exact spechtGenerator_ne_zero α' (hfa (he.trans (map_zero fa).symm))
    have hby : fb (spechtGenerator β'.transpose) ≠ 0 := by
      intro he
      exact spechtGenerator_ne_zero β'.transpose (hfb (he.trans (map_zero fb).symm))
    have he := congrArg (fun t : (Specht α' ⊗[ℂ] Specht β'.transpose) →ₗ[ℂ] Specht lam =>
      t (spechtGenerator α' ⊗ₜ[ℂ] spechtGenerator β'.transpose)) hz
    change F ((fa (spechtGenerator α') ⊗ₜ[ℂ] fb (spechtGenerator β'.transpose)) ⊗ₜ[ℂ]
      spechtGenerator γ) = 0 at he
    exact complex_tmul_ne_zero (complex_tmul_ne_zero hax hby) (spechtGenerator_ne_zero γ)
      (hF (he.trans (map_zero F).symm))
  let k' := ((spechtRepresentation lam σ⁻¹).comp k).intertwiningMap_of_isIntertwiningMap
    (outerTensorRepresentation (spechtRepresentation α') (spechtRepresentation β'.transpose))
    (spinRestriction hL lam) (by
      rintro ⟨a,b⟩ x
      change spechtRepresentation lam σ⁻¹ (k (TensorProduct.map
        (spechtRepresentation α' a) (spechtRepresentation β'.transpose b) x)) =
        spechtRepresentation lam (blockEmbedding hL a b 1) (spechtRepresentation lam σ⁻¹ (k x))
      rw [hk]
      change (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam
        (blockEmbedding h (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1)) (k x) =
        (spechtRepresentation lam (blockEmbedding hL a b 1) * spechtRepresentation lam σ⁻¹) (k x)
      rw [← map_mul, ← map_mul, ← hconj]
      simp only [← mul_assoc, inv_mul_cancel, one_mul])
  apply signed_occurrence_of_spin_intertwiner hL α' β' lam k'
  intro hz
  apply hk0
  apply LinearMap.ext
  intro x
  have he := congrArg (fun t => spechtRepresentation lam σ (t x)) hz
  change (spechtRepresentation lam σ * spechtRepresentation lam σ⁻¹) (k x) = 0 at he
  simpa only [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, LinearMap.zero_apply] using he

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

lemma truncatePartition_le {n : ℕ} (q : ℕ) (lam : Partition n) :
    (truncatePartition q lam).1 ≤ lam.1 := by
  intro c hc
  change c ∈ YoungDiagram.ofRowLens _
    ((lam.1.rowLens_sorted.pairwise.sublist (List.take_sublist q _)).sortedGE) at hc
  obtain ⟨hi, hj⟩ := YoungDiagram.mem_ofRowLens.mp hc
  have hi' : c.1 < lam.1.rowLens.length := by
    rw [List.length_take] at hi
    exact lt_of_lt_of_le hi (min_le_right _ _)
  rw [List.getElem_take] at hj
  rw [YoungDiagram.get_rowLens] at hj
  exact YoungDiagram.mem_iff_lt_rowLen.mpr hj

lemma truncatePartition_length {n : ℕ} (q : ℕ) (lam : Partition n) :
    (truncatePartition q lam).1.rowLens.length ≤ q := by
  rw [truncatePartition_rowLens, List.length_take]
  exact min_le_left _ _

def truncatedRemainder {u v : ℕ} (q l : ℕ) (α : Partition u) (β : Partition v) : ℕ :=
  l + (α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum

lemma truncated_size_eq {u v l n : ℕ} (q : ℕ) (α : Partition u) (β : Partition v)
    (h : u + v + l = n) :
    (α.1.rowLens.take q).sum + (β.1.rowLens.take q).sum +
      truncatedRemainder q l α β = n := by
  have hu := List.sum_take_add_sum_drop α.1.rowLens q
  have hv := List.sum_take_add_sum_drop β.1.rowLens q
  rw [partition_rowLens_sum] at hu hv
  dsimp [truncatedRemainder]
  omega

theorem signed_occurrence_truncate {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (ho : SignedOccurrence h α β γ lam) (q : ℕ) :
    ∃ γ' : Partition (truncatedRemainder q l α β),
      SignedOccurrence (truncated_size_eq q α β h)
        (truncatePartition q α) (truncatePartition q β) γ' lam :=
  signed_occurrence_subdiagrams ho _ _ (truncatePartition_le q α)
    (truncatePartition_le q β) _

theorem signed_moment_of_bounded_lengths {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {d r q : ℕ} (hd : 1 ≤ d) (hq : 0 < q)
    (hcost : coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1 ≤
      coefficient η d * Real.log q)
    (H : ∀ (lam : Partition (2 ^ d)) (u v l : ℕ) (h : u + v + l = 2 ^ d)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      α.1.rowLens.length ≤ q → β.1.rowLens.length ≤ q →
      SignedOccurrence h α β γ lam →
      logMoment (weightedMoment lam r) ≤
        ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal))
    (lam : Partition (2 ^ d)) (u v l : ℕ) (h : u + v + l = 2 ^ d)
    (α : Partition u) (β : Partition v) (γ : Partition l)
    (ho : SignedOccurrence h α β γ lam) :
    logMoment (weightedMoment lam r) ≤
      ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  obtain ⟨γ', hγ'⟩ := signed_occurrence_truncate ho q
  have hm := H lam _ _ _ _ _ _ γ' (truncatePartition_length q α)
    (truncatePartition_length q β) hγ'
  exact hm.trans (EReal.coe_le_coe_iff.mpr (truncated_budget_le hη hκ hd h α β hq hcost))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BalancedErrors
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Topology
open Filter

def sweepColors (d : ℕ) : ℕ := ⌈((2^d : ℕ) : ℝ)^((1:ℝ)/64)⌉₊

lemma sweepColors_pos (d : ℕ) : 0 < sweepColors d := by
  apply Nat.ceil_pos.mpr
  positivity

lemma sweepColors_le_size (d : ℕ) : sweepColors d ≤ 2^d := by
  apply Nat.ceil_le.mpr
  have hn : (1:ℝ) ≤ (2^d : ℕ) := by exact_mod_cast Nat.one_le_pow d 2 (by decide)
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)/64 ≤ 1)

lemma sweepColors_le_twice (d : ℕ) :
    (sweepColors d : ℝ) ≤ 2*((2^d : ℕ) : ℝ)^((1:ℝ)/64) := by
  have hn : (1:ℝ) ≤ (2^d : ℕ) := by exact_mod_cast Nat.one_le_pow d 2 (by decide)
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (2^d : ℕ)) ((1:ℝ)/64))
  have h1 := Real.one_le_rpow hn (by norm_num : (0:ℝ) ≤ 1/64)
  dsimp [sweepColors]
  linarith

lemma two_pow_rpow (d : ℕ) (a : ℝ) :
    ((2^d : ℕ) : ℝ)^a = Real.exp ((d:ℝ)*Real.log 2*a) := by
  rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < (2^d : ℕ)), nat_two_pow_log]

lemma two_pow_le_depth_rpow {k d : ℕ} {a : ℝ} (h : (k:ℝ) ≤ (d:ℝ)*a) :
    ((2^k : ℕ) : ℝ) ≤ ((2^d : ℕ) : ℝ)^a := by
  rw [two_pow_rpow, ← Real.exp_log (by positivity : (0:ℝ) < (2^k : ℕ)), nat_two_pow_log]
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right h (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))

lemma depth_rpow_le_two_pow {k d : ℕ} {a : ℝ} (h : (d:ℝ)*a ≤ (k:ℝ)) :
    ((2^d : ℕ) : ℝ)^a ≤ ((2^k : ℕ) : ℝ) := by
  rw [two_pow_rpow, ← Real.exp_log (by positivity : (0:ℝ) < (2^k : ℕ)), nat_two_pow_log]
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right h (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))

lemma balanced_depth_sizes {d : ℕ} (hd : 10 ≤ d) :
    d/2+childDepth d=d ∧
    ((2^d:ℕ):ℝ)^((1:ℝ)/3) ≤ ((2^(d/2):ℕ):ℝ) ∧
    ((2^d:ℕ):ℝ)^((1:ℝ)/3) ≤ ((2^(childDepth d):ℕ):ℝ) ∧
    ((2^(d/2):ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^((3:ℝ)/5) ∧
    ((2^(childDepth d):ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^((3:ℝ)/5) := by
  have hb : d/2+childDepth d=d := by unfold childDepth; omega
  have h₁ : d ≤ 3*(d/2) := by omega
  have h₂ : d ≤ 3*childDepth d := by unfold childDepth; omega
  have h₃ : 5*(d/2) ≤ 3*d := by omega
  have h₄ : 5*childDepth d ≤ 3*d := by unfold childDepth; omega
  have h₁' : (d:ℝ) ≤ 3*(d/2 : ℕ) := by exact_mod_cast h₁
  have h₂' : (d:ℝ) ≤ 3*(childDepth d : ℕ) := by exact_mod_cast h₂
  have h₃' : 5*(d/2 : ℕ) ≤ 3*(d:ℝ) := by exact_mod_cast h₃
  have h₄' : 5*(childDepth d : ℕ) ≤ 3*(d:ℝ) := by exact_mod_cast h₄
  exact ⟨hb, depth_rpow_le_two_pow (by linarith), depth_rpow_le_two_pow (by linarith),
    two_pow_le_depth_rpow (by linarith), two_pow_le_depth_rpow (by linarith)⟩

lemma cast_nat_sqrt_le {t : ℕ} : (Nat.sqrt t : ℝ) ≤ Real.sqrt t := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have h := Nat.sqrt_le t
  exact_mod_cast (by simpa only [pow_two] using h)

lemma typedLineError_bound {d t : ℕ}
    (ht : (t:ℝ) ≤ ((2^d:ℕ):ℝ)^((3:ℝ)/5)) :
    typedLineError t (sweepColors d) (16*2^d) ≤
      160*((2^d:ℕ):ℝ)^((3:ℝ)/10)*Real.log ((16*2^d : ℕ):ℝ) := by
  let N : ℝ := (2^d : ℕ)
  let W : ℝ := N^((3:ℝ)/10)
  have hn : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_pow d 2 (by decide)
  have hn0 : 0 < N := lt_of_lt_of_le zero_lt_one hn
  have hW : 1 ≤ W := Real.one_le_rpow hn (by norm_num)
  have hsqr : (Nat.sqrt t:ℝ) ≤ W := by
    calc
      _ ≤ Real.sqrt t := cast_nat_sqrt_le
      _ ≤ Real.sqrt (N^((3:ℝ)/5)) := Real.sqrt_le_sqrt ht
      _ = W := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]; norm_num [W]
  have hq : (sweepColors d:ℝ) ≤ 2*W :=
    (sweepColors_le_twice d).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)/64 ≤ 3/10)) (by norm_num))
  have hq2 : (sweepColors d:ℝ)^2 ≤ 4*W := by
    calc
      _ ≤ (2*N^((1:ℝ)/64))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (sweepColors_le_twice d) 2
      _ = 4*N^((1:ℝ)/32) := by rw [mul_pow, ← Real.rpow_natCast (N^((1:ℝ)/64)) 2, ← Real.rpow_mul hn0.le]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)/32 ≤ 3/10)) (by norm_num)
  have hlog : 1 ≤ Real.log ((16*2^d : ℕ):ℝ) := by
    have hN16 : (16:ℝ) ≤ (16*2^d : ℕ) := by rw [Nat.cast_mul, Nat.cast_ofNat]; change 16 ≤ 16*N; nlinarith
    have hl := Real.log_le_log (by norm_num : (0:ℝ) < 16) hN16
    have hl16 : Real.log 16 = 4*Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    rw [hl16] at hl
    linarith [Real.log_two_gt_d9]
  have hA : 6*(Nat.sqrt t:ℝ)+28*(sweepColors d:ℝ)^2+8*sweepColors d+2 ≤ 136*W := by
    nlinarith
  have hB : 8*(sweepColors d:ℝ)+1 ≤ 17*W := by linarith
  have hC := mul_le_mul_of_nonneg_right hA (show 0 ≤ Real.log ((16*2^d : ℕ):ℝ) by linarith)
  have hD := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 17*W by positivity)
  dsimp [typedLineError, localTraceError]
  change _ ≤ 160*W*Real.log ((16*2^d : ℕ):ℝ)
  nlinarith

lemma log_size_radius (d : ℕ) :
    Real.log ((16*2^d : ℕ):ℝ) = Real.log 16+(d:ℝ)*Real.log 2 := by
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity), nat_two_pow_log]

lemma depth_power_log_eventually {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      C*((2^d:ℕ):ℝ)^a*Real.log ((16*2^d : ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^b/2 := by
  let c := (b-a)*Real.log 2
  have hc : 0 < c := mul_pos (sub_pos.mpr hab) (Real.log_pos (by norm_num))
  have ht₁ := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp
    tendsto_natCast_atTop_atTop).const_mul (C*Real.log 2)
  have ht₀ := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp
    tendsto_natCast_atTop_atTop).const_mul (C*Real.log 16)
  have ht : Tendsto (fun d : ℕ => C*Real.log ((16*2^d : ℕ):ℝ)*((2^d:ℕ):ℝ)^(a-b)) atTop (𝓝 0) := by
    convert ht₁.add ht₀ using 1
    · funext d
      rw [log_size_radius, two_pow_rpow]
      have he : (d:ℝ)*Real.log 2*(a-b) = -c*d := by dsimp [c]; ring
      rw [he]
      simp only [Function.comp_apply, Real.rpow_one, Real.rpow_zero, one_mul]
      ring
    · simp
  filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ) < 1/2)] with d hd
  have hh := mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (2^d:ℕ)) b)
  have he : ((2^d:ℕ):ℝ)^(a-b)*((2^d:ℕ):ℝ)^b = ((2^d:ℕ):ℝ)^a := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < (2^d:ℕ))]
    congr 1
    ring
  rw [mul_assoc, he] at hh
  nlinarith only [hh]

lemma balanced_clipping_error {d : ℕ} (hd : 10 ≤ d) {κ : ℝ} (hκ : 0 ≤ κ) :
    holeClippingError (κ/2) (2^(d/2)) (2^(childDepth d)) ≤
      2*((2^d:ℕ):ℝ)^(1-κ/6)*Real.log ((16*2^d:ℕ):ℝ) := by
  obtain ⟨hadd,hsa, hmb,hsu,hmu⟩ := balanced_depth_sizes hd
  let N : ℝ := (2^d : ℕ)
  let S : ℝ := (2^(d/2) : ℕ)
  let M : ℝ := (2^(childDepth d) : ℕ)
  have hN : 0 < N := by positivity
  have hS : 0 < S := by positivity
  have hM : 0 < M := by positivity
  have hSM : S*M=N := by dsimp [S,M,N]; rw [← Nat.cast_mul, ← Nat.pow_add, hadd]
  have hpow (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x*y=N) (hlo : N^((1:ℝ)/3) ≤ x) :
      y*x^(1-κ/2) ≤ N^(1-κ/6) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN _) hlo
      (by linarith : -(κ/2) ≤ 0)
    rw [← Real.rpow_mul hN.le] at hh
    have he : (1:ℝ)/3*(-(κ/2)) = -(κ/6) := by ring
    rw [he] at hh
    calc
      _ = N*x^(-(κ/2)) := by
        rw [show 1-κ/2 = 1+(-(κ/2)) by ring, Real.rpow_add hx, Real.rpow_one]
        rw [← mul_assoc, mul_comm y x, hxy]
      _ ≤ N*N^(-(κ/6)) := mul_le_mul_of_nonneg_left hh hN.le
      _ = N^(1-κ/6) := by
        rw [show 1-κ/6=1+(-(κ/6)) by ring, Real.rpow_add hN, Real.rpow_one]
  have h₁ := hpow S M hS hM hSM hsa
  have h₂ := hpow M S hM hS (by rw [mul_comm]; exact hSM) hmb
  have hSlog : Real.log S ≤ Real.log ((16*2^d:ℕ):ℝ) := by
    apply Real.log_le_log hS
    have hSn : 2^(d/2) ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
    have hSn' : S ≤ N := by dsimp [S,N]; exact_mod_cast hSn
    rw [Nat.cast_mul, Nat.cast_ofNat]
    change S ≤ 16*N
    nlinarith
  have hMlog : Real.log M ≤ Real.log ((16*2^d:ℕ):ℝ) := by
    apply Real.log_le_log hM
    have hMn : 2^(childDepth d) ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
    have hMn' : M ≤ N := by dsimp [M,N]; exact_mod_cast hMn
    rw [Nat.cast_mul, Nat.cast_ofNat]
    change M ≤ 16*N
    nlinarith
  have hSz : 0 ≤ Real.log S := Real.log_nonneg (by dsimp [S]; exact_mod_cast Nat.one_le_pow (d/2) 2 (by decide))
  have hMz : 0 ≤ Real.log M := Real.log_nonneg (by dsimp [M]; exact_mod_cast Nat.one_le_pow (childDepth d) 2 (by decide))
  have hb₁ := mul_le_mul h₁ hSlog hSz (Real.rpow_nonneg hN.le _)
  have hb₂ := mul_le_mul h₂ hMlog hMz (Real.rpow_nonneg hN.le _)
  dsimp [holeClippingError]
  change M*S^(1-κ/2)*Real.log S+S*M^(1-κ/2)*Real.log M ≤ _
  linarith

theorem balanced_recurrence_error_eventually {κ ξ : ℝ} (hκ : 0 < κ)
    (hξ₁ : ξ < 1/10) (hξ₂ : ξ < κ/6) :
    ∃ D : ℕ, 10 ≤ D ∧ ∀ d ≥ D, ∀ (l : ℕ), l ≤ 2^d →
      ((2^(childDepth d):ℕ):ℝ)*typedLineError (2^(d/2)) (sweepColors d) (16*2^d)+
      ((2^(d/2):ℕ):ℝ)*typedLineError (2^(childDepth d)) (sweepColors d) (16*2^d)+
      holeClippingError (κ/2) (2^(d/2)) (2^(childDepth d))+
      (((2^(d/2):ℕ):ℝ)+((2^(childDepth d):ℕ):ℝ))*Real.log (l+1) ≤ ((2^d:ℕ):ℝ)^(1-ξ) := by
  have he₁ := depth_power_log_eventually (by linarith : (9:ℝ)/10 < 1-ξ) 322
  have he₂ := depth_power_log_eventually (by linarith : 1-κ/6 < 1-ξ) 2
  obtain ⟨D,hD⟩ := eventually_atTop.mp (he₁.and he₂)
  refine ⟨max D 10, le_max_right _ _, ?_⟩
  intro d hd l hl
  have hd10 : 10 ≤ d := (le_max_right _ _).trans hd
  obtain ⟨hadd,hsl,hml,hs,hm⟩ := balanced_depth_sizes hd10
  let N : ℝ := (2^d:ℕ)
  let L : ℝ := Real.log ((16*2^d:ℕ):ℝ)
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_pow d 2 (by decide)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hL : 0 ≤ L := Real.log_nonneg (by rw [Nat.cast_mul, Nat.cast_ofNat]; change 1 ≤ 16*N; nlinarith [hN])
  have hterms (t m : ℕ) (ht : (t:ℝ) ≤ N^((3:ℝ)/5)) (hm : (m:ℝ) ≤ N^((3:ℝ)/5)) :
      (m:ℝ)*typedLineError t (sweepColors d) (16*2^d) ≤ 160*N^((9:ℝ)/10)*L := by
    calc
      _ ≤ (m:ℝ)*(160*N^((3:ℝ)/10)*L) :=
        mul_le_mul_of_nonneg_left (typedLineError_bound ht) (Nat.cast_nonneg m)
      _ ≤ N^((3:ℝ)/5)*(160*N^((3:ℝ)/10)*L) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by
        rw [show N^((3:ℝ)/5)*(160*N^((3:ℝ)/10)*L) =
          160*(N^((3:ℝ)/5)*N^((3:ℝ)/10))*L by ring, ← Real.rpow_add hN0]
        norm_num
  have hH := hterms (2^(d/2)) (2^(childDepth d)) hs hm
  have hK := hterms (2^(childDepth d)) (2^(d/2)) hm hs
  have hlog : Real.log ((l:ℝ)+1) ≤ L := by
    apply Real.log_le_log (by positivity)
    have hl' : (l:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hl
    rw [Nat.cast_mul, Nat.cast_ofNat]
    change (l:ℝ)+1 ≤ 16*N
    nlinarith
  have hsum : ((2^(d/2):ℕ):ℝ)+((2^(childDepth d):ℕ):ℝ) ≤ 2*N^((9:ℝ)/10) := by
    have hb := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (3:ℝ)/5 ≤ 9/10)
    linarith
  have hhist := mul_le_mul hsum hlog (Real.log_nonneg (by linarith [show (0:ℝ) ≤ l by positivity] : (1:ℝ) ≤ (l:ℝ)+1))
    (by positivity : 0 ≤ 2*N^((9:ℝ)/10))
  have hclip := balanced_clipping_error hd10 hκ.le
  obtain ⟨he₁,he₂⟩ := hD d ((le_max_left _ _).trans hd)
  change _ ≤ N^(1-ξ)
  change _ ≤ 2*N^(1-κ/6)*L at hclip
  change 322*N^((9:ℝ)/10)*L ≤ N^(1-ξ)/2 at he₁
  change 2*N^(1-κ/6)*L ≤ N^(1-ξ)/2 at he₂
  linarith

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.UniformMoment
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma coefficient_mono_depth {η : ℝ} (hη : 0 ≤ η) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) : coefficient η a ≤ coefficient η b := by
  have hroot : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < a by omega))
  have hroots : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt (by exact_mod_cast hab)
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*Real.sqrt a)
    (mul_le_mul_of_nonneg_left hroots (by norm_num : (0:ℝ) ≤ 2))
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hi 1) hη

lemma signed_sweep_recurrence_depth_sum {d a b j q R : ℕ} (hab : a+b=d) (hq : 0 < q)
    {η τ κ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    (HA : ∀ (lam : Partition (2^a)) (u v l : ℕ) (h : u+v+l=2^a)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^a) l))
    (HB : ∀ (lam : Partition (2^b)) (u v l : ℕ) (h : u+v+l=2^b)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^b) l))
    (hR : 2*max (2^a) (2^b)+2*q+1 ≤ R)
    (lam : Partition (2^d)) (u v l : ℕ) (h : u+v+l=2^d)
    (α : Partition u) (β : Partition v) (γ : Partition l)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (ho : SignedOccurrence h α β γ lam) :
    weightedMoment lam (2^j) ≤ Real.exp (η*signedEntropy α β+
      τ*l*Real.log (2^d : ℕ)-(l:ℝ)*Real.log ((2^d : ℕ)/ (l:ℝ))+6*l+
      (2^b : ℕ)*typedLineError (2^a) q R+(2^a : ℕ)*typedLineError (2^b) q R+
      holeClippingError κ (2^a) (2^b)+((2^a : ℕ)+(2^b : ℕ) : ℝ)*Real.log (l+1)) := by
  subst d
  exact signed_sweep_recurrence hq hη hη' hκ hκτ HA HB hR lam u v l h α β γ hα hβ ho

theorem signed_occurrence_moment_bound_fixed_oai {η κ : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hsmall : κ < η/256) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ d : ℕ, 1 ≤ d →
      ∀ lam : Partition (2^d), ∀ (u v l : ℕ) (h : u+v+l=2^d)
        (α : Partition u) (β : Partition v) (γ : Partition l),
        SignedOccurrence h α β γ lam →
        logMoment (weightedMoment lam r) ≤
          ((coefficient η d*signedEntropy α β+remainderBudget κ d l : ℝ) : EReal) := by
  let ξ : ℝ := min (1/64) (κ/16)
  let δ : ℝ := ξ/4
  have hξ : 0 < ξ := lt_min (by norm_num) (by positivity)
  have hξ₁ : ξ < 1/10 := (min_le_left _ _).trans_lt (by norm_num)
  have hξ₂ : ξ < κ/6 := (min_le_right _ _).trans_lt (by nlinarith)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hδξ : δ < ξ := by dsimp [δ]; linarith
  obtain ⟨D₁,hD₁,herr⟩ := balanced_recurrence_error_eventually hκ hξ₁ hξ₂
  obtain ⟨D₂,_hD₂,hclose⟩ := nonsparse_closing_budget hη hκ (by norm_num : (0:ℝ) ≤ 6) hδ1 hδξ
  obtain ⟨D₃,_hD₃,hcost⟩ := truncation_coefficient_eventually hη hκ.le
    (by norm_num : (0:ℝ) < 1/64) (by nlinarith : κ < η*((1:ℝ)/64)/2)
  let D := max D₁ (max D₂ D₃)
  obtain ⟨r₀,_hr₀,hbase⟩ := signed_occurrence_moment_bound_proved_ranges D hδ hη.le κ
  have hr : r₀ ≤ 2^r₀ := Nat.lt_two_pow_self.le
  refine ⟨2^r₀, Nat.one_le_pow r₀ 2 (by decide), ?_⟩
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hdD : d ≤ D
    · intro lam u v l h α β γ ho
      exact hbase (2^r₀) hr d hd lam (Or.inl hdD) u v l h α β γ ho
    have hlarge : D ≤ d := le_of_not_ge hdD
    have hd10 : 10 ≤ d := hD₁.trans ((le_max_left _ _).trans hlarge)
    have hd₁ : D₁ ≤ d := (le_max_left _ _).trans hlarge
    have hd₂ : D₂ ≤ d := (le_max_left D₂ D₃).trans ((le_max_right _ _).trans hlarge)
    have hd₃ : D₃ ≤ d := (le_max_right D₂ D₃).trans ((le_max_right _ _).trans hlarge)
    have hab : d/2+childDepth d=d := (balanced_depth_sizes hd10).1
    have ha1 : 1 ≤ d/2 := by omega
    have hb1 : 1 ≤ childDepth d := by unfold childDepth; omega
    have hab' : d/2 ≤ childDepth d := by unfold childDepth; omega
    have had : d/2 < d := by omega
    have hbd : childDepth d < d := by omega
    have hlocal (e : ℕ) (he1 : 1 ≤ e) (heb : e ≤ childDepth d) (hed : e < d) :
        ∀ (lam : Partition (2^e)) (u v l : ℕ) (h : u+v+l=2^e)
          (α : Partition u) (β : Partition v) (γ : Partition l),
          SignedOccurrence h α β γ lam → weightedMoment lam (2^r₀) ≤
            Real.exp (coefficient η (childDepth d)*signedEntropy α β+
              clippedBudget (coefficient κ (childDepth d)) (2^e) l) := by
      intro lam u v l h α β γ ho
      have hi := (logMoment_le_iff (weightedMoment_nonneg lam (2^r₀))).mp
        (ih e hed he1 lam u v l h α β γ ho)
      rw [remainderBudget_eq_clippedBudget] at hi
      apply hi.trans (Real.exp_le_exp.mpr _)
      exact add_le_add (mul_le_mul_of_nonneg_right (coefficient_mono_depth hη.le he1 heb)
        (signedEntropy_nonneg α β))
        (clippedBudget_mono (coefficient_mono_depth hκ.le he1 heb) (Nat.one_le_pow e 2 (by decide)))
    have HA := hlocal (d/2) ha1 hab' had
    have HB := hlocal (childDepth d) hb1 le_rfl hbd
    have hηc : 0 ≤ coefficient η (childDepth d) :=
      (by positivity : (0:ℝ) ≤ η/2).trans (coefficient_bounds hη.le hb1).1
    have hηc1 : coefficient η (childDepth d) ≤ 1 := (coefficient_bounds hη.le hb1).2.trans hη1.le
    have hκc : κ/2 ≤ coefficient κ (childDepth d) := (coefficient_bounds hκ.le hb1).1
    have hR : 2*max (2^(d/2)) (2^(childDepth d))+2*sweepColors d+1 ≤ 16*2^d := by
      have haN : 2^(d/2) ≤ 2^d := Nat.pow_le_pow_right (by decide) had.le
      have hbN : 2^(childDepth d) ≤ 2^d := Nat.pow_le_pow_right (by decide) hbd.le
      have hqN := sweepColors_le_size d
      have hn : 1 ≤ 2^d := Nat.one_le_pow d 2 (by decide)
      have hmax : max (2^(d/2)) (2^(childDepth d)) ≤ 2^d := max_le haN hbN
      omega
    apply signed_moment_of_bounded_lengths hη.le hκ.le hd (sweepColors_pos d) (hcost d hd₃)
    intro lam u v l h α β γ hα hβ ho
    by_cases hk : ((2^d-lam.1.rowLen 0 : ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^(1-δ)
    · exact hbase (2^r₀) hr d hd lam (Or.inr (Or.inl hk)) u v l h α β γ ho
    by_cases hc : 2^d/2 < lam.1.colLen 0
    · exact hbase (2^r₀) hr d hd lam (Or.inr (Or.inr (Or.inr hc))) u v l h α β γ ho
    have hcol : lam.1.colLen 0 ≤ 2^d/2 := le_of_not_gt hc
    have hlevel : ((2^d:ℕ):ℝ)^(1-δ) ≤ ((2^d-lam.1.rowLen 0 : ℕ):ℝ) := (lt_of_not_ge hk).le
    have hlengthα : α.1.colLen 0 ≤ sweepColors d := by simpa only [YoungDiagram.length_rowLens] using hα
    have hlengthβ : β.1.colLen 0 ≤ sweepColors d := by simpa only [YoungDiagram.length_rowLens] using hβ
    have hrec := signed_sweep_recurrence_depth_sum hab (sweepColors_pos d) hηc hηc1
      (by positivity : (0:ℝ) ≤ κ/2) hκc HA HB hR lam u v l h α β γ hlengthα hlengthβ ho
    have he := herr d hd₁ l (by omega)
    have hb := hclose d hd₂ lam hcol hlevel u v l h α β γ ho
    apply (logMoment_le_iff (weightedMoment_nonneg lam (2^r₀))).mpr
    apply hrec.trans (Real.exp_le_exp.mpr _)
    have hn : 0 ≤ ((2^d:ℕ):ℝ)^(1-ξ) := Real.rpow_nonneg (by positivity) _
    linarith

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.signed_occurrence_moment_bound_fixed_oai := @OAI.SignedSweeps.signed_occurrence_moment_bound_fixed_oai
