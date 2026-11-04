-- Prove2me | solution 1 for OAI.SignedSweeps.signed_sweep_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:10:11.301537+00:00
-- url     : https://prove2.me/submissions/4cf486c0-2db1-4105-be47-24a6e837659d

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2
import Theorems.Thm_OAI_SignedSweeps_occupied_sweep_trace_bound
import Theorems.Thm_OAI_SignedSweeps_signed_occurrence_marked_trace

section
-- module OAI.Probability.SignedSweeps.Model
namespace TensorProduct

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

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

lemma row_part_le_size {n a : ℕ} (lam : Partition n) (ha : a ∈ lam.1.rowLens) : a ≤ n := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  rw [YoungDiagram.rowLen_eq_card]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2

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

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma spechtRepresentation_norm {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (x : Specht lam) : ‖spechtRepresentation lam g x‖ = ‖x‖ := by
  let x' : (spechtSubrepresentation lam).toSubmodule := x
  change ‖regularIsometry g (x' : RegularSpace n)‖ = ‖(x' : RegularSpace n)‖
  exact (regularIsometry g).norm_map _

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
-- module OAI.Probability.SignedSweeps.HoleEntropy
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma occupancy_sum {l q : ℕ} (f : Fin l → Fin q) :
    ∑ j, (occupancy f j).val = l := by
  simpa [occupancy] using
    Finset.sum_fiberwise' Finset.univ f (fun _ : Fin q => (1 : ℕ))

lemma occupancy_at_pos {l q : ℕ} (f : Fin l → Fin q) (i : Fin l) :
    0 < (occupancy f (f i)).val := by
  change 0 < (Finset.univ.filter (fun j => f j = f i)).card
  exact Finset.card_pos.mpr ⟨i, by simp⟩

lemma occupancy_sum_smul {l q : ℕ} (f : Fin l → Fin q) (a : Fin q → ℝ) :
    ∑ j, ((occupancy f j).val : ℝ) * a j = ∑ i, a (f i) := by
  simpa [occupancy] using Finset.sum_fiberwise' Finset.univ f a

def occupancyEntropy {l q : ℕ} (a : ℝ) (f : Fin l → Fin q) : ℝ :=
  ∑ j, ((occupancy f j).val : ℝ) * Real.log (a / (occupancy f j).val)

def empiricalDensity {l q : ℕ} (f : Fin l → Fin q) (j : Fin q) : ℝ :=
  (occupancy f j).val / (l : ℝ)

lemma empiricalDensity_nonneg {l q : ℕ} (f : Fin l → Fin q) (j : Fin q) :
    0 ≤ empiricalDensity f j := by unfold empiricalDensity; positivity

lemma empiricalDensity_sum {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q) :
    ∑ j, empiricalDensity f j = 1 := by
  unfold empiricalDensity
  rw [← Finset.sum_div, ← Nat.cast_sum, occupancy_sum, div_self]
  exact_mod_cast hl.ne'

lemma empiricalDensity_at_pos {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q) (i : Fin l) :
    0 < empiricalDensity f (f i) := by
  unfold empiricalDensity
  exact div_pos (by exact_mod_cast occupancy_at_pos f i) (by exact_mod_cast hl)

lemma empiricalDensity_total {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q) :
    ∑ g : Fin l → Fin q, ∏ i, empiricalDensity f (g i) = 1 := by
  rw [← Fintype.sum_pow, empiricalDensity_sum hl f, one_pow]

lemma occupancy_entropy_weight {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q)
    {a : ℝ} (ha : 0 < a) :
    Real.exp (-occupancyEntropy a f) =
      Real.exp (-(l : ℝ) * Real.log (a / l)) * ∏ i, empiricalDensity f (f i) := by
  have hn : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have halog : ∀ i, Real.log (a / (occupancy f (f i)).val) =
      Real.log (a / l) - Real.log (empiricalDensity f (f i)) := by
    intro i
    have hh : ((occupancy f (f i)).val : ℝ) ≠ 0 := by
      exact_mod_cast (occupancy_at_pos f i).ne'
    rw [empiricalDensity, Real.log_div ha.ne' hh, Real.log_div ha.ne' hn,
      Real.log_div hh hn]
    ring
  have hd : -occupancyEntropy a f =
      -(l : ℝ) * Real.log (a / l) + ∑ i, Real.log (empiricalDensity f (f i)) := by
    unfold occupancyEntropy
    rw [occupancy_sum_smul]
    simp_rw [halog]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hd, Real.exp_add, Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact Real.exp_log (empiricalDensity_at_pos hl f i)

lemma occupancy_entropy_fiber_bound {l q : ℕ} (hl : 0 < l)
    {a : ℝ} (ha : 0 < a) (h : Fin q → Fin (l + 1)) :
    ∑ f : Fin l → Fin q with occupancy f = h, Real.exp (-occupancyEntropy a f) ≤
      Real.exp (-(l : ℝ) * Real.log (a / l)) := by
  classical
  let S := Finset.univ.filter (fun f : Fin l → Fin q => occupancy f = h)
  change ∑ f ∈ S, _ ≤ _
  rcases Finset.eq_empty_or_nonempty S with hempty | ⟨f, hf⟩
  · simp only [hempty, Finset.sum_empty]
    exact (Real.exp_pos _).le
  · have hh : occupancy f = h := (Finset.mem_filter.mp hf).2
    have he (g : Fin l → Fin q) (hg : g ∈ S) : empiricalDensity g = empiricalDensity f := by
      have hhg := (Finset.mem_filter.mp hg).2
      funext j
      simp only [empiricalDensity, hhg, hh]
    calc
      _ = Real.exp (-(l : ℝ) * Real.log (a / l)) *
          ∑ g ∈ S, ∏ i, empiricalDensity f (g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [occupancy_entropy_weight hl g ha, he g hg]
      _ ≤ Real.exp (-(l : ℝ) * Real.log (a / l)) *
          ∑ g : Fin l → Fin q, ∏ i, empiricalDensity f (g i) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun g hg hgn => Finset.prod_nonneg (fun i hi => empiricalDensity_nonneg f (g i)))
      _ = _ := by rw [empiricalDensity_total hl f, mul_one]

lemma occupancy_entropy_sum {l q : ℕ} {a : ℝ} (ha : 0 < a) :
    ∑ f : Fin l → Fin q, Real.exp (-occupancyEntropy a f) ≤
      Real.exp (-(l : ℝ) * Real.log (a / l)) * (l + 1 : ℝ) ^ q := by
  classical
  by_cases hl : l = 0
  · subst l
    simp [occupancyEntropy, occupancy]
  · have hl' : 0 < l := Nat.pos_of_ne_zero hl
    rw [← Finset.sum_fiberwise Finset.univ occupancy
      (fun f : Fin l → Fin q => Real.exp (-occupancyEntropy a f))]
    apply (Finset.sum_le_sum (fun h _ => occupancy_entropy_fiber_bound hl' ha h)).trans_eq
    simp [mul_comm]

def holeLineEntropy {s m l : ℕ} (z : Fin l → Fin s × Fin m) : ℝ :=
  occupancyEntropy (s : ℝ) (fun i => (z i).2) +
    occupancyEntropy (m : ℝ) (fun i => (z i).1)

lemma hole_entropy_with_replacement {s m l : ℕ} :
    ∑ z : Fin l → Fin s × Fin m, Real.exp (-holeLineEntropy z) =
      (∑ rows : Fin l → Fin s, Real.exp (-occupancyEntropy (m : ℝ) rows)) *
      (∑ cols : Fin l → Fin m, Real.exp (-occupancyEntropy (s : ℝ) cols)) := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Fin l) (fun _ => Fin s) (fun _ => Fin m)
  calc
    _ = ∑ p : (Fin l → Fin s) × (Fin l → Fin m),
        Real.exp (-occupancyEntropy (m : ℝ) p.1) *
          Real.exp (-occupancyEntropy (s : ℝ) p.2) := by
      apply Fintype.sum_equiv e
      intro z
      change Real.exp (-(occupancyEntropy (s : ℝ) (fun i => (z i).2) +
        occupancyEntropy (m : ℝ) (fun i => (z i).1))) = _
      rw [neg_add, Real.exp_add, mul_comm]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun rows : Fin l → Fin s => Real.exp (-occupancyEntropy (m : ℝ) rows))
        (fun cols : Fin l → Fin m => Real.exp (-occupancyEntropy (s : ℝ) cols))).symm

lemma hole_entropy_drop_distinctness {s m l : ℕ} :
    ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1) ≤
      ∑ z : Fin l → Fin s × Fin m, Real.exp (-holeLineEntropy z) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun z : Fin l → Fin s × Fin m =>
    Function.Injective z)) (by simp) (fun z => Real.exp (-holeLineEntropy z))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun z hz hzn => (Real.exp_pos _).le)

lemma inverse_pow_eq_exp_log {x : ℝ} (hx : 0 < x) (l : ℕ) :
    (x ^ l)⁻¹ = Real.exp (-(l : ℝ) * Real.log x) := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx]

lemma hole_assignment_entropy_bound {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) :
    (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1) ≤
      Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l)) *
        (l + 1 : ℝ) ^ (s + m) := by
  classical
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hl : l = 0
  · subst l
    simp [holeLineEntropy, occupancyEntropy, occupancy, HolePlacement]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hl' : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl
  have hn : (0 : ℝ) < (s * m : ℕ) := by exact_mod_cast Nat.mul_pos hs hm
  have hf : (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        (Real.exp (-(l : ℝ) * Real.log ((m : ℝ) / l)) * (l + 1 : ℝ) ^ s) *
        (Real.exp (-(l : ℝ) * Real.log ((s : ℝ) / l)) * (l + 1 : ℝ) ^ m) =
      Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l)) *
        (l + 1 : ℝ) ^ (s + m) := by
    rw [inverse_pow_eq_exp_log hn, pow_add]
    calc
      _ = (Real.exp (-(l : ℝ) * Real.log ((s * m : ℕ) : ℝ)) *
          Real.exp (-(l : ℝ) * Real.log ((m : ℝ) / l)) *
          Real.exp (-(l : ℝ) * Real.log ((s : ℝ) / l))) *
            ((l + 1 : ℝ) ^ s * (l + 1 : ℝ) ^ m) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [Nat.cast_mul, Real.log_mul hs'.ne' hm'.ne',
          Real.log_div hm'.ne' hl'.ne', Real.log_div hs'.ne' hl'.ne',
          Real.log_div (mul_pos hs' hm').ne' hl'.ne', Real.log_mul hs'.ne' hm'.ne']
        ring
  calc
    _ ≤ (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : Fin l → Fin s × Fin m, Real.exp (-holeLineEntropy z) :=
      mul_le_mul_of_nonneg_left hole_entropy_drop_distinctness (by positivity)
    _ = (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ((∑ rows : Fin l → Fin s, Real.exp (-occupancyEntropy (m : ℝ) rows)) *
          ∑ cols : Fin l → Fin m, Real.exp (-occupancyEntropy (s : ℝ) cols)) := by
      rw [hole_entropy_with_replacement]
    _ ≤ (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ((Real.exp (-(l : ℝ) * Real.log ((m : ℝ) / l)) * (l + 1 : ℝ) ^ s) *
          (Real.exp (-(l : ℝ) * Real.log ((s : ℝ) / l)) * (l + 1 : ℝ) ^ m)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (occupancy_entropy_sum hm') (occupancy_entropy_sum hs')
        (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)) (by positivity)
    _ = _ := by rw [← mul_assoc, hf]

lemma hole_assignment_entropy_bound_exp {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) :
    (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1) ≤
      Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l) +
        (s + m : ℝ) * Real.log (l + 1)) := by
  refine (hole_assignment_entropy_bound hs hm).trans_eq ?_
  rw [Real.exp_add, show (s + m : ℝ) = ((s + m : ℕ) : ℝ) by norm_cast,
    Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < l + 1)]

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

lemma clippedBudget_le_unclipped {κ τ : ℝ} (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    {a : ℕ} (ha : 0 < a) (h : ℕ) :
    clippedBudget τ a h ≤
      τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h) +
        (a : ℝ) ^ (1 - κ) * Real.log a := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hal : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have he : 0 ≤ (a : ℝ) ^ (1 - κ) * Real.log a :=
    mul_nonneg (Real.rpow_nonneg hap.le _) hal
  have hτ : 0 ≤ τ := hκ.trans hκτ
  unfold clippedBudget
  by_cases hf : 0 ≤ τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h)
  · rw [max_eq_right hf]
    linarith
  · rw [max_eq_left (le_of_not_ge hf)]
    have hh0 : h ≠ 0 := by intro hh; subst h; simp at hf
    have hhp : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh0
    have hlog : Real.log (h : ℝ) ≤ (1 - κ) * Real.log a := by
      have hb : τ * Real.log a < Real.log ((a : ℝ) / h) := by
        nlinarith
      rw [Real.log_div hap.ne' hhp.ne'] at hb
      nlinarith [mul_nonneg (sub_nonneg.mpr hκτ) hal]
    have hh : (h : ℝ) ≤ (a : ℝ) ^ (1 - κ) := by
      rw [Real.rpow_def_of_pos hap, ← Real.exp_log hhp]
      exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hlog)
    have hd : Real.log ((a : ℝ) / h) ≤ Real.log a := by
      rw [Real.log_div hap.ne' hhp.ne']
      have hhl : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hh0)
      linarith
    have ht : 0 ≤ τ * h * Real.log a := by positivity
    have h₁ := mul_le_mul_of_nonneg_left hd hhp.le
    have h₂ := mul_le_mul_of_nonneg_right hh hal
    linarith

lemma line_budgets_le {κ τ : ℝ} (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) (z : Fin l → Fin s × Fin m) :
    (∑ j : Fin m, clippedBudget τ s (occupancy (fun i => (z i).2) j).val) +
      (∑ j : Fin s, clippedBudget τ m (occupancy (fun i => (z i).1) j).val) ≤
      τ * l * Real.log ((s * m : ℕ) : ℝ) - holeLineEntropy z +
        (m : ℝ) * (s : ℝ) ^ (1 - κ) * Real.log s +
        (s : ℝ) * (m : ℝ) ^ (1 - κ) * Real.log m := by
  classical
  have hc := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    clippedBudget_le_unclipped hκ hκτ hs (occupancy (fun i => (z i).2) j).val)
  have hr := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) =>
    clippedBudget_le_unclipped hκ hκτ hm (occupancy (fun i => (z i).1) j).val)
  refine (add_le_add hc hr).trans_eq ?_
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Nat.cast_sum, occupancy_sum]
  simp only [holeLineEntropy, occupancyEntropy, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hs.ne' : (s : ℝ) ≠ 0)
      (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)]
  ring

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.FallingFactorials
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma descFactorial_exp_lower {a h : ℕ} (ha : 0 < a) (hh : h ≤ a) :
    (a : ℝ) ^ h * Real.exp (-2 * (h : ℝ)) ≤ (a.descFactorial h : ℝ) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  by_cases hsmall : 2 * h ≤ a
  · have hsub : (a : ℝ) / 2 ≤ ((a + 1 - h : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have : (2 : ℝ) * h ≤ a := by exact_mod_cast hsmall
      linarith
    have hexp : Real.exp (-2) ≤ (1 : ℝ) / 2 := by
      rw [Real.exp_neg]
      have he : 2 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he
    calc
      _ = ((a : ℝ) * Real.exp (-2)) ^ h := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ ((a : ℝ) / 2) ^ h :=
        pow_le_pow_left₀ (by positivity)
          (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hexp hap.le) h
      _ ≤ (((a + 1 - h : ℕ) : ℝ)) ^ h := pow_le_pow_left₀ (by positivity) hsub h
      _ ≤ _ := by exact_mod_cast Nat.pow_sub_le_descFactorial a h
  · have hlarge : a ≤ 2 * h := by omega
    have hf : ((a - h).factorial : ℝ) ≤ (a : ℝ) ^ (a - h) := by
      exact_mod_cast (Nat.factorial_le_pow (a - h)).trans
        (Nat.pow_le_pow_left (Nat.sub_le a h) (a - h))
    have hfac : ((a - h).factorial : ℝ) * (a.descFactorial h : ℝ) = (a.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hh
    have he : (a : ℝ) ^ a ≤ Real.exp a * (a.factorial : ℝ) := by
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < a.factorial)).mp
        (Real.pow_div_factorial_le_exp (a : ℝ) hap.le a)
    have h₁ : (a : ℝ) ^ (a - h) * (a : ℝ) ^ h ≤
        (a : ℝ) ^ (a - h) * (Real.exp a * (a.descFactorial h : ℝ)) := by
      calc
        _ = (a : ℝ) ^ a := by rw [← pow_add, Nat.sub_add_cancel hh]
        _ ≤ Real.exp a * (a.factorial : ℝ) := he
        _ = Real.exp a * (((a - h).factorial : ℝ) * (a.descFactorial h : ℝ)) := by rw [hfac]
        _ ≤ Real.exp a * ((a : ℝ) ^ (a - h) * (a.descFactorial h : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf (by positivity)) (by positivity)
        _ = _ := by ring
    have h₂ := le_of_mul_le_mul_left h₁ (pow_pos hap (a - h))
    calc
      _ ≤ (a : ℝ) ^ h * Real.exp (-(a : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        have : (a : ℝ) ≤ 2 * h := by exact_mod_cast hlarge
        linarith
      _ ≤ (Real.exp a * (a.descFactorial h : ℝ)) * Real.exp (-(a : ℝ)) :=
        mul_le_mul_of_nonneg_right h₂ (by positivity)
      _ = _ := by rw [Real.exp_neg]; field_simp

lemma descFactorial_inv_upper {a h : ℕ} (ha : 0 < a) (hh : h ≤ a) :
    (a.descFactorial h : ℝ)⁻¹ ≤ ((a : ℝ) ^ h)⁻¹ * Real.exp (2 * (h : ℝ)) := by
  have hf : (0 : ℝ) < a.descFactorial h := by
    exact_mod_cast Nat.descFactorial_pos.mpr hh
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    _ ≤ ((a : ℝ) ^ h * Real.exp (-2 * (h : ℝ)))⁻¹ :=
      (inv_le_inv₀ hf (by positivity)).mpr (descFactorial_exp_lower ha hh)
    _ = _ := by
      rw [mul_inv_rev, ← Real.exp_neg, mul_comm, show -(-2 * (h : ℝ)) = 2 * h by ring]

lemma occupancy_col_le {s m l : ℕ} (z : HolePlacement s m l) (j : Fin m) :
    (occupancy (fun i => (z.1 i).2) j).val ≤ s := by
  classical
  change (Finset.univ.filter (fun i => (z.1 i).2 = j)).card ≤ s
  calc
    _ ≤ (Finset.univ : Finset (Fin s)).card := ?_
    _ = s := by simp

  refine Finset.card_le_card_of_injOn (fun i => (z.1 i).1) (by simp) ?_
  intro i hi k hk heq
  apply z.2
  exact Prod.ext heq ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm)

lemma occupancy_row_le {s m l : ℕ} (z : HolePlacement s m l) (j : Fin s) :
    (occupancy (fun i => (z.1 i).1) j).val ≤ m := by
  classical
  change (Finset.univ.filter (fun i => (z.1 i).1 = j)).card ≤ m
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card := ?_
    _ = m := by simp

  refine Finset.card_le_card_of_injOn (fun i => (z.1 i).2) (by simp) ?_
  intro i hi k hk heq
  apply z.2
  exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm) heq

lemma occupancy_factorial_bound {a l q : ℕ} (ha : 0 < a) (f : Fin l → Fin q)
    (hf : ∀ j, (occupancy f j).val ≤ a) :
    (∏ j, (a.descFactorial (occupancy f j).val : ℝ)⁻¹) ≤
      ((a : ℝ) ^ l)⁻¹ * Real.exp (2 * (l : ℝ)) := by
  classical
  refine (Finset.prod_le_prod (fun _ _ => by positivity)
    (fun j _ => descFactorial_inv_upper ha (hf j))).trans_eq ?_
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum,
    occupancy_sum, ← Real.exp_sum, ← Finset.mul_sum, ← Nat.cast_sum, occupancy_sum]

lemma holePrefactor_bound {s m l : ℕ} (hs : 0 < s) (hm : 0 < m)
    (z : HolePlacement s m l) :
    holePrefactor z ≤ (((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (4 * (l : ℝ)) := by
  unfold holePrefactor
  refine (mul_le_mul
    (occupancy_factorial_bound hs (fun i => (z.1 i).2) (occupancy_col_le z))
    (occupancy_factorial_bound hm (fun i => (z.1 i).1) (occupancy_row_le z))
    (Finset.prod_nonneg (fun _ _ => by positivity)) (by positivity)).trans_eq ?_
  rw [Nat.cast_mul, mul_pow, mul_inv_rev]
  calc
    _ = (((s : ℝ) ^ l)⁻¹ * ((m : ℝ) ^ l)⁻¹) *
        (Real.exp (2 * (l : ℝ)) * Real.exp (2 * (l : ℝ))) := by ring
    _ = _ := by
      rw [← Real.exp_add, show 2 * (l : ℝ) + 2 * l = 4 * l by ring]
      ring

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HoleCount
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def holeTraceSum (τ : ℝ) (s m l : ℕ) : ℝ :=
  ∑ z : HolePlacement s m l, holePrefactor z * Real.exp (holeBudget τ z.1)

lemma holeTraceSum_bound {κ τ : ℝ} (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) :
    holeTraceSum τ s m l ≤ Real.exp
      (τ * l * Real.log ((s * m : ℕ) : ℝ) -
        2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l) + 4 * l +
        holeClippingError κ s m + (s + m : ℝ) * Real.log (l + 1)) := by
  classical
  let A := 4 * (l : ℝ) + τ * l * Real.log ((s * m : ℕ) : ℝ) + holeClippingError κ s m
  have hz (z : HolePlacement s m l) :
      holePrefactor z * Real.exp (holeBudget τ z.1) ≤
        Real.exp A * ((((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (-holeLineEntropy z.1)) := by
    have hb : holeBudget τ z.1 ≤
        τ * l * Real.log ((s * m : ℕ) : ℝ) - holeLineEntropy z.1 + holeClippingError κ s m := by
      simpa only [holeBudget, holeClippingError, add_assoc] using line_budgets_le hκ hκτ hs hm z.1
    calc
      _ ≤ ((((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (4 * (l : ℝ))) *
          Real.exp (τ * l * Real.log ((s * m : ℕ) : ℝ) - holeLineEntropy z.1 +
            holeClippingError κ s m) :=
        mul_le_mul (holePrefactor_bound hs hm z) (Real.exp_le_exp.mpr hb)
          (Real.exp_pos _).le (by positivity)
      _ = _ := by
        simp only [A, Real.exp_add, Real.exp_sub, Real.exp_neg]
        ring
  calc
    _ ≤ ∑ z : HolePlacement s m l,
        Real.exp A * ((((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (-holeLineEntropy z.1)) :=
      Finset.sum_le_sum (fun z _ => hz z)
    _ = Real.exp A * ((((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.exp A * Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l) +
        (s + m : ℝ) * Real.log (l + 1)) :=
      mul_le_mul_of_nonneg_left (hole_assignment_entropy_bound_exp hs hm) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [A]
      ring

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

def partsEntropy (total : ℝ) (L : List ℕ) : ℝ :=
  (L.map (fun a : ℕ => (a : ℝ) * Real.log (total / a))).sum

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

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.UniquePaths
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma coordinateSubgroup_bit {d : ℕ} {i : Fin d} (g : coordinateSubgroup d i)
    (x : Fin (2 ^ d)) (j : Fin d) (hji : j ≠ i) :
    (positionsEquiv d).symm (g.1 x) j = (positionsEquiv d).symm x j :=
  congrFun (g.property x) ⟨j,hji⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.KernelTransition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma unitary_representation_adjoint {G : Type*} [Group G] (ρ : Representation ℂ G E)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (g : G) : (ρ g).adjoint = ρ g⁻¹ := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact representation_inner_inverse ρ hρ g y x

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MomentMonotonicity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma power_on_eigenvector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) {x : E} {c : ℂ} (hx : T x = c • x) (r : ℕ) :
    (T ^ r) x = c ^ r • x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SpectralAngle
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma quadratic_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) :
    (inner ℂ x (T x)).re = ∑ i : Fin (Module.finrank ℂ E),
      hT.eigenvalues rfl i * ‖inner ℂ (hT.eigenvectorBasis rfl i) x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner x (T x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hT (hT.eigenvectorBasis rfl i) x, hT.apply_eigenvectorBasis,
    inner_smul_left, RCLike.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
  rw [show inner ℂ x (hT.eigenvectorBasis rfl i) *
      ((hT.eigenvalues rfl i : ℂ) * inner ℂ (hT.eigenvectorBasis rfl i) x) =
      (hT.eigenvalues rfl i : ℂ) * (inner ℂ (hT.eigenvectorBasis rfl i) x *
        inner ℂ x (hT.eigenvectorBasis rfl i)) by ring,
    ← inner_conj_symm x (hT.eigenvectorBasis rfl i), Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq]

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

lemma finiteRegular_coefficient_kernel (f : G → ℂ) (i j : G) :
    coefficientAction finiteRegularRepresentation f (EuclideanSpace.basisFun G ℂ j) i =
      f (i * j⁻¹) := by
  simp only [coefficientAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    finiteRegularRepresentation_apply, smul_eq_mul, EuclideanSpace.basisFun_apply]
  simp only [PiLp.single_apply, inv_mul_eq_iff_eq_mul, mul_ite, mul_one, mul_zero]
  have he (x : G) : i = x * j ↔ x = i * j⁻¹ := by
    constructor
    · intro h; rw [h, mul_inv_cancel_right]
    · intro h; rw [h, inv_mul_cancel_right]
  simp_rw [he]
  simp

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

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

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

include hinj hfull

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
-- module OAI.Probability.SignedSweeps.HilbertBlocks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

@[simp] lemma hilbertBlock_apply (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : F) :
    hilbertBlock j A x = j (A (j.toLinearMap.adjoint x)) := rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.InjectionRestriction
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma viaEmbeddingHom_injective {A B : Type*} [Finite A] (i : A ↪ B) :
    Function.Injective (Equiv.Perm.viaEmbeddingHom i) := by
  intro g h he
  apply Equiv.ext
  intro x
  have hx := congrArg (fun k : Equiv.Perm B => k (i x)) he
  change (g.viaEmbedding i) (i x) = (h.viaEmbedding i) (i x) at hx
  rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply] at hx
  exact i.injective hx

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedSites
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

@[simp] lemma markedInjection_apply {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) :
    markedInjection h z i = (markedSites h z i).1 := rfl

lemma markedInjection_avoids {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) (i : Fin p) : markedInjection h z i ∉ Set.range z :=
  (markedSites h z i).2

def markedAllSites {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fin p ⊕ Fin l ≃ Fin n :=
  (Equiv.sumCongr (markedSites h z) (Equiv.ofInjective z z.injective)).trans
    ((Equiv.sumComm _ _).trans (Equiv.Set.sumCompl (Set.range z)))

@[simp] lemma markedAllSites_left {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (i : Fin p) : markedAllSites h z (Sum.inl i) = markedInjection h z i := rfl

@[simp] lemma markedAllSites_right {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (i : Fin l) : markedAllSites h z (Sum.inr i) = z i := rfl

lemma moveMarks_viaEmbedding {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (g : SymmetricGroup p) : moveMarks (g.viaEmbedding (markedInjection h z)) z = z := by
  apply Function.Embedding.ext
  intro a
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,hi⟩
  exact markedInjection_avoids h z i ⟨a,hi.symm⟩

lemma markedSpinTransport_viaEmbedding {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n)
    (g : SymmetricGroup p) : markedSpinTransport h (g.viaEmbedding (markedInjection h z)) z = g := by
  apply Equiv.ext
  intro i
  apply (markedInjection h z).injective
  have he := markedSpinTransport_sites h (g.viaEmbedding (markedInjection h z)) z i
  rw [moveMarks_viaEmbedding, Equiv.Perm.viaEmbedding_apply] at he
  exact he

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertFibers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {Z E : Type*} [Fintype Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

def fiberEvaluation (z : Z) : HilbertFibers Z E →ₗ[ℂ] E where
  toFun f := f.ofLp z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fiberInsertionLinear (z : Z) : E →ₗ[ℂ] HilbertFibers Z E where
  toFun x := PiLp.single 2 z x
  map_add' x y := by
    apply PiLp.ext
    intro w
    simp only [PiLp.single_apply, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    apply PiLp.ext
    intro w
    simp only [PiLp.single_apply, PiLp.smul_apply]
    split_ifs <;> simp

omit [FiniteDimensional ℂ E] in
@[simp] lemma fiberInsertionLinear_apply [FiniteDimensional ℂ E] (z w : Z) (x : E) :
    (fiberInsertionLinear z x).ofLp w = if w = z then x else 0 := by
  exact PiLp.single_apply 2 E z x w

def fiberInsertion (z : Z) : E →ₗᵢ[ℂ] HilbertFibers Z E where
  toLinearMap := fiberInsertionLinear z
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2]
    simp only [fiberInsertionLinear_apply]
    simp only [apply_ite, norm_zero]
    simp [Real.sqrt_sq]

@[simp] lemma fiberInsertion_apply (z w : Z) (x : E) :
    (fiberInsertion z x).ofLp w = if w = z then x else 0 := fiberInsertionLinear_apply z w x

@[simp] lemma fiberEvaluation_insertion (z : Z) (x : E) :
    fiberEvaluation z (fiberInsertion z x) = x := by
  change (fiberInsertion z x).ofLp z = x
  simp

lemma fiberInsertion_adjoint (z : Z) :
    (fiberInsertion (E:=E) z).toLinearMap.adjoint = fiberEvaluation z := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (fiberInsertion z y) x = inner ℂ y (x.ofLp z)
  rw [PiLp.inner_apply]
  simp only [fiberInsertion_apply]
  rw [Finset.sum_eq_single z]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

lemma hilbertBlock_fiber_apply (z w : Z) (A : E →ₗ[ℂ] E) (x : HilbertFibers Z E) :
    (hilbertBlock (fiberInsertion z) A x).ofLp w = if w = z then A (x.ofLp z) else 0 := by
  rw [hilbertBlock_apply, fiberInsertion_adjoint, fiberInsertion_apply]; rfl

omit [FiniteDimensional ℂ E] in
@[simp] lemma fiberDiagonal_apply [FiniteDimensional ℂ E]
    (A : Z → E →ₗ[ℂ] E) (x : HilbertFibers Z E) (z : Z) :
    (fiberDiagonal A x).ofLp z = A z (x.ofLp z) := rfl

lemma fiberDiagonal_eq_sum (A : Z → E →ₗ[ℂ] E) :
    fiberDiagonal A = ∑ z, hilbertBlock (fiberInsertion z) (A z) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro z
  simp only [fiberDiagonal_apply, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    hilbertBlock_fiber_apply]
  simp

lemma trace_fiberDiagonal_mul (P : Z → E →ₗ[ℂ] E)
    (A : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) :
    LinearMap.trace ℂ (HilbertFibers Z E) (fiberDiagonal P * A) =
      ∑ z, LinearMap.trace ℂ E
        (P z * (fiberEvaluation z ∘ₗ A ∘ₗ (fiberInsertion z).toLinearMap)) := by
  rw [fiberDiagonal_eq_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  change LinearMap.trace ℂ _ ((fiberInsertion z).toLinearMap ∘ₗ
    (P z ∘ₗ (fiberInsertion z).toLinearMap.adjoint ∘ₗ A)) = _
  rw [LinearMap.trace_comp_comm', fiberInsertion_adjoint]
  rfl

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedWords
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedTargetTransport_at {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedTargetTransport h g (moveMarks g z) = markedSpinTransport h g z := by
  have he := markedSpinTransport_mul h g⁻¹ g z
  rw [inv_mul_cancel, markedSpinTransport_one] at he
  exact inv_eq_of_mul_eq_one_right he.symm

@[simp] lemma markedWordRepresentation_apply {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C)
    (z : MarkedAssignment l n) :
    (markedWordRepresentation h C g f).ofLp z =
      signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)) := rfl

lemma markedWordRepresentation_insertion {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (z : MarkedAssignment l n)
    (x : WordSpace p (C ⊕ C)) :
    markedWordRepresentation h C g (fiberInsertion z x) =
      fiberInsertion (moveMarks g z) (signedWordRepresentation p C (markedSpinTransport h g z) x) := by
  apply PiLp.ext
  intro w
  simp only [markedWordRepresentation_apply, fiberInsertion_apply]
  by_cases hw : w = moveMarks g z
  · subst w
    rw [← moveMarks_mul, inv_mul_cancel, moveMarks_one, markedTargetTransport_at]
    simp
  · have hn : moveMarks g⁻¹ w ≠ z := by
      intro he
      apply hw
      rw [← he, ← moveMarks_mul, mul_inv_cancel, moveMarks_one]
    rw [if_neg hn, if_neg hw, map_zero]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedPairFibers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedSpinTransport_viaEmbedding_of_fixed {p l n : ℕ} (h : p+l=n)
    (g : SymmetricGroup n) (z : MarkedAssignment l n) (hg : moveMarks g z = z) :
    (markedSpinTransport h g z).viaEmbedding (markedInjection h z) = g := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (markedAllSites h z).surjective i
  cases i with
  | inl i =>
    rw [markedAllSites_left, Equiv.Perm.viaEmbedding_apply]
    simpa only [hg] using markedSpinTransport_sites h g z i
  | inr a =>
    rw [markedAllSites_right, Equiv.Perm.viaEmbedding_apply_of_notMem]
    · exact (congrArg (fun w : MarkedAssignment l n => w a) hg).symm
    · rintro ⟨i,hi⟩
      exact markedInjection_avoids h z i ⟨a,hi.symm⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedCompression
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {Z E : Type*} [Fintype Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

def fiberBlock (A : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) (z w : Z) : E →ₗ[ℂ] E :=
  fiberEvaluation z ∘ₗ A ∘ₗ (fiberInsertion w).toLinearMap

lemma fiber_resolution :
    (∑ z : Z, (fiberInsertion (E:=E) z).toLinearMap ∘ₗ fiberEvaluation z) = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro w
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, fiberInsertion_apply,
    Module.End.one_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

lemma fiberBlock_mul (A B : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) (z w : Z) :
    fiberBlock (A * B) z w = ∑ t : Z, fiberBlock A z t * fiberBlock B t w := by
  calc
    _ = fiberEvaluation z ∘ₗ A ∘ₗ (1 : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) ∘ₗ B ∘ₗ
        (fiberInsertion w).toLinearMap := rfl
    _ = _ := by
      rw [← fiber_resolution]
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, fiberBlock,
        Module.End.mul_apply]

lemma fiberBlock_diagonal_mul {H K : Type*} (col : Z → H) (row : Z → K)
    (hinj : Function.Injective (fun z => (col z, row z)))
    (A B : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E)
    (hA : ∀ z w, col z ≠ col w → fiberBlock A z w = 0)
    (hB : ∀ z w, row z ≠ row w → fiberBlock B z w = 0) (z : Z) :
    fiberBlock (A * B) z z = fiberBlock A z z * fiberBlock B z z := by
  rw [fiberBlock_mul, Finset.sum_eq_single z]
  · intro w _ hw
    by_cases hc : col z = col w
    · have hr : row w ≠ row z := fun hr => hw (hinj (Prod.ext hc.symm hr))
      rw [hB w z hr, mul_zero]
    · rw [hA z w hc, zero_mul]
  · simp

lemma trace_fiber_product {H K : Type*} (col : Z → H) (row : Z → K)
    (hinj : Function.Injective (fun z => (col z, row z)))
    (P : Z → E →ₗ[ℂ] E) (A B : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E)
    (hA : ∀ z w, col z ≠ col w → fiberBlock A z w = 0)
    (hB : ∀ z w, row z ≠ row w → fiberBlock B z w = 0) :
    LinearMap.trace ℂ (HilbertFibers Z E) (fiberDiagonal P * A * B) =
      ∑ z, LinearMap.trace ℂ E (P z * fiberBlock A z z * fiberBlock B z z) := by
  rw [mul_assoc, trace_fiberDiagonal_mul]
  apply Finset.sum_congr rfl
  intro z _
  change LinearMap.trace ℂ E (P z * fiberBlock (A*B) z z) = _
  rw [fiberBlock_diagonal_mul col row hinj A B hA hB, mul_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedWord_fiberBlock {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (z w : MarkedAssignment l n) :
    fiberBlock (markedWordRepresentation h C g) z w =
      if z = moveMarks g w then signedWordRepresentation p C (markedSpinTransport h g w) else 0 := by
  apply LinearMap.ext
  intro x
  change fiberEvaluation z (markedWordRepresentation h C g (fiberInsertion w x)) = _
  rw [markedWordRepresentation_insertion]
  change (fiberInsertion (moveMarks g w) _).ofLp z = _
  rw [fiberInsertion_apply]
  split_ifs <;> rfl

lemma coefficient_fiberBlock {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ) (z w : MarkedAssignment l n) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z w =
      ∑ g : SymmetricGroup n, f g • fiberBlock (markedWordRepresentation h C g) z w := by
  apply LinearMap.ext
  intro x
  simp only [fiberBlock, coefficientAction, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]

lemma marked_fiberBlock_viaEmbedding {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (z : MarkedAssignment l n) (g : SymmetricGroup p) :
    fiberBlock (markedWordRepresentation h C (g.viaEmbedding (markedInjection h z))) z z =
      signedWordRepresentation p C g := by
  rw [markedWord_fiberBlock, moveMarks_viaEmbedding, if_pos rfl, markedSpinTransport_viaEmbedding]

theorem marked_coefficient_compression {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ) (z : MarkedAssignment l n) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z z =
      coefficientAction (signedWordRepresentation p C) (fun g => f (g.viaEmbedding (markedInjection h z))) := by
  rw [coefficient_fiberBlock, coefficientAction]
  let i := Equiv.Perm.viaEmbeddingHom (markedInjection h z)
  have hi : Function.Injective i := viaEmbeddingHom_injective (markedInjection h z)
  calc
    _ = ∑ g ∈ Finset.image i Finset.univ,
        f g • fiberBlock (markedWordRepresentation h C g) z z := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro g _ hg
      have hz : z ≠ moveMarks g z := by
        intro hz
        apply hg
        exact Finset.mem_image.mpr ⟨markedSpinTransport h g z, Finset.mem_univ _,
          markedSpinTransport_viaEmbedding_of_fixed h g z hz.symm⟩
      rw [markedWord_fiberBlock, if_neg hz, smul_zero]
    _ = _ := by
      rw [Finset.sum_image (fun _ _ _ _ he => hi he)]
      apply Finset.sum_congr rfl
      intro g _
      simp only [i, Equiv.Perm.viaEmbeddingHom_apply]
      rw [marked_fiberBlock_viaEmbedding]

def markedRoutes {l n : ℕ} {J : Type*} (route : Fin n → J)
    (z : MarkedAssignment l n) : Fin l → J := route ∘ z

lemma markedRoutes_preserved {l n : ℕ} {J : Type*} (route : Fin n → J)
    (g : SymmetricGroup n) (hg : g ∈ fiberSubgroup route) (z : MarkedAssignment l n) :
    markedRoutes route (moveMarks g z) = markedRoutes route z := by
  funext a
  exact hg (z a)

lemma marked_coefficient_support {p l n : ℕ} {C J : Type*} [Fintype C]
    (h : p+l=n) (route : Fin n → J) (f : SymmetricGroup n → ℂ)
    (hf : ∀ g, g ∉ fiberSubgroup route → f g = 0)
    (z w : MarkedAssignment l n) (hzw : markedRoutes route z ≠ markedRoutes route w) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z w = 0 := by
  rw [coefficient_fiberBlock]
  apply Finset.sum_eq_zero
  intro g _
  by_cases hg : g ∈ fiberSubgroup route
  · have hz : z ≠ moveMarks g w := by
      rintro rfl
      exact hzw (markedRoutes_preserved route g hg w)
    rw [markedWord_fiberBlock, if_neg hz, smul_zero]
  · rw [hf g hg, zero_smul]

lemma marked_routes_injective {l n : ℕ} {A B : Type*} (e : Fin n ≃ A × B) :
    Function.Injective (fun z : MarkedAssignment l n =>
      (markedRoutes (fun x => (e x).2) z, markedRoutes (fun x => (e x).1) z)) := by
  intro z w h
  apply Function.Embedding.ext
  intro a
  apply e.injective
  exact Prod.ext (congrFun (congrArg Prod.snd h) a) (congrFun (congrArg Prod.fst h) a)

theorem marked_positive_product_trace_split {u v p l n : ℕ} {A B C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (e : Fin n ≃ A × B) (f k : SymmetricGroup n → ℂ)
    (hf : ∀ g, g ∉ fiberSubgroup (fun x => (e x).2) → f g = 0)
    (hk : ∀ g, g ∉ fiberSubgroup (fun x => (e x).1) → k g = 0) :
    LinearMap.trace ℂ (MarkedWordSpace p l n C)
      (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f *
        coefficientAction (markedWordRepresentation h C) k) =
      ∑ z : MarkedAssignment l n, LinearMap.trace ℂ (WordSpace p (C ⊕ C))
        (pairTypeProjection hu a b C *
          coefficientAction (signedWordRepresentation p C) (fun g => f (g.viaEmbedding (markedInjection h z))) *
          coefficientAction (signedWordRepresentation p C) (fun g => k (g.viaEmbedding (markedInjection h z)))) := by
  change LinearMap.trace ℂ _ (fiberDiagonal _ * _ * _) = _
  rw [trace_fiber_product (markedRoutes (fun x => (e x).2)) (markedRoutes (fun x => (e x).1))
    (marked_routes_injective e) _ _ _ (marked_coefficient_support h _ f hf)
      (marked_coefficient_support h _ k hk)]
  simp only [marked_coefficient_compression]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientAlgebra
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_mul (ρ : Representation ℂ G E) (f k : G → ℂ) :
    coefficientAction ρ (coefficientProduct f k) = coefficientAction ρ f * coefficientAction ρ k := by
  simp only [coefficientAction, coefficientProduct, Finset.sum_smul]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g => (f h * k (h⁻¹*g)) • ρ g)
  change (∑ g, (f h * k (h⁻¹*(h*g))) • ρ (h*g)) = _ at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  rw [inv_mul_cancel_left, map_mul]
  exact (smul_mul_smul_comm (f h) (ρ h) (k g) (ρ g)).symm

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_one (ρ : Representation ℂ G E) :
    coefficientAction ρ (coefficientOne (G:=G)) = 1 := by
  simp [coefficientAction, coefficientOne]

lemma coefficientAction_star (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ) :
    coefficientAction ρ (coefficientStar f) = (coefficientAction ρ f).adjoint := by
  simp only [coefficientAction, coefficientStar, ← LinearMap.star_eq_adjoint, star_sum, star_smul]
  rw [← Equiv.sum_comp (Equiv.inv G) (fun g => star (f g⁻¹) • ρ g)]
  simp only [Equiv.inv_apply, inv_inv]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact (unitary_representation_adjoint ρ hρ g).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockPermutations
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j, Fintype (A j)]

omit [Fintype J] [∀ j, Fintype (A j)] in
lemma sigmaPermutation_injective : Function.Injective (sigmaPermutation (A := A)) := by
  intro g h he
  funext j
  apply Equiv.ext
  intro x
  have hx := Equiv.congr_fun he ⟨j,x⟩
  exact eq_of_heq (Sigma.mk.inj_iff.mp hx).2

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p : ℕ} {k : J → ℕ}

omit [Fintype J] in
@[simp] lemma blockPermutation_apply (e : (Σ j, Fin (k j)) ≃ Fin p)
    (g : ∀ j, SymmetricGroup (k j)) (j : J) (i : Fin (k j)) :
    blockPermutation e g (e ⟨j,i⟩) = e ⟨j,g j i⟩ := by
  change (e.permCongr (sigmaPermutation g)) (e ⟨j,i⟩) = _
  simp [Equiv.permCongr_apply, sigmaPermutation]

omit [Fintype J] in
lemma blockPermutation_injective (e : (Σ j, Fin (k j)) ≃ Fin p) :
    Function.Injective (blockPermutation e) := by
  intro g h he
  exact sigmaPermutation_injective (e.permCongr.injective he)

omit [Fintype J] in
lemma blockPermutation_fiber (e : (Σ j, Fin (k j)) ≃ Fin p)
    (g : ∀ j, SymmetricGroup (k j)) :
    blockPermutation e g ∈ fiberSubgroup (fun x => (e.symm x).1) := by
  intro x
  obtain ⟨x,rfl⟩ := e.surjective x
  rcases x with ⟨j,i⟩
  rw [blockPermutation_apply]
  simp only [Equiv.symm_apply_apply]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientPush
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

omit [Fintype H] in
lemma coefficientPush_apply (φ : G →* H) (hφ : Function.Injective φ)
    (f : G → ℂ) (g : G) : coefficientPush φ f (φ g) = f g := by
  simp [coefficientPush, hφ.eq_iff]

omit [Fintype H] in
lemma coefficientPush_zero (φ : G →* H) (f : G → ℂ) (h : H)
    (hh : h ∉ Set.range φ) : coefficientPush φ f h = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  exact if_neg (fun he => hh ⟨g,he⟩)

lemma coefficientAction_injective : Function.Injective
    (coefficientAction (finiteRegularRepresentation (G:=G))) := by
  intro f k he
  funext g
  have h := congrArg (fun T : EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G =>
    T (EuclideanSpace.basisFun G ℂ 1) g) he
  simpa only [finiteRegular_coefficient_kernel, inv_one, mul_one] using h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_push (ρ : Representation ℂ H E) (φ : G →* H) (f : G → ℂ) :
    coefficientAction ρ (coefficientPush φ f) = coefficientAction (ρ.comp φ) f := by
  simp only [coefficientAction, coefficientPush, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [ite_smul, zero_smul]
  simp

lemma coefficientPush_product (φ : G →* H) (f k : G → ℂ) :
    coefficientPush φ (coefficientProduct f k) =
      coefficientProduct (coefficientPush φ f) (coefficientPush φ k) := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_mul]

lemma coefficientPush_one (φ : G →* H) :
    coefficientPush φ (coefficientOne (G:=G)) = coefficientOne := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_one]

omit [Fintype H] in
lemma coefficientPush_star (φ : G →* H) (f : G → ℂ) :
    coefficientPush φ (coefficientStar f) = coefficientStar (coefficientPush φ f) := by
  funext h
  unfold coefficientPush coefficientStar
  rw [star_sum, ← Equiv.sum_comp (Equiv.inv G)]
  simp only [Equiv.inv_apply, inv_inv, map_inv, apply_ite, star_zero, inv_eq_iff_eq_inv]

omit [Fintype H] in
lemma coefficientPush_support (φ : G →* H) (f : G → ℂ) (K : Subgroup H)
    (hK : φ.range ≤ K) : ∀ h, h ∉ K → coefficientPush φ f h = 0 := by
  intro h hh
  exact coefficientPush_zero φ f h (fun ⟨g,hg⟩ => hh (hK ⟨g,hg⟩))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)]

lemma productCoefficient_product (f k : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientProduct (f j) (k j)) =
      coefficientProduct (productCoefficient f) (productCoefficient k) := by
  funext g
  simp only [productCoefficient, coefficientProduct, Pi.mul_apply, Pi.inv_apply,
    ← Finset.prod_mul_distrib, Fintype.prod_sum]

omit [∀ j, Fintype (G j)] in
lemma productCoefficient_star (f : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientStar (f j)) = coefficientStar (productCoefficient f) := by
  funext g
  simp only [productCoefficient, coefficientStar, Pi.inv_apply, star_prod]

omit [∀ j, Fintype (G j)] in
lemma productCoefficient_one :
    productCoefficient (fun j => coefficientOne (G:=G j)) = coefficientOne := by
  funext g
  by_cases hg : g = 1
  · subst g
    simp [productCoefficient, coefficientOne]
  · have hn : ∃ j, g j ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hg (funext hn)
    obtain ⟨j,hj⟩ := hn
    rw [coefficientOne, if_neg hg]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_power (ρ : Representation ℂ G E) (f : G → ℂ) (r : ℕ) :
    coefficientAction ρ (coefficientPower f r) = coefficientAction ρ f ^ r := by
  induction r with
  | zero => simp only [coefficientPower, coefficientAction_one, pow_zero]
  | succ r ih => rw [coefficientPower, coefficientAction_mul, ih, pow_succ]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_listProduct (ρ : Representation ℂ G E) (fs : List (G → ℂ)) :
    coefficientAction ρ (coefficientListProduct fs) = (fs.map (coefficientAction ρ)).prod := by
  induction fs with
  | nil => simp only [coefficientListProduct, coefficientAction_one, List.map_nil, List.prod_nil]
  | cons f fs ih => rw [coefficientListProduct, coefficientAction_mul, ih, List.map_cons, List.prod_cons]

lemma coefficientPush_power {H : Type*} [Group H] [Fintype H]
    (φ : G →* H) (f : G → ℂ) (r : ℕ) :
    coefficientPush φ (coefficientPower f r) = coefficientPower (coefficientPush φ f) r := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_power]

lemma productCoefficient_power {J : Type*} [Fintype J] {H : J → Type*}
    [∀ j, Group (H j)] [∀ j, Fintype (H j)] (f : ∀ j, H j → ℂ) (r : ℕ) :
    productCoefficient (fun j => coefficientPower (f j) r) = coefficientPower (productCoefficient f) r := by
  induction r with
  | zero => exact productCoefficient_one
  | succ r ih => simp only [coefficientPower, productCoefficient_product, ih]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockRestriction
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p n : ℕ} {k t : J → ℕ}

def blockFiberEquiv (e : (Σ j, Fin (k j)) ≃ Fin p) (j : J) :
    Fin (k j) ≃ {x : Fin p // (e.symm x).1 = j} where
  toFun x := ⟨e ⟨j,x⟩, by simp⟩
  invFun x := cast (congrArg (fun j => Fin (k j)) x.2) (e.symm x.1).2
  left_inv x := by
    apply eq_of_heq
    exact (cast_heq _ _).trans ((Sigma.ext_iff.mp (e.symm_apply_apply ⟨j,x⟩)).2)
  right_inv x := by
    apply Subtype.ext
    change e _ = x.1
    apply e.symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Sigma.ext x.2.symm (by simp)

omit [Fintype J] in
@[simp] lemma blockFiberEquiv_apply (e : (Σ j, Fin (k j)) ≃ Fin p) (j : J)
    (x : Fin (k j)) : (blockFiberEquiv e j x).1 = e ⟨j,x⟩ := rfl

omit [Fintype J] in
lemma blockPermutation_exists (e : (Σ j, Fin (k j)) ≃ Fin p) (g : SymmetricGroup p)
    (hg : g ∈ fiberSubgroup (fun x => (e.symm x).1)) :
    ∃ a, blockPermutation e a = g := by
  change ∀ x, (e.symm (g x)).1 = (e.symm x).1 at hg
  let a := fun j => (blockFiberEquiv e j).symm.permCongr
    (g.subtypePerm (fun x => by change ((e.symm (g x)).1 = j) ↔ _; rw [hg x]))
  refine ⟨a, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨⟨j,x⟩,rfl⟩ := e.surjective x
  rw [blockPermutation_apply]
  have he := (blockFiberEquiv e j).apply_symm_apply
    ((g.subtypePerm (fun x => by change ((e.symm (g x)).1 = j) ↔ _; rw [hg x]))
      (blockFiberEquiv e j x))
  exact congrArg Subtype.val he

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientUniform
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]

lemma coefficientPush_comp (φ : G →* H) (ψ : H →* K) (f : G → ℂ) :
    coefficientPush ψ (coefficientPush φ f) = coefficientPush (ψ.comp φ) f := by
  apply coefficientAction_injective (G:=K)
  simp only [coefficientAction_push]
  rfl

omit [Fintype H] in
lemma coefficientPush_equiv [Fintype H] (e : G ≃* H) (f : G → ℂ) (h : H) :
    coefficientPush e.toMonoidHom f h = f (e.symm h) := by
  calc
    _ = coefficientPush e.toMonoidHom f (e.toMonoidHom (e.symm h)) := congrArg (coefficientPush e.toMonoidHom f) (e.apply_symm_apply h).symm
    _ = _ := coefficientPush_apply _ e.injective _ _

lemma subgroupAverageCoefficient_equiv (S : Subgroup G) (e : H ≃* S) :
    subgroupAverageCoefficient S =
      coefficientPush (S.subtype.comp e.toMonoidHom) (fun _ => (Fintype.card H : ℂ)⁻¹) := by
  unfold subgroupAverageCoefficient
  rw [← coefficientPush_comp]
  congr 1
  funext s
  rw [coefficientPush_equiv, Fintype.card_congr e.toEquiv]

lemma subgroupAverageCoefficient_image (S : Subgroup H) (φ : G →* H)
    (hi : Function.Injective φ) (he : ∀ h, h ∈ S ↔ ∃ g, φ g = h) :
    subgroupAverageCoefficient S = coefficientPush φ (fun _ => (Fintype.card G : ℂ)⁻¹) := by
  let ψ : G →* S := φ.codRestrict S (fun g => (he (φ g)).mpr ⟨g,rfl⟩)
  have hψ : Function.Bijective ψ := ⟨fun a b h => hi (congrArg Subtype.val h), by
    intro h
    obtain ⟨g,hg⟩ := (he h).mp h.2
    exact ⟨g,Subtype.ext hg⟩⟩
  have hh := subgroupAverageCoefficient_equiv S (MulEquiv.ofBijective ψ hψ)
  exact hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_subgroupAverage [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (S : Subgroup G) :
    coefficientAction ρ (subgroupAverageCoefficient S) =
      (Fintype.card S : ℂ)⁻¹ • ∑ g : S, ρ g := by
  rw [subgroupAverageCoefficient, coefficientAction_push]
  simp only [coefficientAction, Finset.smul_sum, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G H : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)] [∀ j, Group (H j)] [∀ j, Fintype (H j)]

def piHom (φ : ∀ j, G j →* H j) : (∀ j, G j) →* (∀ j, H j) where
  toFun := fun g j => φ j (g j)
  map_one' := funext (fun j => map_one (φ j))
  map_mul' a b := funext (fun j => map_mul (φ j) (a j) (b j))

omit [Fintype J] [∀ index, Fintype (G index)] [∀ index, Fintype (H index)] in
lemma piHom_injective [Fintype J] [∀ index, Fintype (G index)]
    [∀ index, Fintype (H index)]
    (φ : ∀ j, G j →* H j) (hφ : ∀ j, Function.Injective (φ j)) :
    Function.Injective (piHom φ) := by
  intro g h he
  exact funext (fun j => hφ j (congrFun he j))

omit [∀ index, Fintype (H index)] in
lemma productCoefficient_push [∀ index, Fintype (H index)]
    (φ : ∀ j, G j →* H j) (f : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientPush (φ j) (f j)) =
      coefficientPush (piHom φ) (productCoefficient f) := by
  funext h
  simp only [productCoefficient, coefficientPush, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases he : piHom φ g = h
  · rw [if_pos he]
    apply Finset.prod_congr rfl
    intro j _
    exact if_pos (congrFun he j)
  · rw [if_neg he]
    have hn : ∃ j, φ j (g j) ≠ h j := by
      by_contra hn
      push Not at hn
      exact he (funext hn)
    obtain ⟨j,hj⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

lemma product_subgroupAverage (S : ∀ j, Subgroup (G j)) :
    productCoefficient (fun j => subgroupAverageCoefficient (S j)) =
      coefficientPush (piHom (fun j => (S j).subtype))
        (fun _ => (Fintype.card (∀ j, S j) : ℂ)⁻¹) := by
  rw [show (fun j => subgroupAverageCoefficient (S j)) =
    (fun j => coefficientPush (S j).subtype (fun _ => (Fintype.card (S j) : ℂ)⁻¹)) from rfl,
    productCoefficient_push]
  congr 1
  funext g
  simp only [productCoefficient, ← Finset.prod_inv_distrib, Fintype.card_pi, Nat.cast_prod]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges4
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

def columnGroup (a b : ℕ) : Subgroup (SymmetricGroup (2 ^ (a+b))) :=
  fiberSubgroup (fun x => (sweepBoard a b x).2)

def rowGroup (a b : ℕ) : Subgroup (SymmetricGroup (2 ^ (a+b))) :=
  fiberSubgroup (fun x => (sweepBoard a b x).1)

lemma first_layer_le_columns (a b : ℕ) (i : Fin a) :
    coordinateSubgroup (a+b) (i.castAdd b) ≤ columnGroup a b := by
  intro g hg x
  apply (positionsEquiv b).symm.injective

  change (positionsEquiv b).symm ((sweepBoard a b (g x)).2) =
    (positionsEquiv b).symm ((sweepBoard a b x).2)
  simp only [sweepBoard, Equiv.trans_apply, Equiv.prodCongr_apply, splitBinary,
    Equiv.coe_fn_mk, Prod.map_snd, Equiv.symm_apply_apply]
  funext j
  apply coordinateSubgroup_bit ⟨g,hg⟩ x (j.natAdd a)
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
  omega

lemma last_layer_le_rows (a b : ℕ) (j : Fin b) :
    coordinateSubgroup (a+b) (j.natAdd a) ≤ rowGroup a b := by
  intro g hg x
  apply (positionsEquiv a).symm.injective
  change (positionsEquiv a).symm ((sweepBoard a b (g x)).1) =
    (positionsEquiv a).symm ((sweepBoard a b x).1)
  simp only [sweepBoard, Equiv.trans_apply, Equiv.prodCongr_apply, splitBinary,
    Equiv.coe_fn_mk, Prod.map_fst, Equiv.symm_apply_apply]
  funext i
  apply coordinateSubgroup_bit ⟨g,hg⟩ x (i.castAdd b)
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
  omega

def columnSweep {a b : ℕ} (lam : Partition (2 ^ (a+b))) : Specht lam →ₗ[ℂ] Specht lam :=
  (List.ofFn (fun i : Fin a => layerOperator lam (i.castAdd b))).reverse.prod

def rowSweep {a b : ℕ} (lam : Partition (2 ^ (a+b))) : Specht lam →ₗ[ℂ] Specht lam :=
  (List.ofFn (fun j : Fin b => layerOperator lam (j.natAdd a))).reverse.prod

theorem sweepOperator_split {a b : ℕ} (lam : Partition (2 ^ (a+b))) :
    sweepOperator lam = rowSweep lam * columnSweep lam := by
  unfold sweepOperator rowSweep columnSweep
  rw [← Fin.append_castAdd_natAdd (f := layerOperator lam), List.ofFn_fin_append,
    List.reverse_append, List.prod_append]
  simp only [Fin.append_left, Fin.append_right]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {K E : Type*} [CommSemiring K] [AddCommMonoid E] [Module K E]

lemma trace_product_pow_cycle (A B : E →ₗ[K] E) (r : ℕ) :
    LinearMap.trace K E ((A * B) ^ r) = LinearMap.trace K E ((B * A) ^ r) := by
  cases r with
  | zero => simp
  | succ r =>
    rw [pow_succ, ← mul_assoc, mul_pow_mul, LinearMap.trace_mul_cycle K,
      ← pow_succ']

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma trace_positiveSquare_product (R C : E →ₗ[ℂ] E) (r : ℕ) :
    LinearMap.trace ℂ E (positiveSquare (R * C) ^ r) =
      LinearMap.trace ℂ E ((positiveSquare R * (C * C.adjoint)) ^ r) := by
  have he : positiveSquare (R * C) = C.adjoint * (positiveSquare R * C) := by
    simp only [positiveSquare, ← LinearMap.star_eq_adjoint, star_mul, mul_assoc]
  rw [he, trace_product_pow_cycle]
  simp only [mul_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

def columnSquarePower {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    Specht lam →ₗ[ℂ] Specht lam := (columnSweep lam * (columnSweep lam).adjoint) ^ r

def rowSquarePower {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    Specht lam →ₗ[ℂ] Specht lam := positiveSquare (rowSweep lam) ^ r

lemma columnSquarePower_positive {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    (columnSquarePower lam r).IsPositive := by
  apply positive_pow
  simpa only [positiveSquare, LinearMap.adjoint_adjoint] using adjoint_mul_positive (columnSweep lam).adjoint

lemma rowSquarePower_positive {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    (rowSquarePower lam r).IsPositive := positive_pow (adjoint_mul_positive _) r

lemma sweepSquare_trace_split {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ r) =
      LinearMap.trace ℂ (Specht lam)
        ((positiveSquare (rowSweep lam) * (columnSweep lam * (columnSweep lam).adjoint)) ^ r) := by
  rw [sweepSquare, sweepOperator_split, trace_positiveSquare_product]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma exists_unit_eigenvector (T : E →ₗ[ℂ] E) [Nontrivial E] :
    ∃ c : ℂ, ∃ v : E, ‖v‖ = 1 ∧ T v = c • v := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.2
  refine ⟨c, (‖x‖⁻¹ : ℂ) • x, ?_, ?_⟩
  · simp [norm_smul, hn]
  · simp only [map_smul, hx.apply_eq_smul, smul_smul]
    congr 1
    ring

omit [FiniteDimensional ℂ E] in
lemma orthonormal_head_complement {v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin (finrank ℂ (ℂ ∙ v)ᗮ)) ℂ (ℂ ∙ v)ᗮ) :
    Orthonormal ℂ (Fin.cons v (fun i => (b i : E))) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [inner_self_eq_norm_sq_to_K, hv]
  · simp only [Fin.cons_zero, Fin.cons_succ, (Ne.symm (Fin.succ_ne_zero _)), ite_false]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b j).property
  · simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ite_false]
    rw [← inner_conj_symm]
    simp only [Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property, map_zero]
  · simpa only [Fin.cons_succ, Fin.succ_inj, Submodule.coe_inner] using
      orthonormal_iff_ite.mp b.orthonormal i j

theorem exists_schur_basis (T : E →ₗ[ℂ] E) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular := by
  suffices ∀ n, finrank ℂ E = n →
      ∃ b : OrthonormalBasis (Fin n) ℂ E,
        (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular by
    exact this _ rfl
  intro n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    intro hn
    by_cases h0 : n = 0
    · subst h0
      let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hn)
      refine ⟨b, ?_⟩
      intro i
      exact Fin.elim0 i
    have : Nontrivial E := (Module.finrank_pos_iff (R := ℂ)).mp (hn.symm ▸ Nat.pos_of_ne_zero h0)
    obtain ⟨c,v,hv,hTv⟩ := exists_unit_eigenvector T
    have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv
    let F : Submodule ℂ E := (ℂ ∙ v)ᗮ
    have hdim : 1 + finrank ℂ F = n := by
      simpa only [F, finrank_span_singleton hv0] using
        (Submodule.finrank_add_finrank_orthogonal (ℂ ∙ v)).trans hn
    let S : F →ₗ[ℂ] F := F.orthogonalProjectionOnto.toLinearMap ∘ₗ T ∘ₗ F.subtype
    obtain ⟨b,hb⟩ := ih (finrank ℂ F) (by omega) S rfl
    have hon := orthonormal_head_complement hv b
    let b' : OrthonormalBasis (Fin (finrank ℂ F + 1)) ℂ E :=
      OrthonormalBasis.mk hon (by
        apply le_of_eq
        symm
        apply hon.linearIndependent.span_eq_top_of_card_eq_finrank
        simpa only [Fintype.card_fin, hn] using (by omega : finrank ℂ F + 1 = n))
    have hb' (i : Fin (finrank ℂ F + 1)) : b' i = (Fin.cons v (fun i => (b i : E)) : Fin (finrank ℂ F + 1) → E) i :=
      congrFun (OrthonormalBasis.coe_mk hon _) i
    have hu : (LinearMap.toMatrix b'.toBasis b'.toBasis T).IsUpperTriangular := by
      intro i j hji
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [hb', hb']
      revert hji
      refine Fin.cases ?_ (fun i => ?_) i
      · intro h; exact False.elim (Nat.not_lt_zero _ h)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          simp only [Fin.cons_zero, Fin.cons_succ, hTv, inner_smul_right]
          rw [← inner_conj_symm, Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property]
          simp
        · intro hji
          have h := hb (Fin.succ_lt_succ_iff.mp hji)
          simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
            OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] at h
          simp only [Fin.cons_succ]
          change inner ℂ (b i : E) (T (b j : E)) = 0
          have he : inner ℂ (b i : E) (T (b j : E)) = inner ℂ (b i) (S (b j)) := by
            change _ = inner ℂ (b i : E) (F.starProjection (T (b j : E)))
            rw [← F.inner_starProjection_left_eq_right, F.starProjection_eq_self_iff.mpr (b i).property]
          exact he.trans h
    let e : Fin (finrank ℂ F + 1) ≃ Fin n := finCongr (by omega)
    refine ⟨b'.reindex e, ?_⟩
    intro i j hji
    simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.reindex_apply] using
      hu (i := e.symm i) (j := e.symm j) hji

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {I R : Type*} [Fintype I] [LinearOrder I] [Semiring R]

lemma upper_triangular_mul_diagonal (A B : Matrix I I R)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : I) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma upper_triangular_pow_diagonal (A : Matrix I I R)
    (hA : A.IsUpperTriangular) (i : I) (m : ℕ) :
    (A ^ m) i i = A i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, upper_triangular_mul_diagonal _ _ (hA.pow m) hA, ih, pow_succ]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma schur_trace_power (T : E →ₗ[ℂ] E)
    (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E)
    (hb : (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular) (m : ℕ) :
    LinearMap.trace ℂ E (T ^ m) = ∑ i, (inner ℂ (b i) (T (b i))) ^ m := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, ← LinearMap.toMatrix_pow]
  simp only [Matrix.trace, Matrix.diag, upper_triangular_pow_diagonal _ hb,
    LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]

lemma quadratic_power_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) (m : ℕ) :
    (inner ℂ x ((T ^ m) x)).re = ∑ i : Fin (finrank ℂ E),
      hT.eigenvalues rfl i ^ m * ‖inner ℂ (hT.eigenvectorBasis rfl i) x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner x ((T ^ m) x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (hT.pow m) (hT.eigenvectorBasis rfl i) x,
    power_on_eigenvector T (hT.apply_eigenvectorBasis rfl i), inner_smul_left]
  simp only [map_pow, RCLike.ofReal_eq_complex_ofReal, Complex.conj_ofReal]
  rw [show inner ℂ x (hT.eigenvectorBasis rfl i) *
      ((hT.eigenvalues rfl i : ℂ) ^ m * inner ℂ (hT.eigenvectorBasis rfl i) x) =
      (hT.eigenvalues rfl i : ℂ) ^ m * (inner ℂ (hT.eigenvectorBasis rfl i) x *
        inner ℂ x (hT.eigenvectorBasis rfl i)) by ring,
    ← inner_conj_symm x (hT.eigenvectorBasis rfl i), Complex.mul_conj]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]

lemma quadratic_power_jensen (T : E →ₗ[ℂ] E) (hT : T.IsPositive) {x : E}
    (hx : ‖x‖ = 1) (m : ℕ) :
    (inner ℂ x (T x)).re ^ m ≤ (inner ℂ x ((T ^ m) x)).re := by
  rw [quadratic_spectral T hT.isSymmetric, quadratic_power_spectral T hT.isSymmetric]
  have hw : ∑ i : Fin (finrank ℂ E),
      ‖inner ℂ (hT.isSymmetric.eigenvectorBasis rfl i) x‖ ^ 2 = 1 := by
    rw [(hT.isSymmetric.eigenvectorBasis rfl).sum_sq_norm_inner_right, hx, one_pow]
  simpa only [smul_eq_mul, mul_comm] using
    (convexOn_pow (𝕜 := ℝ) m).map_sum_le
      (t := Finset.univ)
      (w := fun i => ‖inner ℂ (hT.isSymmetric.eigenvectorBasis rfl i) x‖ ^ 2)
      (p := hT.isSymmetric.eigenvalues rfl)
      (fun _ _ => sq_nonneg _) (by simpa using hw) (fun i _ => hT.nonneg_eigenvalues rfl i)

lemma unit_diagonal_power_le (T : E →ₗ[ℂ] E) {x : E} (hx : ‖x‖ = 1) (m : ℕ) :
    ‖inner ℂ x (T x)‖ ^ (2 * m) ≤
      (inner ℂ x ((positiveSquare T ^ m) x)).re := by
  have hc : ‖inner ℂ x (T x)‖ ≤ ‖T x‖ := by
    simpa only [hx, one_mul] using norm_inner_le_norm x (T x)
  have he : (inner ℂ x (positiveSquare T x)).re = ‖T x‖ ^ 2 := by
    simp only [positiveSquare, Module.End.mul_apply, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  calc
    _ = (‖inner ℂ x (T x)‖ ^ 2) ^ m := by rw [pow_mul]
    _ ≤ (‖T x‖ ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hc 2) m
    _ ≤ _ := he ▸ quadratic_power_jensen (positiveSquare T) (adjoint_mul_positive T) hx m

theorem trace_even_power_le_square (T : E →ₗ[ℂ] E) (m : ℕ) :
    (LinearMap.trace ℂ E (T ^ (2 * m))).re ≤
      (LinearMap.trace ℂ E (positiveSquare T ^ m)).re := by
  obtain ⟨b,hb⟩ := exists_schur_basis T
  rw [schur_trace_power T b hb, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (Complex.re_le_norm _).trans ((norm_pow _ _).le.trans
    (unit_diagonal_power_le T (b.norm_eq_one i) m))

lemma trace_product_double_le (A B : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (m : ℕ) :
    (LinearMap.trace ℂ E ((A * B) ^ (2 * m))).re ≤
      (LinearMap.trace ℂ E ((A ^ 2 * B ^ 2) ^ m)).re := by
  have h := trace_even_power_le_square (A * B) m
  have he : positiveSquare (A * B) = B * (A ^ 2 * B) := by
    simp only [positiveSquare, ← LinearMap.star_eq_adjoint, star_mul]
    simp only [LinearMap.star_eq_adjoint, hA.adjoint_eq, hB.adjoint_eq, pow_two, mul_assoc]
  rw [he, trace_product_pow_cycle B, mul_assoc, ← pow_two B] at h
  exact h

theorem dyadic_trace_product_le (A B : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (j : ℕ) :
    (LinearMap.trace ℂ E ((A * B) ^ (2 ^ j))).re ≤
      (LinearMap.trace ℂ E (A ^ (2 ^ j) * B ^ (2 ^ j))).re := by
  induction j generalizing A B with
  | zero => simp
  | succ j ih =>
    rw [pow_succ']
    apply (trace_product_double_le A B hA hB (2 ^ j)).trans
    simpa only [← pow_mul] using ih (A ^ 2) (B ^ 2) (hA.pow 2) (hB.pow 2)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical

theorem sweepSquare_dyadic_trace_split {a b : ℕ} (lam : Partition (2 ^ (a+b))) (j : ℕ) :
    (LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ (2 ^ j))).re ≤
      (LinearMap.trace ℂ (Specht lam)
        (rowSquarePower lam (2 ^ j) * columnSquarePower lam (2 ^ j))).re := by
  rw [sweepSquare_trace_split]
  exact dyadic_trace_product_le _ _ (rowSquarePower_positive lam 1 |>.isSymmetric |>
    (by simpa only [rowSquarePower, pow_one] using ·))
    (columnSquarePower_positive lam 1 |>.isSymmetric |>
    (by simpa only [columnSquarePower, pow_one] using ·)) j

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SweepBlockLayers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) sweepBlockLayersFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

@[simp] lemma columnEnumeration_board (a b : ℕ) (j : Fin (2^b)) (x : Fin (2^a)) :
    sweepBoard a b (columnEnumeration a b ⟨j,x⟩) = (x,j) := by
  simp [columnEnumeration]

@[simp] lemma rowEnumeration_board (a b : ℕ) (i : Fin (2^a)) (x : Fin (2^b)) :
    sweepBoard a b (rowEnumeration a b ⟨i,x⟩) = (i,x) := by
  simp [rowEnumeration]

lemma columnEnumeration_bits (a b : ℕ) (j : Fin (2^b)) (x : Fin (2^a)) :
    (positionsEquiv (a+b)).symm (columnEnumeration a b ⟨j,x⟩) =
      Fin.append ((positionsEquiv a).symm x) ((positionsEquiv b).symm j) := by
  simp [columnEnumeration, sweepBoard, splitBinary]

lemma rowEnumeration_bits (a b : ℕ) (i : Fin (2^a)) (x : Fin (2^b)) :
    (positionsEquiv (a+b)).symm (rowEnumeration a b ⟨i,x⟩) =
      Fin.append ((positionsEquiv a).symm i) ((positionsEquiv b).symm x) := by
  simp [rowEnumeration, sweepBoard, splitBinary]

lemma coordinateSubgroup_iff (d : ℕ) (i : Fin d) (g : SymmetricGroup (2^d)) :
    g ∈ coordinateSubgroup d i ↔ ∀ x j, j ≠ i →
      (positionsEquiv d).symm (g x) j = (positionsEquiv d).symm x j := by
  constructor
  · intro hg x j hj
    exact coordinateSubgroup_bit ⟨g,hg⟩ x j hj
  · intro h x
    funext j
    exact h x j.1 j.2

lemma column_block_coordinate (a b : ℕ) (i : Fin a)
    (g : ∀ _ : Fin (2^b), SymmetricGroup (2^a)) :
    blockPermutation (columnEnumeration a b) g ∈ coordinateSubgroup (a+b) (i.castAdd b) ↔
      ∀ j, g j ∈ coordinateSubgroup a i := by
  simp only [coordinateSubgroup_iff]
  constructor
  · intro hg j x t ht
    have hh := hg (columnEnumeration a b ⟨j,x⟩) (t.castAdd b)
      (fun he => ht (Fin.ext (congrArg (fun y : Fin (a+b) => y.val) he)))
    simpa only [blockPermutation_apply, columnEnumeration_bits, Fin.append_left] using hh
  · intro hg x t ht
    obtain ⟨⟨j,x⟩,rfl⟩ := (columnEnumeration a b).surjective x
    rw [blockPermutation_apply, columnEnumeration_bits, columnEnumeration_bits]
    revert ht
    refine Fin.addCases ?_ ?_ t
    · intro t ht
      simp only [Fin.append_left]
      apply hg j x t
      intro he
      exact ht (congrArg (Fin.castAdd b) he)
    · intro t ht
      simp only [Fin.append_right]

lemma row_block_coordinate (a b : ℕ) (i : Fin b)
    (g : ∀ _ : Fin (2^a), SymmetricGroup (2^b)) :
    blockPermutation (rowEnumeration a b) g ∈ coordinateSubgroup (a+b) (i.natAdd a) ↔
      ∀ j, g j ∈ coordinateSubgroup b i := by
  simp only [coordinateSubgroup_iff]
  constructor
  · intro hg j x t ht
    have hh := hg (rowEnumeration a b ⟨j,x⟩) (t.natAdd a)
      (fun he => ht (Fin.ext (by have hh := congrArg Fin.val he; simpa using hh)))
    simpa only [blockPermutation_apply, rowEnumeration_bits, Fin.append_right] using hh
  · intro hg x t ht
    obtain ⟨⟨j,x⟩,rfl⟩ := (rowEnumeration a b).surjective x
    rw [blockPermutation_apply, rowEnumeration_bits, rowEnumeration_bits]
    revert ht
    refine Fin.addCases ?_ ?_ t
    · intro t ht
      simp only [Fin.append_left]
    · intro t ht
      simp only [Fin.append_right]
      apply hg j x t
      intro he
      exact ht (congrArg (Fin.natAdd a) he)

lemma coordinate_column_image (a b : ℕ) (i : Fin a) (g : SymmetricGroup (2^(a+b))) :
    g ∈ coordinateSubgroup (a+b) (i.castAdd b) ↔
      ∃ h : Fin (2^b) → coordinateSubgroup a i,
        blockPermutation (columnEnumeration a b) (fun j => (h j).val) = g := by
  constructor
  · intro hg
    have hc := first_layer_le_columns a b i hg
    have hc' : g ∈ fiberSubgroup (fun x => ((columnEnumeration a b).symm x).1) := by
      simpa only [columnGroup, columnEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
        Equiv.coe_fn_symm_mk, Equiv.prodComm_symm, Equiv.prodComm_apply, Equiv.symm_symm, Prod.swap] using hc
    obtain ⟨h,rfl⟩ := blockPermutation_exists (columnEnumeration a b) g hc'
    exact ⟨fun j => ⟨h j,(column_block_coordinate a b i h).mp hg j⟩,rfl⟩
  · rintro ⟨h,rfl⟩
    exact (column_block_coordinate a b i _).mpr (fun j => (h j).2)

lemma coordinate_row_image (a b : ℕ) (i : Fin b) (g : SymmetricGroup (2^(a+b))) :
    g ∈ coordinateSubgroup (a+b) (i.natAdd a) ↔
      ∃ h : Fin (2^a) → coordinateSubgroup b i,
        blockPermutation (rowEnumeration a b) (fun j => (h j).val) = g := by
  constructor
  · intro hg
    have hc := last_layer_le_rows a b i hg
    have hc' : g ∈ fiberSubgroup (fun x => ((rowEnumeration a b).symm x).1) := by
      simpa only [rowGroup, rowEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
        Equiv.coe_fn_symm_mk, Equiv.symm_symm] using hc
    obtain ⟨h,rfl⟩ := blockPermutation_exists (rowEnumeration a b) g hc'
    exact ⟨fun j => ⟨h j,(row_block_coordinate a b i h).mp hg j⟩,rfl⟩
  · rintro ⟨h,rfl⟩
    exact (row_block_coordinate a b i _).mpr (fun j => (h j).2)

lemma column_layer_coefficient (a b : ℕ) (i : Fin a) :
    subgroupAverageCoefficient (coordinateSubgroup (a+b) (i.castAdd b)) =
      coefficientPush (blockPermutation (columnEnumeration a b))
        (productCoefficient (fun _ => subgroupAverageCoefficient (coordinateSubgroup a i))) := by
  rw [product_subgroupAverage, coefficientPush_comp]
  apply subgroupAverageCoefficient_image
  · exact (blockPermutation_injective _).comp (piHom_injective _ (fun _ => Subtype.val_injective))
  · exact coordinate_column_image a b i

lemma row_layer_coefficient (a b : ℕ) (i : Fin b) :
    subgroupAverageCoefficient (coordinateSubgroup (a+b) (i.natAdd a)) =
      coefficientPush (blockPermutation (rowEnumeration a b))
        (productCoefficient (fun _ => subgroupAverageCoefficient (coordinateSubgroup b i))) := by
  rw [product_subgroupAverage, coefficientPush_comp]
  apply subgroupAverageCoefficient_image
  · exact (blockPermutation_injective _).comp (piHom_injective _ (fun _ => Subtype.val_injective))
  · exact coordinate_row_image a b i

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SweepCoefficients
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma coefficientAction_layer {d : ℕ} (lam : Partition (2^d)) (i : Fin d)
    (I : Fintype (SymmetricGroup (2^d))) :
    letI := I
    coefficientAction (spechtRepresentation lam)
      (subgroupAverageCoefficient (coordinateSubgroup d i)) = layerOperator lam i := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^d)) (Fin (2^d)) (instDecidableEqFin _) (instDecidableEqFin _) (Fin.fintype _) (Fin.fintype _))
  rw [coefficientAction_subgroupAverage]
  rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

lemma coefficientPush_list (φ : G →* H) (L : List (G → ℂ)) :
    coefficientPush φ (coefficientListProduct L) =
      coefficientListProduct (L.map (coefficientPush φ)) := by
  induction L with
  | nil => exact coefficientPush_one φ
  | cons f L ih => simp only [coefficientListProduct, List.map_cons, coefficientPush_product, ih]

lemma productCoefficient_list {J : Type*} [Fintype J] (L : List (G → ℂ)) :
    productCoefficient (fun _ : J => coefficientListProduct L) =
      coefficientListProduct (L.map (fun f => productCoefficient (fun _ : J => f))) := by
  induction L with
  | nil => exact productCoefficient_one
  | cons f L ih => simp only [coefficientListProduct, List.map_cons, productCoefficient_product, ih]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
attribute [local instance 2000] OAI.SignedSweeps.instDecidableEqFin_oAI_1

def columnSweepCoefficient (a b : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (columnEnumeration a b))
    (productCoefficient (fun _ => sweepCoefficient a))

def rowSweepCoefficient (a b : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (rowEnumeration a b))
    (productCoefficient (fun _ => sweepCoefficient b))

lemma columnSweepCoefficient_layers (a b : ℕ) :
    columnSweepCoefficient a b = coefficientListProduct
      ((List.ofFn (fun i : Fin a => subgroupAverageCoefficient
        (coordinateSubgroup (a+b) (i.castAdd b)))).reverse) := by
  simp only [columnSweepCoefficient, sweepCoefficient, productCoefficient_list,
    coefficientPush_list, List.map_reverse, List.map_ofFn, Function.comp_def,
    ← column_layer_coefficient]

lemma rowSweepCoefficient_layers (a b : ℕ) :
    rowSweepCoefficient a b = coefficientListProduct
      ((List.ofFn (fun i : Fin b => subgroupAverageCoefficient
        (coordinateSubgroup (a+b) (i.natAdd a)))).reverse) := by
  simp only [rowSweepCoefficient, sweepCoefficient, productCoefficient_list,
    coefficientPush_list, List.map_reverse, List.map_ofFn, Function.comp_def,
    ← row_layer_coefficient]

lemma columnSweepCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) :
    coefficientAction (spechtRepresentation lam) (columnSweepCoefficient a b) = columnSweep lam := by
  rw [columnSweepCoefficient_layers]
  simp only [coefficientAction_listProduct, List.map_reverse, List.map_ofFn,
    Function.comp_def, coefficientAction_layer, columnSweep]

lemma rowSweepCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) :
    coefficientAction (spechtRepresentation lam) (rowSweepCoefficient a b) = rowSweep lam := by
  rw [rowSweepCoefficient_layers]
  simp only [coefficientAction_listProduct, List.map_reverse, List.map_ofFn,
    Function.comp_def, coefficientAction_layer, rowSweep]

lemma columnPowerCoefficient_formula (a b r : ℕ) : columnPowerCoefficient a b r =
    coefficientPower (coefficientProduct (columnSweepCoefficient a b)
      (coefficientStar (columnSweepCoefficient a b))) r := by
  simp only [columnPowerCoefficient, sweepPowerCoefficient, ↓reduceIte, productCoefficient_power,
    productCoefficient_product, productCoefficient_star, coefficientPush_power,
    coefficientPush_product, coefficientPush_star, columnSweepCoefficient]

lemma rowPowerCoefficient_formula (a b r : ℕ) : rowPowerCoefficient a b r =
    coefficientPower (coefficientProduct (coefficientStar (rowSweepCoefficient a b))
      (rowSweepCoefficient a b)) r := by
  simp only [rowPowerCoefficient, sweepPowerCoefficient, Bool.false_eq_true, ↓reduceIte,
    productCoefficient_power, productCoefficient_product, productCoefficient_star,
    coefficientPush_power, coefficientPush_product, coefficientPush_star, rowSweepCoefficient]

lemma columnPowerCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ) :
    coefficientAction (spechtRepresentation lam) (columnPowerCoefficient a b r) = columnSquarePower lam r := by
  simp only [columnPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ (spechtRepresentation_norm lam), columnSweepCoefficient_action,
    columnSquarePower]

lemma rowPowerCoefficient_action {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ) :
    coefficientAction (spechtRepresentation lam) (rowPowerCoefficient a b r) = rowSquarePower lam r := by
  simp only [rowPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ (spechtRepresentation_norm lam), rowSweepCoefficient_action,
    rowSquarePower, positiveSquare]

lemma columnPowerCoefficient_positive (a b r : ℕ) :
    (coefficientAction finiteRegularRepresentation (columnPowerCoefficient a b r)).IsPositive := by
  rw [columnPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ finiteRegularRepresentation_norm]
  apply positive_pow
  simpa only [positiveSquare, LinearMap.adjoint_adjoint] using
    adjoint_mul_positive (coefficientAction finiteRegularRepresentation (columnSweepCoefficient a b)).adjoint

lemma rowPowerCoefficient_positive (a b r : ℕ) :
    (coefficientAction finiteRegularRepresentation (rowPowerCoefficient a b r)).IsPositive := by
  rw [rowPowerCoefficient_formula, coefficientAction_power, coefficientAction_mul,
    coefficientAction_star _ finiteRegularRepresentation_norm]
  exact positive_pow (adjoint_mul_positive _) r

lemma columnPowerCoefficient_support (a b r : ℕ) :
    ∀ g, g ∉ columnGroup a b → columnPowerCoefficient a b r g = 0 := by
  apply coefficientPush_support
  rintro g ⟨h,rfl⟩
  simpa only [columnGroup, columnEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
    Equiv.coe_fn_symm_mk, Equiv.prodComm_symm, Equiv.prodComm_apply, Equiv.symm_symm,
    Prod.swap] using blockPermutation_fiber (columnEnumeration a b) h

lemma rowPowerCoefficient_support (a b r : ℕ) :
    ∀ g, g ∉ rowGroup a b → rowPowerCoefficient a b r g = 0 := by
  apply coefficientPush_support
  rintro g ⟨h,rfl⟩
  simpa only [rowGroup, rowEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
    Equiv.coe_fn_symm_mk, Equiv.symm_symm] using blockPermutation_fiber (rowEnumeration a b) h

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccupiedSweep
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

@[simp] lemma columnEnumeration_symm_fst (a b : ℕ) (x : Fin (2^(a+b))) :
    ((columnEnumeration a b).symm x).1 = (sweepBoard a b x).2 := rfl

@[simp] lemma rowEnumeration_symm_fst (a b : ℕ) (x : Fin (2^(a+b))) :
    ((rowEnumeration a b).symm x).1 = (sweepBoard a b x).1 := rfl

lemma columnPowerCoefficient_positive_fintype (a b r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (columnPowerCoefficient a b r)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact columnPowerCoefficient_positive a b r

lemma rowPowerCoefficient_positive_fintype (a b r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (rowPowerCoefficient a b r)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact rowPowerCoefficient_positive a b r

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SweepRecurrence
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma columnPowerCoefficient_action_fintype {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    coefficientAction (spechtRepresentation lam) (columnPowerCoefficient a b r) =
      columnSquarePower lam r := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact columnPowerCoefficient_action lam r

lemma rowPowerCoefficient_action_fintype {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    coefficientAction (spechtRepresentation lam) (rowPowerCoefficient a b r) =
      rowSquarePower lam r := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact rowPowerCoefficient_action lam r

theorem signed_sweep_recurrence_oai {a b j q R : ℕ} (hq : 0 < q)
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
    (lam : Partition (2^(a+b))) (u v l : ℕ) (h : u+v+l=2^(a+b))
    (α : Partition u) (β : Partition v) (γ : Partition l)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (ho : SignedOccurrence h α β γ lam) :
    weightedMoment lam (2^j) ≤ Real.exp (η*signedEntropy α β+
      τ*l*Real.log (2^(a+b) : ℕ)-(l:ℝ)*Real.log ((2^(a+b) : ℕ)/ (l:ℝ))+6*l+
      (2^b : ℕ)*typedLineError (2^a) q R+(2^a : ℕ)*typedLineError (2^b) q R+
      holeClippingError κ (2^a) (2^b)+((2^a : ℕ)+(2^b : ℕ) : ℝ)*Real.log (l+1)) := by
  let f := columnPowerCoefficient a b (2^j)
  let g := rowPowerCoefficient a b (2^j)
  have hf : (coefficientAction finiteRegularRepresentation f).IsPositive :=
    columnPowerCoefficient_positive_fintype a b (2^j) _
  have hg : (coefficientAction finiteRegularRepresentation g).IsPositive :=
    rowPowerCoefficient_positive_fintype a b (2^j) _
  let M := (LinearMap.trace ℂ (MarkedWordSpace (u+v) l (2^(a+b)) (Fin q))
      (markedTypeProjection rfl h α β (Fin q) *
        coefficientAction (markedWordRepresentation h (Fin q)) f *
        coefficientAction (markedWordRepresentation h (Fin q)) g)).re
  have ht : (spechtDimension γ:ℝ) *
      (LinearMap.trace ℂ (Specht lam) (sweepSquare lam^(2^j))).re ≤ M := by
    have hx := signed_occurrence_marked_trace rfl h h α β γ lam
      (Fin.castLEEmb hα) (Fin.castLEEmb hβ) ho
      (Fin.castLEEmb (show l ≤ 2^(a+b) by omega))
      ⟨Finset.univ.map (Fin.castLEEmb (show u ≤ u+v by omega)), by simp⟩ f g hf hg
    have hs := sweepSquare_dyadic_trace_split lam j
    rw [LinearMap.trace_mul_comm] at hs
    apply (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (spechtDimension γ))).trans
    simpa only [f, g, columnPowerCoefficient_action_fintype,
      rowPowerCoefficient_action_fintype] using hx
  have hd := signedOccurrence_dimension (by positivity : 0 < 2^(a+b)) ho
  have hJ : weightedMoment lam (2^j) ≤
      Real.exp (signedEntropy α β+(l:ℝ)*Real.log ((2^(a+b):ℕ)/(l:ℝ))+l)*M := by
    calc
      _ ≤ (Real.exp (signedEntropy α β+(l:ℝ)*Real.log ((2^(a+b):ℕ)/(l:ℝ))+l)*spechtDimension γ)*
          (LinearMap.trace ℂ (Specht lam) (sweepSquare lam^(2^j))).re :=
        mul_le_mul_of_nonneg_right hd (Complex.re_le_re (sweepSquare_pow_positive lam (2^j)).trace_nonneg)
      _ = Real.exp (signedEntropy α β+(l:ℝ)*Real.log ((2^(a+b):ℕ)/(l:ℝ))+l)*
          ((spechtDimension γ:ℝ)*(LinearMap.trace ℂ (Specht lam) (sweepSquare lam^(2^j))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
  let E : ℝ := (η-1)*signedEntropy α β+l+(2^b : ℕ)*typedLineError (2^a) q R+
      (2^a : ℕ)*typedLineError (2^b) q R
  have hM : M ≤ Real.exp E*holeTraceSum τ (2^a) (2^b) l := by
    dsimp only [M]
    rw [marked_positive_product_trace_split rfl h α β (sweepBoard a b) f g
      (columnPowerCoefficient_support a b (2^j)) (rowPowerCoefficient_support a b (2^j)), Complex.re_sum]
    calc
      _ ≤ ∑ z : MarkedAssignment l (2^(a+b)),
          holePrefactor (markedBoardPlacement (sweepBoard a b) z)*
            Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1+E) := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [E, add_assoc] using occupied_sweep_trace_bound hq h z hη hη' HA HB hR rfl α β hα hβ
      _ = Real.exp E * (∑ z : MarkedAssignment l (2^(a+b)),
          holePrefactor (markedBoardPlacement (sweepBoard a b) z)*
            Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1)) := by
        simp only [Real.exp_add, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by
        congr 1
        change (∑ z : MarkedAssignment l (2^(a+b)),
            holePrefactor (markedBoardPlacement (sweepBoard a b) z) *
              Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1)) =
          ∑ z : HolePlacement (2^a) (2^b) l,
            holePrefactor z * Real.exp (holeBudget τ z.1)
        exact Equiv.sum_comp (markedBoardPlacement (sweepBoard a b))
          (fun z : HolePlacement (2^a) (2^b) l => holePrefactor z * Real.exp (holeBudget τ z.1))
  have hh := holeTraceSum_bound (l:=l) hκ hκτ (by positivity : 0 < 2^a) (by positivity : 0 < 2^b)
  rw [← Nat.pow_add] at hh
  apply hJ.trans
  apply (mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)) (Real.exp_nonneg _)).trans_eq
  dsimp only [E]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.signed_sweep_recurrence_oai := @OAI.SignedSweeps.signed_sweep_recurrence_oai
