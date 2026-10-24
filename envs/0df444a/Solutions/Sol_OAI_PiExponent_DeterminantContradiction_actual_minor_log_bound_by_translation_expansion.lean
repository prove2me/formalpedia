-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_log_bound_by_translation_expansion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:01:59.197052+00:00
-- url     : https://prove2.me/submissions/7de66d58-c3e6-44c6-9efc-061b291625dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_expansion_identity
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_estimate
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_collision_determinant_estimate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators
noncomputable section

namespace MinorTranslationProof

theorem weights_one_le {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    1 ≤ fixedWeights d i := by
  change 1 ≤ (⌈Real.log (d.q i.val)⌉₊ : ℝ)
  rw [← d.x_log i.val]
  exact d.x_one_le _

theorem weights_pos {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < fixedWeights d i := lt_of_lt_of_le zero_lt_one (weights_one_le d i)

theorem mem_simplex {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (a : Fin m → ℕ) :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), h⟩
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    calc
      (a i : ℝ) * w i = w i * (a i : ℝ) := mul_comm _ _
      _ ≤ ∑ k, w k * (a k : ℝ) :=
        Finset.single_le_sum (fun k _ => mul_nonneg (hw k).le (Nat.cast_nonneg _))
          (Finset.mem_univ i)
      _ ≤ H := h

theorem mem_transverse {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (a : Fin m →₀ ℕ) :
    a ∈ transverseIndices w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  simp only [transverseIndices, Finset.mem_map_equiv, mem_simplex w H hw]
  rfl

theorem index_nonneg {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) :
    0 ≤ indexWeight d a :=
  Finset.sum_nonneg fun i _ => mul_nonneg (weights_pos d i).le (Nat.cast_nonneg _)

theorem index_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) :
    indexWeight d a ≤ H := (mem_transverse _ H (weights_pos d) a.1).mp a.2

theorem row_order_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) :
    (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
  have hp : ∀ i, 0 < InterpolationMatrix.rowWeights d.v0 d.base.theta (fixedWeights d) i := by
    intro i
    refine Fin.cases d.v0_pos (fun k => ?_) i
    exact div_pos (weights_pos d k) d.base.theta_pos
  have hr : (∑ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (fixedWeights d) i * (r.2.1 i : ℝ)) < H := (Finset.mem_filter.mp r.2.2).2
  have hs : (d.v0 : ℝ) * (r.2.1 0 : ℝ) ≤
      ∑ i, InterpolationMatrix.rowWeights d.v0 d.base.theta (fixedWeights d) i *
        (r.2.1 i : ℝ) :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hp i).le (Nat.cast_nonneg _))
      (Finset.mem_univ 0)
  apply (le_div_iff₀ d.v0_pos).mpr
  nlinarith

theorem row_count_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H := by
  classical
  let z : Fin (d.m + 1) → ℕ := fun _ => 0
  have hz : z ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights d.v0 d.base.theta (fixedWeights d)) H := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        simp [z]
      · simpa [z] using hH.le
    · simpa [z] using hH
  let r : Row d H := (⟨0, lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩, ⟨z, hz⟩)
  exact Fintype.card_pos_iff.mpr ⟨r⟩

theorem transverse_coordinate_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) {a : Fin m →₀ ℕ}
    (ha : a ∈ transverseIndices w H) (i : Fin m) : a i ≤ ⌊H⌋₊ := by
  have hp : ∀ i, 0 < w i := fun i => lt_of_lt_of_le zero_lt_one (hw i)
  have h := (mem_transverse w H hp a).mp ha
  have hai : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  apply Nat.le_floor
  calc
    (a i : ℝ) ≤ w i * (a i : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i) hai
    _ ≤ ∑ k, w k * (a k : ℝ) :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hp k).le (Nat.cast_nonneg _))
        (Finset.mem_univ i)
    _ ≤ H := h

theorem transverse_card_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) : (transverseIndices w H).card ≤ (⌊H⌋₊ + 1) ^ m := by
  classical
  let box : Finset (Fin m → ℕ) := Fintype.piFinset (fun _ => Finset.range (⌊H⌋₊ + 1))
  have hb : (transverseIndices w H).card ≤ box.card := by
    apply Finset.card_le_card_of_injOn (fun a : Fin m →₀ ℕ => fun i => a i)
    · intro a ha
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (transverse_coordinate_le w H hw ha i))
    · intro a ha b hb he
      exact Finsupp.ext (fun i => congrFun he i)
  simpa [box, Fintype.card_piFinset] using hb

theorem row_choice_card_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) :
    Fintype.card (RowChoice d H r) ≤ termCount d.m d.v0 H := by
  classical
  have hbounded (a : Transverse d H) :
      Fintype.card (∀ i, Fin (a.1 i - beta d r i + 1)) ≤ (⌊H⌋₊ + 1) ^ d.m := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∏ _i : Fin d.m, (⌊H⌋₊ + 1) := by
        refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) ?_
        intro i _
        exact Nat.add_le_add_right ((Nat.sub_le _ _).trans
          (transverse_coordinate_le _ H (weights_one_le d) a.2 i)) 1
      _ = _ := by simp
  have hb : Fintype.card (RowChoice d H r) ≤
      (transverseIndices (fixedWeights d) H).card *
        (⌊H⌋₊ + 1) ^ d.m * (r.2.1 0 + 1) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc
      _ ≤ ∑ _a : Transverse d H, (⌊H⌋₊ + 1) ^ d.m * (r.2.1 0 + 1) := by
        apply Finset.sum_le_sum
        intro a _
        exact Nat.mul_le_mul_right _ (hbounded a)
      _ = _ := by simp [Nat.mul_assoc, Transverse]
  calc
    _ ≤ (⌊H⌋₊ + 1) ^ d.m * (⌊H⌋₊ + 1) ^ d.m * (r.2.1 0 + 1) :=
      hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (transverse_card_le _ H (weights_one_le d))))
    _ = (⌊H⌋₊ + 1) ^ (2 * d.m) * (r.2.1 0 + 1) := by rw [← pow_add, two_mul]
    _ ≤ termCount d.m d.v0 H :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_floor (row_order_le d r)) 1)

theorem choice_card_le {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ termCount d.m d.v0 H ^ actualRowCount d H := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _r : Row d H, termCount d.m d.v0 H :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun r _ => row_choice_card_le d r)
    _ = _ := by simp [actualRowCount]

theorem sum_row_weight {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H * actualMean d H := by
  have hm : (actualRowCount d H : ℝ) ≠ 0 := by
    exact_mod_cast (row_count_pos d hH).ne'
  unfold actualMean MatrixArithmetic.meanRowWeight
  change (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H *
    (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H /
      ((actualRowCount d H : ℝ) * H))
  rw [mul_div_cancel₀ _ (mul_ne_zero hm hH.ne')]
  unfold MatrixArithmetic.rowWeightedSum rowWeight beta fixedWeights InterpolationMatrix.exponentVector
  simp only [Finsupp.coe_equivFunOnFinite_symm, mul_comm]

theorem weight_mono {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) (ht : choiceScalar d r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  classical
  have h : ∀ i, beta d r i ≤ t.1.1 i := by
    intro i
    by_contra hi
    have hz : (∏ j, (t.1.1 j).choose (beta d r j) *
        (t.1.1 j - beta d r j).choose (t.2.1 j) : ℕ) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi)]
    exact ht (by simp [choiceScalar, hz])
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (by exact_mod_cast h i) (weights_pos d i).le

theorem low_capacity {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun a => indexWeight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤ lowIndexCount d H := by
  classical
  have hc : ((Finset.univ : Finset (Transverse d H)).filter
      (fun a => indexWeight d a ≤ (d.base.A : ℝ) * H)).card ≤ lowIndexCount d H := by
    change _ ≤ (realWeightedSimplex (fixedWeights d) ((d.base.A : ℝ) * H)).card
    apply Finset.card_le_card_of_injOn (fun a : Transverse d H => fun i => a.1 i)
    · intro a ha
      apply (mem_simplex _ _ (weights_pos d) _).mpr
      exact (Finset.mem_filter.mp ha).2
    · intro a _ b _ hab
      apply Subtype.ext
      exact Finsupp.ext (fun i => congrFun hab i)
  exact_mod_cast hc

theorem low_count_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < lowIndexCount d H := by
  have ha : (0 : ℝ) < d.base.A := lt_trans d.base.theta_pos d.base.theta_lt_A
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, ?_⟩
  apply (mem_simplex _ _ (weights_pos d) _).mpr
  simpa only [Nat.cast_zero, mul_zero, Finset.sum_const_zero] using mul_nonneg ha.le hH.le

-- Elementary occupancy estimates, independent of the analytic children.
theorem square_mass_le {κ : Type*} [Fintype κ] (S : Finset κ) (n : κ → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a, n a ^ 2 := by
  have h : (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, n a ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : κ => (1 : ℝ)) n
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun a _ _ => sq_nonneg (n a))

theorem high_weight_bound {ι : Type*} (rows : Finset ι) (weight : ι → ℝ)
    {cutoff eta : ℝ} (hc : 0 ≤ cutoff) (hw : ∀ i ∈ rows, 0 ≤ weight i)
    (hlow : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) ≤ eta * rows.card) :
    cutoff * (1 - eta) * rows.card ≤ ∑ i ∈ rows, weight i := by
  classical
  have hcard : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) +
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) = rows.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := rows)
      (fun i => weight i ≤ cutoff))
  have hh : (1 - eta) * rows.card ≤
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) := by nlinarith
  calc
    _ = cutoff * ((1 - eta) * rows.card) := by ring
    _ ≤ cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) :=
      mul_le_mul_of_nonneg_left hh hc
    _ = ∑ _i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), cutoff := by simp [mul_comm]
    _ ≤ ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ rows, weight i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ rows) (fun i hi _ => hw i hi)

theorem exponent_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) {H A eta nu c N bbar E : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N) :
    -nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) -
      c * (∑ a, (MinorTranslationData.multiplicity group a : ℝ) ^ 2) + (Fintype.card ι : ℝ) * H * E ≤
    (Fintype.card ι : ℝ) * H *
      (E + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar))) := by
  classical
  let S := (Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)
  let M : ℝ := Fintype.card ι
  let Z : ℝ := ∑ a, (MinorTranslationData.multiplicity group a : ℝ) ^ 2
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass : (∑ a ∈ S, (MinorTranslationData.multiplicity group a : ℝ)) =
      (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) := by
    have hn := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset ι) S group
    have hn' : (∑ a ∈ S, MinorTranslationData.multiplicity group a) =
        ((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card := by
      simpa only [MinorTranslationData.multiplicity, S, Finset.mem_filter,
        Finset.mem_univ, true_and] using hn
    exact_mod_cast hn'
  by_cases hlow : eta * M ≤ ∑ a ∈ S, (MinorTranslationData.multiplicity group a : ℝ)
  · have hsq : eta ^ 2 * M ^ 2 ≤ N * Z := by
      calc
        _ = (eta * M) ^ 2 := by ring
        _ ≤ (∑ a ∈ S, (MinorTranslationData.multiplicity group a : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg heta hM) hlow 2
        _ ≤ (S.card : ℝ) * Z := square_mass_le S _
        _ ≤ N * Z := mul_le_mul_of_nonneg_right hcap hZ
    have hcollision : -c * Z ≤ M * H * (-c * eta ^ 2 * M / (H * N)) := by
      have hz : eta ^ 2 * M ^ 2 / N ≤ Z := (div_le_iff₀ hN).mpr (by nlinarith [hsq])
      have hh := mul_le_mul_of_nonneg_left hz hc
      have he : M * H * (-c * eta ^ 2 * M / (H * N)) =
          -c * (eta ^ 2 * M ^ 2 / N) := by field_simp [hH.ne', hN.ne'] <;> ring
      rw [he]
      nlinarith [hh]
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤ 0 := by
      have hp := mul_nonneg hnu (sub_nonneg.mpr hbeta)
      nlinarith [hp]
    have hm := mul_le_mul_of_nonneg_left
      (le_max_left (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith
  · have hl : (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) ≤
        eta * (Finset.univ : Finset ι).card := by
      rw [← hmass]
      exact le_of_not_ge hlow
    have hg := high_weight_bound (Finset.univ : Finset ι) (fun i => weight (group i))
      (mul_nonneg hA hH.le) (fun i _ => hw _) hl
    have hg' : A * H * (1 - eta) * M ≤ ∑ i, weight (group i) := by
      simpa only [Finset.card_univ, M] using hg
    have hmul := mul_le_mul_of_nonneg_left hg' hnu
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤
        M * H * (-nu * (A * (1 - eta) - bbar)) := by nlinarith [hmul]
    have hcollision : -c * Z ≤ 0 := by nlinarith [mul_nonneg hc hZ]
    have hm := mul_le_mul_of_nonneg_left
      (le_max_right (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith

theorem scalar_product_bound {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) - (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod (fun r _ => norm_nonneg _)
    (fun r _ => translation_scalar_estimate d hnu r (f r))).trans
  rw [← Real.exp_sum]
  apply le_of_eq
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_row_weight d hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
  ring

theorem summand_bound {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det‖ ≤
    Real.exp ((actualRowCount d H : ℝ) * H *
      (d.analyticError + remainder (actualRowCount d H) H +
        max (-collisionRate d H) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r, choiceScalar d r (f r)) = 0
  · simp [hs, Real.exp_nonneg]
  have hmono : (actualRowCount d H : ℝ) * H * actualMean d H ≤ ∑ r, indexWeight d (f r).1 := by
    rw [← sum_row_weight d hH]
    apply Finset.sum_le_sum
    intro r _
    exact weight_mono d r (f r) (Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r))
  have ha : (0 : ℝ) ≤ d.base.A := (lt_trans d.base.theta_pos d.base.theta_lt_A).le
  have hc : (0 : ℝ) ≤ Real.log 2 / 4 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hn : (0 : ℝ) < lowIndexCount d H := by exact_mod_cast low_count_pos d hH
  have he := exponent_bound (fun r : Row d H => (f r).1) (fun a : Transverse d H => indexWeight d a)
    (E := d.analyticError + remainder (actualRowCount d H) H)
    hH ha d.base.eta_pos.le hnu hc hn (index_nonneg d) hmono (low_capacity d H)
  rw [norm_mul]
  apply (mul_le_mul (scalar_product_bound d hnu hH f)
    (translation_collision_determinant_estimate d hH selection f)
    (norm_nonneg _) (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert he using 1 <;>
    simp only [AdmissibleParameters.analyticError, collisionRate, collisionConstant,
      actualRowCount, neg_div, neg_mul] <;> ring

theorem log_sum_bound {Ω : Type*} [Fintype Ω]
    (term : Ω → ℂ) (delta : ℂ) {M : ℕ} {H Q E : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hQ : 0 < Q)
    (hcard : (Fintype.card Ω : ℝ) ≤ Q ^ M)
    (hexpansion : delta = ∑ x, term x) (hne : delta ≠ 0)
    (hterm : ∀ x, ‖term x‖ ≤ Real.exp ((M : ℝ) * H * E)) :
    Real.log ‖delta‖ / ((M : ℝ) * H) ≤ E + Real.log Q / H := by
  have hb : ‖delta‖ ≤ Real.exp ((M : ℝ) * H * (E + Real.log Q / H)) := by
    calc
      _ = ‖∑ x, term x‖ := by rw [hexpansion]
      _ ≤ ∑ x, ‖term x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : Ω, Real.exp ((M : ℝ) * H * E) := Finset.sum_le_sum fun x _ => hterm x
      _ = (Fintype.card Ω : ℝ) * Real.exp ((M : ℝ) * H * E) := by simp
      _ ≤ Q ^ M * Real.exp ((M : ℝ) * H * E) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by
        have he : Q ^ M = Real.exp ((M : ℝ) * Real.log Q) := by
          rw [Real.exp_nat_mul, Real.exp_log hQ]
        rw [he, ← Real.exp_add]
        congr 1
        field_simp [hH.ne'] <;> ring
  have hl := Real.log_le_log (norm_pos_iff.mpr hne) hb
  rw [Real.log_exp] at hl
  apply (div_le_iff₀ (mul_pos (by exact_mod_cast hM) hH)).mpr
  nlinarith [hl]

end MinorTranslationProof

theorem solution {nu : Real} (d : FixedData nu) (hnu : 0 ≤ nu) {H : Real} (hH : 0 < H)
    (selection : Row d H → Column d H) (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : Real) * H) ≤
      d.analyticError +
        (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-Real.log 2 / 2))) / H +
        Real.log ((((⌊H⌋₊ + 1) ^ (2 * d.m) *
          (⌊H / (d.v0 : Real)⌋₊ + 1) : Nat) : Real)) / H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) := by
  have hQ : (0 : ℝ) < termCount d.m d.v0 H := by unfold termCount; positivity
  have hcard : (Fintype.card (ChoiceFamily d H) : ℝ) ≤
      (termCount d.m d.v0 H : ℝ) ^ actualRowCount d H := by
    exact_mod_cast MinorTranslationProof.choice_card_le d H
  have hb := MinorTranslationProof.log_sum_bound
    (fun f : ChoiceFamily d H => (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det)
    (actualMinor d H selection).det (MinorTranslationProof.row_count_pos d hH) hH hQ hcard
    (translation_expansion_identity d selection) hne (MinorTranslationProof.summand_bound d hnu hH selection)
  convert hb using 1 <;> simp only [remainder, termCount] <;> ring
