-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_child_affine_residue_descent_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:21:28.706744+00:00
-- url     : https://prove2.me/submissions/96f4e2c5-70fb-4d11-a210-d65a6f1a7fd4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B192

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem scalarResidue_relative_count_error (a b r v : ℤ) (hab : a < b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1| ≤ (r : ℝ) / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_absolute_error a b r v hab.le hr
  have heq : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1 =
      (((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
        ((b - a : ℤ) : ℝ) / r) * ((r : ℝ) / ((b - a : ℤ) : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (div_pos hrR hL)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (div_nonneg hrR.le hL.le)

end Erdos3

end

section

namespace Erdos3

theorem refined_residue_constraints_iff {M d J : ℕ} (hcop : (M * d).Coprime J)
    {u v w c : ℤ} (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)])
    (hJ : c ≡ w [ZMOD (J : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)] ∧ x ≡ w [ZMOD (J : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d * J : ℤ)] := by
  have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
  rw [← and_assoc, residue_constraints_iff_lcm hM hd x,
    residue_constraints_iff_lcm (Int.ModEq.refl c) hJ x, hL.lcm_eq_mul]
  simp only [Nat.cast_mul]

end Erdos3

end

section

namespace Erdos3

theorem CompatibleAuxResidue.baseValue_spec {M d : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) :
    v.baseValue ≡ u [ZMOD (M : ℤ)] ∧
      v.baseValue ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] := Classical.choose_spec v.property

theorem CompatibleAuxResidue.refinedValue_spec {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J) (w : ℤ) :
    v.refinedValue hcop w ≡ u [ZMOD (M : ℤ)] ∧
      v.refinedValue hcop w ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] ∧
      v.refinedValue hcop w ≡ w [ZMOD (J : ℤ)] :=
  Classical.choose_spec ((coprime_refinement_preserves_compatibility hcop u v.val.val w).mp v.property)

theorem CompatibleAuxResidue.baseConstraint_iff {M d : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)]) ↔
      x ≡ v.baseValue [ZMOD (Nat.lcm M d : ℤ)] :=
  residue_constraints_iff_lcm v.baseValue_spec.1 v.baseValue_spec.2 x

theorem refinement_modEq_iff {M J : ℕ} (hcop : M.Coprime J) {u w : ℤ}
    (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) :
    x ≡ w [ZMOD (M * J : ℕ)] ↔
      (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ w [ZMOD (J : ℤ)]) := by
  simpa only [hcop.lcm_eq_mul] using
    (residue_constraints_iff_lcm hw (show w ≡ w [ZMOD (J : ℤ)] from Int.ModEq.refl w) x).symm

theorem CompatibleAuxResidue.refinedConstraint_iff {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J)
    (w : ℤ) (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) :
    (x ≡ w [ZMOD (M * J : ℕ)] ∧ x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)]) ↔
      x ≡ v.refinedValue hcop w [ZMOD (Nat.lcm M d * J : ℕ)] := by
  have hMJ : M.Coprime J := hcop.of_dvd_left (dvd_mul_right M d)
  rw [refinement_modEq_iff hMJ hw x]
  have hc := v.refinedValue_spec hcop w
  exact (and_assoc.trans (and_congr_right fun _ => and_comm)).trans
    (refined_residue_constraints_iff hcop hc.1 hc.2.1 hc.2.2 x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedDensityL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem positive_mass_inverse_difference {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    J * |1 / I - 1 / J| = |I - J| / I := by
  have he : 1 / I - 1 / J = (J - I) / (I * J) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hI, abs_of_pos hJ, abs_sub_comm J I]
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ofPositiveWeights_complexMean {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (f : X → ℂ) :
    (ofPositiveWeights w hw hmass).complexMean f =
      (∑ x, (w x : ℂ) * f x) / ((∑ x, w x : ℝ) : ℂ) := by
  simp only [complexMean, ofPositiveWeights, Complex.ofReal_div, div_mul_eq_mul_div, Finset.sum_div]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem norm_complexMean_sub_le_weight_l1 {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean f - q.complexMean f‖ ≤ ∑ x, |p.weight x - q.weight x| := by
  simp only [complexMean, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

theorem exists_positive_weight_norm_ge_mean {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (f : X → ℂ) :
    ∃ x, 0 < p.weight x ∧ ‖p.complexMean f‖ ≤ ‖f x‖ := by
  classical
  let A := Finset.univ.filter (fun x => 0 < p.weight x)
  have hA : A.Nonempty := by
    by_contra hn
    have hzero (x : X) : p.weight x = 0 := by
      apply le_antisymm _ (p.nonneg x)
      apply le_of_not_gt
      intro hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    have ht := p.total
    simp only [hzero, Finset.sum_const_zero] at ht
    norm_num at ht
  obtain ⟨x, hx, hmax⟩ := A.exists_max_image (fun y => ‖f y‖) hA
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  apply (norm_sum_le _ _).trans
  calc
    (∑ y, ‖(p.weight y : ℂ) * f y‖) = ∑ y, p.weight y * ‖f y‖ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.nonneg y)]
    _ ≤ ∑ y, p.weight y * ‖f x‖ := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : 0 < p.weight y
      · exact mul_le_mul_of_nonneg_left (hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)) hy.le
      · have hz : p.weight y = 0 := le_antisymm (le_of_not_gt hy) (p.nonneg y)
        simp only [hz, zero_mul, le_refl]
    _ = ‖f x‖ := by rw [← Finset.sum_mul, p.total, one_mul]

theorem exists_piece_discrepancy_of_weight_l1 {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (f g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1)
    {η : ℝ} (hweights : (∑ x, |p.weight x - q.weight x|) ≤ η) :
    ∃ x, 0 < p.weight x ∧ ‖p.complexMean f - q.complexMean g‖ - η ≤ ‖f x - g x‖ := by
  obtain ⟨x, hx, hnorm⟩ := p.exists_positive_weight_norm_ge_mean (fun y => f y - g y)
  have heq : p.complexMean (fun y => f y - g y) = p.complexMean f - p.complexMean g := by
    simp only [complexMean, mul_sub, Finset.sum_sub_distrib]
  rw [heq] at hnorm
  have hmove := (norm_complexMean_sub_le_weight_l1 p q g hg).trans hweights
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (p.complexMean f) (p.complexMean g) (q.complexMean g)
  exact ⟨x, hx, by linarith⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem normalized_finite_weights_l1_le {X : Type*} [Fintype X] (f g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hfMass : 0 < ∑ x, f x) (hgMass : 0 < ∑ x, g x) :
    (∑ x, |f x / (∑ y, f y) - g x / (∑ y, g y)|) ≤
      2 * (∑ x, |f x - g x|) / (∑ x, f x) := by
  let I := ∑ x, f x
  let J := ∑ x, g x
  have hI : 0 < I := hfMass
  have hJ : 0 < J := hgMass
  have hm : |I - J| ≤ ∑ x, |f x - g x| := by
    dsimp only [I, J]
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hpoint (x : X) : |f x / I - g x / J| ≤
      |f x - g x| / I + g x * |1 / I - 1 / J| := by
    have heq : f x / I - g x / J = (f x - g x) / I + g x * (1 / I - 1 / J) := by ring
    rw [heq]
    simpa only [abs_div, abs_of_pos hI, abs_mul, abs_of_nonneg (hg x)] using
      abs_add_le ((f x - g x) / I) (g x * (1 / I - 1 / J))
  calc
    _ ≤ ∑ x, (|f x - g x| / I + g x * |1 / I - 1 / J|) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (∑ x, |f x - g x|) / I + J * |1 / I - 1 / J| := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ = (∑ x, |f x - g x|) / I + |I - J| / I := by
      rw [positive_mass_inverse_difference hI hJ]
    _ ≤ (∑ x, |f x - g x|) / I + (∑ x, |f x - g x|) / I :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hm hI.le)
    _ = 2 * (∑ x, |f x - g x|) / (∑ x, f x) := by dsimp only [I]; ring

theorem finite_weight_mass_pos_of_relative_error {X : Type*} [Fintype X]
    (f g : X → ℝ) (hfMass : 0 < ∑ x, f x) {δ : ℝ} (hδ : δ < 1)
    (herr : ∀ x, |g x - f x| ≤ δ * f x) : 0 < ∑ x, g x := by
  have hlower : (1 - δ) * (∑ x, f x) ≤ ∑ x, g x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have h := (abs_le.mp (herr x)).1
    nlinarith
  exact (mul_pos (sub_pos.mpr hδ) hfMass).trans_le hlower

theorem normalized_finite_weights_l1_relative {X : Type*} [Fintype X] (f g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hfMass : 0 < ∑ x, f x) (hgMass : 0 < ∑ x, g x)
    {δ : ℝ} (herr : ∀ x, |g x - f x| ≤ δ * f x) :
    (∑ x, |f x / (∑ y, f y) - g x / (∑ y, g y)|) ≤ 2 * δ := by
  have he : (∑ x, |f x - g x|) ≤ δ * ∑ x, f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    simpa only [abs_sub_comm] using herr x
  apply (normalized_finite_weights_l1_le f g hg hfMass hgMass).trans
  calc
    2 * (∑ x, |f x - g x|) / (∑ x, f x) ≤
        2 * (δ * ∑ x, f x) / (∑ x, f x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hfMass.le
    _ = 2 * δ := by field_simp

theorem normalized_finite_weights_pair_l1 {X : Type*} [Fintype X] (f g h : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hh : ∀ x, 0 ≤ h x)
    (hfMass : 0 < ∑ x, f x) (hgMass : 0 < ∑ x, g x) (hhMass : 0 < ∑ x, h x)
    {δ : ℝ} (hgerr : ∀ x, |g x - f x| ≤ δ * f x) (hherr : ∀ x, |h x - f x| ≤ δ * f x) :
    (∑ x, |g x / (∑ y, g y) - h x / (∑ y, h y)|) ≤ 4 * δ := by
  have hg' := normalized_finite_weights_l1_relative f g hg hfMass hgMass hgerr
  have hh' := normalized_finite_weights_l1_relative f h hh hfMass hhMass hherr
  have ht : (∑ x, |g x / (∑ y, g y) - h x / (∑ y, h y)|) ≤
      (∑ x, |f x / (∑ y, f y) - g x / (∑ y, g y)|) +
      (∑ x, |f x / (∑ y, f y) - h x / (∑ y, h y)|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    simpa only [abs_sub_comm] using
      abs_sub_le (g x / (∑ y, g y)) (f x / (∑ y, f y)) (h x / (∑ y, h y))
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

theorem one_sub_sum_mul_prod_one_add_le_one {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) :
    (1 - ∑ i ∈ S, e i) * (∏ i ∈ S, (1 + e i)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have heS : ∀ i ∈ S, 0 ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg heS
    have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [heS i hi])
    have hstep : (1 - (e a + ∑ i ∈ S, e i)) * (1 + e a) ≤ 1 - ∑ i ∈ S, e i := by
      nlinarith [mul_nonneg hea hs, sq_nonneg (e a)]
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hstep hp).trans (ih heS)

theorem prod_one_add_le_one_add_twice_sum {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    (∏ i ∈ S, (1 + e i)) ≤ 1 + 2 * ∑ i ∈ S, e i := by
  have h := one_sub_sum_mul_prod_one_add_le_one S e he
  have hs := Finset.sum_nonneg he
  have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [he i hi])
  have hp2 : (∏ i ∈ S, (1 + e i)) ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hp2 hs]

theorem positive_prod_sub_one_le_twice_sum {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, 0 ≤ e i)
    (herror : ∀ i ∈ S, |f i - 1| ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    |(∏ i ∈ S, f i) - 1| ≤ 2 * ∑ i ∈ S, e i := by
  have hs := Finset.sum_nonneg he
  have he1 (i) (hi : i ∈ S) : e i ≤ 1 :=
    (Finset.single_le_sum he hi).trans (hsmall.trans (by norm_num))
  have hlo := one_sub_sum_le_positive_prod S f e hf (fun i hi => ⟨he i hi, he1 i hi⟩)
    (fun i hi => by have h := (abs_le.mp (herror i hi)).1; linarith)
  have hhi : (∏ i ∈ S, f i) ≤ 1 + 2 * ∑ i ∈ S, e i := by
    apply (Finset.prod_le_prod hf (fun index hindex => ?_)).trans
      (prod_one_add_le_one_add_twice_sum S e he hsmall)
    have hupper := (abs_le.mp (herror index hindex)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rectangularResidueCount_eq_card {I : Type*} [Fintype I] [DecidableEq I] (a b r v : I → ℤ) :
    rectangularResidueCount a b r v = Fintype.card
      (∀ i, ↥(Finset.filter (fun x => x ≡ v i [ZMOD r i]) (Finset.Ico (a i) (b i)))) := by
  classical
  rw [Fintype.card_pi]
  simp [rectangularResidueCount, integerResidueCount]

theorem rectangularResidueCount_relative_error {I : Type*} [Fintype I]
    (a b r v : I → ℤ) (hab : ∀ i, a i < b i) (hr : ∀ i, 0 < r i)
    (hsmall : (∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) ≤ 1 / 2) :
    |(∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) - integerRectangleVolume a b| ≤
      (2 * ∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) * integerRectangleVolume a b := by
  let L : I → ℝ := fun i => ((b i - a i : ℤ) : ℝ)
  let c : I → ℝ := fun i => integerResidueCount (a i) (b i) (r i) (v i)
  let f : I → ℝ := fun i => c i * r i / L i
  let e : I → ℝ := fun i => (r i : ℝ) / L i
  have hL (i) : 0 < L i := by
    dsimp only [L]
    exact_mod_cast sub_pos.mpr (hab i)
  have hrR (i) : (0 : ℝ) < r i := by exact_mod_cast hr i
  have hV : 0 < integerRectangleVolume a b := Finset.prod_pos (fun i _ => hL i)
  have hprod := positive_prod_sub_one_le_twice_sum Finset.univ f e
    (fun i _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hrR i).le) (hL i).le)
    (fun i _ => (div_pos (hrR i) (hL i)).le)
    (fun i _ => scalarResidue_relative_count_error (a i) (b i) (r i) (v i) (hab i) (hr i)) hsmall
  have heq : (∏ i, f i) * integerRectangleVolume a b =
      (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
    change (∏ i, f i) * (∏ i, L i) = _
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i, f i * L i) = ∏ i, c i * r i := by
        apply Finset.prod_congr rfl
        intro i _
        exact div_mul_cancel₀ (c i * r i) (hL i).ne'
      _ = (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
        simp only [Finset.prod_mul_distrib, rectangularResidueCount, Nat.cast_prod, c]
        ring
  calc
    _ = |((∏ i, f i) - 1) * integerRectangleVolume a b| := by
      rw [← heq]
      congr 1
      ring
    _ = |(∏ i, f i) - 1| * integerRectangleVolume a b := by rw [abs_mul, abs_of_pos hV]
    _ ≤ (2 * ∑ i, e i) * integerRectangleVolume a b := mul_le_mul_of_nonneg_right hprod hV.le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rectangularResidueCount_pos {I : Type*} [Fintype I]
    (a b r v : I → ℤ) (hab : ∀ i, a i < b i) (hr : ∀ i, 0 < r i)
    (hsmall : (∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) < 1 / 2) :
    0 < rectangularResidueCount a b r v := by
  have hV : 0 < integerRectangleVolume a b :=
    Finset.prod_pos (fun i _ => by exact_mod_cast sub_pos.mpr (hab i))
  have hR : 0 < ∏ i, (r i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hr i)
  have hlower := (abs_le.mp (rectangularResidueCount_relative_error a b r v hab hr hsmall.le)).1
  have hmargin : 0 < (1 - 2 * ∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) * integerRectangleVolume a b :=
    mul_pos (by linarith) hV
  have hprod : 0 < (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by nlinarith
  exact_mod_cast (mul_pos_iff_of_pos_left hR).mp hprod

theorem rectangularResidueLaws_l1 {K I : Type*} [Fintype K] [Nonempty K] [Fintype I]
    (a b : K → I → ℤ) (r s : I → ℤ) (v w : K → I → ℤ)
    (hab : ∀ k i, a k i < b k i) (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    {ε : ℝ} (hε : ε < 1 / 2)
    (hsmallR : ∀ k, (∑ i, (r i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε)
    (hsmallS : ∀ k, (∑ i, (s i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε) :
    0 < (∑ k, (rectangularResidueCount (a k) (b k) r (v k) : ℝ)) ∧
    0 < (∑ k, (rectangularResidueCount (a k) (b k) s (w k) : ℝ)) ∧
    (∑ k, |(rectangularResidueCount (a k) (b k) r (v k) : ℝ) /
        (∑ j, (rectangularResidueCount (a j) (b j) r (v j) : ℝ)) -
      (rectangularResidueCount (a k) (b k) s (w k) : ℝ) /
        (∑ j, (rectangularResidueCount (a j) (b j) s (w j) : ℝ))|) ≤ 8 * ε := by
  let f : K → ℝ := fun k => integerRectangleVolume (a k) (b k)
  let R : ℝ := ∏ i, (r i : ℝ)
  let S : ℝ := ∏ i, (s i : ℝ)
  let cr : K → ℝ := fun k => rectangularResidueCount (a k) (b k) r (v k)
  let cs : K → ℝ := fun k => rectangularResidueCount (a k) (b k) s (w k)
  let g : K → ℝ := fun k => R * cr k
  let h : K → ℝ := fun k => S * cs k
  have hf (k) : 0 < f k := Finset.prod_pos (fun i _ => by exact_mod_cast sub_pos.mpr (hab k i))
  have hR : 0 < R := Finset.prod_pos (fun i _ => by exact_mod_cast hr i)
  have hS : 0 < S := Finset.prod_pos (fun i _ => by exact_mod_cast hs i)
  have hfMass : 0 < ∑ k, f k := Finset.sum_pos (fun k _ => hf k) Finset.univ_nonempty
  have hg (k) : 0 ≤ g k := mul_nonneg hR.le (Nat.cast_nonneg _)
  have hh (k) : 0 ≤ h k := mul_nonneg hS.le (Nat.cast_nonneg _)
  have hgerr (k) : |g k - f k| ≤ (2 * ε) * f k := by
    exact (rectangularResidueCount_relative_error (a k) (b k) r (v k) (hab k) hr
      ((hsmallR k).trans hε.le)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsmallR k) (by norm_num)) (hf k).le)
  have hherr (k) : |h k - f k| ≤ (2 * ε) * f k := by
    exact (rectangularResidueCount_relative_error (a k) (b k) s (w k) (hab k) hs
      ((hsmallS k).trans hε.le)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsmallS k) (by norm_num)) (hf k).le)
  have hgMass := finite_weight_mass_pos_of_relative_error f g hfMass (by linarith : 2 * ε < 1) hgerr
  have hhMass := finite_weight_mass_pos_of_relative_error f h hfMass (by linarith : 2 * ε < 1) hherr
  have hgsum : (∑ k, g k) = R * ∑ k, cr k := (Finset.mul_sum _ _ _).symm
  have hhsum : (∑ k, h k) = S * ∑ k, cs k := (Finset.mul_sum _ _ _).symm
  have hcr : 0 < ∑ k, cr k := (mul_pos_iff_of_pos_left hR).mp (hgsum ▸ hgMass)
  have hcs : 0 < ∑ k, cs k := (mul_pos_iff_of_pos_left hS).mp (hhsum ▸ hhMass)
  have hgnorm (k) : g k / (∑ j, g j) = cr k / (∑ j, cr j) := by
    rw [hgsum]
    dsimp only [g]
    field_simp
  have hhnorm (k) : h k / (∑ j, h j) = cs k / (∑ j, cs j) := by
    rw [hhsum]
    dsimp only [h]
    field_simp
  have hbound := normalized_finite_weights_pair_l1 f g h hg hh hfMass hgMass hhMass hgerr hherr
  simp only [hgnorm, hhnorm] at hbound
  refine ⟨hcr, hcs, hbound.trans_eq ?_⟩
  ring

theorem exists_rectangular_residue_piece_discrepancy {K I : Type*}
    [Fintype K] [Nonempty K] [Fintype I]
    (a b : K → I → ℤ) (r s : I → ℤ) (v w : K → I → ℤ)
    (hab : ∀ k i, a k i < b k i) (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    {ε : ℝ} (hε : ε < 1 / 2)
    (hsmallR : ∀ k, (∑ i, (r i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε)
    (hsmallS : ∀ k, (∑ i, (s i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε)
    (F G : K → ℂ) (hG : ∀ k, ‖G k‖ ≤ 1) :
    let nr : K → ℝ := fun k => rectangularResidueCount (a k) (b k) r (v k)
    let ns : K → ℝ := fun k => rectangularResidueCount (a k) (b k) s (w k)
    ∃ k, 0 < nr k ∧ 0 < ns k ∧
      ‖(∑ j, (nr j : ℂ) * F j) / ((∑ j, nr j : ℝ) : ℂ) -
        (∑ j, (ns j : ℂ) * G j) / ((∑ j, ns j : ℝ) : ℂ)‖ - 8 * ε ≤ ‖F k - G k‖ := by
  intro nr ns
  obtain ⟨hnr, hns, hl1⟩ := rectangularResidueLaws_l1 a b r s v w hab hr hs hε hsmallR hsmallS
  let p := FiniteProbabilityWeights.ofPositiveWeights nr (fun _ => Nat.cast_nonneg _) hnr
  let q := FiniteProbabilityWeights.ofPositiveWeights ns (fun _ => Nat.cast_nonneg _) hns
  obtain ⟨k, hk, hgap⟩ := p.exists_piece_discrepancy_of_weight_l1 q F G hG hl1
  have hk' : 0 < nr k / (∑ j, nr j) := hk
  have hkS : 0 < ns k := by
    change (0 : ℝ) < (rectangularResidueCount (a k) (b k) s (w k) : ℝ)
    exact_mod_cast rectangularResidueCount_pos (a k) (b k) s (w k) (hab k) hs ((hsmallS k).trans_lt hε)
  refine ⟨k, (div_pos_iff_of_pos_right hnr).mp hk', hkS, ?_⟩
  simpa only [p, q, FiniteProbabilityWeights.ofPositiveWeights_complexMean] using hgap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem comparableBoxPartitions_step {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (i : I)
    (k : (comparableBoxPartitions N H hH hHN i).Label) :
    (comparableBoxPartitions N H hH hHN i).step k = 1 := rfl

theorem comparableBoxPartitions_nonempty {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) :
    Nonempty (∀ i, (comparableBoxPartitions N H hH hHN i).Label) :=
  ⟨fun i => ⟨0, Nat.div_pos (hHN i) (hH i)⟩⟩

theorem intervalCell_width (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) :
    intervalCellUpper a P k - intervalCellLower a P k = P.length k := by
  dsimp only [intervalCellLower, intervalCellUpper]
  omega

theorem comparableBoxPartitions_ratio_le {I : Type*} [Fintype I]
    (a : I → ℤ) (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (r : I → ℤ) (hr : ∀ i, 0 ≤ r i)
    (k : ∀ i, (comparableBoxPartitions N H hH hHN i).Label) :
    (∑ i, (r i : ℝ) /
      ((intervalCellUpper (a i) (comparableBoxPartitions N H hH hHN i) (k i) -
        intervalCellLower (a i) (comparableBoxPartitions N H hH hHN i) (k i) : ℤ) : ℝ)) ≤
      ∑ i, (r i : ℝ) / (H i : ℝ) := by
  apply Finset.sum_le_sum
  intro i _
  rw [intervalCell_width]
  have hlen : (H i : ℝ) ≤ (comparableBoxPartitions N H hH hHN i).length (k i) := by
    exact_mod_cast (comparableBoxPartitions_length N H hH hHN i (k i)).1
  simp only [Int.cast_natCast]
  exact div_le_div_of_nonneg_left (by exact_mod_cast hr i) (by exact_mod_cast hH i) hlen

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonStrideResidueGeometry
namespace OAI

section

namespace Erdos3

theorem commonStridePoint_index_of_modEq {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) :
    commonStridePoint c m (commonStrideIndex c m y) = y := by
  funext i
  have hd := Int.modEq_iff_dvd.mp (hy i).symm
  change c i + (m : ℤ) * ((y i - c i) / (m : ℤ)) = y i
  rw [mul_comm, Int.ediv_mul_cancel hd]
  omega

theorem commonStrideIndex_difference {I : Type*} (c : I → ℤ) (m : ℕ) (y z : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)]) (i : I) :
    (m : ℤ) * (commonStrideIndex c m y i - commonStrideIndex c m z i) = y i - z i := by
  have hye := congrFun (commonStridePoint_index_of_modEq c m y hy) i
  have hze := congrFun (commonStridePoint_index_of_modEq c m z hz) i
  change c i + (m : ℤ) * commonStrideIndex c m y i = y i at hye
  change c i + (m : ℤ) * commonStrideIndex c m z i = z i at hze
  calc
    _ = (c i + (m : ℤ) * commonStrideIndex c m y i) -
        (c i + (m : ℤ) * commonStrideIndex c m z i) := by ring
    _ = _ := by rw [hye, hze]

theorem commonStrideIndex_period {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m)
    (q : ℕ) (y z : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)])
    (hperiod : ∀ i, ((m * q : ℕ) : ℤ) ∣ (y i - z i)) :
    ∀ i, (q : ℤ) ∣ commonStrideIndex c m y i - commonStrideIndex c m z i := by
  intro i
  apply (mul_dvd_mul_iff_left (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)).mp
  rw [commonStrideIndex_difference c m y z hy hz i]
  simpa only [Nat.cast_mul] using hperiod i

theorem commonStrideIndex_abs_difference {I : Type*} (c : I → ℤ) (m : ℕ) (y z : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)]) (i : I) :
    (m : ℝ) * |(commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ)| =
      |(y i : ℝ) - (z i : ℝ)| := by
  have he : (m : ℝ) * ((commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ)) =
      (y i : ℝ) - (z i : ℝ) := by
    exact_mod_cast commonStrideIndex_difference c m y z hy hz i
  calc
    _ = |(m : ℝ) * ((commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ))| := by
      rw [abs_mul, (show |(m : ℝ)| = (m : ℝ) from abs_of_nonneg (Nat.cast_nonneg m))]
    _ = _ := congrArg abs he

theorem commonStrideIndex_distance_le {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m)
    (y z : I → ℤ) (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)])
    (A : I → ℝ) (δ : ℝ) (hdist : ∀ i, |(y i : ℝ) - (z i : ℝ)| ≤ (m : ℝ) * A i * δ) :
    ∀ i, |(commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ)| ≤ A i * δ := by
  intro i
  apply (mul_le_mul_iff_right₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mp
  rw [commonStrideIndex_abs_difference c m y z hy hz i]
  simpa only [mul_assoc] using hdist i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AuxiliaryBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boxAuxiliaryCell_card {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (R c : I → ℤ)
    (hcombine : ∀ i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c i [ZMOD R i]) :
    (partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k).card =
      rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c := by
  have he := Fintype.card_congr (boxAuxiliaryCellEquiv a N P hstep hpos M d hd u r b hbase k R c hcombine)
  calc
    _ = Fintype.card (IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c) := by
      simpa only [Fintype.card_coe] using he
    _ = _ := (rectangularResidueCount_eq_card _ _ _ _).symm

theorem boxAuxiliaryCell_mixture {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (R : I → ℤ) (c : AuxiliaryBoxLabels P M d u → I → ℤ)
    (hcombine : ∀ k i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c k i [ZMOD R i])
    (f : IntegerResidueBox a (fun i => a i + N i) r b → ℂ) :
    (𝔼 x, f x) = ∑ k : AuxiliaryBoxLabels P M d u,
      ((rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
          (fun i => intervalCellUpper (a i) (P i) (k i).1) R (c k) : ℝ) /
        (∑ j : AuxiliaryBoxLabels P M d u, (rectangularResidueCount
          (fun i => intervalCellLower (a i) (P i) (j i).1)
          (fun i => intervalCellUpper (a i) (P i) (j i).1) R (c j) : ℝ)) : ℂ) *
      (𝔼 x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k, f x) := by
  have hcard (k : AuxiliaryBoxLabels P M d u) :=
    boxAuxiliaryCell_card a N P hstep hpos M d hd u r b hbase k R (c k) (hcombine k)
  simpa only [hcard] using
    complex_expect_partition_count_weights (boxAuxiliaryCell a N P M d hd u r b hbase) f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AuxiliaryBoxLaws
namespace OAI

section

namespace Erdos3

theorem auxiliaryBoxLabels_nonempty {I : Type*} {N : I → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hP : Nonempty (∀ i, (P i).Label))
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u : I → ℤ) :
    Nonempty (AuxiliaryBoxLabels P M d u) := by
  obtain ⟨k⟩ := hP
  exact ⟨fun i => (k i, compatibleAuxResidueOfPoint (M i) (d i) (hd i)
    (u i) (u i) (Int.ModEq.refl (u i)))⟩

theorem baseAuxiliaryBoxCell_card {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u : I → ℤ) (k : AuxiliaryBoxLabels P M d u) :
    (partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k).card =
      rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1)
        (fun i => (Nat.lcm (M i) (d i) : ℤ)) (fun i => (k i).2.baseValue) :=
  boxAuxiliaryCell_card a N P hstep hpos M d hd u (fun i => (M i : ℤ)) u
    (fun _ _ hx => hx) k (fun i => (Nat.lcm (M i) (d i) : ℤ)) (fun i => (k i).2.baseValue)
    (fun i => (k i).2.baseConstraint_iff)

theorem refinedAuxiliaryBoxCell_card {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d J : I → ℕ) (hd : ∀ i, 0 < d i) (u w : I → ℤ)
    (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)]) (hcop : ∀ i, (M i * d i).Coprime (J i))
    (k : AuxiliaryBoxLabels P M d u) :
    (partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k).card =
      rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1)
        (fun i => (Nat.lcm (M i) (d i) * J i : ℕ))
        (fun i => (k i).2.refinedValue (hcop i) (w i)) :=
  boxAuxiliaryCell_card a N P hstep hpos M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i)) k
    (fun i => (Nat.lcm (M i) (d i) * J i : ℕ)) (fun i => (k i).2.refinedValue (hcop i) (w i))
    (fun i => (k i).2.refinedConstraint_iff (hcop i) (w i) (hw i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AuxiliaryStrideGeometry
namespace OAI

section

namespace Erdos3

theorem mem_boxAuxiliaryCell_iff {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (x : IntegerResidueBox a (fun i => a i + N i) r b) :
    x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k ↔
      ∀ i, (intervalCellLower (a i) (P i) (k i).1 ≤ (x i).val ∧
        (x i).val < intervalCellUpper (a i) (P i) (k i).1) ∧
        (x i).val ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)] := by
  simp only [mem_partitionCell, boxAuxiliaryCell, funext_iff]
  apply forall_congr'
  intro i
  exact intervalAuxiliaryCell_eq_iff (a i) (P i) (hstep i) (M i) (d i) (hd i)
    (u i) (r i) (b i) (hbase i) (x i) (k i)

theorem boxAuxiliaryCell_same_piece {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b s c : I → ℤ)
    (hbaseR : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (hbaseS : ∀ i (x : ℤ), x ≡ c i [ZMOD s i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u)
    (x : IntegerResidueBox a (fun i => a i + N i) r b)
    (y : IntegerResidueBox a (fun i => a i + N i) s c)
    (hx : x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbaseR) k)
    (hy : y ∈ partitionCell (boxAuxiliaryCell a N P M d hd u s c hbaseS) k) :
    ∀ i, (d i : ℤ) ∣ (x i).val - (y i).val ∧
      |((x i).val : ℝ) - ((y i).val : ℝ)| < ((P i).length (k i).1 : ℝ) := by
  have hx' := (mem_boxAuxiliaryCell_iff a N P hstep M d hd u r b hbaseR k x).mp hx
  have hy' := (mem_boxAuxiliaryCell_iff a N P hstep M d hd u s c hbaseS k y).mp hy
  intro i
  refine ⟨Int.modEq_iff_dvd.mp ((hy' i).2.trans (hx' i).2.symm), ?_⟩
  have hxi := (hx' i).1
  have hyi := (hy' i).1
  have hw := intervalCell_width (a i) (P i) (k i).1
  have hdiff : |(x i).val - (y i).val| < ((P i).length (k i).1 : ℤ) :=
    abs_lt.mpr ⟨by omega, by omega⟩
  exact_mod_cast hdiff

end Erdos3

end

section

namespace Erdos3

theorem commonStrideIndex_bound {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m)
    (y : I → ℤ) (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (A : I → ℝ)
    (hbound : ∀ i, |(y i : ℝ) - (c i : ℝ)| ≤ (m : ℝ) * A i) :
    ∀ i, |(commonStrideIndex c m y i : ℝ)| ≤ A i := by
  have h := commonStrideIndex_distance_le c hm y c hy (fun i => Int.ModEq.refl (c i)) A 1
    (by simpa only [mul_one] using hbound)
  simpa only [commonStrideIndex, sub_self, Int.zero_ediv, Int.cast_zero, sub_zero, mul_one] using h

theorem auxiliaryPiece_stride_geometry {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (Q : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (Q i).step k = 1) (M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (u r b : I → ℤ) (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M : ℤ)])
    (k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * q) u)
    (y : IntegerResidueBox a (fun i => a i + N i) r b)
    (z : IntegerResidueBox a (fun i => a i + N i) (fun _ => (M : ℤ)) u)
    (hy : y ∈ partitionCell (boxAuxiliaryCell a N Q (fun _ => M) (fun _ => M * q)
      (fun _ => Nat.mul_pos hM hq) u r b hbase) k)
    (hz : z ∈ partitionCell (baseAuxiliaryBoxCell a N Q (fun _ => M) (fun _ => M * q)
      (fun _ => Nat.mul_pos hM hq) u) k)
    (A : I → ℝ) (δ : ℝ)
    (hwidth : ∀ i, ((Q i).length (k i).1 : ℝ) ≤ (M : ℝ) * A i * δ) :
    (∀ i, (q : ℤ) ∣ commonStrideIndex u M (fun j => (y j).val) i -
      commonStrideIndex u M (fun j => (z j).val) i) ∧
    (∀ i, |(commonStrideIndex u M (fun j => (y j).val) i : ℝ) -
      (commonStrideIndex u M (fun j => (z j).val) i : ℝ)| ≤ A i * δ) := by
  have hgeom := boxAuxiliaryCell_same_piece a N Q hstep (fun _ => M) (fun _ => M * q)
    (fun _ => Nat.mul_pos hM hq) u r b (fun _ => (M : ℤ)) u hbase (fun _ _ hx => hx) k y z hy hz
  have hmy : ∀ i, (y i).val ≡ u i [ZMOD (M : ℤ)] :=
    fun i => hbase i (y i).val (Finset.mem_filter.mp (y i).property).2
  have hmz : ∀ i, (z i).val ≡ u i [ZMOD (M : ℤ)] :=
    fun i => (Finset.mem_filter.mp (z i).property).2
  exact ⟨commonStrideIndex_period u hM q _ _ hmy hmz (fun i => (hgeom i).1),
    commonStrideIndex_distance_le u hM _ _ hmy hmz A δ (fun i => (hgeom i).2.le.trans (hwidth i))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eval₂_substitute (f : σ → MvPolynomial τ R) (x : τ → S)
    (p : VectorPolynomial σ R V) :
    eval₂ x (substitute f p) = eval₂ (fun i => MvPolynomial.aeval x (f i)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
      simp only [substitute_tmul, eval₂_tmul]
      rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem eval_freeze_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) (a₀ r₀ : D.RealGroup)
    {p δ : ℝ} (hT : T.ComplexityLE p)
    (hr : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) R) : D.Space) =
      QuotientGroup.mk r₀)
    (hE : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      dist (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) E) a₀ ≤ δ) :
    ‖T.eval x - T.observable (QuotientGroup.mk
      (a₀ * D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
      Real.exp p * δ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hLip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  rw [eval_of_lattice_factorization D w T E b R κ hκ hprod x]
  exact (T.observable_freeze_factors _ a₀ _ _ r₀ hr).trans
    ((mul_le_mul_of_nonneg_right hLip dist_nonneg).trans
      (mul_le_mul_of_nonneg_left hE (Real.exp_pos p).le))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

theorem residueBox_stride_bound {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (M : ℕ) (hM : 0 < M) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M : ℤ)])
    (A : I → ℝ)
    (hphysical : ∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (a i : ℝ) ∧
      (a i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i)
    (x : IntegerResidueBox a (fun i => a i + N i) r b) :
    ∀ i, |(commonStrideIndex u M (fun j => (x j).val) i : ℝ)| ≤ A i := by
  apply commonStrideIndex_bound u hM _
    (fun i => hbase i (x i).val (Finset.mem_filter.mp (x i).property).2) A
  intro i
  have hx := Finset.mem_Ico.mp (Finset.mem_filter.mp (x i).property).1
  have hlo : (a i : ℝ) ≤ (x i).val := by exact_mod_cast hx.1
  have hhi : ((x i).val : ℝ) < (a i : ℝ) + (N i : ℝ) := by exact_mod_cast hx.2
  exact abs_le.mpr ⟨by linarith [(hphysical i).1], by linarith [(hphysical i).2]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AuxiliaryResidueLocalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_auxiliary_residue_piece {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (M d J : I → ℕ) (hM : ∀ i, 0 < M i) (hd : ∀ i, 0 < d i) (hJ : ∀ i, 0 < J i)
    (u w : I → ℤ) (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)])
    (hcop : ∀ i, (M i * d i).Coprime (J i)) {ε : ℝ} (hε : ε < 1 / 2)
    (hsmall : (∑ i, (Nat.lcm (M i) (d i) * J i : ℕ) / (H i : ℝ)) ≤ ε)
    (f : IntegerResidueBox a (fun i => a i + N i) (fun i => (M i : ℤ)) u → ℂ)
    (g : IntegerResidueBox a (fun i => a i + N i) (fun i => (M i * J i : ℕ)) w → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) :
    let P := comparableBoxPartitions N H hH hHN
    ∃ k : AuxiliaryBoxLabels P M d u,
      0 < (partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k).card ∧
      0 < (partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k).card ∧
      ‖(𝔼 x, f x) - (𝔼 x, g x)‖ - 8 * ε ≤
        ‖(𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k, f x) -
          (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k, g x)‖ := by
  intro P
  let := auxiliaryBoxLabels_nonempty P (comparableBoxPartitions_nonempty N H hH hHN) M d hd u
  have hstep : ∀ i k, (P i).step k = 1 := comparableBoxPartitions_step N H hH hHN
  have hpos : ∀ i k, 0 < (P i).length k := fun i k =>
    (hH i).trans_le (comparableBoxPartitions_length N H hH hHN i k).1
  let lo : AuxiliaryBoxLabels P M d u → I → ℤ :=
    fun k i => intervalCellLower (a i) (P i) (k i).1
  let hi : AuxiliaryBoxLabels P M d u → I → ℤ :=
    fun k i => intervalCellUpper (a i) (P i) (k i).1
  let R : I → ℤ := fun i => Nat.lcm (M i) (d i)
  let S : I → ℤ := fun i => (Nat.lcm (M i) (d i) * J i : ℕ)
  let v : AuxiliaryBoxLabels P M d u → I → ℤ := fun k i => (k i).2.baseValue
  let z : AuxiliaryBoxLabels P M d u → I → ℤ := fun k i => (k i).2.refinedValue (hcop i) (w i)
  have hL : ∀ i, 0 < Nat.lcm (M i) (d i) := fun i =>
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hM i).ne' (hd i).ne')
  have hRpos : ∀ i, 0 < R i := by
    intro i
    dsimp only [R]
    exact_mod_cast hL i
  have hSpos : ∀ i, 0 < S i := by
    intro i
    dsimp only [S]
    exact_mod_cast Nat.mul_pos (hL i) (hJ i)
  have hsmallS : (∑ i, (S i : ℝ) / (H i : ℝ)) ≤ ε := by
    simpa only [S, Int.cast_natCast] using hsmall
  have hsmallR : (∑ i, (R i : ℝ) / (H i : ℝ)) ≤ ε := by
    apply le_trans (Finset.sum_le_sum fun i _ => ?_) hsmallS
    apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have hle : Nat.lcm (M i) (d i) ≤ Nat.lcm (M i) (d i) * J i := by
      nlinarith [hJ i]
    dsimp only [R, S]
    exact_mod_cast hle
  have hbox : ∀ k i, lo k i < hi k i := by
    intro k i
    apply sub_pos.mp
    change 0 < intervalCellUpper (a i) (P i) (k i).1 - intervalCellLower (a i) (P i) (k i).1
    rw [intervalCell_width]
    exact_mod_cast hpos i (k i).1
  have hR : ∀ k, (∑ i, (R i : ℝ) / ((hi k i - lo k i : ℤ) : ℝ)) ≤ ε :=
    fun k => (comparableBoxPartitions_ratio_le a N H hH hHN R (fun i => (hRpos i).le)
      (fun i => (k i).1)).trans hsmallR
  have hS : ∀ k, (∑ i, (S i : ℝ) / ((hi k i - lo k i : ℤ) : ℝ)) ≤ ε :=
    fun k => (comparableBoxPartitions_ratio_le a N H hH hHN S (fun i => (hSpos i).le)
      (fun i => (k i).1)).trans hsmallS
  let F : AuxiliaryBoxLabels P M d u → ℂ := fun k =>
    𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k, f x
  let G : AuxiliaryBoxLabels P M d u → ℂ := fun k =>
    𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k, g x
  have hG : ∀ k, ‖G k‖ ≤ 1 := by
    intro k
    let A := partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k
    change ‖𝔼 x ∈ A, g x‖ ≤ 1
    by_cases hA : A.Nonempty
    · apply (RCLike.norm_expect_le (K := ℂ)).trans
      exact (Finset.expect_le_expect (fun x _ => hg x)).trans_eq (Finset.expect_const hA 1)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hA
      simp only [he, Finset.expect_empty, norm_zero, zero_le_one]
  obtain ⟨k, hkr, hks, hgap⟩ := exists_rectangular_residue_piece_discrepancy
    lo hi R S v z hbox hRpos hSpos hε hR hS F G hG
  have hmR := boxAuxiliaryCell_mixture a N P hstep hpos M d hd u (fun i => (M i : ℤ)) u
    (fun _ _ hx => hx) R v (fun k i => (k i).2.baseConstraint_iff) f
  have hmS := boxAuxiliaryCell_mixture a N P hstep hpos M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i)) S z
    (fun k i => (k i).2.refinedConstraint_iff (hcop i) (w i) (hw i)) g
  simp only [div_mul_eq_mul_div, ← Finset.sum_div] at hmR hmS
  dsimp only [F, G, lo, hi, baseAuxiliaryBoxCell, refinedAuxiliaryBoxCell] at hgap
  rw [← hmR, ← hmS] at hgap
  refine ⟨k, ?_, ?_, hgap⟩
  · rw [baseAuxiliaryBoxCell_card a N P hstep hpos M d hd u]
    exact Nat.cast_pos.mp hkr
  · rw [refinedAuxiliaryBoxCell_card a N P hstep hpos M d J hd u w hw hcop]
    exact Nat.cast_pos.mp hks

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem complex_discrepancy_after_freezing {X Y : Type*} (A : Finset X) (B : Finset Y)
    (f f₀ : X → ℂ) (g g₀ : Y → ℂ) {η₀ η₁ : ℝ} (hη₀ : 0 ≤ η₀) (hη₁ : 0 ≤ η₁)
    (hf : ∀ x ∈ A, ‖f x - f₀ x‖ ≤ η₀) (hg : ∀ y ∈ B, ‖g y - g₀ y‖ ≤ η₁) :
    ‖(𝔼 x ∈ A, f x) - (𝔼 y ∈ B, g y)‖ - η₀ - η₁ ≤
      ‖(𝔼 x ∈ A, f₀ x) - (𝔼 y ∈ B, g₀ y)‖ := by
  have hf' := complex_expect_error_le A f f₀ hη₀ hf
  have hg' := complex_expect_error_le B g g₀ hη₁ hg
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (𝔼 x ∈ A, f x) (𝔼 x ∈ A, f₀ x) (𝔼 y ∈ B, g y)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (𝔼 x ∈ A, f₀ x) (𝔼 y ∈ B, g₀ y) (𝔼 y ∈ B, g y)
  rw [norm_sub_rev (𝔼 y ∈ B, g₀ y) (𝔼 y ∈ B, g y)] at h₂
  linarith

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_slow_factor_freezing (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      ∀ S : D.Niltest w, S.ComplexityLE p →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
          D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) E →
          ∀ (x : σ → ℤ) (z : σ → ℝ) (r₀ : D.RealGroup) (δ : ℝ), 0 ≤ δ →
            (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |z i| ≤ T i) →
            (∀ i, |(x i : ℝ) - z i| ≤ T i * δ) →
            (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
              (fun i => (x i : ℝ)) R) : D.Space) = QuotientGroup.mk r₀ →
            ‖S.eval x - S.observable (QuotientGroup.mk
              (D.filtration.adaptedPolynomialRealValueHom w z E *
                D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
              Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hmove⟩ := exists_polynomialSlowBound_dist_exp s r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hσ S hS E b R κ hκ hprod T hT hE x z r₀ δ hδ hx hz hxz hR
  have hdist := hmove D w hw p hp hS.1 hσ T hT E hE
    (fun i => (x i : ℝ)) z δ hδ hx hz hxz
  have hfreeze := S.eval_freeze_of_lattice_factorization E b R κ hκ hprod x
    (D.filtration.adaptedPolynomialRealValueHom w z E) r₀ hS hR hdist
  apply hfreeze.trans
  rw [← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hδ
  simpa [Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_anchored_factor_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ S : D.Niltest w, S.ComplexityLE p →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis w q R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E →
          ∀ z : σ → ℤ, (∀ i, |(z i : ℝ)| ≤ A i) →
            let l₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z i : ℝ)) E
            let r₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z i : ℝ)) R
            (∀ i, |(D.basis.baseChange ℝ).repr l₀.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r₀.coord ∈ realDenominatorGrid q ∧
            ∀ (x : σ → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, (P : ℤ) ∣ x i - z i) →
              (∀ i, |(x i : ℝ) - (z i : ℝ)| ≤ A i * δ) →
              ‖S.eval x - S.observable (QuotientGroup.mk
                (l₀ * D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
                Real.exp ((p + 2) ^ C) * δ := by
  obtain ⟨u, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨v, _, hfreeze⟩ := exists_slow_factor_freezing s a
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C s * (X + 1) + (X + 2) ^ a +
    (X + Polynomial.C u) ^ u + (X + Polynomial.C v) ^ v
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget B
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  have hsum : (s : ℝ) * (p + 1) + (p + 2) ^ a + (p + u) ^ u + (p + v) ^ v ≤
      (p + 2) ^ C := by
    simpa [B, X, Polynomial.eval₂_pow] using hbudget p hp
  have hcoord : (s : ℝ) * (p + 1) + (p + 2) ^ a ≤ (p + 2) ^ C := by
    nlinarith [pow_nonneg (by positivity : 0 ≤ p + (u : ℝ)) u,
      pow_nonneg (by positivity : 0 ≤ p + (v : ℝ)) v]
  have hu : (p + u) ^ u ≤ (p + 2) ^ C := by
    nlinarith [pow_nonneg (by positivity : 0 ≤ p + 2) a,
      pow_nonneg (by positivity : 0 ≤ p + (v : ℝ)) v, Nat.cast_nonneg (α := ℝ) s]
  have hv : (p + v) ^ v ≤ (p + 2) ^ C := by
    nlinarith [pow_nonneg (by positivity : 0 ≤ p + 2) a,
      pow_nonneg (by positivity : 0 ≤ p + (u : ℝ)) u, Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨P, hP, hPb, hcoset⟩ := hperiod D w hw p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hu), ?_⟩
  intro S hS E b R κ hκ hprod hgrid A hA hE z hz l₀ r₀
  refine ⟨?_, D.filtration.polynomialRationalGrid_value D.basis w q R hgrid z, ?_⟩
  · intro i
    have hzbound := D.filtration.polynomialSlowBound_value D.basis w hw A hA
      (Real.exp_nonneg _) E hE (fun j => (z j : ℝ)) hz i
    have hn1 : (Fintype.card σ : ℝ) + 1 ≤ Real.exp p := by
      linarith [Real.add_one_le_exp p]
    apply hzbound.trans
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (Real.add_one_le_exp (s : ℝ))
            (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = Real.exp ((s : ℝ) * (p + 1) + (p + 2) ^ a) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hcoord
  · intro x δ hδ hx hcongr hdist
    have hb := hfreeze D w hw p hp hσ S hS E b R κ hκ hprod A hA hE
      x (fun i => (z i : ℝ)) r₀ δ hδ hx hz hdist (hcoset R hgrid x z hcongr).1
    exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hv) hδ)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_auxiliary_frozen_discrepancy (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ S : D.Niltest w, S.ComplexityLE p → S.UnitIntervalValued →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis w q R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E →
          ∀ (M : ℕ) (hM : 0 < M) (lo : σ → ℤ) (N H : σ → ℕ)
            (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (u v : σ → ℤ) (J : σ → ℕ),
            (∀ i, 0 < J i) → ∀ (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]),
            (∀ i, (M * (M * P)).Coprime (J i)) →
            ∀ (δ ε : ℝ), 0 ≤ δ → ε < 1 / 2 →
            (∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ) →
            (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
              (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
            (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (H i : ℝ)) ≤ ε →
            let Q := comparableBoxPartitions N H hH hHN
            let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
              (fun _ => Nat.mul_pos hM hP) u
            let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
              (fun _ => Nat.mul_pos hM hP) u v hv
            let F : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u → ℂ :=
              residueBoxStrideValue S.eval u M
            let G : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v → ℂ :=
              residueBoxStrideValue S.eval u M
            ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
              0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
              ∃ l₀ r₀ : D.RealGroup,
                (∀ i, |(D.basis.baseChange ℝ).repr l₀.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
                (D.basis.baseChange ℝ).equivFun r₀.coord ∈ realDenominatorGrid q ∧
                let T : (σ → ℤ) → ℂ := fun x => S.observable (QuotientGroup.mk
                  (l₀ * D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))
                ‖(𝔼 x, F x) - (𝔼 x, G x)‖ - 8 * ε - 2 * (Real.exp ((p + 2) ^ C) * δ) ≤
                  ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue T u M x) -
                    (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue T u M x)‖ := by
  obtain ⟨C, hC, hanchor⟩ := exists_anchored_factor_freezing s a
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨P, hP, hPb, hfreeze⟩ := hanchor D w hw p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb, ?_⟩
  intro S hS hunit E b R κ hκ hprod hgrid A hA hE M hM lo N H hH hHN u v J hJ hv hcop
    δ ε hδ hε hsize hphysical hsmall Q c₀ c₁ F G
  have hG : ∀ x, ‖G x‖ ≤ 1 := fun x => hunit.norm_le_one _
  obtain ⟨k, hk₀, hk₁, hgap⟩ := exists_auxiliary_residue_piece lo N H hH hHN
    (fun _ => M) (fun _ => M * P) J (fun _ => hM) (fun _ => Nat.mul_pos hM hP) hJ
    u v hv hcop hε hsmall F G hG
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hk₀
  have hzb := residueBox_stride_bound lo N M hM u (fun _ => (M : ℤ)) u
    (fun _ _ hx => hx) A hphysical z
  let z₀ := commonStrideIndex u M (fun i => (z i).val)
  let l₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z₀ i : ℝ)) E
  let r₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z₀ i : ℝ)) R
  obtain ⟨hl₀, hr₀, hpoint⟩ := hfreeze S hS E b R κ hκ hprod hgrid A hA hE z₀ hzb
  refine ⟨k, hk₀, hk₁, l₀, r₀, hl₀, hr₀, ?_⟩
  intro T
  have hstep : ∀ i j, (Q i).step j = 1 := comparableBoxPartitions_step N H hH hHN
  have hwidth : ∀ i, ((Q i).length (k i).1 : ℝ) ≤ (M : ℝ) * A i * δ := by
    intro i
    have hlen : ((Q i).length (k i).1 : ℝ) < 2 * (H i : ℝ) := by
      exact_mod_cast (comparableBoxPartitions_length N H hH hHN i (k i).1).2
    exact hlen.le.trans (hsize i)
  have hnear₀ : ∀ x ∈ partitionCell c₀ k,
      ‖F x - residueBoxStrideValue T u M x‖ ≤ Real.exp ((p + 2) ^ C) * δ := by
    intro x hx
    have hgeom := auxiliaryPiece_stride_geometry lo N Q hstep M P hM hP
      u (fun _ => (M : ℤ)) u (fun _ _ he => he) k x z hx hz A δ hwidth
    have hxb := residueBox_stride_bound lo N M hM u (fun _ => (M : ℤ)) u
      (fun _ _ he => he) A hphysical x
    exact hpoint (commonStrideIndex u M (fun i => (x i).val)) δ hδ hxb hgeom.1 hgeom.2
  have hnear₁ : ∀ x ∈ partitionCell c₁ k,
      ‖G x - residueBoxStrideValue T u M x‖ ≤ Real.exp ((p + 2) ^ C) * δ := by
    intro x hx
    have hgeom := auxiliaryPiece_stride_geometry lo N Q hstep M P hM hP
      u (fun i => (M * J i : ℕ)) v
      (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) k x z hx hz A δ hwidth
    have hxb := residueBox_stride_bound lo N M hM u (fun i => (M * J i : ℕ)) v
      (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) A hphysical x
    exact hpoint (commonStrideIndex u M (fun i => (x i).val)) δ hδ hxb hgeom.1 hgeom.2
  have hη : 0 ≤ Real.exp ((p + 2) ^ C) * δ := mul_nonneg (Real.exp_nonneg _) hδ
  have herr := complex_discrepancy_after_freezing (partitionCell c₀ k) (partitionCell c₁ k)
    F (residueBoxStrideValue T u M) G (residueBoxStrideValue T u M) hη hη hnear₀ hnear₁
  linarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledSingleRefilteredReconstruction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem SingleRefilteredRecoveryFamily.exists_fixed_child
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
    (hEF : E.filtration = D.filtration.gradedRefiltration W)
    (hQF : Q.filtration = E.filtration.quotientTop)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (b : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hb : ∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hb0 : coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    {p cost : ℝ} {q k : ℕ} (hcost : 0 ≤ cost)
    (h : SingleRefilteredRecoveryFamily D W E Q p q k cost) :
    let H := D.filtration.gradedRefiltrationSubalgebra W
    let N := H ⧸ E.filtration.layerIdeal (s + 1)
    let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
    let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
    let := realification_moduleTopology_t2 Q.basis
    let T := Q.raiseStep (Nat.le_succ s)
    ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
      (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
      (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
      ∃ (B : ℕ) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
        (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
        let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
        V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
        ∃ child : V.filtration.realification.PolynomialOrbit w,
          DegreeLE w s child.log ∧
          ∀ l r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (let := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
                ∀ x, S (z • x) = S x) →
              V.FixedPositiveNiltestRealization child (cost + 4) (fun x =>
                S (QuotientGroup.mk (l *
                  D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r))) := by
  intro H N _ _ _ T
  obtain ⟨g, hg⟩ := D.filtration.exists_model_refiltered_polynomial W E hEF w hw b hb hb0
  let gbar := E.topQuotientOrbit Q hQF g
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV, hfrozen⟩ := h
  let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
  let child : V.filtration.realification.PolynomialOrbit w := gbar
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, child.degreeLE, ?_⟩
  intro l r hl hr S ℓ hℓ hS hunit hinvariant
  obtain ⟨v, K, hK, hv, hpos, hcap, heval⟩ := hfrozen l r hl hr S ℓ hℓ hS hunit hinvariant
  let U : V.Niltest w := {
    orbit := child
    observable := v
    normBound := 1
    lipBound := K
    norm_le := hcap
    lipschitz := hv }
  have hUc : U.ComplexityLE (cost + 4) := by
    refine ⟨hV.mono V (by linarith), ?_⟩
    change Real.log (2 + (1 : ℝ) + (K : ℝ)) ≤ cost + 4
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    calc
      _ ≤ 4 * Real.exp cost := by linarith [Real.one_le_exp hcost]
      _ ≤ Real.exp 4 * Real.exp cost := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (cost + 4) := by rw [← Real.exp_add, add_comm]
  refine ⟨U, rfl, hpos, hUc, ?_⟩
  intro x
  have hquot := E.topQuotientOrbit_eval Q hQF g x
  have hfirst := congrArg (fun y : Q.RealGroup => v (QuotientGroup.mk y)) hquot
  have hsecond := heval (E.filtration.realification.polynomialOrbitEval w x g)
  have hthird := congrArg (fun y : D.RealGroup => S (QuotientGroup.mk (l * y * r))) (hg x)
  exact hfirst.trans (hsecond.trans hthird)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem FixedPositiveNiltestRealization.transfer_discrepancy
    {σ K X Y : Type*} [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {t d : ℕ}
    {V : RationalFilteredNilmanifold K t d} {w : σ → ℕ}
    {child : V.filtration.realification.PolynomialOrbit w} {cost : ℝ} {f : (σ → ℤ) → ℂ}
    (h : V.FixedPositiveNiltestRealization child cost f)
    (A : Finset X) (B : Finset Y) (x : X → σ → ℤ) (y : Y → σ → ℤ)
    {Δ : ℝ} (hgap : Δ ≤ ‖(𝔼 i ∈ A, f (x i)) - (𝔼 j ∈ B, f (y j))‖) :
    ∃ U : V.Niltest w, U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
      Δ ≤ ‖(𝔼 i ∈ A, U.eval (x i)) - (𝔼 j ∈ B, U.eval (y j))‖ := by
  obtain ⟨U, hU, hunit, hcost, heval⟩ := h
  refine ⟨U, hU, hunit, hcost, ?_⟩
  simpa only [heval] using hgap

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem scalarAffineAdaptedHom_coord {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ)
    (g : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    ((F.scalarAffineAdaptedHom r h g).coord : VectorPolynomial σ ℚ L) =
      weightedDilation (fun _ : σ => 1) r (translate h (g.coord : VectorPolynomial σ ℚ L)) := by
  change substitute (scalarAffinePolynomial r h) (g.coord : VectorPolynomial σ ℚ L) = _
  exact substitute_scalarAffinePolynomial r h _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem scalarAffineAdaptedHom_value (r : ℚ) (h : σ → ℚ) (x : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedPolynomialRealValueHom (fun _ : σ => 1) x
        (F.realification.scalarAffineAdaptedHom r h g) =
      F.adaptedPolynomialRealValueHom (fun _ : σ => 1)
        (fun i => (h i : ℝ) + (r : ℝ) * x i) g := by
  apply NilpotentLieBCHGroup.ext
  rw [adaptedPolynomialRealValueHom_coord, adaptedPolynomialRealValueHom_coord,
    scalarAffineAdaptedHom_coord, ← substitute_scalarAffinePolynomial, eval₂_substitute]
  apply congrArg (fun y : σ → ℝ => eval₂ y (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  funext i
  simp [scalarAffinePolynomial]

theorem scalarAffineAdaptedHom_value_integer (r : ℚ) (h : σ → ℚ) (x y : σ → ℤ)
    (hxy : ∀ i, h i + r * (x i : ℚ) = (y i : ℚ))
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ))
        (F.realification.scalarAffineAdaptedHom r h g) =
      F.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (y i : ℝ)) g := by
  rw [scalarAffineAdaptedHom_value]
  have heq : (fun i => (h i : ℝ) + (r : ℝ) * (x i : ℝ)) = (fun i => (y i : ℝ)) := by
    funext i
    exact_mod_cast hxy i
  rw [heq]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

theorem FixedPositiveNiltestRealization.scalarAffine
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {child : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)}
    {cost : ℝ} {f : (σ → ℤ) → ℂ}
    (h : D.FixedPositiveNiltestRealization child cost f) (a : ℤ) (shift : σ → ℤ) :
    D.FixedPositiveNiltestRealization
      (D.filtration.realification.scalarAffineOrbitHom (a : ℚ) (fun i => (shift i : ℚ)) child)
      cost (fun x => f (fun i => a * x i + shift i)) := by
  obtain ⟨U, hU, hunit, hcost, heval⟩ := h
  refine ⟨U.scalarAffinePullback (a : ℚ) (fun i => (shift i : ℚ)), ?_, hunit, hcost, ?_⟩
  · change D.filtration.realification.scalarAffineOrbitHom (a : ℚ) (fun i => (shift i : ℚ)) U.orbit = _
    rw [hU]
  · intro x
    rw [U.scalarAffinePullback_eval_integer]
    exact heval _

end RationalFilteredNilmanifold

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineResidueEpoch
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_child_affine_residue_descent_s2_oai (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d),
      ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) {e n : ℕ}
        (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
        (Q : RationalFilteredNilmanifold
          ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
        (_hEF : E.filtration = D.filtration.gradedRefiltration W)
        (_hQF : Q.filtration = E.filtration.quotientTop)
        (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) →
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
        ∀ cost : ℝ, 0 ≤ cost → SingleRefilteredRecoveryFamily D W E Q p q C cost →
        let H := D.filtration.gradedRefiltrationSubalgebra W
        let N := H ⧸ E.filtration.layerIdeal (s + 1)
        let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
        let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
        let := realification_moduleTopology_t2 Q.basis
        let T := Q.raiseStep (Nat.le_succ s)
        ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
          (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
          (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (B : ℕ) (hB : 0 < B)
            (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
            (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
            let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
            V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
            ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
              DegreeLE (fun _ => 1) s child.log ∧
              FixedAffineResidueDescent D W V b child p q P hP C a (cost + 4) := by
  obtain ⟨C, hC, hfreezing⟩ := Niltest.exists_auxiliary_frozen_discrepancy (s + 1) a
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d D p hp hD hσ q hq hqp
  obtain ⟨P, hP, hPb, hfreeze⟩ := hfreezing D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb, ?_⟩
  intro W e n E Q hEF hQF b hb hb0 cost hcost hfamily H N _ _ _ T
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, hdegree, hrealize⟩ :=
    SingleRefilteredRecoveryFamily.exists_fixed_child D W E Q hEF hQF
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) b hb hb0 hcost hfamily
  let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, hdegree, ?_⟩
  intro scale shift S hS hunit hinvariant slow rational κ hκ hprod hgrid A hA hslow M hM lo length width
    hwidth hwidthN u v J hJ hv hcop δ ε hδ hε hsize hphysical hsmall cells c₀ c₁ F G
  let middle := D.filtration.realification.scalarAffineAdaptedHom (scale : ℚ) (fun i => (shift i : ℚ)) b
  obtain ⟨k, hk₀, hk₁, l₀, r₀, hl₀, hr₀, hgap⟩ :=
    hfreeze S hS hunit slow middle rational κ hκ hprod hgrid A hA hslow
      M hM lo length width hwidth hwidthN u v J hJ hv hcop δ ε hδ hε hsize hphysical hsmall
  have hℓ : (S.lipBound : ℝ) ≤ Real.exp p := by
    linarith [S.observable_budget hS, S.normBound.coe_nonneg]
  have hreal := (hrealize l₀ r₀ hl₀ hr₀ S.observable S.lipBound hℓ S.lipschitz hunit hinvariant).scalarAffine scale shift
  have heq : (fun x : σ → ℤ => S.observable (QuotientGroup.mk
      (l₀ * D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1)
        (fun i => (x i : ℝ)) middle * r₀))) =
      (fun x : σ → ℤ => S.observable (QuotientGroup.mk
        (l₀ * D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1)
          (fun i => ((scale * x i + shift i : ℤ) : ℝ)) b * r₀))) := by
    funext x
    exact congrArg (fun z : D.RealGroup => S.observable (QuotientGroup.mk (l₀ * z * r₀)))
      (D.filtration.scalarAffineAdaptedHom_value_integer (scale : ℚ)
        (fun i => (shift i : ℚ)) x (fun i => scale * x i + shift i)
        (fun i => by push_cast; ring) b)
  rw [← heq] at hreal
  obtain ⟨U, hU, hunitU, hcostU, hgapU⟩ := hreal.transfer_discrepancy
    (partitionCell c₀ k) (partitionCell c₁ k)
    (fun x => commonStrideIndex u M (fun i => (x i).val))
    (fun x => commonStrideIndex u M (fun i => (x i).val)) hgap
  exact ⟨k, hk₀, hk₁, U, hU, hunitU, hcostU, hgapU⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_child_affine_residue_descent_s2_oai.{u_1, u_2} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_child_affine_residue_descent_s2_oai.{u_1, u_2}
