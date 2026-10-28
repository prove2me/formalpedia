-- Prove2me | solution 1 for OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:23:03.270805+00:00
-- url     : https://prove2.me/submissions/d16f2a8f-079c-461d-addf-8b22a22b5e85

import Mathlib
import Definitions.Def_OAIQ63Br004

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineProfileIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FiniteProfile

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem incidence_count (D : Finset (Line F)) (U : Finset (Point F)) :
    (∑ l ∈ D, (U.filter fun p ↦ OnLine p l).card) =
      ∑ p ∈ U, deletionMultiplicity D p := by
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, deletionMultiplicity]
    using Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun l p ↦ OnLine p l) (s := D) (t := U)

omit [Field F] in

theorem deletionSet_card {k : ℕ} {D : Finset (Line F)} (hD : IsDeletionSet k D) :
    D.card = k * (Fintype.card F + 1) := by
  have h := Finset.sum_card_fiberwise_eq_card_filter D
    (Finset.univ : Finset (Direction F)) Prod.fst
  have heach (d : Direction F) : (D.filter fun l ↦ l.1 = d).card = k := hD d
  simpa [heach, Fintype.card_option, Nat.mul_comm] using h.symm

omit [Fintype F] in

theorem multiplicity_union (D C : Finset (Line F)) (hDC : Disjoint D C) (p : Point F) :
    deletionMultiplicity (D ∪ C) p = deletionMultiplicity D p + deletionMultiplicity C p := by
  unfold deletionMultiplicity
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact hDC.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem sum_multiplicity_on_line_le (E : Finset (Line F)) {l : Line F}
    (hl : l ∈ E) :
    (∑ p ∈ linePoints l, deletionMultiplicity E p) ≤
      Fintype.card F + E.card - 1 := by
  rw [← incidence_count]
  have heq (m : Line F) : (linePoints l).filter (fun p ↦ OnLine p m) =
      linePoints l ∩ linePoints m := by
    ext p
    simp [linePoints]
  simp_rw [heq]
  let f : Line F → ℕ := fun m ↦ (linePoints l ∩ linePoints m).card
  have hsum := Finset.sum_erase_add E f hl
  have hbound : (∑ m ∈ E.erase l, f m) ≤ (E.erase l).card := by
    calc
      (∑ m ∈ E.erase l, f m) ≤ ∑ _m ∈ E.erase l, 1 := by
        apply Finset.sum_le_sum
        intro m hm
        exact linePoints_inter_card_le_one l m
          (Ne.symm (Finset.ne_of_mem_erase hm))
      _ = (E.erase l).card := by simp
  have hself : f l = Fintype.card F := by simp [f, linePoints_card]
  have hcard := Finset.card_erase_of_mem hl
  change (∑ m ∈ E, f m) ≤ _
  rw [← hsum, hself]
  calc
    (∑ m ∈ E.erase l, f m) + Fintype.card F ≤
        (E.erase l).card + Fintype.card F := Nat.add_le_add_right hbound _
    _ ≤ Fintype.card F + E.card - 1 := by
      rw [hcard]
      have hE : 0 < E.card := Finset.card_pos.mpr ⟨l, hl⟩
      omega

theorem line_profile_firstMoment_le (D C : Finset (Line F)) (hDC : Disjoint D C)
    {l : Line F} (hl : l ∈ D ∪ C) :
    (∑ p ∈ linePoints l,
      ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) /
        (Fintype.card F : ℝ) ≤
      1 + (((D.card + C.card : ℕ) : ℝ) - 1) / (Fintype.card F : ℝ) := by
  have hb := sum_multiplicity_on_line_le (D ∪ C) hl
  simp_rw [multiplicity_union D C hDC] at hb
  rw [Finset.card_union_of_disjoint hDC] at hb
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast hpos
  have hR : (∑ p ∈ linePoints l,
      ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) ≤
      (Fintype.card F : ℝ) + ((D.card + C.card : ℕ) : ℝ) - 1 := by
    have hnat : 1 ≤ Fintype.card F + (D.card + C.card) := by omega
    exact_mod_cast hb
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ (Fintype.card F : ℝ) + ((D.card + C.card : ℕ) : ℝ) - 1 := hR
    _ = (1 + (((D.card + C.card : ℕ) : ℝ) - 1) /
        (Fintype.card F : ℝ)) * (Fintype.card F : ℝ) := by
      field_simp
      ring

theorem line_firstMoment_le_source_bound {k : ℕ} {D C : Finset (Line F)}
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F)
    (hDC : Disjoint D C) {l : Line F} (hl : l ∈ D ∪ C) :
    (∑ p ∈ linePoints l,
      ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) /
        (Fintype.card F : ℝ) ≤ 2 * k + 4 := by
  apply (line_profile_firstMoment_le D C hDC hl).trans
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hqpos : (0 : ℝ) < Fintype.card F := by linarith
  have hCR : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hC
  have hDR : (D.card : ℝ) = (k : ℝ) * (Fintype.card F + 1) := by
    exact_mod_cast deletionSet_card hD
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← le_sub_iff_add_le', div_le_iff₀ hqpos, Nat.cast_add, hDR]
  nlinarith

end Balanced.FiniteProfile

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineUniformCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PairEvaluation

noncomputable section
open scoped ENNReal

variable {F : Type*} [Field F] [Fintype F]

theorem linePoints_card_via_coordinates [DecidableEq F]
    (d e : Direction F) (hde : d ≠ e) (a : F) :
    (linePoints (d, a)).card = Fintype.card F := by
  calc
    _ = Fintype.card {p : Point F // OnLine p (d, a)} := by
      simp [Fintype.card_subtype, linePoints]
    _ = _ := Fintype.card_congr (lineCoordinateEquiv d e hde a)

end
end Balanced.PairEvaluation

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineTargetError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffineTargetError

theorem sum_error_of_eq_off {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (heq : ∀ x, x ∉ S → f x = g x) :
    |(∑ x, f x) - ∑ x, g x| ≤ (S.card : ℝ) := by
  calc
    |(∑ x, f x) - ∑ x, g x| = |∑ x, (f x - g x)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x, |f x - g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, if x ∈ S then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ S
      · rw [ite_eq_left hx, abs_le]
        constructor <;> linarith [(hf x).1, (hf x).2, (hg x).1, (hg x).2]
      · simp [hx, heq x hx]
    _ = (S.card : ℝ) := by simp

theorem average_error_of_eq_off {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (heq : ∀ x, x ∉ S → f x = g x) :
    |((∑ x, f x) / (Fintype.card α : ℝ)) -
      (∑ x, g x) / (Fintype.card α : ℝ)| ≤ (S.card : ℝ) / Fintype.card α := by
  rw [← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card α from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (sum_error_of_eq_off S f g hf hg heq) (Nat.cast_nonneg _)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem target_card (l : Line F) : (linePoints l).card = Fintype.card F := by
  rcases l with ⟨d, a⟩
  cases d with
  | none => exact PairEvaluation.linePoints_card_via_coordinates none (some 0) (by simp) a
  | some m => exact PairEvaluation.linePoints_card_via_coordinates (some m) none (by simp) a

theorem plane_average_error (l : Line F) (f g : Point F → ℝ)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (heq : ∀ p, ¬ OnLine p l → f p = g p) :
    |((∑ p, f p) / (Fintype.card F : ℝ) ^ 2) -
      (∑ p, g p) / (Fintype.card F : ℝ) ^ 2| ≤ 1 / Fintype.card F := by
  have h := average_error_of_eq_off (linePoints l) f g hf hg (by
    intro p hp
    apply heq p
    simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] using hp)
  have hcard : Fintype.card (Point F) = Fintype.card F * Fintype.card F := Fintype.card_prod _ _
  rw [target_card, hcard, Nat.cast_mul] at h
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hratio : (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) * Fintype.card F) =
      1 / Fintype.card F := by field_simp
  simpa only [pow_two, hratio] using h

end Balanced.AffineTargetError

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_HypergeometricApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem abs_prod_sub_prod_le_sum_errors {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgp0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i hi => (hgs i hi).1
    have hgp1 : (∏ i ∈ s, g i) ≤ 1 := Finset.prod_le_one
      (fun i hi => (hgs i hi).1) (fun i hi => (hgs i hi).2)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      |f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i|
          = |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
              (f a - g a) * ∏ i ∈ s, g i| := by congr 1; ring
      _ ≤ |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| +
            |(f a - g a) * ∏ i ∈ s, g i| := abs_add_le _ _
      _ = f a * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| +
            |f a - g a| * ∏ i ∈ s, g i := by
        rw [abs_mul, abs_mul, abs_of_nonneg hfa.1, abs_of_nonneg hgp0]
      _ ≤ |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| + |f a - g a| := by
        nlinarith [abs_nonneg ((∏ i ∈ s, f i) - ∏ i ∈ s, g i), abs_nonneg (f a - g a)]
      _ ≤ |f a - g a| + ∑ i ∈ s, |f i - g i| := by linarith [ih hfs hgs]

theorem descFactorial_factor_error (d N i r : ℕ)
    (hd : d ≤ N) (hi : i < r) (hr : r < N) :
    |((d - i : ℕ) : ℝ) / (N - i : ℕ) - (d : ℝ) / N| ≤
      (r : ℝ) / ((N : ℝ) - r) := by
  have hiN : i < N := hi.trans hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hNipos : (0 : ℝ) < (N : ℝ) - i := sub_pos.mpr (by exact_mod_cast hiN)
  have hNrpos : (0 : ℝ) < (N : ℝ) - r := sub_pos.mpr (by exact_mod_cast hr)
  have hdi_nonneg : (0 : ℝ) ≤ (d : ℝ) / N := by positivity
  have hir : (i : ℝ) ≤ r := by exact_mod_cast hi.le
  have hdN : (d : ℝ) ≤ N := by exact_mod_cast hd
  rw [Nat.cast_sub hiN.le]
  by_cases hid : i ≤ d
  · rw [Nat.cast_sub hid]
    have hratio : ((d : ℝ) - i) / ((N : ℝ) - i) ≤ (d : ℝ) / N := by
      apply (div_le_div_iff₀ hNipos hNpos).2
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
    have hfirst : (d : ℝ) / N - ((d : ℝ) - i) / ((N : ℝ) - i) ≤
        (i : ℝ) / ((N : ℝ) - i) := by
      apply (le_div_iff₀ hNipos).2
      have hcancel : (((d : ℝ) - i) / ((N : ℝ) - i)) * ((N : ℝ) - i) = (d : ℝ) - i :=
        div_mul_cancel₀ _ hNipos.ne'
      have hcancel' : ((d : ℝ) / N) * N = d := div_mul_cancel₀ _ hNpos.ne'
      nlinarith [mul_nonneg hdi_nonneg (Nat.cast_nonneg i)]
    have hsecond : (i : ℝ) / ((N : ℝ) - i) ≤ (r : ℝ) / ((N : ℝ) - r) := by
      apply (div_le_div_iff₀ hNipos hNrpos).2
      nlinarith
    linarith
  · have hdi : d < i := Nat.lt_of_not_ge hid
    rw [Nat.sub_eq_zero_of_le hdi.le, Nat.cast_zero, zero_div, zero_sub, abs_neg,
      abs_of_nonneg hdi_nonneg]
    apply (div_le_div_iff₀ hNpos hNrpos).2
    have hdr : (d : ℝ) ≤ r := by exact_mod_cast (hdi.trans hi).le
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

theorem descFactorial_ratio_power_error (d N r : ℕ) (hd : d ≤ N) (hr : r < N) :
    |(d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) - ((d : ℝ) / N) ^ r| ≤
      (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  let f : ℕ → ℝ := fun i => ((d - i : ℕ) : ℝ) / (N - i : ℕ)
  let g : ℕ → ℝ := fun _ => (d : ℝ) / N
  have hf : ∀ i ∈ Finset.range r, 0 ≤ f i ∧ f i ≤ 1 := by
    intro i hi
    have hiN : i < N := (Finset.mem_range.mp hi).trans hr
    have hden : (0 : ℝ) < (N - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hiN
    refine ⟨by dsimp [f]; positivity, ?_⟩
    apply (div_le_one hden).2
    exact_mod_cast Nat.sub_le_sub_right hd i
  have hg : ∀ i ∈ Finset.range r, 0 ≤ g i ∧ g i ≤ 1 := by
    intro i hi
    refine ⟨by dsimp [g]; positivity, ?_⟩
    apply (div_le_one hNpos).2
    exact_mod_cast hd
  have hprod := abs_prod_sub_prod_le_sum_errors (Finset.range r) f g hf hg
  have hsum : (∑ i ∈ Finset.range r, |f i - g i|) ≤
      (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
    calc
      (∑ i ∈ Finset.range r, |f i - g i|)
          ≤ ∑ _i ∈ Finset.range r, (r : ℝ) / ((N : ℝ) - r) := by
        apply Finset.sum_le_sum
        intro i hi
        exact descFactorial_factor_error d N i r hd (Finset.mem_range.mp hi) hr
      _ = (r : ℝ) ^ 2 / ((N : ℝ) - r) := by simp; ring
  have heq : (∏ i ∈ Finset.range r, f i) =
      (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) := by
    simp only [f, Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]
  have heqg : (∏ i ∈ Finset.range r, g i) = ((d : ℝ) / N) ^ r := by simp [g, div_pow]
  rw [heq, heqg] at hprod
  exact hprod.trans hsum

theorem descFactorial_ratio_power_error_uniform (d N r B : ℕ)
    (hd : d ≤ N) (hrB : r ≤ B) (hN : 0 < N) (hlarge : 2 * B ≤ N) :
    |(d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) - ((d : ℝ) / N) ^ r| ≤
      2 * (B : ℝ) ^ 2 / N := by
  by_cases hr0 : r = 0
  · subst r
    simp only [Nat.descFactorial_zero, Nat.cast_one, div_self one_ne_zero, pow_zero,
      sub_self, abs_zero]
    positivity
  have hr : r < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) - r := sub_pos.mpr (by exact_mod_cast hr)
  have hrBreal : (r : ℝ) ≤ B := by exact_mod_cast hrB
  have hlargeReal : 2 * (B : ℝ) ≤ N := by exact_mod_cast hlarge
  apply (descFactorial_ratio_power_error d N r hd hr).trans
  apply (div_le_div_iff₀ hden hNreal).2
  have hrr : (r : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r), (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ N by positivity) (sub_nonneg.mpr hrr),
    mul_nonneg (sq_nonneg (B : ℝ)) (show 0 ≤ (N : ℝ) - 2 * r by linarith)]

theorem choose_ratio_eq_descFactorial_ratio (d N r : ℕ) (hrd : r ≤ d) (hdN : d ≤ N) :
    ((N - r).choose (d - r) : ℝ) / (N.choose d : ℝ) =
      (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) := by
  have hNd : (N.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdN).ne'
  have hNr : (N.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hrd.trans hdN)).ne'
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  calc
    ((N - r).choose (d - r) : ℝ) / (N.choose d : ℝ)
        = (d.choose r : ℝ) / (N.choose r : ℝ) := by
      apply (div_eq_div_iff hNd hNr).2
      have h := Nat.choose_mul (n := N) hrd
      exact_mod_cast (by nlinarith : (N - r).choose (d - r) * N.choose r = d.choose r * N.choose d)
    _ = (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      field_simp

theorem uniform_subset_contains_probability {α : Type*} [DecidableEq α]
    (U T : Finset α) (d : ℕ) (hTU : T ⊆ U) (hd : d ≤ U.card) :
    ((PMF.uniformOfFinset (U.powersetCard d) (Finset.powersetCard_nonempty.mpr hd)).toOuterMeasure
      {S : Finset α | T ⊆ S}).toReal =
      (d.descFactorial T.card : ℝ) / (U.card.descFactorial T.card : ℝ) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Finset.card_powersetCard, Set.mem_ofPred_eq]
  by_cases hTd : T.card ≤ d
  · rw [Finset.card_filter_powersetCard_subset T U d hTU hTd]
    exact choose_ratio_eq_descFactorial_ratio d U.card T.card hTd hd
  · have hempty : (U.powersetCard d).filter (T ⊆ ·) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro S hS hTS
      have hcard := Finset.card_le_card hTS
      rw [(Finset.mem_powersetCard.mp hS).2] at hcard
      exact hTd hcard
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hTd), Nat.cast_zero, zero_div]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformSubsetExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
attribute [local instance] Classical.propDecidable

theorem uniform_product_event_probability {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (hA : A.Nonempty) (hB : B.Nonempty)
    (P : α → Prop) (Q : β → Prop) :
    ((PMF.uniformOfFinset (A ×ˢ B) (hA.product hB)).toOuterMeasure
      {x | P x.1 ∧ Q x.2}).toReal =
      ((PMF.uniformOfFinset A hA).toOuterMeasure {x | P x}).toReal *
        ((PMF.uniformOfFinset B hB).toOuterMeasure {x | Q x}).toReal := by
  classical
  simp only [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  have hf : (A ×ˢ B).filter (fun x => P x.1 ∧ Q x.2) = (A.filter P) ×ˢ (B.filter Q) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hf, Finset.card_product, Finset.card_product]
  push_cast
  ring

theorem uniform_two_subsets_contains_probability {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (U T : Finset α) (V R : Finset β) (d e : ℕ)
    (hTU : T ⊆ U) (hRV : R ⊆ V) (hd : d ≤ U.card) (he : e ≤ V.card) :
    ((PMF.uniformOfFinset ((U.powersetCard d) ×ˢ (V.powersetCard e))
      (Finset.Nonempty.product (Finset.powersetCard_nonempty.mpr hd)
        (Finset.powersetCard_nonempty.mpr he))).toOuterMeasure
      {S | T ⊆ S.1 ∧ R ⊆ S.2}).toReal =
      ((d.descFactorial T.card : ℝ) / (U.card.descFactorial T.card : ℝ)) *
        ((e.descFactorial R.card : ℝ) / (V.card.descFactorial R.card : ℝ)) := by
  rw [uniform_product_event_probability _ _ (Finset.powersetCard_nonempty.mpr hd)
    (Finset.powersetCard_nonempty.mpr he)]
  rw [uniform_subset_contains_probability U T d hTU hd,
    uniform_subset_contains_probability V R e hRV he]

theorem uniform_expected_filtered_card {Ω α : Type*} [DecidableEq Ω] [DecidableEq α]
    (A : Finset Ω) (hA : A.Nonempty) (X : Finset α) (P : α → Ω → Prop) :
    (∑ ω ∈ A, ((X.filter (fun x => P x ω)).card : ℝ) / (A.card : ℝ)) =
      ∑ x ∈ X, ((PMF.uniformOfFinset A hA).toOuterMeasure {ω | P x ω}).toReal := by
  classical
  simp only [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
    Finset.sum_div]
  exact Finset.sum_comm

theorem uncovered_iff_incident_subset {L : Type*} [DecidableEq L]
    (D S : Finset L) (incident : L → Prop) :
    (∀ l ∈ D \ S, ¬ incident l) ↔ D.filter incident ⊆ S := by
  classical
  constructor
  · intro h l hl
    rcases Finset.mem_filter.mp hl with ⟨hlD, hlI⟩
    by_contra hlS
    exact h l (Finset.mem_sdiff.mpr ⟨hlD, hlS⟩) hlI
  · intro h l hl hlI
    rcases Finset.mem_sdiff.mp hl with ⟨hlD, hlS⟩
    exact hlS (h (Finset.mem_filter.mpr ⟨hlD, hlI⟩))

theorem uniform_two_subsets_expected_uncovered_card {L α : Type*}
    [DecidableEq L] [DecidableEq α]
    (D C : Finset L) (X : Finset α) (incident : α → L → Prop)
    (d c : ℕ) (hd : d ≤ D.card) (hc : c ≤ C.card) :
    (∑ S ∈ (D.powersetCard d) ×ˢ (C.powersetCard c),
      ((X.filter (fun x =>
        (∀ l ∈ D \ S.1, ¬ incident x l) ∧ (∀ l ∈ C \ S.2, ¬ incident x l))).card : ℝ) /
          (((D.powersetCard d) ×ˢ (C.powersetCard c)).card : ℝ)) =
      ∑ x ∈ X,
        ((d.descFactorial ((D.filter (incident x)).card) : ℝ) /
          (D.card.descFactorial ((D.filter (incident x)).card) : ℝ)) *
        ((c.descFactorial ((C.filter (incident x)).card) : ℝ) /
          (C.card.descFactorial ((C.filter (incident x)).card) : ℝ)) := by
  classical
  convert (uniform_expected_filtered_card _
    ((Finset.powersetCard_nonempty.mpr hd).product (Finset.powersetCard_nonempty.mpr hc))
    X (fun x S => (∀ l ∈ D \ S.1, ¬ incident x l) ∧ (∀ l ∈ C \ S.2, ¬ incident x l))).trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro S hS
    congr 1
    congr 2
    ext x
    simp only [Finset.mem_filter]
  · apply Finset.sum_congr rfl
    intro x hx
    simp_rw [uncovered_iff_incident_subset]
    exact uniform_two_subsets_contains_probability D (D.filter (incident x))
      C (C.filter (incident x)) d c (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd hc

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileHypergeometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem weighted_profile_error_of_mean_bound {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (height : ι → ℕ) (f g : ι → ℝ)
    (B : ℕ) {ε M : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * (height i : ℝ) ≤ M)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1)
    (hsmall : ∀ i ∈ s, height i ≤ B → |f i - g i| ≤ ε) :
    |(∑ i ∈ s, w i * f i) - ∑ i ∈ s, w i * g i| ≤
      ε + M / (B + 1 : ℝ) := by
  have hden : (0 : ℝ) < B + 1 := by positivity
  have hpoint (i : ι) (hi : i ∈ s) :
      |f i - g i| ≤ ε + (height i : ℝ) / (B + 1 : ℝ) := by
    by_cases hBi : height i ≤ B
    · have h := hsmall i hi hBi
      have hnonneg : (0 : ℝ) ≤ (height i : ℝ) / (B + 1 : ℝ) := by positivity
      linarith
    · have hlarge : (B + 1 : ℝ) ≤ height i := by exact_mod_cast (show B + 1 ≤ height i by omega)
      have htail : (1 : ℝ) ≤ (height i : ℝ) / (B + 1 : ℝ) := by
        apply (le_div_iff₀ hden).2
        simpa using hlarge
      have habs : |f i - g i| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hf i hi).1, (hf i hi).2, (hg i hi).1, (hg i hi).2]
      linarith
  calc
    |(∑ i ∈ s, w i * f i) - ∑ i ∈ s, w i * g i|
        = |∑ i ∈ s, w i * (f i - g i)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |w i * (f i - g i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, w i * |f i - g i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * (ε + (height i : ℝ) / (B + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i hi) (hw i hi)
    _ = ε + (∑ i ∈ s, w i * (height i : ℝ)) / (B + 1 : ℝ) := by
      simp_rw [mul_add]
      simp only [← mul_div_assoc]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_div]
    _ ≤ ε + M / (B + 1 : ℝ) :=
      by linarith [div_le_div_of_nonneg_right hmean hden.le]

theorem descFactorial_ratio_bounds (d N r : ℕ) (hd : d ≤ N) :
    0 ≤ (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) ∧
      (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  by_cases hzero : N.descFactorial r = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < N.descFactorial r := by exact_mod_cast Nat.pos_of_ne_zero hzero
    apply (div_le_one hpos).2
    exact_mod_cast Nat.descFactorial_le r hd

theorem abs_mul_sub_mul_le_errors {a b c d : ℝ}
    (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hc.1]
    _ ≤ |a - c| + |b - d| := by nlinarith [abs_nonneg (a - c), abs_nonneg (b - d)]

theorem two_descFactorial_factors_error (d₁ N₁ d₂ N₂ r₁ r₂ B : ℕ)
    (hd₁ : d₁ ≤ N₁) (hd₂ : d₂ ≤ N₂) (hr₁ : r₁ ≤ B) (hr₂ : r₂ ≤ B)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hlarge₁ : 2 * B ≤ N₁) (hlarge₂ : 2 * B ≤ N₂) :
    |((d₁.descFactorial r₁ : ℝ) / (N₁.descFactorial r₁ : ℝ)) *
        ((d₂.descFactorial r₂ : ℝ) / (N₂.descFactorial r₂ : ℝ)) -
      ((d₁ : ℝ) / N₁) ^ r₁ * ((d₂ : ℝ) / N₂) ^ r₂| ≤
      2 * (B : ℝ) ^ 2 / N₁ + 2 * (B : ℝ) ^ 2 / N₂ := by
  have hratio : 0 ≤ ((d₁ : ℝ) / N₁) ^ r₁ ∧ ((d₁ : ℝ) / N₁) ^ r₁ ≤ 1 := by
    have hpos : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
    have hbase : (d₁ : ℝ) / N₁ ≤ 1 := (div_le_one hpos).2 (by exact_mod_cast hd₁)
    exact ⟨by positivity, pow_le_one₀ (by positivity) hbase⟩
  have h := abs_mul_sub_mul_le_errors (a := (d₁.descFactorial r₁ : ℝ) / (N₁.descFactorial r₁ : ℝ))
    (d := ((d₂ : ℝ) / N₂) ^ r₂) (descFactorial_ratio_bounds d₂ N₂ r₂ hd₂) hratio
  exact h.trans (add_le_add
    (descFactorial_ratio_power_error_uniform d₁ N₁ r₁ B hd₁ hr₁ hN₁ hlarge₁)
    (descFactorial_ratio_power_error_uniform d₂ N₂ r₂ B hd₂ hr₂ hN₂ hlarge₂))

theorem weighted_two_descFactorial_factors_error {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ)
    (d₁ N₁ d₂ N₂ B : ℕ) {M : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M)
    (hd₁ : d₁ ≤ N₁) (hd₂ : d₂ ≤ N₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hlarge₁ : 2 * B ≤ N₁) (hlarge₂ : 2 * B ≤ N₂) :
    |(∑ i ∈ s, w i *
        (((d₁.descFactorial (a i) : ℝ) / (N₁.descFactorial (a i) : ℝ)) *
         ((d₂.descFactorial (b i) : ℝ) / (N₂.descFactorial (b i) : ℝ)))) -
      ∑ i ∈ s, w i * (((d₁ : ℝ) / N₁) ^ (a i) * ((d₂ : ℝ) / N₂) ^ (b i))| ≤
      (2 * (B : ℝ) ^ 2 / N₁ + 2 * (B : ℝ) ^ 2 / N₂) + M / (B + 1 : ℝ) := by
  apply weighted_profile_error_of_mean_bound s w (fun i => a i + b i) _ _ B
    (by positivity) hw hsum hmean
  · intro i hi
    have h₁ := descFactorial_ratio_bounds d₁ N₁ (a i) hd₁
    have h₂ := descFactorial_ratio_bounds d₂ N₂ (b i) hd₂
    exact ⟨mul_nonneg h₁.1 h₂.1, by nlinarith⟩
  · intro i hi
    have hpos₁ : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
    have hpos₂ : (0 : ℝ) < N₂ := by exact_mod_cast hN₂
    have hbase₁ : (d₁ : ℝ) / N₁ ≤ 1 := (div_le_one hpos₁).2 (by exact_mod_cast hd₁)
    have hbase₂ : (d₂ : ℝ) / N₂ ≤ 1 := (div_le_one hpos₂).2 (by exact_mod_cast hd₂)
    have hpow₁ : ((d₁ : ℝ) / N₁) ^ (a i) ≤ 1 := pow_le_one₀ (by positivity) hbase₁
    have hpow₂ : ((d₂ : ℝ) / N₂) ^ (b i) ≤ 1 := pow_le_one₀ (by positivity) hbase₂
    have hnonneg₁ : 0 ≤ ((d₁ : ℝ) / N₁) ^ (a i) := by positivity
    have hnonneg₂ : 0 ≤ ((d₂ : ℝ) / N₂) ^ (b i) := by positivity
    exact ⟨mul_nonneg hnonneg₁ hnonneg₂, by nlinarith⟩
  · intro i hi hsmall
    exact two_descFactorial_factors_error d₁ N₁ d₂ N₂ (a i) (b i) B hd₁ hd₂
      (by omega) (by omega) hN₁ hN₂ hlarge₁ hlarge₂

theorem exists_profile_approximation_cutoff (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B N₀ : ℕ, 1 ≤ N₀ ∧ 2 * B ≤ N₀ ∧
      ∀ N₁ N₂ : ℕ, N₀ ≤ N₁ → N₀ ≤ N₂ →
        (2 * (B : ℝ) ^ 2 / N₁ + 2 * (B : ℝ) ^ 2 / N₂) +
          M / (B + 1 : ℝ) < ε := by
  have htail : Filter.Tendsto (fun B : ℕ => M / (B + 1 : ℝ)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_atTop_add_const_right Filter.atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop M
  obtain ⟨B, hB⟩ := (htail.eventually_lt_const (half_pos hε)).exists
  have hmain : Filter.Tendsto (fun N : ℕ => 4 * (B : ℝ) ^ 2 / N) Filter.atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (4 * (B : ℝ) ^ 2)
  have hlarge := (Filter.eventually_ge_atTop (1 : ℕ)).and
    ((Filter.eventually_ge_atTop (2 * B)).and (hmain.eventually_lt_const (half_pos hε)))
  obtain ⟨N₀, hN₀, hBN₀, herror⟩ := hlarge.exists
  refine ⟨B, N₀, hN₀, hBN₀, ?_⟩
  intro N₁ N₂ h₁ h₂
  have hpos : (0 : ℝ) < N₀ := by exact_mod_cast (show 0 < N₀ by omega)
  have h₁' : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h₁
  have h₂' : (N₀ : ℝ) ≤ N₂ := by exact_mod_cast h₂
  have hb₁ : 2 * (B : ℝ) ^ 2 / N₁ ≤ 2 * (B : ℝ) ^ 2 / N₀ :=
    div_le_div_of_nonneg_left (by positivity) hpos h₁'
  have hb₂ : 2 * (B : ℝ) ^ 2 / N₂ ≤ 2 * (B : ℝ) ^ 2 / N₀ :=
    div_le_div_of_nonneg_left (by positivity) hpos h₂'
  have hid : 2 * (B : ℝ) ^ 2 / N₀ + 2 * (B : ℝ) ^ 2 / N₀ =
      4 * (B : ℝ) ^ 2 / N₀ := by ring
  linarith

theorem uniform_weighted_hypergeometric_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {ι : Type*} (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ)
      (d₁ N₁ d₂ N₂ : ℕ),
      N₀ ≤ N₁ → N₀ ≤ N₂ → d₁ ≤ N₁ → d₂ ≤ N₂ →
      (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
      (∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M) →
      |(∑ i ∈ s, w i *
          (((d₁.descFactorial (a i) : ℝ) / (N₁.descFactorial (a i) : ℝ)) *
           ((d₂.descFactorial (b i) : ℝ) / (N₂.descFactorial (b i) : ℝ)))) -
        ∑ i ∈ s, w i * (((d₁ : ℝ) / N₁) ^ (a i) * ((d₂ : ℝ) / N₂) ^ (b i))| < ε := by
  obtain ⟨B, N₀, hN₀, hBN₀, hcut⟩ := exists_profile_approximation_cutoff M hε
  refine ⟨N₀, ?_⟩
  intro ι s w a b d₁ N₁ d₂ N₂ h₁ h₂ hd₁ hd₂ hw hsum hmean
  exact (weighted_two_descFactorial_factors_error s w a b d₁ N₁ d₂ N₂ B
    hw hsum hmean hd₁ hd₂ (by omega) (by omega) (by omega) (by omega)).trans_lt
      (hcut N₁ N₂ h₁ h₂)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileTargetExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ProfileTargetExclusion

theorem fraction_error (d N : ℕ) (hN : 2 ≤ N) (hd : d ≤ N) :
    |((d - 1 : ℕ) : ℝ) / (N - 1 : ℕ) - (d : ℝ) / N| ≤
      1 / (N - 1 : ℕ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNm : (0 : ℝ) < (N : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one]
  by_cases hd0 : d = 0
  · subst d
    simp only [Nat.zero_sub, Nat.cast_zero, zero_div, sub_self, abs_zero]
    positivity
  have hd1 : 1 ≤ d := by omega
  rw [Nat.cast_sub hd1, Nat.cast_one]
  have hdN : (d : ℝ) ≤ N := by exact_mod_cast hd
  have hratio : ((d : ℝ) - 1) / ((N : ℝ) - 1) ≤ (d : ℝ) / N := by
    apply (div_le_div_iff₀ hNm hNpos).2
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  have hid : -(((d : ℝ) - 1) / ((N : ℝ) - 1) - (d : ℝ) / N) =
      (1 - (d : ℝ) / N) / ((N : ℝ) - 1) := by
    field_simp
    ring
  rw [hid]
  apply div_le_div_of_nonneg_right _ hNm.le
  have : (0 : ℝ) ≤ (d : ℝ) / N := by positivity
  linarith

theorem power_error (x y : ℝ) (r : ℕ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    |x ^ r - y ^ r| ≤ (r : ℝ) * |x - y| := by
  have h := Balanced.abs_prod_sub_prod_le_sum_errors (Finset.range r)
    (fun _ => x) (fun _ => y) (fun _ _ => hx) (fun _ _ => hy)
  simpa only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul] using h

theorem monomial_error (x x' y y' : ℝ) (a b : ℕ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hx' : 0 ≤ x' ∧ x' ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hy' : 0 ≤ y' ∧ y' ≤ 1) :
    |x ^ a * y ^ b - x' ^ a * y' ^ b| ≤
      (a : ℝ) * |x - x'| + (b : ℝ) * |y - y'| := by
  apply (Balanced.abs_mul_sub_mul_le_errors
    ⟨pow_nonneg hy.1 _, pow_le_one₀ hy.1 hy.2⟩
    ⟨pow_nonneg hx'.1 _, pow_le_one₀ hx'.1 hx'.2⟩).trans
  exact add_le_add (power_error x x' a hx hx') (power_error y y' b hy hy')

theorem weighted_parameter_error {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a b : ι → ℕ) (x x' y y' ε M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmean : ∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M)
    (hx : 0 ≤ x ∧ x ≤ 1) (hx' : 0 ≤ x' ∧ x' ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hy' : 0 ≤ y' ∧ y' ≤ 1)
    (hε : 0 ≤ ε) (hex : |x - x'| ≤ ε) (hey : |y - y'| ≤ ε) :
    |(∑ i ∈ s, w i * (x ^ a i * y ^ b i)) -
      ∑ i ∈ s, w i * (x' ^ a i * y' ^ b i)| ≤ M * ε := by
  calc
    |(∑ i ∈ s, w i * (x ^ a i * y ^ b i)) -
        ∑ i ∈ s, w i * (x' ^ a i * y' ^ b i)| =
        |∑ i ∈ s, w i * (x ^ a i * y ^ b i - x' ^ a i * y' ^ b i)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |w i * (x ^ a i * y ^ b i - x' ^ a i * y' ^ b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * (((a i + b i : ℕ) : ℝ) * ε) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      apply (monomial_error x x' y y' (a i) (b i) hx hx' hy hy').trans
      rw [Nat.cast_add, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hex (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hey (Nat.cast_nonneg _))
    _ = (∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ)) * ε := by
      simp only [← mul_assoc, Finset.sum_mul]
    _ ≤ M * ε := mul_le_mul_of_nonneg_right hmean hε

theorem fraction_bounds (d N : ℕ) (hd : d ≤ N) :
    0 ≤ (d : ℝ) / N ∧ (d : ℝ) / N ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  by_cases hN : N = 0
  · simp [hN]
  have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  exact (div_le_one hpos).2 (by exact_mod_cast hd)

theorem weighted_exclusion_error {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a b : ι → ℕ) (d N : ℕ) (y M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmean : ∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M)
    (hN : 2 ≤ N) (hd : d ≤ N) (hy : 0 ≤ y ∧ y ≤ 1) :
    |(∑ i ∈ s, w i * ((((d - 1 : ℕ) : ℝ) / (N - 1 : ℕ)) ^ a i * y ^ b i)) -
      ∑ i ∈ s, w i * (((d : ℝ) / N) ^ a i * y ^ b i)| ≤
        M / (N - 1 : ℕ) := by
  have h := weighted_parameter_error s w a b
    (((d - 1 : ℕ) : ℝ) / (N - 1 : ℕ)) ((d : ℝ) / N) y y
    (1 / (N - 1 : ℕ)) M hw hmean
    (fraction_bounds (d - 1) (N - 1) (Nat.sub_le_sub_right hd 1))
    (fraction_bounds d N hd) hy hy (by positivity) (fraction_error d N hN hd)
    (by simp)
  simpa only [mul_one_div] using h

theorem uniform_target_hypergeometric_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ {ι : Type*}
      (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ) (d₁ N₁ d₂ N₂ : ℕ),
      N₀ ≤ N₁ → N₀ ≤ N₂ → d₁ ≤ N₁ → d₂ ≤ N₂ →
      (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
      (∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M) →
      |(∑ i ∈ s, w i *
          ((((d₁ - 1).descFactorial (a i) : ℝ) /
              ((N₁ - 1).descFactorial (a i) : ℝ)) *
           ((d₂.descFactorial (b i) : ℝ) / (N₂.descFactorial (b i) : ℝ)))) -
        ∑ i ∈ s, w i * (((d₁ : ℝ) / N₁) ^ a i * ((d₂ : ℝ) / N₂) ^ b i)| < ε := by
  obtain ⟨Nₐ, hNₐ⟩ := Balanced.uniform_weighted_hypergeometric_approximation M (half_pos hε)
  have hlim : Filter.Tendsto (fun n : ℕ => M / (n : ℝ)) Filter.atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop M
  obtain ⟨Nᵦ, hNᵦ⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const (half_pos hε))
  refine ⟨max Nₐ Nᵦ + 2, by omega, ?_⟩
  intro ι s w a b d₁ N₁ d₂ N₂ hN₁ hN₂ hd₁ hd₂ hw hsum hmean
  have hshift : Nₐ ≤ N₁ - 1 := by omega
  have hsecond : Nₐ ≤ N₂ := by omega
  have hApprox := hNₐ s w a b (d₁ - 1) (N₁ - 1) d₂ N₂
    hshift hsecond (Nat.sub_le_sub_right hd₁ 1) hd₂ hw hsum hmean
  have hExclude := weighted_exclusion_error s w a b d₁ N₁ ((d₂ : ℝ) / N₂) M
    hw hmean (by omega) hd₁ (fraction_bounds d₂ N₂ hd₂)
  have hSmall := hNᵦ (N₁ - 1) (by omega)
  have hsumerror := add_lt_add hApprox (hExclude.trans_lt hSmall)
  have htriangle := (abs_sub_le _ _ _).trans_lt hsumerror
  simpa only [add_halves] using htriangle

theorem uniform_target_hypergeometric_approximation_one_population
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ {ι : Type*}
      (s : Finset ι) (w : ι → ℝ) (a : ι → ℕ) (d N : ℕ),
      N₀ ≤ N → d ≤ N → (∀ i ∈ s, 0 ≤ w i) →
      (∑ i ∈ s, w i = 1) → (∑ i ∈ s, w i * (a i : ℝ) ≤ M) →
      |(∑ i ∈ s, w i *
          (((d - 1).descFactorial (a i) : ℝ) / ((N - 1).descFactorial (a i) : ℝ))) -
        ∑ i ∈ s, w i * (((d : ℝ) / N) ^ a i)| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ := uniform_target_hypergeometric_approximation M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro ι s w a d N hN hd hw hsum hmean
  have h := happrox s w a (fun _ => 0) d N 0 N hN hN hd (Nat.zero_le _)
    hw hsum (by simpa only [Nat.add_zero] using hmean)
  simpa only [Nat.descFactorial_zero, Nat.cast_one, div_self one_ne_zero,
    pow_zero, mul_one] using h

end Balanced.ProfileTargetExclusion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineProfileExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffineProfileExposure

universe u

noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem multiplicity_erase_on_target (D : Finset (Line F)) (l : Line F)
    (hl : l ∈ D) (p : Point F) (hp : OnLine p l) :
    lineMultiplicity (D.erase l) p = lineMultiplicity D p - 1 := by
  unfold lineMultiplicity
  rw [Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hl, hp⟩)]

theorem targetExposureMean_eq (D C : Finset (Line F)) (l : Line F) (d c : ℕ)
    (hl : l ∈ D) (hd : d ≤ D.card) (hc : c ≤ C.card) :
    targetExposureMean D C l d c =
      (∑ p ∈ linePoints l,
        (((d - 1).descFactorial (lineMultiplicity D p - 1) : ℝ) /
          ((D.card - 1).descFactorial (lineMultiplicity D p - 1) : ℝ)) *
        ((c.descFactorial (lineMultiplicity C p) : ℝ) /
          (C.card.descFactorial (lineMultiplicity C p) : ℝ))) / (Fintype.card F : ℝ) := by
  have hd' : d - 1 ≤ (D.erase l).card := by
    rw [Finset.card_erase_of_mem hl]
    exact Nat.sub_le_sub_right hd 1
  unfold targetExposureMean
  congr 1
  convert (Balanced.uniform_two_subsets_expected_uncovered_card (D.erase l) C
    (linePoints l) (fun p m => OnLine p m) (d - 1) c hd' hc).trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro S _
    congr 1
    congr 2
    ext p
    simp only [Finset.mem_filter]
  · apply Finset.sum_congr rfl
    intro p hp
    have hp' : OnLine p l := (Finset.mem_filter.mp hp).2
    have hm := multiplicity_erase_on_target D l hl p hp'
    have hE := Finset.card_erase_of_mem hl
    calc
      _ = (((d - 1).descFactorial (lineMultiplicity (D.erase l) p) : ℝ) /
          ((D.erase l).card.descFactorial (lineMultiplicity (D.erase l) p) : ℝ)) *
          ((c.descFactorial (lineMultiplicity C p) : ℝ) /
            (C.card.descFactorial (lineMultiplicity C p) : ℝ)) := by
        unfold lineMultiplicity
        congr 6
      _ = _ := by rw [hm, hE]

theorem target_weights_sum (l : Line F) :
    ∑ _p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) = 1 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [AffineTargetError.target_card, hq]

theorem uniform_target_exposure_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (l : Line F) (d c : ℕ),
      N₀ ≤ D.card → N₀ ≤ C.card → l ∈ D → d ≤ D.card → c ≤ C.card →
      (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        (((lineMultiplicity D p - 1 + lineMultiplicity C p : ℕ) : ℝ))) ≤ M →
      |targetExposureMean D C l d c - targetPowerMean D C l d c| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C l d c hD hC hl hd hc hmean
  have h := happrox (linePoints l) (fun _ => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) (fun p => lineMultiplicity C p)
    d D.card c C.card hD hC hd hc (by intros; positivity) (target_weights_sum l) hmean
  rw [targetExposureMean_eq D C l d c hl hd hc]
  unfold targetPowerMean
  simpa only [one_div_mul_eq_div, ← Finset.sum_div] using h

theorem uniform_target_exposure_approximation_empty_witness
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (l : Line F) (d : ℕ),
      N₀ ≤ D.card → l ∈ D → d ≤ D.card →
      (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        ((lineMultiplicity D p - 1 : ℕ) : ℝ)) ≤ M →
      |targetExposureMean D ∅ l d 0 - targetPowerMean D ∅ l d 0| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation_one_population M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D l d hD hl hd hmean
  have h := happrox (linePoints l) (fun _ => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) d D.card hD hd
    (by intros; positivity) (target_weights_sum l) hmean
  rw [targetExposureMean_eq D ∅ l d 0 hl hd (by simp)]
  unfold targetPowerMean
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  simp only [hm, Nat.descFactorial_zero, Nat.cast_one, div_self one_ne_zero, pow_zero, mul_one]
  simpa only [one_div_mul_eq_div, ← Finset.sum_div] using h

theorem shifted_target_mean_le {k : ℕ} {D C : Finset (Line F)} {l : Line F}
    (hpair : IsProfilePair k D C) (hl : l ∈ D) :
    (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
      (((lineMultiplicity D p - 1 + lineMultiplicity C p : ℕ) : ℝ))) ≤ 2 * k + 4 := by
  obtain ⟨hD, hDC, hC⟩ := hpair
  calc
    _ ≤ ∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le _ _) _
    _ = (∑ p ∈ linePoints l,
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ))) /
        (Fintype.card F : ℝ) := by
      simp only [one_div_mul_eq_div, Finset.sum_div]
    _ ≤ 2 * k + 4 := by
      simpa only [lineMultiplicity, deletionMultiplicity] using
        FiniteProfile.line_firstMoment_le_source_bound hD hC hDC
          (Finset.mem_union_left C hl)

theorem uniform_profile_pair_target_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (l : Line F) (d c : ℕ),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C →
      l ∈ D → d ≤ D.card → c ≤ C.card →
      |targetExposureMean D C l d c - targetPowerMean D C l d c| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ := uniform_target_exposure_approximation (2 * k + 4) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C l d c hD hC hpair hl hd hc
  exact happrox F D C l d c hD hC hl hd hc (shifted_target_mean_le hpair hl)

theorem uniform_deletion_target_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (l : Line F) (d : ℕ),
      N₀ ≤ D.card → IsDeletionSet k D → l ∈ D → d ≤ D.card →
      |targetExposureMean D ∅ l d 0 - targetPowerMean D ∅ l d 0| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    uniform_target_exposure_approximation_empty_witness (2 * k + 4) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D l d hD hDel hl hd
  apply happrox F D l d hD hl hd
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  simpa only [lineMultiplicity, Finset.filter_empty, Finset.card_empty, Nat.add_zero] using
    shifted_target_mean_le hpair hl

theorem shifted_cover_target_mean_le {k : ℕ} {D C : Finset (Line F)} {l : Line F}
    (hpair : IsProfilePair k D C) (hl : l ∈ C) :
    (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
      (((lineMultiplicity C p - 1 + lineMultiplicity D p : ℕ) : ℝ))) ≤ 2 * k + 4 := by
  obtain ⟨hD, hDC, hC⟩ := hpair
  calc
    _ ≤ ∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast (show lineMultiplicity C p - 1 + lineMultiplicity D p ≤
        lineMultiplicity D p + lineMultiplicity C p by omega)
    _ = (∑ p ∈ linePoints l,
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ))) /
        (Fintype.card F : ℝ) := by
      simp only [one_div_mul_eq_div, Finset.sum_div]
    _ ≤ 2 * k + 4 := by
      simpa only [lineMultiplicity, deletionMultiplicity] using
        FiniteProfile.line_firstMoment_le_source_bound hD hC hDC
          (Finset.mem_union_right D hl)

theorem uniform_profile_pair_cover_target_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (l : Line F) (d c : ℕ),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C →
      l ∈ C → d ≤ D.card → c ≤ C.card →
      |targetExposureMean C D l c d - targetPowerMean C D l c d| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ := uniform_target_exposure_approximation (2 * k + 4) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C l d c hD hC hpair hl hd hc
  exact happrox F C D l c d hC hD hl hc hd (shifted_cover_target_mean_le hpair hl)

end
end Balanced.AffineProfileExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PermutationSubsetLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.PermutationSubsetLaw

theorem expect_comp_of_fiber_card_eq {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (t : Finset β) (f : Ω → β) (m : ℕ) (hm : 0 < m)
    (hmap : ∀ ω ∈ s, f ω ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter (fun ω => f ω = b)).card = m)
    (g : β → ℝ) :
    (𝔼 ω ∈ s, g (f ω)) = 𝔼 b ∈ t, g b := by
  classical
  have hcard : s.card = t.card * m := by
    have h := Finset.sum_card_fiberwise_eq_card_filter s t f
    rw [Finset.filter_eq_self.mpr hmap] at h
    calc
      s.card = ∑ b ∈ t, (s.filter (fun ω => f ω = b)).card := h.symm
      _ = ∑ _b ∈ t, m := Finset.sum_congr rfl hfiber
      _ = t.card * m := by simp
  have hsum : (∑ ω ∈ s, g (f ω)) = (m : ℝ) * ∑ b ∈ t, g b := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    calc
      _ = ∑ b ∈ t, (m : ℝ) * g b := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          (∑ ω ∈ s.filter (fun ω => f ω = b), g (f ω)) =
              ∑ _ω ∈ s.filter (fun ω => f ω = b), g b := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [(Finset.mem_filter.mp hω).2]
          _ = _ := by simp [hfiber b hb]
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, hsum, hcard]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  by_cases ht : (t.card : ℝ) = 0
  · simp [ht]
  · field_simp

variable {α : Type*} [DecidableEq α]

theorem exists_perm_fixing_map (S T : Finset α) (x : α)
    (hcard : S.card = T.card) (hxS : x ∉ S) (hxT : x ∉ T) :
    ∃ τ : Equiv.Perm α, τ x = x ∧ S.map τ.toEmbedding = T := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
  have hsx : σ x ∉ T := by
    intro h
    rw [← hσ] at h
    obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp h
    exact hxS ((σ.injective hzx) ▸ hz)
  have hswap : T.map (Equiv.swap (σ x) x).toEmbedding = T := by
    apply Finset.eq_of_subset_of_card_le _ (by simp)
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    change Equiv.swap (σ x) x z ∈ T
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hz hsx)
      (ne_of_mem_of_not_mem hz hxT)]
    exact hz
  refine ⟨σ.trans (Equiv.swap (σ x) x), by simp, ?_⟩
  change S.map (σ.toEmbedding.trans (Equiv.swap (σ x) x).toEmbedding) = T
  rw [← Finset.map_map, hσ, hswap]

theorem target_image_fiber_card_eq [Fintype α]
    (I S T : Finset α) (i x : α) (hcard : S.card = T.card)
    (hxS : x ∉ S) (hxT : x ∉ T) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α =>
      σ i = x ∧ I.map σ.toEmbedding = S)).card) =
    ((Finset.univ.filter (fun σ : Equiv.Perm α =>
      σ i = x ∧ I.map σ.toEmbedding = T)).card) := by
  classical
  obtain ⟨τ, hτx, hτ⟩ := exists_perm_fixing_map S T x hcard hxS hxT
  apply Finset.card_equiv (postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change τ (σ i) = x
      rw [h.1, hτx]
    · change I.map (σ.toEmbedding.trans τ.toEmbedding) = T
      rw [← Finset.map_map, h.2, hτ]
  · intro h
    have hi : σ i = x := by
      apply τ.injective
      exact h.1.trans hτx.symm
    refine ⟨hi, ?_⟩
    apply Finset.map_injective τ.toEmbedding
    rw [hτ]
    have himage := h.2
    change I.map (σ.toEmbedding.trans τ.toEmbedding) = T at himage
    simpa only [Finset.map_map] using himage

theorem expect_image_conditioned_target [Fintype α]
    (I : Finset α) (i x : α) (hi : i ∉ I) (g : Finset α → ℝ) :
    (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x),
      g (I.map σ.toEmbedding)) =
    𝔼 S ∈ (Finset.univ.erase x).powersetCard I.card, g S := by
  classical
  let s := Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)
  let t := (Finset.univ.erase x).powersetCard I.card
  have hmaps (σ : Equiv.Perm α) (hσ : σ ∈ s) : I.map σ.toEmbedding ∈ t := by
    have hσx : σ i = x := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp⟩
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hax
    exact hi ((σ.injective (hax.trans hσx.symm)) ▸ ha)
  let σ₀ := Equiv.swap i x
  have hσ₀ : σ₀ ∈ s := by simp [s, σ₀]
  let S₀ := I.map σ₀.toEmbedding
  have hS₀ : S₀ ∈ t := hmaps σ₀ hσ₀
  let m := (s.filter (fun σ => I.map σ.toEmbedding = S₀)).card
  have hm : 0 < m := Finset.card_pos.mpr ⟨σ₀, Finset.mem_filter.mpr ⟨hσ₀, rfl⟩⟩
  apply expect_comp_of_fiber_card_eq s t (fun σ => I.map σ.toEmbedding) m hm hmaps
  intro S hS
  have hS' := Finset.mem_powersetCard.mp hS
  have hS₀' := Finset.mem_powersetCard.mp hS₀
  have hxS : x ∉ S := fun hx => (Finset.mem_erase.mp (hS'.1 hx)).1 rfl
  have hxS₀ : x ∉ S₀ := fun hx => (Finset.mem_erase.mp (hS₀'.1 hx)).1 rfl
  have h := target_image_fiber_card_eq I S S₀ i x
    (hS'.2.trans hS₀'.2.symm) hxS hxS₀
  simpa only [m, s, Finset.filter_filter] using h

theorem image_fiber_card_eq [Fintype α] (I S T : Finset α)
    (hcard : S.card = T.card) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α => I.map σ.toEmbedding = S)).card) =
    ((Finset.univ.filter (fun σ : Equiv.Perm α => I.map σ.toEmbedding = T)).card) := by
  classical
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
  apply Finset.card_equiv (postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    change I.map (σ.toEmbedding.trans τ.toEmbedding) = T
    rw [← Finset.map_map, h, hτ]
  · intro h
    apply Finset.map_injective τ.toEmbedding
    rw [hτ]
    change I.map (σ.toEmbedding.trans τ.toEmbedding) = T at h
    simpa only [Finset.map_map] using h

theorem expect_image [Fintype α] (I : Finset α) (g : Finset α → ℝ) :
    (𝔼 σ : Equiv.Perm α, g (I.map σ.toEmbedding)) =
      𝔼 S ∈ (Finset.univ : Finset α).powersetCard I.card, g S := by
  classical
  let m := ((Finset.univ : Finset (Equiv.Perm α)).filter
    (fun σ => I.map σ.toEmbedding = I)).card
  have hm : 0 < m := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.refl α, by simp⟩
  apply expect_comp_of_fiber_card_eq (Finset.univ : Finset (Equiv.Perm α))
    ((Finset.univ : Finset α).powersetCard I.card) (fun σ : Equiv.Perm α => I.map σ.toEmbedding) m hm
  · intro σ _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩
  · intro S hS
    exact image_fiber_card_eq I S I (Finset.mem_powersetCard.mp hS).2

theorem expect_two_images_conditioned_target [Fintype α]
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : Finset α) (J : Finset β) (i x : α) (hi : i ∉ I)
    (g : Finset α → Finset β → ℝ) :
    (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x),
      𝔼 τ : Equiv.Perm β, g (I.map σ.toEmbedding) (J.map τ.toEmbedding)) =
    𝔼 S ∈ (Finset.univ.erase x).powersetCard I.card,
      𝔼 T ∈ (Finset.univ : Finset β).powersetCard J.card, g S T := by
  calc
    _ = 𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x),
        𝔼 T ∈ (Finset.univ : Finset β).powersetCard J.card,
          g (I.map σ.toEmbedding) T := by
      apply Finset.expect_congr rfl
      intro σ _
      exact expect_image J (g (I.map σ.toEmbedding))
    _ = _ := expect_image_conditioned_target I i x hi
      (fun S => 𝔼 T ∈ (Finset.univ : Finset β).powersetCard J.card, g S T)

theorem expect_eq_expect_fiber_of_card_eq {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (t : Finset β) (f : Ω → β) (m : ℕ)
    (hmap : ∀ ω ∈ s, f ω ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter (fun ω => f ω = b)).card = m)
    (g : Ω → ℝ) :
    (𝔼 ω ∈ s, g ω) = 𝔼 b ∈ t, 𝔼 ω ∈ s.filter (fun ω => f ω = b), g ω := by
  classical
  have hcard : s.card = t.card * m := by
    have h := Finset.sum_card_fiberwise_eq_card_filter s t f
    rw [Finset.filter_eq_self.mpr hmap] at h
    calc
      s.card = ∑ b ∈ t, (s.filter (fun ω => f ω = b)).card := h.symm
      _ = ∑ _b ∈ t, m := Finset.sum_congr rfl hfiber
      _ = t.card * m := by simp
  have hsum : (∑ b ∈ t, 𝔼 ω ∈ s.filter (fun ω => f ω = b), g ω) =
      (∑ ω ∈ s, g ω) / (m : ℝ) := by
    calc
      _ = ∑ b ∈ t, (∑ ω ∈ s.filter (fun ω => f ω = b), g ω) / (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.expect_eq_sum_div_card, hfiber b hb]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_fiberwise_of_maps_to hmap]
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, hsum, hcard]
  simp only [Nat.cast_mul, div_div, mul_comm]

theorem target_fiber_card_eq [Fintype α] (i x y : α) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)).card) =
    ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = y)).card) := by
  classical
  let τ := Equiv.swap x y
  apply Finset.card_equiv (postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    change τ (σ i) = y
    simp [τ, h]
  · intro h
    apply τ.injective
    change τ (σ i) = y at h
    simpa [τ] using h

theorem expect_by_target [Fintype α] (i : α) (g : Equiv.Perm α → ℝ) :
    (𝔼 σ : Equiv.Perm α, g σ) =
      𝔼 x : α, 𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x), g σ := by
  classical
  apply expect_eq_expect_fiber_of_card_eq (Finset.univ : Finset (Equiv.Perm α))
    (Finset.univ : Finset α) (fun σ : Equiv.Perm α => σ i)
    ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = i)).card)
    (fun _ _ => Finset.mem_univ _)
  intro x _
  exact target_fiber_card_eq i x i

end Balanced.PermutationSubsetLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PermutationExposureMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
attribute [local instance] Classical.propDecidable

theorem two_species_subset_uncovered_mean {A B P : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq P]
    (U : Finset A) (V : Finset B) (X : Finset P)
    (incidentA : P → A → Prop) (incidentB : P → B → Prop)
    (d e : ℕ) (hd : d ≤ U.card) (he : e ≤ V.card) :
    (𝔼 S ∈ U.powersetCard d, 𝔼 T ∈ V.powersetCard e,
      ((X.filter (fun p =>
        (∀ l ∈ U \ S, ¬ incidentA p l) ∧
        (∀ l ∈ V \ T, ¬ incidentB p l))).card : ℝ)) =
      ∑ p ∈ X,
        ((d.descFactorial (U.filter (incidentA p)).card : ℝ) /
          (U.card.descFactorial (U.filter (incidentA p)).card : ℝ)) *
        ((e.descFactorial (V.filter (incidentB p)).card : ℝ) /
          (V.card.descFactorial (V.filter (incidentB p)).card : ℝ)) := by
  classical
  rw [← Finset.expect_product']
  rw [Finset.expect_eq_sum_div_card, Finset.sum_div]
  convert (uniform_expected_filtered_card _
    ((Finset.powersetCard_nonempty.mpr hd).product (Finset.powersetCard_nonempty.mpr he))
    X (fun p S => (∀ l ∈ U \ S.1, ¬ incidentA p l) ∧
      (∀ l ∈ V \ S.2, ¬ incidentB p l))).trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro S hS
    congr 3
    ext p
    simp only [Finset.mem_filter]
  · apply Finset.sum_congr rfl
    intro p hp
    simp_rw [uncovered_iff_incident_subset]
    exact uniform_two_subsets_contains_probability U (U.filter (incidentA p))
      V (V.filter (incidentB p)) d e
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd he

theorem permutation_target_uncovered_mean {A B P : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq P]
    (I : Finset A) (J : Finset B) (i x : A) (hi : i ∉ I)
    (X : Finset P) (incidentA : P → A → Prop) (incidentB : P → B → Prop) :
    (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm A => σ i = x),
      𝔼 τ : Equiv.Perm B,
        ((X.filter (fun p =>
          (∀ l ∈ (Finset.univ.erase x) \ I.map σ.toEmbedding, ¬ incidentA p l) ∧
          (∀ l ∈ Finset.univ \ J.map τ.toEmbedding, ¬ incidentB p l))).card : ℝ)) =
      ∑ p ∈ X,
        ((I.card.descFactorial ((Finset.univ.erase x).filter (incidentA p)).card : ℝ) /
          ((Finset.univ.erase x).card.descFactorial
            ((Finset.univ.erase x).filter (incidentA p)).card : ℝ)) *
        ((J.card.descFactorial (Finset.univ.filter (incidentB p)).card : ℝ) /
          ((Finset.univ : Finset B).card.descFactorial
            (Finset.univ.filter (incidentB p)).card : ℝ)) := by
  classical
  have hI : I.card ≤ (Finset.univ.erase x).card := by
    have hsub : I ⊆ (Finset.univ.erase i) := by
      intro a ha
      exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem ha hi, Finset.mem_univ _⟩
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem (Finset.mem_univ x)] using Finset.card_le_card hsub
  have hJ : J.card ≤ (Finset.univ : Finset B).card :=
    Finset.card_le_card (Finset.subset_univ J)
  convert (PermutationSubsetLaw.expect_two_images_conditioned_target I J i x hi
    (fun S T => ((X.filter (fun p =>
      (∀ l ∈ (Finset.univ.erase x) \ S, ¬ incidentA p l) ∧
      (∀ l ∈ Finset.univ \ T, ¬ incidentB p l))).card : ℝ))).trans ?_ using 1
  all_goals try with_reducible_and_instances rfl
  convert two_species_subset_uncovered_mean (Finset.univ.erase x) Finset.univ
      X incidentA incidentB I.card J.card hI hJ using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.expect_congr rfl
  intro S hS
  apply Finset.expect_congr rfl
  intro T hT
  congr 2
  ext p
  simp only [Finset.mem_filter]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePermutationExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffinePermutationExposure

universe u

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem subtype_filter_card {α : Type*} [DecidableEq α]
    (U : Finset α) (P : α → Prop) :
    ((Finset.univ : Finset U).filter (fun x => P x.1)).card =
      (U.filter P).card := by
  classical
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.2, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro y hy
    refine ⟨⟨y, (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem erased_subtype_incidence_card
    (D : Finset (Line F)) (l : D) (p : Point F) (hp : OnLine p l.1) :
    (((Finset.univ : Finset D).erase l).filter (fun m => OnLine p m.1)).card =
      lineMultiplicity D p - 1 := by
  rw [Finset.filter_erase, Finset.card_erase_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hp⟩)]
  apply congrArg (fun n : ℕ => n - 1)
  unfold lineMultiplicity
  apply Finset.card_bij (fun m _ => m.1)
  · intro m hm
    exact Finset.mem_filter.mpr ⟨m.2, (Finset.mem_filter.mp hm).2⟩
  · intro m _ n _ hmn
    exact Subtype.ext hmn
  · intro m hm
    refine ⟨⟨m, (Finset.mem_filter.mp hm).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm).2⟩

omit [Field F] [Fintype F] in

theorem remaining_count_le (D : Finset (Line F)) (I : Finset D)
    (i : D) (hi : i ∉ I) : I.card + 1 ≤ D.card := by
  have hsub : I ⊆ (Finset.univ : Finset D).erase i := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem ha hi, Finset.mem_univ _⟩
  have h := Finset.card_le_card hsub
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_coe] at h
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨i.1, i.2⟩
  omega

theorem targetOrderMean_eq_targetExposureMean
    (D C : Finset (Line F)) (I : Finset D) (J : Finset C)
    (i l : D) (hi : i ∉ I) :
    targetOrderMean D C I J i l =
      AffineProfileExposure.targetExposureMean D C l.1 (I.card + 1) J.card := by
  have hd := remaining_count_le D I i hi
  have hc : J.card ≤ C.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  unfold targetOrderMean
  convert (congrArg (fun z : ℝ => z / (Fintype.card F : ℝ))
    (permutation_target_uncovered_mean I J i l hi (linePoints l.1)
      (fun p m => OnLine p m.1) (fun p m => OnLine p m.1))).trans ?_ using 1
  · apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ))
    apply Finset.expect_congr rfl
    intro σ hσ
    apply Finset.expect_congr rfl
    intro τ hτ
    apply congrArg (fun S : Finset (Point F) => (S.card : ℝ))
    ext p
    simp only [Finset.mem_filter]
  · rw [AffineProfileExposure.targetExposureMean_eq D C l.1 (I.card + 1) J.card
      l.2 hd hc]
    apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ))
    apply Finset.sum_congr rfl
    intro p hp
    have hon : OnLine p l.1 := (Finset.mem_filter.mp hp).2
    simp only [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
      Fintype.card_coe, Nat.add_sub_cancel]
    congr 4
    · convert erased_subtype_incidence_card D l p hon using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert erased_subtype_incidence_card D l p hon using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]

theorem uniform_deletion_order_target_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D),
      N₀ ≤ D.card → IsDeletionSet k D → i ∉ I →
      |targetOrderMean D ∅ I ∅ i l -
        AffineProfileExposure.targetPowerMean D ∅ l.1 (I.card + 1) 0| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    AffineProfileExposure.uniform_deletion_target_approximation k hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D I i l hD hDel hi
  rw [targetOrderMean_eq_targetExposureMean D ∅ I ∅ i l hi, Finset.card_empty]
  exact happrox F D l.1 (I.card + 1) hD hDel l.2 (remaining_count_le D I i hi)

end
end Balanced.AffinePermutationExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePlaneOrderExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffinePlaneOrderExposure

universe u
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open AffinePermutationExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem erased_subtype_card (D : Finset (Line F)) (l : D) (p : Point F) :
    (((Finset.univ : Finset D).erase l).filter (fun m => OnLine p m.1)).card =
      lineMultiplicity (D.erase l.1) p := by
  unfold lineMultiplicity
  apply Finset.card_bij (fun m _ => m.1)
  · intro m hm
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, m.2⟩, hp⟩
    intro heq
    exact (Finset.mem_erase.mp hm).1 (Subtype.ext heq)
  · intro m _ n _ hmn
    exact Subtype.ext hmn
  · intro m hm
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    refine ⟨⟨m, (Finset.mem_erase.mp hm).2⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hp⟩
    intro heq
    exact (Finset.mem_erase.mp hm).1 (congrArg Subtype.val heq)

theorem planeOrderMean_eq (D C : Finset (Line F)) (I : Finset D) (J : Finset C)
    (i l : D) (hi : i ∉ I) :
    planeOrderMean D C I J i l =
      (∑ p : Point F,
        ((I.card.descFactorial (lineMultiplicity (D.erase l.1) p) : ℝ) /
          ((D.card - 1).descFactorial (lineMultiplicity (D.erase l.1) p) : ℝ)) *
        ((J.card.descFactorial (lineMultiplicity C p) : ℝ) /
          (C.card.descFactorial (lineMultiplicity C p) : ℝ))) /
            (Fintype.card F : ℝ) ^ 2 := by
  unfold planeOrderMean
  convert (congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
    (permutation_target_uncovered_mean I J i l hi Finset.univ
      (fun p m => OnLine p m.1) (fun p m => OnLine p m.1))).trans ?_ using 1
  · apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
    apply Finset.expect_congr rfl
    intro σ hσ
    apply Finset.expect_congr rfl
    intro τ hτ
    apply congrArg (fun S : Finset (Point F) => (S.card : ℝ))
    ext p
    simp only [Finset.mem_filter]
  · apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
      Fintype.card_coe]
    congr 4
    · convert erased_subtype_card D l p using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert erased_subtype_card D l p using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]

omit [DecidableEq F] in

theorem plane_weights_sum :
    ∑ _p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) = 1 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, Point, Fintype.card_prod,
    Nat.cast_mul, nsmul_eq_mul, pow_two]
  field_simp

omit [Fintype F] in

theorem multiplicity_erase_le (D : Finset (Line F)) (l : Line F) (p : Point F) :
    lineMultiplicity (D.erase l) p ≤ lineMultiplicity D p := by
  unfold lineMultiplicity
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))

omit [Fintype F] in

theorem multiplicity_erase_eq_off (D : Finset (Line F)) (l : Line F)
    (p : Point F) (hp : ¬ OnLine p l) :
    lineMultiplicity (D.erase l) p = lineMultiplicity D p := by
  unfold lineMultiplicity
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp only [Finset.mem_filter, not_and]
  exact fun _ => hp

theorem erasedPlanePowerMean_error (D C : Finset (Line F)) (l : Line F) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) :
    |erasedPlanePowerMean D C l d c - planePowerMean D C d c| ≤
      1 / (Fintype.card F : ℝ) := by
  have hx := ProfileTargetExclusion.fraction_bounds d D.card hd
  have hy := ProfileTargetExclusion.fraction_bounds c C.card hc
  have hb (a b : ℕ) :
      0 ≤ ((d : ℝ) / D.card) ^ a * ((c : ℝ) / C.card) ^ b ∧
      ((d : ℝ) / D.card) ^ a * ((c : ℝ) / C.card) ^ b ≤ 1 := by
    refine ⟨mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg hy.1 _), ?_⟩
    calc
      _ ≤ 1 * ((c : ℝ) / C.card) ^ b :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hx.1 hx.2) (pow_nonneg hy.1 _)
      _ = ((c : ℝ) / C.card) ^ b := one_mul _
      _ ≤ 1 := pow_le_one₀ hy.1 hy.2
  apply AffineTargetError.plane_average_error l _ _
    (fun p => hb _ _) (fun p => hb _ _)
  intro p hp
  rw [multiplicity_erase_eq_off D l p hp]

theorem planePowerMean_eq_profile_transform (D C : Finset (Line F)) (d c : ℕ) :
    planePowerMean D C d c =
      ∑' ij : ℕ × ℕ, planeProfile D C ij *
        (((d : ℝ) / D.card) ^ ij.1 * ((c : ℝ) / C.card) ^ ij.2) := by
  have h := planeProfile_weighted_hasSum D C (fun ij =>
    ((d : ℝ) / D.card) ^ ij.1 * ((c : ℝ) / C.card) ^ ij.2)
  exact h.tsum_eq.symm.trans (tsum_congr (fun ij => mul_comm _ _))

theorem plane_mean_le {k : ℕ} {D C : Finset (Line F)} (hpair : IsProfilePair k D C) :
    (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
      (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ))) ≤ 2 * (k : ℝ) + 4 := by
  have hb := (planeProfile_isBounded k D C hpair.1 hpair.2.2).2.2.2
  rw [(planeProfile_weighted_hasSum D C
    (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ))).tsum_eq] at hb
  simpa only [one_div_mul_eq_div, ← Finset.sum_div] using hb

theorem erased_plane_mean_le {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) :
    (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
      (((lineMultiplicity (D.erase l) p + lineMultiplicity C p : ℕ) : ℝ))) ≤
        2 * (k : ℝ) + 4 := by
  apply le_trans _ (plane_mean_le hpair)
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Nat.add_le_add_right (multiplicity_erase_le D l p) _

theorem uniform_plane_order_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i l : D),
      N₀ ≤ D.card → N₀ ≤ C.card → i ∉ I →
      (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
        (((lineMultiplicity (D.erase l.1) p + lineMultiplicity C p : ℕ) : ℝ))) ≤ M →
      |planeOrderMean D C I J i l - planePowerMean D C (I.card + 1) J.card| <
        ε + 1 / (Fintype.card F : ℝ) := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C I J i l hD hC hi hmean
  have hd := remaining_count_le D I i hi
  have hc : J.card ≤ C.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  have h := happrox Finset.univ (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity (D.erase l.1) p) (fun p => lineMultiplicity C p)
    (I.card + 1) D.card J.card C.card hD hC hd hc
    (by intros; positivity) plane_weights_sum hmean
  have hfirst : |planeOrderMean D C I J i l -
      erasedPlanePowerMean D C l.1 (I.card + 1) J.card| < ε := by
    rw [planeOrderMean_eq D C I J i l hi]
    simpa only [Nat.add_sub_cancel, one_div_mul_eq_div, ← Finset.sum_div,
      erasedPlanePowerMean] using h
  exact (abs_sub_le _ _ _).trans_lt
    (add_lt_add_of_lt_of_le hfirst (erasedPlanePowerMean_error D C l.1
      (I.card + 1) J.card hd hc))

theorem uniform_plane_order_approximation_empty_witness
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D),
      N₀ ≤ D.card → i ∉ I →
      (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
        ((lineMultiplicity (D.erase l.1) p : ℕ) : ℝ)) ≤ M →
      |planeOrderMean D ∅ I ∅ i l - planePowerMean D ∅ (I.card + 1) 0| <
        ε + 1 / (Fintype.card F : ℝ) := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation_one_population M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D I i l hD hi hmean
  have hd := remaining_count_le D I i hi
  have h := happrox Finset.univ (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity (D.erase l.1) p) (I.card + 1) D.card hD hd
    (by intros; positivity) plane_weights_sum hmean
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  have hfirst : |planeOrderMean D ∅ I ∅ i l -
      erasedPlanePowerMean D ∅ l.1 (I.card + 1) 0| < ε := by
    rw [planeOrderMean_eq D ∅ I ∅ i l hi]
    simpa only [Nat.add_sub_cancel, one_div_mul_eq_div, ← Finset.sum_div,
      erasedPlanePowerMean, hm, Nat.descFactorial_zero, Nat.cast_one,
      div_self one_ne_zero, pow_zero, mul_one] using h
  exact (abs_sub_le _ _ _).trans_lt
    (add_lt_add_of_lt_of_le hfirst (erasedPlanePowerMean_error D ∅ l.1
      (I.card + 1) 0 hd (by simp)))

theorem planePowerMean_swap (D C : Finset (Line F)) (d c : ℕ) :
    planePowerMean C D c d = planePowerMean D C d c := by
  unfold planePowerMean
  apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
  apply Finset.sum_congr rfl
  intro p hp
  exact mul_comm _ _

theorem erased_cover_plane_mean_le {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) :
    (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
      (((lineMultiplicity (C.erase l) p + lineMultiplicity D p : ℕ) : ℝ))) ≤
        2 * (k : ℝ) + 4 := by
  apply le_trans _ (plane_mean_le hpair)
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (show lineMultiplicity (C.erase l) p + lineMultiplicity D p ≤
    lineMultiplicity D p + lineMultiplicity C p by
      have h := multiplicity_erase_le C l p
      omega)

theorem exists_reciprocal_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, Q₀ ≤ q → 1 / (q : ℝ) < ε := by
  have hlim : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop 1
  exact Filter.eventually_atTop.mp (hlim.eventually_lt_const hε)

theorem uniform_profile_pair_order_plane_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i l : D),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I →
      |planeOrderMean D C I J i l -
        ∑' ij : ℕ × ℕ, planeProfile D C ij *
          ((((I.card + 1 : ℕ) : ℝ) / D.card) ^ ij.1 *
            ((J.card : ℝ) / C.card) ^ ij.2)| < ε := by
  obtain ⟨N, hN, happrox⟩ :=
    uniform_plane_order_approximation (2 * (k : ℝ) + 4) (half_pos hε)
  obtain ⟨Q, hQ⟩ := exists_reciprocal_cutoff (half_pos hε)
  refine ⟨max N Q, by omega, ?_⟩
  intro F hField hFin hDec D C I J i l hq hD hC hpair hi
  rw [← planePowerMean_eq_profile_transform]
  have h := happrox F D C I J i l (by omega) (by omega) hi
    (erased_plane_mean_le hpair l.1)
  have hsmall := hQ (Fintype.card F) (by omega)
  linarith

theorem uniform_profile_pair_order_cover_plane_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset C) (J : Finset D) (i l : C),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I →
      |planeOrderMean C D I J i l -
        ∑' ij : ℕ × ℕ, planeProfile D C ij *
          (((J.card : ℝ) / D.card) ^ ij.1 *
            (((I.card + 1 : ℕ) : ℝ) / C.card) ^ ij.2)| < ε := by
  obtain ⟨N, hN, happrox⟩ :=
    uniform_plane_order_approximation (2 * (k : ℝ) + 4) (half_pos hε)
  obtain ⟨Q, hQ⟩ := exists_reciprocal_cutoff (half_pos hε)
  refine ⟨max N Q, by omega, ?_⟩
  intro F hField hFin hDec D C I J i l hq hD hC hpair hi
  rw [← planePowerMean_eq_profile_transform, ← planePowerMean_swap D C]
  have h := happrox F C D I J i l (by omega) (by omega) hi
    (erased_cover_plane_mean_le hpair l.1)
  have hsmall := hQ (Fintype.card F) (by omega)
  linarith

theorem uniform_deletion_order_plane_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → IsDeletionSet k D → i ∉ I →
      |planeOrderMean D ∅ I ∅ i l - planePowerMean D ∅ (I.card + 1) 0| < ε := by
  obtain ⟨N, hN, happrox⟩ :=
    uniform_plane_order_approximation_empty_witness (2 * (k : ℝ) + 4) (half_pos hε)
  obtain ⟨Q, hQ⟩ := exists_reciprocal_cutoff (half_pos hε)
  refine ⟨max N Q, by omega, ?_⟩
  intro F hField hFin hDec D I i l hq hD hDel hi
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  have hmean := erased_plane_mean_le hpair l.1
  have h := happrox F D I i l (by omega) hi (by
    simpa only [lineMultiplicity, Finset.filter_empty, Finset.card_empty,
      Nat.add_zero] using hmean)
  have hsmall := hQ (Fintype.card F) (by omega)
  linarith

end
end Balanced.AffinePlaneOrderExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineProfileParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffineProfileParameter

universe u

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open AffinePlaneOrderExposure AffineProfileExposure ProfileDetectionBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem monomial_eq_real_power {z : ℝ} (hz : 0 < z) (a b : ℕ) :
    z ^ a * (z ^ Real.sqrt 2) ^ b =
      z ^ ((a : ℝ) + Real.sqrt 2 * b) := by
  rw [Real.rpow_add hz, Real.rpow_natCast, Real.rpow_mul hz.le,
    Real.rpow_natCast]

omit [Fintype F] in

theorem target_multiplicity_pos (D : Finset (Line F)) (l : Line F)
    (hl : l ∈ D) (p : Point F) (hp : OnLine p l) :
    1 ≤ lineMultiplicity D p := by
  exact Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hp⟩⟩

theorem planeTest_eq_average (D C : Finset (Line F)) {z : ℝ} (hz : 0 < z) :
    planeTest (planeProfile D C) z =
      (∑ p : Point F, z ^ lineMultiplicity D p *
        (z ^ Real.sqrt 2) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) ^ 2 := by
  have h := planeProfile_weighted_hasSum D C (fun ij =>
    z ^ ((ij.1 : ℝ) + Real.sqrt 2 * ij.2))
  calc
    _ = (∑ p : Point F,
        z ^ ((lineMultiplicity D p : ℝ) + Real.sqrt 2 * lineMultiplicity C p)) /
          (Fintype.card F : ℝ) ^ 2 := by
      exact (tsum_congr (fun ij => mul_comm _ _)).trans h.tsum_eq
    _ = _ := by
      apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ) ^ 2)
      apply Finset.sum_congr rfl
      intro p hp
      exact (monomial_eq_real_power hz _ _).symm

theorem dTest_eq_average (D C : Finset (Line F)) (l : Line F)
    (hl : l ∈ D) {z : ℝ} (hz : 0 < z) :
    dTest (lineProfile D C l) z =
      (∑ p ∈ linePoints l, z ^ (lineMultiplicity D p - 1) *
        (z ^ Real.sqrt 2) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) := by
  have h := lineProfile_weighted_hasSum D C l (fun ij =>
    z ^ ((ij.1 : ℝ) - 1 + Real.sqrt 2 * ij.2))
  calc
    _ = (∑ p ∈ linePoints l,
        z ^ ((lineMultiplicity D p : ℝ) - 1 + Real.sqrt 2 * lineMultiplicity C p)) /
          (Fintype.card F : ℝ) := by
      exact (tsum_congr (fun ij => mul_comm _ _)).trans h.tsum_eq
    _ = _ := by
      apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ))
      apply Finset.sum_congr rfl
      intro p hp
      have hm := target_multiplicity_pos D l hl p (Finset.mem_filter.mp hp).2
      rw [monomial_eq_real_power hz, Nat.cast_sub hm, Nat.cast_one]

theorem cTest_eq_average (D C : Finset (Line F)) (l : Line F)
    (hl : l ∈ C) {z : ℝ} (hz : 0 < z) :
    cTest (lineProfile D C l) z =
      (∑ p ∈ linePoints l, z ^ lineMultiplicity D p *
        (z ^ Real.sqrt 2) ^ (lineMultiplicity C p - 1)) / (Fintype.card F : ℝ) := by
  have h := lineProfile_weighted_hasSum D C l (fun ij =>
    z ^ ((ij.1 : ℝ) + Real.sqrt 2 * ((ij.2 : ℝ) - 1)))
  calc
    _ = (∑ p ∈ linePoints l,
        z ^ ((lineMultiplicity D p : ℝ) + Real.sqrt 2 * ((lineMultiplicity C p : ℝ) - 1))) /
          (Fintype.card F : ℝ) := by
      exact (tsum_congr (fun ij => mul_comm _ _)).trans h.tsum_eq
    _ = _ := by
      apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ))
      apply Finset.sum_congr rfl
      intro p hp
      have hm := target_multiplicity_pos C l hl p (Finset.mem_filter.mp hp).2
      rw [monomial_eq_real_power hz, Nat.cast_sub hm, Nat.cast_one]

theorem planePowerMean_error_to_planeTest {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ)
    (hC : |(c : ℝ) / C.card - z ^ Real.sqrt 2| ≤ δ) :
    |planePowerMean D C d c - planeTest (planeProfile D C) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hy : 0 ≤ z ^ Real.sqrt 2 ∧ z ^ Real.sqrt 2 ≤ 1 :=
    ⟨Real.rpow_nonneg hz.le _, Real.rpow_le_one hz.le hz1 (Real.sqrt_nonneg 2)⟩
  have h := ProfileTargetExclusion.weighted_parameter_error Finset.univ
    (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity D p) (fun p => lineMultiplicity C p)
    ((d : ℝ) / D.card) z ((c : ℝ) / C.card) (z ^ Real.sqrt 2)
    δ (2 * (k : ℝ) + 4) (by intros; positivity) (plane_mean_le hpair)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    (ProfileTargetExclusion.fraction_bounds c C.card hc) hy hδ hD hC
  rw [planeTest_eq_average D C hz]
  simpa only [planePowerMean, one_div_mul_eq_div, ← Finset.sum_div] using h

theorem targetPowerMean_error_to_dTest {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) (hl : l ∈ D) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ)
    (hC : |(c : ℝ) / C.card - z ^ Real.sqrt 2| ≤ δ) :
    |targetPowerMean D C l d c - dTest (lineProfile D C l) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hy : 0 ≤ z ^ Real.sqrt 2 ∧ z ^ Real.sqrt 2 ≤ 1 :=
    ⟨Real.rpow_nonneg hz.le _, Real.rpow_le_one hz.le hz1 (Real.sqrt_nonneg 2)⟩
  have h := ProfileTargetExclusion.weighted_parameter_error (linePoints l)
    (fun _ : Point F => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) (fun p => lineMultiplicity C p)
    ((d : ℝ) / D.card) z ((c : ℝ) / C.card) (z ^ Real.sqrt 2)
    δ (2 * (k : ℝ) + 4) (by intros; positivity) (shifted_target_mean_le hpair hl)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    (ProfileTargetExclusion.fraction_bounds c C.card hc) hy hδ hD hC
  rw [dTest_eq_average D C l hl hz]
  simpa only [targetPowerMean, one_div_mul_eq_div, ← Finset.sum_div] using h

theorem targetPowerMean_error_to_cTest {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) (hl : l ∈ C) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ)
    (hC : |(c : ℝ) / C.card - z ^ Real.sqrt 2| ≤ δ) :
    |targetPowerMean C D l c d - cTest (lineProfile D C l) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hy : 0 ≤ z ^ Real.sqrt 2 ∧ z ^ Real.sqrt 2 ≤ 1 :=
    ⟨Real.rpow_nonneg hz.le _, Real.rpow_le_one hz.le hz1 (Real.sqrt_nonneg 2)⟩
  have h := ProfileTargetExclusion.weighted_parameter_error (linePoints l)
    (fun _ : Point F => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity C p - 1) (fun p => lineMultiplicity D p)
    ((c : ℝ) / C.card) (z ^ Real.sqrt 2) ((d : ℝ) / D.card) z
    δ (2 * (k : ℝ) + 4) (by intros; positivity) (shifted_cover_target_mean_le hpair hl)
    (ProfileTargetExclusion.fraction_bounds c C.card hc) hy
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩ hδ hC hD
  rw [cTest_eq_average D C l hl hz]
  simp only [one_div_mul_eq_div, ← Finset.sum_div] at h
  simpa only [targetPowerMean, mul_comm] using h

theorem planePowerMean_empty_error_to_planeTest {k : ℕ} {D : Finset (Line F)}
    (hDel : IsDeletionSet k D) (d : ℕ) (hd : d ≤ D.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ) :
    |planePowerMean D ∅ d 0 - planeTest (planeProfile D ∅) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  have hmean := plane_mean_le hpair
  simp only [hm, Nat.add_zero] at hmean
  have h := ProfileTargetExclusion.weighted_parameter_error Finset.univ
    (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity D p) (fun _ => 0)
    ((d : ℝ) / D.card) z 0 0 δ (2 * (k : ℝ) + 4)
    (by intros; positivity) (by simpa only [Nat.add_zero] using hmean)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩ hδ hD (by simpa using hδ)
  rw [planeTest_eq_average D ∅ hz]
  simpa only [planePowerMean, hm, pow_zero, mul_one,
    one_div_mul_eq_div, ← Finset.sum_div] using h

theorem targetPowerMean_empty_error_to_dTest {k : ℕ} {D : Finset (Line F)}
    (hDel : IsDeletionSet k D) (l : Line F) (hl : l ∈ D) (d : ℕ)
    (hd : d ≤ D.card) {z δ : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ) :
    |targetPowerMean D ∅ l d 0 - dTest (lineProfile D ∅ l) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  have hmean := shifted_target_mean_le hpair hl
  simp only [hm, Nat.add_zero] at hmean
  have h := ProfileTargetExclusion.weighted_parameter_error (linePoints l)
    (fun _ : Point F => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) (fun _ => 0)
    ((d : ℝ) / D.card) z 0 0 δ (2 * (k : ℝ) + 4)
    (by intros; positivity) (by simpa only [Nat.add_zero] using hmean)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩ hδ hD (by simpa using hδ)
  rw [dTest_eq_average D ∅ l hl hz]
  simpa only [targetPowerMean, hm, pow_zero, mul_one,
    one_div_mul_eq_div, ← Finset.sum_div] using h

theorem uniform_order_d_tests_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i l : D) (z : ℝ),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I → 0 < z → z ≤ 1 →
      |(((I.card + 1 : ℕ) : ℝ) / D.card) - z| ≤ δ →
      |((J.card : ℝ) / C.card) - z ^ Real.sqrt 2| ≤ δ →
      |AffinePermutationExposure.targetOrderMean D C I J i l -
        dTest (lineProfile D C l.1) z| < ε ∧
      |planeOrderMean D C I J i l - planeTest (planeProfile D C) z| < ε := by
  obtain ⟨Nt, hNt, ht⟩ := uniform_profile_pair_target_approximation k (half_pos hε)
  obtain ⟨Np, hNp, hp⟩ := uniform_profile_pair_order_plane_approximation k (half_pos hε)
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (2 * (k : ℝ) + 4)
  refine ⟨max Nt Np, by omega, δ, hδ, ?_⟩
  intro F hField hFin hDec D C I J i l z hq hD hC hpair hi hz hz1 heD heC
  have hd := AffinePermutationExposure.remaining_count_le D I i hi
  have hc : J.card ≤ C.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  have ht' : |AffinePermutationExposure.targetOrderMean D C I J i l -
      targetPowerMean D C l.1 (I.card + 1) J.card| < ε / 2 := by
    rw [AffinePermutationExposure.targetOrderMean_eq_targetExposureMean D C I J i l hi]
    exact ht F D C l.1 (I.card + 1) J.card (by omega) (by omega) hpair l.2 hd hc
  have hp' : |planeOrderMean D C I J i l - planePowerMean D C (I.card + 1) J.card| < ε / 2 := by
    simpa only [← planePowerMean_eq_profile_transform] using
      hp F D C I J i l (by omega) (by omega) (by omega) hpair hi
  have hte := targetPowerMean_error_to_dTest hpair l.1 l.2 (I.card + 1) J.card
    hd hc hz hz1 hδ.le heD heC
  have hpe := planePowerMean_error_to_planeTest hpair (I.card + 1) J.card
    hd hc hz hz1 hδ.le heD heC
  constructor
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add ht' (hte.trans_lt hsmall))
    simpa only [add_halves] using htri
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add hp' (hpe.trans_lt hsmall))
    simpa only [add_halves] using htri

theorem uniform_order_c_tests_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset C) (J : Finset D) (i l : C) (z : ℝ),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I → 0 < z → z ≤ 1 →
      |((J.card : ℝ) / D.card) - z| ≤ δ →
      |(((I.card + 1 : ℕ) : ℝ) / C.card) - z ^ Real.sqrt 2| ≤ δ →
      |AffinePermutationExposure.targetOrderMean C D I J i l -
        cTest (lineProfile D C l.1) z| < ε ∧
      |planeOrderMean C D I J i l - planeTest (planeProfile D C) z| < ε := by
  obtain ⟨Nt, hNt, ht⟩ := uniform_profile_pair_cover_target_approximation k (half_pos hε)
  obtain ⟨Np, hNp, hp⟩ := uniform_profile_pair_order_cover_plane_approximation k (half_pos hε)
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (2 * (k : ℝ) + 4)
  refine ⟨max Nt Np, by omega, δ, hδ, ?_⟩
  intro F hField hFin hDec D C I J i l z hq hD hC hpair hi hz hz1 heD heC
  have hc := AffinePermutationExposure.remaining_count_le C I i hi
  have hd : J.card ≤ D.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  have ht' : |AffinePermutationExposure.targetOrderMean C D I J i l -
      targetPowerMean C D l.1 (I.card + 1) J.card| < ε / 2 := by
    rw [AffinePermutationExposure.targetOrderMean_eq_targetExposureMean C D I J i l hi]
    exact ht F D C l.1 J.card (I.card + 1) (by omega) (by omega) hpair l.2 hd hc
  have hp' : |planeOrderMean C D I J i l - planePowerMean D C J.card (I.card + 1)| < ε / 2 := by
    simpa only [← planePowerMean_eq_profile_transform] using
      hp F D C I J i l (by omega) (by omega) (by omega) hpair hi
  have hte := targetPowerMean_error_to_cTest hpair l.1 l.2 J.card (I.card + 1)
    hd hc hz hz1 hδ.le heD heC
  have hpe := planePowerMean_error_to_planeTest hpair J.card (I.card + 1)
    hd hc hz hz1 hδ.le heD heC
  constructor
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add ht' (hte.trans_lt hsmall))
    simpa only [add_halves] using htri
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add hp' (hpe.trans_lt hsmall))
    simpa only [add_halves] using htri

theorem uniform_order_empty_tests_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D) (z : ℝ),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → IsDeletionSet k D →
      i ∉ I → 0 < z → z ≤ 1 → |(((I.card + 1 : ℕ) : ℝ) / D.card) - z| ≤ δ →
      |AffinePermutationExposure.targetOrderMean D ∅ I ∅ i l -
        dTest (lineProfile D ∅ l.1) z| < ε ∧
      |planeOrderMean D ∅ I ∅ i l - planeTest (planeProfile D ∅) z| < ε := by
  obtain ⟨Nt, hNt, ht⟩ :=
    AffinePermutationExposure.uniform_deletion_order_target_approximation k (half_pos hε)
  obtain ⟨Np, hNp, hp⟩ := uniform_deletion_order_plane_approximation k (half_pos hε)
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (2 * (k : ℝ) + 4)
  refine ⟨max Nt Np, by omega, δ, hδ, ?_⟩
  intro F hField hFin hDec D I i l z hq hD hDel hi hz hz1 heD
  have hd := AffinePermutationExposure.remaining_count_le D I i hi
  have ht' := ht F D I i l (by omega) hDel hi
  have hp' := hp F D I i l (by omega) (by omega) hDel hi
  have hte := targetPowerMean_empty_error_to_dTest hDel l.1 l.2 (I.card + 1)
    hd hz hz1 hδ.le heD
  have hpe := planePowerMean_empty_error_to_planeTest hDel (I.card + 1)
    hd hz hz1 hδ.le heD
  constructor
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add ht' (hte.trans_lt hsmall))
    simpa only [add_halves] using htri
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add hp' (hpe.trans_lt hsmall))
    simpa only [add_halves] using htri

end
end Balanced.AffineProfileParameter

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_WithoutReplacementCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.WithoutReplacement

variable {α : Type*} [DecidableEq α]

theorem swap_mem_iff {U : Finset α} {x y z : α} (hx : x ∈ U) (hy : y ∈ U) :
    Equiv.swap x y z ∈ U ↔ z ∈ U := by
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  by_cases hzy : z = y
  · subst z
    simp [hx, hy]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem swapSet_mem_completions_iff {U S : Finset α} {x y : α} {r : ℕ}
    (hx : x ∈ U) (hy : y ∈ U) :
    swapSet x y S ∈ (U.erase y).powersetCard r ↔
      S ∈ (U.erase x).powersetCard r := by
  simp only [Finset.mem_powersetCard, card_swapSet]
  have hsub : swapSet x y S ⊆ U.erase y ↔ S ⊆ U.erase x := by
    constructor
    · intro h z hz
      have hm : Equiv.swap x y z ∈ swapSet x y S := by simpa using hz
      have hmem := Finset.mem_erase.mp (h hm)
      refine Finset.mem_erase.mpr ⟨?_, (swap_mem_iff hx hy).mp hmem.2⟩
      intro hzx
      subst z
      simpa using hmem.1
    · intro h z hz
      have hmem := Finset.mem_erase.mp (h ((mem_swapSet x y z S).mp hz))
      refine Finset.mem_erase.mpr ⟨?_, (swap_mem_iff hx hy).mp hmem.2⟩
      intro hzy
      subst z
      simpa using hmem.1
  rw [hsub]

theorem swapSet_eq_self_of_notMem {S : Finset α} {x y : α}
    (hx : x ∉ S) (hy : y ∉ S) : swapSet x y S = S := by
  ext z
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  by_cases hzy : z = y
  · subst z
    simp [hx, hy]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem swapSet_eq_self_of_mem {S : Finset α} {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) : swapSet x y S = S := by
  ext z
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  by_cases hzy : z = y
  · subst z
    simp [hx, hy]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem swapSet_eq_exchange {S : Finset α} {x y : α}
    (hx : x ∈ S) (hy : y ∉ S) : swapSet x y S = insert y (S.erase x) := by
  ext z
  by_cases hzx : z = x
  · subst z
    have hxy : x ≠ y := by intro h; subst y; exact hy hx
    simp [hy, hxy]
  by_cases hzy : z = y
  · subst z
    simp [hx]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy, hzx, hzy]

theorem swapSet_comm (x y : α) (S : Finset α) :
    swapSet x y S = swapSet y x S := by
  simp only [swapSet, Equiv.swap_comm]

theorem abs_sub_swapSet_le (U : Finset α) (f : Finset α → ℝ) {c : ℝ} {n : ℕ}
    (hc : 0 ≤ c)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = n →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c)
    {S : Finset α} (hSU : S ⊆ U) (hcard : S.card = n)
    {x y : α} (hxU : x ∈ U) (hyU : y ∈ U) :
    |f S - f (swapSet x y S)| ≤ c := by
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · rw [swapSet_eq_self_of_mem hx hy]
      simpa using hc
    · rw [swapSet_eq_exchange hx hy]
      exact hf S hSU hcard x hx y hyU hy
  · by_cases hy : y ∈ S
    · rw [swapSet_comm, swapSet_eq_exchange hy hx]
      exact hf S hSU hcard y hy x hxU hx
    · rw [swapSet_eq_self_of_notMem hx hy]
      simpa using hc

theorem completionAverage_eq_sum_div_choose (U : Finset α) (r : ℕ) (x : α)
    (f : Finset α → ℝ) :
    completionAverage U r x f =
      (∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) /
        (Nat.choose (U.erase x).card r : ℝ) := by
  simp only [completionAverage, Finset.expect_eq_sum_div_card, Finset.card_powersetCard]

theorem completionAverage_swap {U : Finset α} (r : ℕ) (f : Finset α → ℝ)
    {x y : α} (hx : x ∈ U) (hy : y ∈ U) :
    completionAverage U r y f =
      𝔼 S ∈ (U.erase x).powersetCard r, f (insert y (swapSet x y S)) := by
  symm
  apply Finset.expect_equiv (Equiv.swap x y).finsetCongr
  · intro S
    exact (swapSet_mem_completions_iff hx hy).symm
  · intro S _
    rfl

theorem completionAverage_oscillation (U : Finset α) (r : ℕ)
    (f : Finset α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hr : r < U.card)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = r + 1 →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c)
    {x y : α} (hx : x ∈ U) (hy : y ∈ U) :
    |completionAverage U r x f - completionAverage U r y f| ≤ c := by
  rw [completionAverage_swap r f hx hy]
  change |(𝔼 S ∈ (U.erase x).powersetCard r, f (insert x S)) -
    (𝔼 S ∈ (U.erase x).powersetCard r, f (insert y (swapSet x y S)))| ≤ c
  rw [← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le
  · apply Finset.powersetCard_nonempty.mpr
    rw [Finset.card_erase_of_mem hx]
    omega
  · intro S hS
    obtain ⟨hSU, hScard⟩ := Finset.mem_powersetCard.mp hS
    have hnot : x ∉ S := fun h => (Finset.mem_erase.mp (hSU h)).1 rfl
    have hsub : insert x S ⊆ U := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact (Finset.mem_erase.mp (hSU hz)).2
    have hcard : (insert x S).card = r + 1 := by simp [Finset.card_insert_of_notMem hnot, hScard]
    simpa using abs_sub_swapSet_le U f hc hf hsub hcard hx hy

theorem sum_completions_eq_sum_filter {U : Finset α} (r : ℕ)
    (f : Finset α → ℝ) {x : α} (hx : x ∈ U) :
    (∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) =
      ∑ T ∈ (U.powersetCard (r + 1)).filter (fun T => x ∈ T), f T := by
  apply Finset.sum_bij (fun S _ => insert x S)
  · intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    have hnot : x ∉ S := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset hx (hsub.trans (Finset.erase_subset _ _))
    · simp [hnot, hcard]
  · intro S hS T hT heq
    have hs : x ∉ S := by
      intro hxS
      exact (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hS).1 hxS)).1 rfl
    have ht : x ∉ T := by
      intro hxT
      exact (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hT).1 hxT)).1 rfl
    have := congrArg (fun W : Finset α => W.erase x) heq
    simpa [Finset.erase_insert hs, Finset.erase_insert ht] using this
  · intro T hT
    obtain ⟨hT, hxT⟩ := Finset.mem_filter.mp hT
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
    refine ⟨T.erase x, ?_, Finset.insert_erase hxT⟩
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨hne, hzT⟩ := Finset.mem_erase.mp hz
      exact Finset.mem_erase.mpr ⟨hne, hsub hzT⟩
    · simp [Finset.card_erase_of_mem hxT, hcard]
  · intro S _
    rfl

theorem sum_completions (U : Finset α) (r : ℕ) (f : Finset α → ℝ) :
    (∑ x ∈ U, ∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) =
      ((r : ℝ) + 1) * ∑ T ∈ U.powersetCard (r + 1), f T := by
  calc
    _ = ∑ x ∈ U, ∑ T ∈ U.powersetCard (r + 1), if x ∈ T then f T else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [sum_completions_eq_sum_filter r f hx, Finset.sum_filter]
    _ = ∑ T ∈ U.powersetCard (r + 1), ∑ x ∈ U, if x ∈ T then f T else 0 :=
      Finset.sum_comm
    _ = ∑ T ∈ U.powersetCard (r + 1), ((r : ℝ) + 1) * f T := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
      simp [hcard]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem average_completion_eq (U : Finset α) (r : ℕ) (f : Finset α → ℝ)
    (hr : r < U.card) :
    (𝔼 x ∈ U, completionAverage U r x f) =
      𝔼 T ∈ U.powersetCard (r + 1), f T := by
  have hUpos : 0 < U.card := lt_of_le_of_lt (Nat.zero_le r) hr
  have hn : U.card - 1 + 1 = U.card := Nat.sub_add_cancel hUpos
  have hbinom : (U.card : ℝ) * (Nat.choose (U.card - 1) r : ℝ) =
      (Nat.choose U.card (r + 1) : ℝ) * ((r : ℝ) + 1) := by
    have h := Nat.add_one_mul_choose_eq (U.card - 1) r
    rw [hn] at h
    exact_mod_cast h
  have hcardpos : (0 : ℝ) < U.card := by exact_mod_cast hUpos
  have hchoosepos : (0 : ℝ) < Nat.choose U.card (r + 1) := by
    exact_mod_cast Nat.choose_pos (by omega : r + 1 ≤ U.card)
  calc
    _ = (∑ x ∈ U, (∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) /
        (Nat.choose (U.card - 1) r : ℝ)) / (U.card : ℝ) := by
      rw [Finset.expect_eq_sum_div_card]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [completionAverage_eq_sum_div_choose, Finset.card_erase_of_mem hx]
    _ = (∑ x ∈ U, ∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) /
        ((Nat.choose (U.card - 1) r : ℝ) * (U.card : ℝ)) := by
      rw [← Finset.sum_div, div_div]
    _ = (((r : ℝ) + 1) * ∑ T ∈ U.powersetCard (r + 1), f T) /
        ((Nat.choose U.card (r + 1) : ℝ) * ((r : ℝ) + 1)) := by
      rw [sum_completions, mul_comm (Nat.choose (U.card - 1) r : ℝ), hbinom]
    _ = (∑ T ∈ U.powersetCard (r + 1), f T) /
        (Nat.choose U.card (r + 1) : ℝ) := by
      field_simp
    _ = _ := by rw [Finset.expect_eq_sum_div_card, Finset.card_powersetCard]

theorem completionAverage_increment (U : Finset α) (r : ℕ)
    (f : Finset α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hr : r < U.card)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = r + 1 →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c)
    {x : α} (hx : x ∈ U) :
    |completionAverage U r x f - (𝔼 T ∈ U.powersetCard (r + 1), f T)| ≤ c := by
  rw [← average_completion_eq U r f hr]
  have hU : U.Nonempty := ⟨x, hx⟩
  rw [← Finset.expect_const hU (completionAverage U r x f), ← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le hU
  intro y hy
  exact completionAverage_oscillation U r f hc hr hf hx hy

theorem expect_sq_sub_eq {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (f : β → ℝ) (a : ℝ) :
    (𝔼 x ∈ s, (f x - a)^2) =
      (𝔼 x ∈ s, (f x)^2) - 2 * a * (𝔼 x ∈ s, f x) + a^2 := by
  calc
    _ = 𝔼 x ∈ s, ((f x)^2 - (2 * a) * f x + a^2) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        ← Finset.mul_expect, Finset.expect_const hs]

theorem expect_sq_sub_mean_eq {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (f : β → ℝ) (a : ℝ) :
    (𝔼 x ∈ s, (f x - a)^2) =
      finiteVariance s f + ((𝔼 x ∈ s, f x) - a)^2 := by
  rw [expect_sq_sub_eq s hs f a, finiteVariance, expect_sq_sub_eq s hs f]
  ring

theorem finiteVariance_powersetCard_le (U : Finset α) (n : ℕ)
    (f : Finset α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hn : n ≤ U.card)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = n →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c) :
    finiteVariance (U.powersetCard n) f ≤ (n : ℝ) * c^2 := by
  induction n generalizing U f with
  | zero => simp [finiteVariance]
  | succ r ih =>
    have hr : r < U.card := by omega
    have hU : U.Nonempty := Finset.card_pos.mp (by omega)
    let M : ℝ := 𝔼 T ∈ U.powersetCard (r+1), f T
    have hparent : finiteVariance (U.powersetCard (r+1)) f =
        𝔼 x ∈ U, 𝔼 S ∈ (U.erase x).powersetCard r, (f (insert x S) - M)^2 := by
      simpa only [finiteVariance, completionAverage, M] using
        (average_completion_eq U r (fun T => (f T - M)^2) hr).symm
    rw [hparent]
    refine (Finset.expect_le hU (a := (r : ℝ) * c^2 + c^2) ?_).trans_eq (by push_cast; ring)
    intro x hx
    have hrx : r ≤ (U.erase x).card := by
      rw [Finset.card_erase_of_mem hx]
      omega
    have hs : ((U.erase x).powersetCard r).Nonempty :=
      Finset.powersetCard_nonempty.mpr hrx
    rw [expect_sq_sub_mean_eq _ hs]
    have hchild : finiteVariance ((U.erase x).powersetCard r)
        (fun S => f (insert x S)) ≤ (r : ℝ) * c^2 := by
      apply ih (U.erase x) (fun S => f (insert x S)) hrx
      intro S hSU hScard a ha b hb hbS
      have hxS : x ∉ S := fun h => (Finset.mem_erase.mp (hSU h)).1 rfl
      have hax : a ≠ x := (Finset.mem_erase.mp (hSU ha)).1
      have hbx : b ≠ x := (Finset.mem_erase.mp hb).1
      have hsub : insert x S ⊆ U :=
        Finset.insert_subset hx (hSU.trans (Finset.erase_subset _ _))
      have hcard : (insert x S).card = r+1 := by simp [hxS, hScard]
      have h := hf (insert x S) hsub hcard a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_erase.mp hb).2 (by simp [hbx, hbS])
      simpa only [Finset.erase_insert_of_ne hax.symm, Finset.insert_comm x b] using h
    have hinc := completionAverage_increment U r f hc hr hf hx
    have hsq := (sq_le_sq₀ (abs_nonneg _) hc).mpr hinc
    have hsq' : (completionAverage U r x f - M)^2 ≤ c^2 := by
      simpa only [sq_abs, M] using hsq
    change finiteVariance ((U.erase x).powersetCard r) (fun S => f (insert x S)) +
      (completionAverage U r x f - M)^2 ≤ (r : ℝ) * c^2 + c^2
    exact add_le_add hchild hsq'

end Balanced.WithoutReplacement

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteUniformVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Balanced.WithoutReplacement

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem integral_uniformOfFinset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∫ x, f x ∂(PMF.uniformOfFinset s hs).toMeasure = 𝔼 x ∈ s, f x := by
  classical
  rw [PMF.integral_eq_sum, Finset.expect_eq_sum_div_card]
  simp [PMF.uniformOfFinset_apply, apply_ite, ite_mul,
    div_eq_inv_mul, ← Finset.mul_sum]

theorem variance_uniformOfFinset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    variance f (PMF.uniformOfFinset s hs).toMeasure = finiteVariance s f := by
  rw [variance_eq_integral (measurable_of_countable f).aemeasurable,
    integral_uniformOfFinset, integral_uniformOfFinset]
  rfl

end Balanced.WithoutReplacement

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ProductSubsetVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.WithoutReplacement

theorem finiteVariance_product {α β : Type*} (s : Finset α) (t : Finset β)
    (ht : t.Nonempty) (f : α → β → ℝ) :
    finiteVariance (s ×ˢ t) (fun p => f p.1 p.2) =
      (𝔼 x ∈ s, finiteVariance t (f x)) +
        finiteVariance s (fun x => 𝔼 y ∈ t, f x y) := by
  unfold finiteVariance
  rw [Finset.expect_product]
  simp_rw [Finset.expect_product]
  calc
    _ = 𝔼 x ∈ s, ((𝔼 y ∈ t, (f x y - (𝔼 z ∈ t, f x z))^2) +
        ((𝔼 y ∈ t, f x y) - (𝔼 a ∈ s, 𝔼 b ∈ t, f a b))^2) := by
      apply Finset.expect_congr rfl
      intro x _
      exact expect_sq_sub_mean_eq t ht (f x) _
    _ = _ := by rw [Finset.expect_add_distrib]

theorem abs_expect_sub_expect_le {β : Type*} (t : Finset β) (ht : t.Nonempty)
    (f g : β → ℝ) {c : ℝ} (h : ∀ y ∈ t, |f y - g y| ≤ c) :
    |(𝔼 y ∈ t, f y) - (𝔼 y ∈ t, g y)| ≤ c := by
  rw [← Finset.expect_sub_distrib]
  exact (Finset.abs_expect_le _ _).trans (Finset.expect_le ht h)

theorem finiteVariance_powersetCard_product_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (m n : ℕ)
    (f : Finset α → Finset β → ℝ) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hm : m ≤ U.card) (hn : n ≤ V.card)
    (hfirst : ∀ S : Finset α, S ⊆ U → S.card = m →
      ∀ T : Finset β, T ⊆ V → T.card = n →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S →
        |f S T - f (insert b (S.erase a)) T| ≤ c)
    (hsecond : ∀ S : Finset α, S ⊆ U → S.card = m →
      ∀ T : Finset β, T ⊆ V → T.card = n →
      ∀ a ∈ T, ∀ b ∈ V, b ∉ T →
        |f S T - f S (insert b (T.erase a))| ≤ d) :
    finiteVariance (U.powersetCard m ×ˢ V.powersetCard n)
      (fun p => f p.1 p.2) ≤ (m : ℝ)*c^2 + (n : ℝ)*d^2 := by
  have hU := Finset.powersetCard_nonempty.mpr hm
  have hV := Finset.powersetCard_nonempty.mpr hn
  rw [finiteVariance_product _ _ hV]
  have hconditional : (𝔼 S ∈ U.powersetCard m,
      finiteVariance (V.powersetCard n) (f S)) ≤ (n : ℝ)*d^2 := by
    apply Finset.expect_le hU
    intro S hS
    obtain ⟨hSU, hScard⟩ := Finset.mem_powersetCard.mp hS
    exact finiteVariance_powersetCard_le V n (f S) hd hn (hsecond S hSU hScard)
  have hmeans : finiteVariance (U.powersetCard m)
      (fun S => 𝔼 T ∈ V.powersetCard n, f S T) ≤ (m : ℝ)*c^2 := by
    apply finiteVariance_powersetCard_le U m _ hc hm
    intro S hSU hScard a ha b hb hbS
    apply abs_expect_sub_expect_le _ hV
    intro T hT
    obtain ⟨hTV, hTcard⟩ := Finset.mem_powersetCard.mp hT
    exact hfirst S hSU hScard T hTV hTcard a ha b hb hbS
  exact (add_le_add hconditional hmeans).trans_eq (add_comm _ _)

end Balanced.WithoutReplacement

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UncoveredExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.UncoveredExchange

lemma missed_subset {Point Line : Type*} (A : Finset Point) (D : Finset Line)
    (On : Point → Line → Prop) [DecidableRel On] : missed A D On ⊆ A :=
  Finset.filter_subset _ _

lemma missed_insert {Point Line : Type*} [DecidableEq Line]
    (A : Finset Point) (D : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (l : Line) :
    missed A (insert l D) On = (missed A D On).filter (fun p => ¬ On p l) := by
  ext p
  simp [missed, and_left_comm, and_comm]

lemma abs_card_filter_not_sub_le {Point : Type*} (S : Finset Point)
    (P Q : Point → Prop) [DecidablePred P] [DecidablePred Q] :
    |((S.filter (fun p => ¬ P p)).card : ℝ) -
      ((S.filter (fun p => ¬ Q p)).card : ℝ)| ≤
      (S.filter P).card + (S.filter Q).card := by
  have hP : ((S.filter P).card : ℝ) + (S.filter (fun p => ¬ P p)).card = S.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) P)
  have hQ : ((S.filter Q).card : ℝ) + (S.filter (fun p => ¬ Q p)).card = S.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) Q)
  have hp : (0 : ℝ) ≤ (S.filter P).card := by positivity
  have hq : (0 : ℝ) ≤ (S.filter Q).card := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem missed_exchange_bound {Point Line : Type*} [DecidableEq Line]
    (A : Finset Point) (D : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (l m : Line) :
    |((missed A (insert l D) On).card : ℝ) -
      ((missed A (insert m D) On).card : ℝ)| ≤
      (A.filter (fun p => On p l)).card + (A.filter (fun p => On p m)).card := by
  rw [missed_insert, missed_insert]
  apply (abs_card_filter_not_sub_le (missed A D On) (fun p => On p l)
    (fun p => On p m)).trans
  have hl := Finset.card_le_card
    (Finset.filter_subset_filter (fun p => On p l) (missed_subset A D On))
  have hm := Finset.card_le_card
    (Finset.filter_subset_filter (fun p => On p m) (missed_subset A D On))
  exact_mod_cast Nat.add_le_add hl hm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem plane_exchange_bound (D : Finset (Line F)) (l m : Line F) :
    |((uncoveredBy (insert l D)).card : ℝ) -
      ((uncoveredBy (insert m D)).card : ℝ)| ≤ 2 * (Fintype.card F : ℝ) := by
  have h := missed_exchange_bound (Finset.univ : Finset (Point F)) D OnLine l m
  have hm (E : Finset (Line F)) : missed Finset.univ E OnLine = uncoveredBy E := by
    ext p
    simp [missed, uncoveredBy]
  rw [hm, hm] at h
  have hc (a : Line F) : ((Finset.univ : Finset (Point F)).filter
      (fun p => OnLine p a)).card = Fintype.card F := linePoints_card a
  simpa only [hc, two_mul] using h

lemma missed_line (D : Finset (Line F)) (T : Line F) :
    missed (linePoints T) D OnLine = linePoints T ∩ uncoveredBy D := by
  ext p
  simp [missed, uncoveredBy]

theorem target_exchange_bound (D : Finset (Line F)) (T l m : Line F)
    (hl : T ≠ l) (hm : T ≠ m) :
    |((linePoints T ∩ uncoveredBy (insert l D)).card : ℝ) -
      ((linePoints T ∩ uncoveredBy (insert m D)).card : ℝ)| ≤ 2 := by
  have h := missed_exchange_bound (linePoints T) D OnLine l m
  have heq (a : Line F) : (linePoints T).filter (fun p => OnLine p a) =
      linePoints T ∩ linePoints a := by
    ext p
    simp [linePoints]
  rw [missed_line, missed_line, heq l, heq m] at h
  have hlc : ((linePoints T ∩ linePoints l).card : ℝ) ≤ 1 := by
    exact_mod_cast linePoints_inter_card_le_one T l hl
  have hmc : ((linePoints T ∩ linePoints m).card : ℝ) ≤ 1 := by
    exact_mod_cast linePoints_inter_card_le_one T m hm
  linarith

theorem normalized_plane_exchange_bound (D : Finset (Line F)) (l m : Line F) :
    |((uncoveredBy (insert l D)).card : ℝ) / (Fintype.card F : ℝ)^2 -
      ((uncoveredBy (insert m D)).card : ℝ) / (Fintype.card F : ℝ)^2| ≤
      2 / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  rw [← sub_div, abs_div, abs_of_nonneg (sq_nonneg (Fintype.card F : ℝ))]
  calc
    _ ≤ (2 * (Fintype.card F : ℝ)) / (Fintype.card F : ℝ)^2 :=
      div_le_div_of_nonneg_right (plane_exchange_bound D l m) (sq_nonneg _)
    _ = 2 / (Fintype.card F : ℝ) := by field_simp

theorem normalized_target_exchange_bound (D : Finset (Line F)) (T l m : Line F)
    (hl : T ≠ l) (hm : T ≠ m) :
    |((linePoints T ∩ uncoveredBy (insert l D)).card : ℝ) / (Fintype.card F : ℝ) -
      ((linePoints T ∩ uncoveredBy (insert m D)).card : ℝ) / (Fintype.card F : ℝ)| ≤
      2 / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  rw [← sub_div, abs_div, abs_of_pos hq]
  exact div_le_div_of_nonneg_right (target_exchange_bound D T l m hl hm) hq.le

end Balanced.UncoveredExchange

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UncoveredSubsetVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Balanced.UncoveredSampling

open WithoutReplacement UncoveredExchange

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem planeFraction_exchange_left (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ S) (b : Line F) :
    |planeFraction S T - planeFraction (insert b (S.erase a)) T| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [planeFraction, ← Finset.insert_union, Finset.insert_erase ha] using
    normalized_plane_exchange_bound (S.erase a ∪ T) a b

theorem planeFraction_exchange_right (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ T) (b : Line F) :
    |planeFraction S T - planeFraction S (insert b (T.erase a))| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [planeFraction, ← Finset.union_insert, Finset.insert_erase ha] using
    normalized_plane_exchange_bound (S ∪ T.erase a) a b

theorem targetFraction_exchange_left (L : Line F) (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ S) (b : Line F) (hLa : L ≠ a) (hLb : L ≠ b) :
    |targetFraction L S T - targetFraction L (insert b (S.erase a)) T| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [targetFraction, ← Finset.insert_union, Finset.insert_erase ha] using
    normalized_target_exchange_bound (S.erase a ∪ T) L a b hLa hLb

theorem targetFraction_exchange_right (L : Line F) (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ T) (b : Line F) (hLa : L ≠ a) (hLb : L ≠ b) :
    |targetFraction L S T - targetFraction L S (insert b (T.erase a))| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [targetFraction, ← Finset.union_insert, Finset.insert_erase ha] using
    normalized_target_exchange_bound (S ∪ T.erase a) L a b hLa hLb

end Balanced.UncoveredSampling

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConditionalOrderVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.ConditionalOrderVariance

open WithoutReplacement PermutationSubsetLaw UncoveredSampling

theorem variance_two_images_conditioned_target
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (I : Finset α) (J : Finset β) (i x : α) (hi : i ∉ I)
    (g : Finset α → Finset β → ℝ) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm β)))
      (fun p => g (I.map p.1.toEmbedding) (J.map p.2.toEmbedding)) =
    finiteVariance ((Finset.univ.erase x).powersetCard I.card ×ˢ
      (Finset.univ : Finset β).powersetCard J.card) (fun p => g p.1 p.2) := by
  unfold finiteVariance
  simp_rw [Finset.expect_product]
  rw [expect_two_images_conditioned_target I J i x hi g]
  exact expect_two_images_conditioned_target I J i x hi
    (fun S T => (g S T - (𝔼 A ∈ (Finset.univ.erase x).powersetCard I.card,
      𝔼 B ∈ (Finset.univ : Finset β).powersetCard J.card, g A B))^2)

theorem conditioned_order_variance_le
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (I : Finset α) (J : Finset β) (i x : α) (hi : i ∉ I)
    (g : Finset α → Finset β → ℝ) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfirst : ∀ S : Finset α, S ⊆ Finset.univ.erase x → S.card = I.card →
      ∀ T : Finset β, T ⊆ Finset.univ → T.card = J.card →
      ∀ a ∈ S, ∀ b ∈ Finset.univ.erase x, b ∉ S →
        |g S T - g (insert b (S.erase a)) T| ≤ c)
    (hsecond : ∀ S : Finset α, S ⊆ Finset.univ.erase x → S.card = I.card →
      ∀ T : Finset β, T ⊆ Finset.univ → T.card = J.card →
      ∀ a ∈ T, ∀ b ∈ Finset.univ, b ∉ T →
        |g S T - g S (insert b (T.erase a))| ≤ d) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm β)))
      (fun p => g (I.map p.1.toEmbedding) (J.map p.2.toEmbedding)) ≤
        (I.card : ℝ) * c^2 + (J.card : ℝ) * d^2 := by
  rw [variance_two_images_conditioned_target I J i x hi]
  have hI : I ⊆ Finset.univ.erase i := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem ha hi, Finset.mem_univ _⟩
  have hm : I.card ≤ (Finset.univ.erase x).card := by
    simpa using Finset.card_le_card hI
  exact finiteVariance_powersetCard_product_le _ _ _ _ g hc hd hm
    (Finset.card_le_card (Finset.subset_univ J)) hfirst hsecond

section Affine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem mem_populationLines (U : Finset (Line F)) (S : Finset U) {a : U}
    (ha : a ∈ S) : a.val ∈ populationLines U S :=
  Finset.mem_map.mpr ⟨a, ha, rfl⟩

theorem plane_conditioned_order_variance_le
    (U V : Finset (Line F)) (I : Finset U) (J : Finset V)
    (i x : U) (hi : i ∉ I) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm V)))
      (fun p => planeFraction
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding))) ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  have hc : 0 ≤ 2 / (Fintype.card F : ℝ) := by positivity
  have h := conditioned_order_variance_le I J i x hi
    (fun S T => planeFraction (populationLines U S) (populationLines V T)) hc hc
    (by
      intro S _ _ T _ _ a ha b _ _
      simpa using planeFraction_exchange_left (populationLines U S)
        (populationLines V T) (mem_populationLines U S ha) b.val)
    (by
      intro S _ _ T _ _ a ha b _ _
      simpa using planeFraction_exchange_right (populationLines U S)
        (populationLines V T) (mem_populationLines V T ha) b.val)
  exact h.trans_eq (by ring)

theorem target_conditioned_order_variance_le
    (U V : Finset (Line F)) (hUV : Disjoint U V)
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm V)))
      (fun p => targetFraction x.val
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding))) ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  have hc : 0 ≤ 2 / (Fintype.card F : ℝ) := by positivity
  have hxV (a : V) : x.val ≠ a.val := by
    intro h
    exact Finset.disjoint_left.mp hUV x.property (h ▸ a.property)
  have h := conditioned_order_variance_le I J i x hi
    (fun S T => targetFraction x.val (populationLines U S) (populationLines V T)) hc hc
    (by
      intro S hS _ T _ _ a ha b hb _
      have hxa : x.val ≠ a.val := by
        intro h
        exact (Finset.mem_erase.mp (hS ha)).1 (Subtype.ext h.symm)
      have hxb : x.val ≠ b.val := by
        intro h
        exact (Finset.mem_erase.mp hb).1 (Subtype.ext h.symm)
      simpa using targetFraction_exchange_left x.val (populationLines U S)
        (populationLines V T) (mem_populationLines U S ha) b.val hxa hxb)
    (by
      intro S _ _ T _ _ a ha b _ _
      simpa using targetFraction_exchange_right x.val (populationLines U S)
        (populationLines V T) (mem_populationLines V T ha) b.val (hxV a) (hxV b))
  exact h.trans_eq (by ring)

theorem plane_conditioned_order_measure_variance_le
    (U V : Finset (Line F))
    [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    ProbabilityTheory.variance
      (fun p : OrderPair U V => planeFraction
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding)))
      (conditionedOrderLaw U V i x).toMeasure ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  erw [conditionedOrderLaw, variance_uniformOfFinset]
  exact plane_conditioned_order_variance_le U V I J i x hi

theorem target_conditioned_order_measure_variance_le
    (U V : Finset (Line F))
    [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]
    (hUV : Disjoint U V) (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    ProbabilityTheory.variance
      (fun p : OrderPair U V => targetFraction x.val
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding)))
      (conditionedOrderLaw U V i x).toMeasure ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  erw [conditionedOrderLaw, variance_uniformOfFinset]
  exact target_conditioned_order_variance_le U V hUV I J i x hi

end Affine

end Balanced.ConditionalOrderVariance

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ExposureInterleaving
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ExposureInterleaving

theorem grid_le_one {n : ℕ} (i : Fin n) : grid i ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  rw [grid, div_le_iff₀ hn, one_mul]
  exact_mod_cast Nat.succ_le_iff.mpr i.isLt

theorem countLE_eq_floor {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : countLE n x = ⌊(n : ℝ) * x⌋₊ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hnR.le hx
  have hf : ⌊(n : ℝ) * x⌋₊ ≤ n := Nat.floor_le_of_le (by nlinarith)
  have hmem (i : Fin n) : grid i ≤ x ↔ i.val < ⌊(n : ℝ) * x⌋₊ := by
    rw [grid, div_le_iff₀ hnR]
    have hc : (i.val + 1 : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by simp
    rw [hc, mul_comm x, ← Nat.le_floor_iff hnx]
    exact Nat.succ_le_iff
  unfold countLE
  rw [← Finset.card_range ⌊(n : ℝ) * x⌋₊]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr ((hmem i).mp (Finset.mem_filter.mp hi).2)
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    have hjf := Finset.mem_range.mp hj
    let i : Fin n := ⟨j, hjf.trans_le hf⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem i).mpr hjf⟩, rfl⟩

theorem countLT_eq_ceil_sub_one {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx1 : x ≤ 1) : countLT n x = ⌈(n : ℝ) * x⌉₊ - 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ⌈(n : ℝ) * x⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hmem (i : Fin n) : grid i < x ↔ i.val < ⌈(n : ℝ) * x⌉₊ - 1 := by
    rw [grid, div_lt_iff₀ hnR]
    have he : (i.val + 1 : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by simp
    rw [he, mul_comm x, ← Nat.lt_ceil]
    omega
  unfold countLT
  rw [← Finset.card_range (⌈(n : ℝ) * x⌉₊ - 1)]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr ((hmem i).mp (Finset.mem_filter.mp hi).2)
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    have hjc := Finset.mem_range.mp hj
    have hjn : j < n := by omega
    let i : Fin n := ⟨j, hjn⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem i).mpr hjc⟩, rfl⟩

theorem countLE_fraction_error {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |(countLE n x : ℝ) / n - x| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [countLE_eq_floor hn hx hx1, div_sub', abs_div,
    abs_of_pos hnR]
  · exact (div_le_div_iff_of_pos_right hnR).2 <|
      by simpa [mul_comm] using Nat.abs_floor_sub_le (mul_nonneg hnR.le hx)
  · exact hnR.ne'

theorem countLT_fraction_error {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    |(countLT n x : ℝ) / n - x| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 < (n : ℝ) * x := mul_pos hnR hx
  have hc : 1 ≤ ⌈(n : ℝ) * x⌉₊ := Nat.one_le_ceil_iff.mpr hnx
  have hlow := Nat.le_ceil ((n : ℝ) * x)
  have hupp : ((⌈(n : ℝ) * x⌉₊ - 1 : ℕ) : ℝ) < (n : ℝ) * x := by
    apply Nat.lt_ceil.mp
    omega
  rw [countLT_eq_ceil_sub_one hn hx1]
  apply abs_le.mpr
  constructor
  · have h : x - 1 / (n : ℝ) ≤ ((⌈(n : ℝ) * x⌉₊ - 1 : ℕ) : ℝ) / n := by
      apply (le_div_iff₀ hnR).2
      rw [sub_mul, div_mul_cancel₀ _ hnR.ne', Nat.cast_sub hc, Nat.cast_one]
      nlinarith
    linarith
  · have h : ((⌈(n : ℝ) * x⌉₊ - 1 : ℕ) : ℝ) / n - x ≤ 0 := by
      apply sub_nonpos.mpr
      exact (div_le_iff₀ hnR).2 (by nlinarith)
    exact h.trans (by positivity)

theorem coverGrid_pos {m : ℕ} (γ : ℝ) (i : Fin m) : 0 < coverGrid γ i :=
  Real.rpow_pos_of_pos (grid_pos i) _

theorem coverGrid_le_one {m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin m) :
    coverGrid γ i ≤ 1 :=
  Real.rpow_le_one (grid_pos i).le (grid_le_one i) (inv_nonneg.mpr hγ.le)

theorem coverGrid_rpow {m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin m) :
    coverGrid γ i ^ γ = grid i :=
  Real.rpow_inv_rpow (grid_pos i).le hγ.ne'

theorem remainingD_at_D {n m : ℕ} (γ : ℝ) (i : Fin n) :
    (remainingD γ (Sum.inl i : Step n m)).card = i.val + 1 := by
  classical
  have hs : remainingD γ (Sum.inl i : Step n m) =
      (Finset.range (i.val + 1)).attachFin (fun j hj =>
        (Finset.mem_range.mp hj).trans_le (Nat.succ_le_iff.mpr i.isLt)) := by
    ext j
    simp only [remainingD, Finset.mem_filter, Finset.mem_univ, true_and,
      Before, not_lt, Finset.mem_attachFin, Finset.mem_range]
    change j.val ≤ i.val ↔ j.val < i.val + 1
    omega
  rw [hs, Finset.card_attachFin, Finset.card_range]

theorem remainingC_at_C {n m : ℕ} (γ : ℝ) (j : Fin m) :
    (remainingC γ (Sum.inr j : Step n m)).card = j.val + 1 := by
  classical
  have hs : remainingC γ (Sum.inr j : Step n m) =
      (Finset.range (j.val + 1)).attachFin (fun i hi =>
        (Finset.mem_range.mp hi).trans_le (Nat.succ_le_iff.mpr j.isLt)) := by
    ext i
    simp only [remainingC, Finset.mem_filter, Finset.mem_univ, true_and,
      Before, not_lt, Finset.mem_attachFin, Finset.mem_range]
    change i.val ≤ j.val ↔ i.val < j.val + 1
    omega
  rw [hs, Finset.card_attachFin, Finset.card_range]

theorem remainingD_at_C {n m : ℕ} (γ : ℝ) (j : Fin m) :
    (remainingD γ (Sum.inr j : Step n m)).card = countLT n (coverGrid γ j) := by
  simp only [remainingD, Before, not_le, countLT]

theorem remainingC_at_D {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin n) :
    (remainingC γ (Sum.inl i : Step n m)).card = countLE m (grid i ^ γ) := by
  congr 1
  ext j
  simp only [remainingC, Before, not_lt, Finset.mem_filter,
    Finset.mem_univ, true_and, coverGrid]
  exact Real.rpow_inv_le_iff_of_pos (grid_pos j).le (grid_pos i).le hγ

theorem remainingD_fraction_error {n m : ℕ} (hn : 0 < n)
    {γ : ℝ} (hγ : 0 < γ) (s : Step n m) :
    |((remainingD γ s).card : ℝ) / n - parameter γ s| ≤ 1 / n := by
  cases s with
  | inl i =>
    rw [remainingD_at_D]
    simp only [parameter, grid, Nat.cast_add, Nat.cast_one, sub_self, abs_zero]
    positivity
  | inr j =>
    rw [remainingD_at_C]
    exact countLT_fraction_error hn (coverGrid_pos γ j) (coverGrid_le_one hγ j)

theorem remainingC_fraction_error {n m : ℕ} (hm : 0 < m)
    {γ : ℝ} (hγ : 0 < γ) (s : Step n m) :
    |((remainingC γ s).card : ℝ) / m - parameter γ s ^ γ| ≤ 1 / m := by
  cases s with
  | inl i =>
    rw [remainingC_at_D hγ]
    exact countLE_fraction_error hm (Real.rpow_nonneg (grid_pos i).le _)
      (Real.rpow_le_one (grid_pos i).le (grid_le_one i) hγ.le)
  | inr j =>
    rw [remainingC_at_C]
    change |((j.val + 1 : ℕ) : ℝ) / m - coverGrid γ j ^ γ| ≤ 1 / m
    rw [coverGrid_rpow hγ]
    simp only [grid, Nat.cast_add, Nat.cast_one, sub_self, abs_zero]
    positivity

theorem previousD_add_remainingD {n m : ℕ} (γ : ℝ) (s : Step n m) :
    (previousD γ s).card + (remainingD γ s).card = n := by
  simpa [previousD, remainingD] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => Before γ (Sum.inl i) s))

theorem previousC_add_remainingC {n m : ℕ} (γ : ℝ) (s : Step n m) :
    (previousC γ s).card + (remainingC γ s).card = m := by
  simpa [previousC, remainingC] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => Before γ (Sum.inr i) s))

theorem source_remaining_fraction_bounds {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : Step n m) :
    |((remainingD (Real.sqrt 2) s).card : ℝ) / n - parameter (Real.sqrt 2) s| ≤ 1 / n ∧
    |((remainingC (Real.sqrt 2) s).card : ℝ) / m -
      parameter (Real.sqrt 2) s ^ (Real.sqrt 2)| ≤ 1 / m := by
  have hγ : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact ⟨remainingD_fraction_error hn hγ s, remainingC_fraction_error hm hγ s⟩

end Balanced.ExposureInterleaving

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetectionConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Balanced.ProfileDetectionConcentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem measureReal_deviation_le [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {r : ℝ} (hr : 0 < r) :
    μ.real {ω | r ≤ |X ω - ∫ x, X x ∂μ|} ≤ variance X μ / r ^ 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (meas_ge_le_variance_div_sq hX hr)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg r))] at h
  exact h

omit [MeasurableSpace Ω] in

theorem small_gap_subset_deviations (X Y : Ω → ℝ) (a b ε : ℝ)
    (hgap : 2 * ε < |a - b|) :
    {ω | |X ω - Y ω| ≤ ε} ⊆
      {ω | ε / 2 ≤ |X ω - a|} ∪ {ω | ε / 2 ≤ |Y ω - b|} := by
  intro ω hω
  change ε / 2 ≤ |X ω - a| ∨ ε / 2 ≤ |Y ω - b|
  by_contra h
  push Not at h
  have h₁ := abs_sub_le a (X ω) b
  have h₂ := abs_sub_le (X ω) (Y ω) b
  rw [abs_sub_comm a (X ω)] at h₁
  change |X ω - Y ω| ≤ ε at hω
  linarith

theorem unmarked_probability_le_of_mean_gap [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : 2 * ε < |(∫ x, X x ∂μ) - ∫ x, Y x ∂μ|) :
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤
      4 * (variance X μ + variance Y μ) / ε ^ 2 := by
  have hr : 0 < ε / 2 := by positivity
  calc
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤
        μ.real ({ω | ε / 2 ≤ |X ω - ∫ x, X x ∂μ|} ∪
          {ω | ε / 2 ≤ |Y ω - ∫ x, Y x ∂μ|}) :=
      measureReal_mono (small_gap_subset_deviations X Y _ _ ε hgap)
    _ ≤ μ.real {ω | ε / 2 ≤ |X ω - ∫ x, X x ∂μ|} +
        μ.real {ω | ε / 2 ≤ |Y ω - ∫ x, Y x ∂μ|} := measureReal_union_le _ _
    _ ≤ variance X μ / (ε / 2) ^ 2 + variance Y μ / (ε / 2) ^ 2 :=
      add_le_add (measureReal_deviation_le hX hr) (measureReal_deviation_le hY hr)
    _ = 4 * (variance X μ + variance Y μ) / ε ^ 2 := by ring

theorem unmarked_probability_le_of_profile_gap [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {a b ε : ℝ} (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hXa : |(∫ x, X x ∂μ) - a| ≤ ε / 2)
    (hYb : |(∫ x, Y x ∂μ) - b| ≤ ε / 2) :
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤
      4 * (variance X μ + variance Y μ) / ε ^ 2 := by
  apply unmarked_probability_le_of_mean_gap hX hY hε
  have h₁ := abs_sub_le a (∫ x, X x ∂μ) b
  have h₂ := abs_sub_le (∫ x, X x ∂μ) (∫ x, Y x ∂μ) b
  rw [abs_sub_comm a (∫ x, X x ∂μ)] at h₁
  linarith

theorem marked_probability_eq [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (ε : ℝ) :
    μ.real {ω | ε < |X ω - Y ω|} =
      1 - μ.real {ω | |X ω - Y ω| ≤ ε} := by
  have hm : NullMeasurableSet {ω | |X ω - Y ω| ≤ ε} μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hX.aestronglyMeasurable.sub hY.aestronglyMeasurable).norm.nullMeasurableSet_le
        (aestronglyMeasurable_const (b := ε))
  have hc := measureReal_compl₀ hm
  simpa only [Set.compl_ofPred, not_le, probReal_univ] using hc

theorem marked_probability_ge_of_profile_gap [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {a b ε : ℝ} (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hXa : |(∫ x, X x ∂μ) - a| ≤ ε / 2)
    (hYb : |(∫ x, Y x ∂μ) - b| ≤ ε / 2) :
    1 - 4 * (variance X μ + variance Y μ) / ε ^ 2 ≤
      μ.real {ω | ε < |X ω - Y ω|} := by
  rw [marked_probability_eq hX hY]
  exact sub_le_sub_left (unmarked_probability_le_of_profile_gap hX hY hε hgap hXa hYb) 1

end Balanced.ProfileDetectionConcentration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarkedOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace Balanced.ProfileMarkedOrders

open ConditionalOrderVariance UncoveredSampling PermutationSubsetLaw

section FiniteLaws

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

theorem expect_pair_by_target (i : α)
    (f : Equiv.Perm α × Equiv.Perm β → ℝ) :
    (𝔼 p, f p) = 𝔼 x : α,
      𝔼 p ∈ (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm β)), f p := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  rw [expect_by_target i]
  apply Finset.expect_congr rfl
  intro x _
  exact (Finset.expect_product _ _ _).symm

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem real_uniform_event (s : Finset Ω) (hs : s.Nonempty) (E : Set Ω) :
    (PMF.uniformOfFinset s hs).toMeasure.real E =
      𝔼 p ∈ s, if p ∈ E then (1 : ℝ) else 0 := by
  classical
  rw [← integral_indicator_one (Set.to_countable E).measurableSet,
    WithoutReplacement.integral_uniformOfFinset]
  rfl

theorem memLp_finite (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (p : ℝ≥0∞) : MemLp f p μ := by
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun ω => ‖f ω‖)
  exact MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => hC ⟨ω, rfl⟩))

end FiniteLaws

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mean_firstMarkCount_eq_sum (U V : Finset (Line F))
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ) (η ε : ℝ) :
    (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) =
      ∑ i : U, 𝔼 p : OrderPair U V,
        if firstMark U V I J z η ε i p then (1 : ℝ) else 0 := by
  classical
  simp only [firstMarkCount, Finset.card_eq_sum_ones, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter]
  exact Finset.expect_sum_comm _ _ _

variable (U V : Finset (Line F))
  [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]

theorem mean_firstMark_eq_conditioned (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) (i : U) :
    (𝔼 p : OrderPair U V,
      if firstMark U V I J z η ε i p then (1 : ℝ) else 0) =
    if η < z i then
      𝔼 x : U, (conditionedOrderLaw U V i x).toMeasure.real
        (targetMarkEvent U V (I i) (J i) x ε)
    else 0 := by
  classical
  by_cases hz : η < z i
  · simp only [ite_eq_left hz]
    rw [expect_pair_by_target i]
    apply Finset.expect_congr rfl
    intro x _
    erw [conditionedOrderLaw, real_uniform_event]
    apply Finset.expect_congr rfl
    intro p hp
    have hx : p.1 i = x := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    simp only [firstMark, hz, true_and, targetMarkEvent, Set.mem_ofPred_eq, hx]
    rfl
  · simp [firstMark, hz]

theorem mean_firstMarkCount_eq_conditioned_sum
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ) (η ε : ℝ) :
    (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) =
      ∑ i : U, if η < z i then
        𝔼 x : U, (conditionedOrderLaw U V i x).toMeasure.real
          (targetMarkEvent U V (I i) (J i) x ε)
      else 0 := by
  rw [mean_firstMarkCount_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => mean_firstMark_eq_conditioned U V I J z η ε i)

omit [Field F] [Fintype F] in
theorem integral_conditioned_eq (i x : U) (f : OrderPair U V → ℝ) :
    (∫ p, f p ∂(conditionedOrderLaw U V i x).toMeasure) =
      conditionalMean U V i x f := by
  exact WithoutReplacement.integral_uniformOfFinset _ _ f

theorem detection_le_targetMark_add_error (hUV : Disjoint U V)
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I)
    (a b ε : ℝ) (hε : 0 < ε)
    (hXa : |conditionalMean U V i x (targetStatistic U V I J x) - a| ≤ ε / 2)
    (hYb : |conditionalMean U V i x (planeStatistic U V I J) - b| ≤ ε / 2) :
    (if 3 * ε < |a - b| then (1 : ℝ) else 0) ≤
      (conditionedOrderLaw U V i x).toMeasure.real (targetMarkEvent U V I J x ε) +
        32 * ((I.card : ℝ) + J.card) /
          ((Fintype.card F : ℝ)^2 * ε^2) := by
  let μ := (conditionedOrderLaw U V i x).toMeasure
  let X := targetStatistic U V I J x
  let Y := planeStatistic U V I J
  have hX : MemLp X 2 μ := memLp_finite μ X 2
  have hY : MemLp Y 2 μ := memLp_finite μ Y 2
  have hXt : |(∫ p, X p ∂μ) - a| ≤ ε / 2 := by
    simpa only [μ, X, integral_conditioned_eq] using hXa
  have hYt : |(∫ p, Y p ∂μ) - b| ≤ ε / 2 := by
    simpa only [μ, Y, integral_conditioned_eq] using hYb
  have hVX : variance X μ ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 :=
    target_conditioned_order_measure_variance_le U V hUV I J i x hi
  have hVY : variance Y μ ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 :=
    plane_conditioned_order_measure_variance_le U V I J i x hi
  have herr : 4 * (variance X μ + variance Y μ) / ε^2 ≤
      32 * ((I.card : ℝ) + J.card) / ((Fintype.card F : ℝ)^2 * ε^2) := by
    calc
      _ ≤ 4 * (4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 +
          4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2) / ε^2 := by
        gcongr
      _ = _ := by ring
  by_cases hgap : 3 * ε < |a - b|
  · simp only [ite_eq_left hgap]
    have hd := ProfileDetectionConcentration.marked_probability_ge_of_profile_gap
      hX hY hε hgap hXt hYt
    change 1 - 4 * (variance X μ + variance Y μ) / ε^2 ≤
      (conditionedOrderLaw U V i x).toMeasure.real (targetMarkEvent U V I J x ε) at hd
    linarith
  · simp only [ite_eq_right hgap]
    exact add_nonneg measureReal_nonneg (by positivity)

theorem detection_sum_le_mean_firstMarkCount_add_error (hUV : Disjoint U V)
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ)
    (hi : ∀ i, i ∉ I i) (a b : U → U → ℝ) (η ε : ℝ) (hε : 0 < ε)
    (hXa : ∀ i x, η < z i →
      |conditionalMean U V i x (targetStatistic U V (I i) (J i) x) - a i x| ≤ ε / 2)
    (hYb : ∀ i x, η < z i →
      |conditionalMean U V i x (planeStatistic U V (I i) (J i)) - b i x| ≤ ε / 2) :
    (∑ i : U, if η < z i then
      (𝔼 x : U, if 3 * ε < |a i x - b i x| then (1 : ℝ) else 0) else 0) ≤
      (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) +
        ∑ i : U, if η < z i then
          32 * (((I i).card : ℝ) + (J i).card) /
            ((Fintype.card F : ℝ)^2 * ε^2) else 0 := by
  rw [mean_firstMarkCount_eq_conditioned_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hz : η < z i
  · simp only [ite_eq_left hz]
    let : Nonempty U := ⟨i⟩
    have h := Finset.expect_le_expect (s := (Finset.univ : Finset U))
      (fun x _ => detection_le_targetMark_add_error U V hUV (I i) (J i) i x (hi i)
        (a i x) (b i x) ε hε (hXa i x hz) (hYb i x hz))
    simpa only [Finset.expect_add_distrib, Fintype.expect_const] using h
  · simp only [ite_eq_right hz, add_zero, le_refl]

omit [DecidableEq F] [MeasurableSpace (OrderPair U V)]
    [MeasurableSingletonClass (OrderPair U V)] in

theorem normalized_variance_error_le (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε C : ℝ) (hC : 0 ≤ C)
    (hsize : ∀ i, ((I i).card : ℝ) + (J i).card ≤ C * Fintype.card F) :
    (∑ i : U, if η < z i then
      32 * (((I i).card : ℝ) + (J i).card) /
        ((Fintype.card F : ℝ)^2 * ε^2) else 0) / Fintype.card F ≤
      32 * C * U.card / ((Fintype.card F : ℝ)^2 * ε^2) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ i : U, if η < z i then
      32 * (((I i).card : ℝ) + (J i).card) /
        ((Fintype.card F : ℝ)^2 * ε^2) else 0) ≤
      ∑ _i : U, 32 * (C * Fintype.card F) /
        ((Fintype.card F : ℝ)^2 * ε^2) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · gcongr
      exact hsize i
    · positivity
  calc
    _ ≤ (∑ _i : U, 32 * (C * Fintype.card F) /
        ((Fintype.card F : ℝ)^2 * ε^2)) / (Fintype.card F : ℝ) := by
      exact div_le_div_of_nonneg_right hsum hq.le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      field_simp

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in

theorem mean_markCount_eq_add (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ) (η ε : ℝ) :
    (𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η ε p : ℝ)) =
      (𝔼 p : OrderPair U V, (firstMarkCount U V ID JD zD η ε p : ℝ)) +
      (𝔼 p : OrderPair V U, (firstMarkCount V U IC JC zC η ε p : ℝ)) := by
  simp only [markCount, Nat.cast_add, Finset.expect_add_distrib]
  congr 1
  exact Fintype.expect_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)

end Balanced.ProfileMarkedOrders

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarkedError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Balanced.ProfileMarkedError

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem population_size_le (k : ℕ) (D C : Finset (Line F))
    (hp : IsProfilePair k D C) :
    (D.card : ℝ) + C.card ≤ (2 * (k : ℝ) + 1) * Fintype.card F := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hD : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast profile_deletionSet_card k D hp.1
  have hC : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hp.2.2
  rw [hD]
  nlinarith [mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hq)]

omit [Field F] [Fintype F] [DecidableEq F] in

theorem prefix_size_le (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) :
    (I.card : ℝ) + J.card ≤ (U.card : ℝ) + V.card := by
  have hI : I.card ≤ U.card := by simpa using Finset.card_le_univ I
  have hJ : J.card ≤ V.card := by simpa using Finset.card_le_univ J
  exact_mod_cast Nat.add_le_add hI hJ

theorem total_loss_div_le (k : ℕ) (D C : Finset (Line F))
    (hp : IsProfilePair k D C)
    (ID : D → Finset D) (JD : D → Finset C) (zD : D → ℝ)
    (IC : C → Finset C) (JC : C → Finset D) (zC : C → ℝ)
    (η ε : ℝ) :
    (loss D C ID JD zD η ε + loss C D IC JC zC η ε) / Fintype.card F ≤
      32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  let B : ℝ := 2 * (k : ℝ) + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsize := population_size_le k D C hp
  have hD := ProfileMarkedOrders.normalized_variance_error_le D C ID JD zD η ε B hB
    (fun i => (prefix_size_le D C (ID i) (JD i)).trans hsize)
  have hC := ProfileMarkedOrders.normalized_variance_error_le C D IC JC zC η ε B hB
    (fun i => (prefix_size_le C D (IC i) (JC i)).trans (by simpa [B, add_comm] using hsize))
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  calc
    _ ≤ 32 * B * D.card / ((Fintype.card F : ℝ)^2 * ε^2) +
        32 * B * C.card / ((Fintype.card F : ℝ)^2 * ε^2) := by
      rw [add_div]
      exact add_le_add hD hC
    _ = 32 * B * ((D.card : ℝ) + C.card) /
        ((Fintype.card F : ℝ)^2 * ε^2) := by ring
    _ ≤ 32 * B * (B * Fintype.card F) /
        ((Fintype.card F : ℝ)^2 * ε^2) := by
      gcongr
    _ = _ := by
      dsimp [B]
      field_simp

end Balanced.ProfileMarkedError

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileScheduledMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileScheduledMarks

open ExposureInterleaving ConditionalOrderVariance ProfileMarkedOrders

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in
theorem prefixD_complement (D C : Finset (Line F)) (s : Step D.card C.card) :
    Finset.univ \ prefixD D C s = unexposedD D C s := by
  ext i
  simp [prefixD, unexposedD, previousD, remainingD, Finset.mem_map_equiv]

omit [Field F] [Fintype F] in
theorem prefixC_complement (D C : Finset (Line F)) (s : Step D.card C.card) :
    Finset.univ \ prefixC D C s = unexposedC D C s := by
  ext j
  simp [prefixC, unexposedC, previousC, remainingC, Finset.mem_map_equiv]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prefixD_add_unexposedD (D C : Finset (Line F))
    (s : Step D.card C.card) :
    (prefixD D C s).card + (unexposedD D C s).card = D.card := by
  simpa [prefixD, unexposedD] using previousD_add_remainingD (Real.sqrt 2) s

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prefixC_add_unexposedC (D C : Finset (Line F))
    (s : Step D.card C.card) :
    (prefixC D C s).card + (unexposedC D C s).card = C.card := by
  simpa [prefixC, unexposedC] using previousC_add_remainingC (Real.sqrt 2) s

omit [Field F] [Fintype F] [DecidableEq F] in

theorem unexposed_fraction_bounds (D C : Finset (Line F))
    (hD : 0 < D.card) (hC : 0 < C.card) (s : Step D.card C.card) :
    |((unexposedD D C s).card : ℝ) / D.card - parameter (Real.sqrt 2) s| ≤
      1 / D.card ∧
    |((unexposedC D C s).card : ℝ) / C.card -
      parameter (Real.sqrt 2) s ^ (Real.sqrt 2)| ≤ 1 / C.card := by
  simpa [unexposedD, unexposedC] using source_remaining_fraction_bounds hD hC s

end Balanced.ProfileScheduledMarks

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileFiniteMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Balanced.ProfileFiniteMarks

open ConditionalOrderVariance ProfileMarkedOrders ProfileScheduledMarks
open ProfileDetectionBridge ProfileMarkedError

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem detectionSum_le_cutoffSum (U : Finset (Line F)) (z : U → ℝ)
    (a b : U → U → ℝ) (η ε : ℝ) :
    detectionSum U z a b η ε ≤ ∑ i : U, if η < z i then
      (𝔼 x : U, if 3 * ε < |a i x - b i x| then (1 : ℝ) else 0) else 0 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : η < z i
  · simp only [ite_eq_left hi]
    apply Finset.expect_le_expect
    intro x _
    split_ifs <;> simp_all
  · simp [hi]

theorem detectionSum_le_mean_add_loss (U V : Finset (Line F))
    (hUV : Disjoint U V) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (hi : ∀ i, i ∉ I i) (a b : U → U → ℝ)
    (η ε : ℝ) (hε : 0 < ε)
    (hXa : ∀ i x, η < z i →
      |conditionalMean U V i x (targetStatistic U V (I i) (J i) x) - a i x| ≤ ε / 2)
    (hYb : ∀ i x, η < z i →
      |conditionalMean U V i x (planeStatistic U V (I i) (J i)) - b i x| ≤ ε / 2) :
    detectionSum U z a b η ε ≤
      (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) +
        loss U V I J z η ε := by
  let : MeasurableSpace (OrderPair U V) := ⊤
  exact (detectionSum_le_cutoffSum U z a b η ε).trans
    (detection_sum_le_mean_firstMarkCount_add_error U V hUV I J z hi a b η ε hε hXa hYb)

theorem finiteDetection_le_normalizedMean_add_bound
    (k : ℕ) (D C : Finset (Line F)) (hp : IsProfilePair k D C)
    (η ε : ℝ) (hε : 0 < ε)
    (hDX : ∀ i x, η < zD D i →
      |conditionalMean D C i x (targetStatistic D C (ID D C i) (JD D C i) x) -
        dTest (lineProfile D C x) (zD D i)| ≤ ε / 2)
    (hDY : ∀ i x, η < zD D i →
      |conditionalMean D C i x (planeStatistic D C (ID D C i) (JD D C i)) -
        planeTest (planeProfile D C) (zD D i)| ≤ ε / 2)
    (hCX : ∀ i x, η < zC C i →
      |conditionalMean C D i x (targetStatistic C D (IC D C i) (JC D C i) x) -
        cTest (lineProfile D C x) (zC C i)| ≤ ε / 2)
    (hCY : ∀ i x, η < zC C i →
      |conditionalMean C D i x (planeStatistic C D (IC D C i) (JC D C i)) -
        planeTest (planeProfile D C) (zC C i)| ≤ ε / 2) :
    dFinite D C η ε + cFinite D C η ε ≤ normalizedMean D C η ε +
      32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  have hD := detectionSum_le_mean_add_loss D C hp.2.1
    (ID D C) (JD D C) (zD D) (current_not_ID D C)
    (fun i x => dTest (lineProfile D C x) (zD D i))
    (fun i _ => planeTest (planeProfile D C) (zD D i)) η ε hε hDX hDY
  have hC := detectionSum_le_mean_add_loss C D hp.2.1.symm
    (IC D C) (JC D C) (zC C) (current_not_IC D C)
    (fun i x => cTest (lineProfile D C x) (zC C i))
    (fun i _ => planeTest (planeProfile D C) (zC C i)) η ε hε hCX hCY
  have hsum := div_le_div_of_nonneg_right (add_le_add hD hC)
    (show (0 : ℝ) ≤ Fintype.card F by positivity)
  have he := total_loss_div_le k D C hp (ID D C) (JD D C) (zD D)
    (IC D C) (JC D C) (zC C) η ε
  have hmean := mean_markCount_eq_add D C (ID D C) (JD D C) (zD D)
    (IC D C) (JC D C) (zC C) η ε
  unfold dFinite cFinite normalizedMean sourceMarkCount
  rw [hmean]
  simp only [add_div] at hsum he ⊢
  linarith

end Balanced.ProfileFiniteMarks

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileOrderComplements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileOrderComplements

universe u

open ConditionalOrderVariance UncoveredSampling ProfileMarkedOrders

section Finite
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exposed_image_eq (I : Finset α) (i x : α) (hi : i ∉ I)
    (σ : Equiv.Perm α) (hx : σ i = x) :
    Finset.univ.erase x \ (future I i).map σ.toEmbedding = I.map σ.toEmbedding := by
  ext y
  have hix : σ.symm x = i := by rw [← hx]; simp
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_map_equiv, future]
  constructor
  · rintro ⟨hy, h⟩
    by_contra hyI
    apply h
    refine ⟨?_, hyI⟩
    intro hsi
    apply hy
    calc y = σ (σ.symm y) := (σ.apply_symm_apply y).symm
         _ = x := by rw [hsi, hx]
  · intro hyI
    refine ⟨?_, ?_⟩
    · intro hy
      rw [hy, hix] at hyI
      exact hi hyI
    · exact fun h => h.2 hyI

theorem exposed_image_eq_complement (J : Finset α) (τ : Equiv.Perm α) :
    Finset.univ \ (Finset.univ \ J).map τ.toEmbedding = J.map τ.toEmbedding := by
  ext y
  simp [Finset.mem_map_equiv]

theorem future_card_add_one (I : Finset α) (i : α) (hi : i ∉ I) :
    (future I i).card + 1 = Fintype.card α - I.card := by
  have hI : I ⊆ Finset.univ.erase i := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hx hi, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hI
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at hcard
  rw [future, Finset.card_sdiff_of_subset hI,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

end Finite

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem targetFraction_eq_filter (U V : Finset (Line F)) (x : U)
    (S : Finset U) (T : Finset V) :
    targetFraction x.1 (populationLines U S) (populationLines V T) =
      (((linePoints x.1).filter (fun p =>
        (∀ m ∈ S, ¬ OnLine p m.1) ∧ (∀ m ∈ T, ¬ OnLine p m.1))).card : ℝ) /
        Fintype.card F := by
  unfold targetFraction
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / Fintype.card F)
  ext p
  simp only [Finset.mem_inter, uncoveredBy, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.forall_mem_union, populationLines, Finset.forall_mem_map]
  rfl

theorem conditional_targetMean_eq_remaining (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    conditionalMean U V i x (targetStatistic U V I J x) =
      AffinePermutationExposure.targetOrderMean U V (future I i)
        (Finset.univ \ J) i x := by
  unfold conditionalMean AffinePermutationExposure.targetOrderMean
  rw [Finset.expect_product, Finset.expect_div]
  apply Finset.expect_congr rfl
  intro σ hσ
  rw [Finset.expect_div]
  apply Finset.expect_congr rfl
  intro τ _
  have hx : σ i = x := (Finset.mem_filter.mp hσ).2
  rw [exposed_image_eq I i x hi σ hx, exposed_image_eq_complement J τ]
  unfold targetStatistic
  rw [targetFraction_eq_filter]
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / Fintype.card F)
  ext p
  simp only [Finset.mem_filter]

end Balanced.ProfileOrderComplements

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileScheduledApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileScheduledApproximation

universe u
open ConditionalOrderVariance UncoveredSampling ProfileMarkedOrders
  ProfileOrderComplements ProfileScheduledMarks ExposureInterleaving
  AffinePlaneOrderExposure AffineProfileParameter ProfileDetectionBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem planeFraction_eq_filter (U V : Finset (Line F))
    (S : Finset U) (T : Finset V) :
    planeFraction (populationLines U S) (populationLines V T) =
      (((Finset.univ : Finset (Point F)).filter (fun p =>
        (∀ m ∈ S, ¬ OnLine p m.1) ∧ (∀ m ∈ T, ¬ OnLine p m.1))).card : ℝ) /
        (Fintype.card F : ℝ)^2 := by
  unfold planeFraction
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / (Fintype.card F : ℝ)^2)
  ext p
  simp only [uncoveredBy, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.forall_mem_union, populationLines, Finset.forall_mem_map]
  rfl

theorem conditional_planeMean_eq_remaining (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    conditionalMean U V i x (planeStatistic U V I J) =
      planeOrderMean U V (future I i) (Finset.univ \ J) i x := by
  unfold conditionalMean planeOrderMean
  rw [Finset.expect_product, Finset.expect_div]
  apply Finset.expect_congr rfl
  intro σ hσ
  rw [Finset.expect_div]
  apply Finset.expect_congr rfl
  intro τ _
  have hx : σ i = x := (Finset.mem_filter.mp hσ).2
  rw [exposed_image_eq I i x hi σ hx, exposed_image_eq_complement J τ]
  unfold planeStatistic
  rw [planeFraction_eq_filter]
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / (Fintype.card F : ℝ)^2)
  ext p
  simp only [Finset.mem_filter]

omit [Field F] [Fintype F] in
theorem remaining_D_counts (D C : Finset (Line F)) (i : D) :
    (future (ID D C i) i).card + 1 = (unexposedD D C (stepD D C i)).card ∧
    (Finset.univ \ JD D C i).card = (unexposedC D C (stepD D C i)).card := by
  constructor
  · rw [future_card_add_one _ _ (current_not_ID D C i), Fintype.card_coe]
    have h := prefixD_add_unexposedD D C (stepD D C i)
    dsimp only [ID]
    omega
  · exact congrArg Finset.card (prefixC_complement D C (stepD D C i))

omit [Field F] [Fintype F] in
theorem remaining_C_counts (D C : Finset (Line F)) (i : C) :
    (Finset.univ \ JC D C i).card = (unexposedD D C (stepC D C i)).card ∧
    (future (IC D C i) i).card + 1 = (unexposedC D C (stepC D C i)).card := by
  constructor
  · exact congrArg Finset.card (prefixD_complement D C (stepC D C i))
  · rw [future_card_add_one _ _ (current_not_IC D C i), Fintype.card_coe]
    have h := prefixC_add_unexposedC D C (stepC D C i)
    dsimp only [IC]
    omega

theorem uniform_scheduled_D_means (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (i x : D),
      N ≤ Fintype.card F → N ≤ D.card → N ≤ C.card → IsProfilePair k D C →
      |conditionalMean D C i x (targetStatistic D C (ID D C i) (JD D C i) x) -
        dTest (lineProfile D C x.1) (zD D i)| < ε ∧
      |conditionalMean D C i x (planeStatistic D C (ID D C i) (JD D C i)) -
        planeTest (planeProfile D C) (zD D i)| < ε := by
  obtain ⟨N₀, hN₀, δ, hδ, happ⟩ := uniform_order_d_tests_approximation k hε
  obtain ⟨N₁, hN₁⟩ := exists_reciprocal_cutoff hδ
  refine ⟨max N₀ N₁, by omega, ?_⟩
  intro F hField hFin hDec D C i x hq hD hC hp
  have hDpos : 0 < D.card := by omega
  have hCpos : 0 < C.card := by omega
  have hm := unexposed_fraction_bounds D C hDpos hCpos (stepD D C i)
  have hc := remaining_D_counts D C i
  have hdlt := hN₁ D.card (by omega)
  have hclt := hN₁ C.card (by omega)
  rw [conditional_targetMean_eq_remaining D C _ _ i x (current_not_ID D C i),
    conditional_planeMean_eq_remaining D C _ _ i x (current_not_ID D C i)]
  apply happ F D C _ _ i x (zD D i) (by omega) (by omega) (by omega) hp
    (current_not_future _ _) (grid_pos (label D i)) (grid_le_one (label D i))
  · rw [hc.1]
    exact hm.1.trans hdlt.le
  · rw [hc.2]
    exact hm.2.trans hclt.le

theorem uniform_scheduled_C_means (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (i x : C),
      N ≤ Fintype.card F → N ≤ D.card → N ≤ C.card → IsProfilePair k D C →
      |conditionalMean C D i x (targetStatistic C D (IC D C i) (JC D C i) x) -
        cTest (lineProfile D C x.1) (zC C i)| < ε ∧
      |conditionalMean C D i x (planeStatistic C D (IC D C i) (JC D C i)) -
        planeTest (planeProfile D C) (zC C i)| < ε := by
  obtain ⟨N₀, hN₀, δ, hδ, happ⟩ := uniform_order_c_tests_approximation k hε
  obtain ⟨N₁, hN₁⟩ := exists_reciprocal_cutoff hδ
  refine ⟨max N₀ N₁, by omega, ?_⟩
  intro F hField hFin hDec D C i x hq hD hC hp
  have hDpos : 0 < D.card := by omega
  have hCpos : 0 < C.card := by omega
  have hm := unexposed_fraction_bounds D C hDpos hCpos (stepC D C i)
  have hc := remaining_C_counts D C i
  have hdlt := hN₁ D.card (by omega)
  have hclt := hN₁ C.card (by omega)
  rw [conditional_targetMean_eq_remaining C D _ _ i x (current_not_IC D C i),
    conditional_planeMean_eq_remaining C D _ _ i x (current_not_IC D C i)]
  apply happ F D C _ _ i x (zC C i) (by omega) (by omega) (by omega) hp
    (current_not_future _ _) (coverGrid_pos _ (label C i))
    (coverGrid_le_one (Real.sqrt_pos.2 (by norm_num)) (label C i))
  · rw [hc.1]
    exact hm.1.trans hdlt.le
  · rw [hc.2]
    exact hm.2.trans hclt.le

omit [Field F] [Fintype F] in

theorem future_ID_fraction_exact (D C : Finset (Line F)) (i : D) :
    (((future (ID D C i) i).card + 1 : ℕ) : ℝ) / D.card = zD D i := by
  rw [(remaining_D_counts D C i).1]
  simp only [unexposedD, Finset.card_map, stepD, remainingD_at_D,
    zD, grid, Nat.cast_add, Nat.cast_one]

theorem uniform_scheduled_empty_means (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (i x : D),
      N ≤ Fintype.card F → N ≤ D.card → IsDeletionSet k D →
      |conditionalMean D ∅ i x (targetStatistic D ∅ (ID D ∅ i) (JD D ∅ i) x) -
        dTest (lineProfile D ∅ x.1) (zD D i)| < ε ∧
      |conditionalMean D ∅ i x (planeStatistic D ∅ (ID D ∅ i) (JD D ∅ i)) -
        planeTest (planeProfile D ∅) (zD D i)| < ε := by
  obtain ⟨N, hN, δ, hδ, happ⟩ := uniform_order_empty_tests_approximation k hε
  refine ⟨N, hN, ?_⟩
  intro F hField hFin hDec D i x hq hD hp
  rw [conditional_targetMean_eq_remaining D ∅ _ _ i x (current_not_ID D ∅ i),
    conditional_planeMean_eq_remaining D ∅ _ _ i x (current_not_ID D ∅ i)]
  have hJ : (Finset.univ \ JD D (∅ : Finset (Line F)) i) = ∅ := by
    exact Finset.eq_empty_of_forall_notMem (fun j => (Finset.notMem_empty j.1 j.2).elim)
  rw [hJ]
  apply happ F D _ i x (zD D i) hq hD hp (current_not_future _ _)
    (grid_pos (label D i)) (grid_le_one (label D i))
  rw [future_ID_fraction_exact, sub_self, abs_zero]
  exact hδ.le

end Balanced.ProfileScheduledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileFiniteScheduledLemmas
attribute [-instance] _root_.OAI.Balanced.ProfileClassMargin.instDecidableEqCarrier _root_.OAI.Balanced.ProfileClassMargin.instFieldCarrier _root_.OAI.Balanced.ProfileClassMargin.instFintypeCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Filter
open scoped Topology

namespace Balanced.ProfileScheduledFiniteComparison

universe u

open ProfileScheduledApproximation ProfileScheduledMarks ProfileFiniteMarks

theorem uniform_finiteDetection_le_normalizedMean_add_bound
    (k : ℕ) (η ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)),
      N ≤ Fintype.card F → N ≤ D.card → (C = ∅ ∨ N ≤ C.card) →
      IsProfilePair k D C →
      dFinite D C η ε + cFinite D C η ε ≤ normalizedMean D C η ε +
        32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  obtain ⟨ND, hND, hD⟩ := uniform_scheduled_D_means k (half_pos hε)
  obtain ⟨NC, hNC, hC⟩ := uniform_scheduled_C_means k (half_pos hε)
  obtain ⟨NE, hNE, hE⟩ := uniform_scheduled_empty_means k (half_pos hε)
  refine ⟨max (max ND NC) NE, by omega, ?_⟩
  intro F _ _ _ D C hq hd hc hp
  rcases hc with rfl | hc
  · apply finiteDetection_le_normalizedMean_add_bound k D ∅ hp η ε hε
    · intro i x _
      exact (hE F D i x (by omega) (by omega) hp.1).1.le
    · intro i x _
      exact (hE F D i x (by omega) (by omega) hp.1).2.le
    · intro i
      exact (Finset.notMem_empty i.val i.property).elim
    · intro i
      exact (Finset.notMem_empty i.val i.property).elim
  · apply finiteDetection_le_normalizedMean_add_bound k D C hp η ε hε
    · intro i x _
      exact (hD F D C i x (by omega) (by omega) (by omega) hp).1.le
    · intro i x _
      exact (hD F D C i x (by omega) (by omega) (by omega) hp).2.le
    · intro i x _
      exact (hC F D C i x (by omega) (by omega) (by omega) hp).1.le
    · intro i x _
      exact (hC F D C i x (by omega) (by omega) (by omega) hp).2.le

theorem eventually_finiteDetection_le_normalizedMean_add_bound
    {F : ℕ → Type u} [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)]
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 < a)
    (D C : ∀ t, Finset (Line (F t)))
    (hp : ∀ t, IsProfilePair k (D t) (C t))
    (hgap : ∀ t, (C t).card = 0 ∨
      a * (Fintype.card (F t) : ℝ) ≤ (C t).card)
    (hq : Tendsto (fun t => Fintype.card (F t)) atTop atTop)
    (η ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      dFinite (D t) (C t) η ε + cFinite (D t) (C t) η ε ≤
        normalizedMean (D t) (C t) η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F t) : ℝ) * ε^2) := by
  obtain ⟨N, _hN, hfinite⟩ :=
    uniform_finiteDetection_le_normalizedMean_add_bound k η ε hε
  have hqR : Tendsto (fun t => (Fintype.card (F t) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hlarge : ∀ᶠ t in atTop, (N : ℝ) ≤ a * (Fintype.card (F t) : ℝ) :=
    (hqR.const_mul_atTop ha).eventually_ge_atTop N
  filter_upwards [hq.eventually_ge_atTop N, hlarge] with t ht hta
  have hd : N ≤ (D t).card := by
    rw [profile_deletionSet_card k (D t) (hp t).1]
    have hm := Nat.mul_le_mul_right (Fintype.card (F t) + 1) hk
    simp only [Nat.one_mul] at hm
    exact ht.trans ((Nat.le_succ _).trans hm)
  have hc : C t = ∅ ∨ N ≤ (C t).card := by
    rcases hgap t with hz | hbig
    · exact Or.inl (Finset.card_eq_zero.mp hz)
    · exact Or.inr (by exact_mod_cast hta.trans hbig)
  exact hfinite (F t) (D t) (C t) ht hd hc (hp t)

theorem eventually_finiteDetection_of_profileClass_oai
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    {F : ℕ → Type u} [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)]
    (D C : ∀ t, Finset (Line (F t)))
    (hA : ∀ t, A (F t) (D t) (C t))
    (hq : Tendsto (fun t => Fintype.card (F t)) atTop atTop)
    (η ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      dFinite (D t) (C t) η ε + cFinite (D t) (C t) η ε ≤
        normalizedMean (D t) (C t) η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F t) : ℝ) * ε^2) := by
  obtain ⟨a, ha, hsize⟩ := hgap
  exact eventually_finiteDetection_le_normalizedMean_add_bound k hk a ha D C
    (fun t => hvalid (F t) (D t) (C t) (hA t))
    (fun t => hsize (F t) (D t) (C t) (hA t)) hq η ε hε

end Balanced.ProfileScheduledFiniteComparison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass_oai.{u} := @OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass_oai.{u}
