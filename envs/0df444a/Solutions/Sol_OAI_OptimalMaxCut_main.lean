-- Prove2me | solution 1 for OAI.OptimalMaxCut.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:11:02.291032+00:00
-- url     : https://prove2.me/submissions/5ede8338-0e68-4911-892e-322b08e62fd5

import Mathlib
import Definitions.Def_OptimalMaxCut
import Definitions.Def_OAIQ087A032
import Theorems.Thm_OAI_MaxCutGames_theorem11
import Theorems.Thm_OAI_OptimalMaxCut_LongCode_Game_exists_weighted_soundness
import Theorems.Thm_OAI_OptimalMaxCut_LongCode_InstanceAdapter_exists_encoded_gridComputer

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitCube
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman
open scoped BigOperators
open Set Finset

 theorem corrAverage_mul_const (t c : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y * c) = corrAverage t n F * c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverage, ← mul_assoc, ← Finset.sum_mul, ih]

 theorem corrAverage_const_mul (t c : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => c * F x y) = c * corrAverage t n F := by
  simpa only [mul_comm] using corrAverage_mul_const t c n F

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Degree
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace OptimalMaxCut

lemma borellCurve_le (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : borellCurve t ≤ t := by
  have h := Real.mul_le_sin (Real.arcsin_nonneg.mpr ht) (Real.arcsin_le_pi_div_two t)
  rwa [Real.sin_arcsin (by linarith) ht1] at h

lemma gwRatio_nonneg {ρ : ℝ} (hρ : ρ < 1) : 0 ≤ gwRatio ρ := by
  unfold gwRatio
  exact div_nonneg (mul_nonneg (by norm_num) (Real.arccos_nonneg _))
    (mul_nonneg Real.pi_pos.le (sub_pos.mpr hρ).le)

lemma gwRatio_neg_identity (t : ℝ) :
    gwRatio (-t) = (1 + borellCurve t) / (1 + t) := by
  unfold gwRatio borellCurve
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arcsin_neg]
  field_simp
  ring

lemma gwRatio_ge_one_of_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    1 ≤ gwRatio ρ := by
  have hb := borellCurve_le ρ hρ hρ1.le
  unfold borellCurve at hb
  have hb' : 2 * Real.arcsin ρ ≤ Real.pi * ρ := by
    have hmul := (mul_le_mul_of_nonneg_right hb Real.pi_pos.le)
    field_simp at hmul
    nlinarith
  unfold gwRatio
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  apply (le_div_iff₀ (mul_pos Real.pi_pos (sub_pos.mpr hρ1))).mpr
  nlinarith

lemma borellCurve_half : borellCurve (1 / 2) = 1 / 3 := by
  have ha : Real.arcsin (1 / 2) = Real.pi / 6 :=
    Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩
  unfold borellCurve
  rw [ha]
  field_simp
  ring

lemma gwRatio_neg_half : gwRatio (-(1 / 2)) = 8 / 9 := by
  rw [gwRatio_neg_identity, borellCurve_half]
  norm_num

theorem alphaGW_attained :
    ∃ ρ : ℝ, -1 < ρ ∧ ρ < 0 ∧ alphaGW = gwRatio ρ ∧
      ∀ x : ℝ, -1 ≤ x → x < 1 → gwRatio ρ ≤ gwRatio x := by
  have hc : ContinuousOn gwRatio (Set.Icc (-1 : ℝ) 0) := by
    unfold gwRatio
    apply (continuous_const.mul Real.continuous_arccos).continuousOn.div
      (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
    intro x hx
    apply ne_of_gt
    change 0 < Real.pi * (1 - x)
    exact mul_pos Real.pi_pos (by linarith [hx.2])
  obtain ⟨ρ, hρ, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) hc
  have hless : gwRatio ρ < 1 := by
    have hx := hmin (show (-(1 / 2) : ℝ) ∈ Set.Icc (-1 : ℝ) 0 by constructor <;> norm_num)
    change gwRatio ρ ≤ gwRatio (-(1 / 2)) at hx
    rw [gwRatio_neg_half] at hx
    linarith
  have hleft : -1 < ρ := lt_of_le_of_ne hρ.1 (by
    intro heq
    have : ρ = -1 := heq.symm
    subst ρ
    simp at hless)
  have hright : ρ < 0 := lt_of_le_of_ne hρ.2 (by
    intro heq
    subst ρ
    simp at hless)
  have hglobal : ∀ x : ℝ, -1 ≤ x → x < 1 → gwRatio ρ ≤ gwRatio x := by
    intro x hx hx1
    by_cases hx0 : x ≤ 0
    · exact hmin ⟨hx, hx0⟩
    · exact hless.le.trans (gwRatio_ge_one_of_nonneg (by linarith) hx1)
  have hne : ((fun x : ℝ => gwRatio x) '' Set.Ico (-1 : ℝ) 1).Nonempty :=
    ⟨gwRatio 0, 0, by norm_num, rfl⟩
  have hbd : BddBelow ((fun x : ℝ => gwRatio x) '' Set.Ico (-1 : ℝ) 1) := by
    refine ⟨0, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact gwRatio_nonneg hx.2
  refine ⟨ρ, hleft, hright, le_antisymm ?_ ?_, hglobal⟩
  · exact csInf_le hbd ⟨ρ, ⟨hleft.le, by linarith⟩, rfl⟩
  · apply le_csInf hne
    rintro z ⟨x, hx, rfl⟩
    exact hglobal x hx.1 hx.2

/-- Positivity of the exact attained GW constant. -/
theorem alphaGW_pos : 0 < alphaGW := by
  obtain ⟨ρ, hρ, hρ0, heq, _⟩ := alphaGW_attained
  rw [heq]
  unfold gwRatio
  exact div_pos (mul_pos (by norm_num) (Real.arccos_pos.mpr (by linarith)))
    (mul_pos Real.pi_pos (by linarith))

theorem exists_rational_test_correlation (α : ℝ) (hα : alphaGW < α) :
    ∃ t : ℚ, 0 < t ∧ t < 1 ∧
      (1 + borellCurve t) / 2 < α * ((1 + (t : ℝ)) / 2) := by
  obtain ⟨ρ, hρ, hρ0, heq, _⟩ := alphaGW_attained
  have hid := gwRatio_neg_identity (-ρ)
  simp only [neg_neg] at hid
  have hratio : (1 + borellCurve (-ρ)) / (1 + -ρ) < α := by
    rw [← hid, ← heq]
    exact hα
  have hgap : (1 + borellCurve (-ρ)) / 2 < α * ((1 + -ρ) / 2) := by
    have hm := (div_lt_iff₀ (show 0 < 1 + -ρ by linarith)).mp hratio
    linarith
  let S : Set ℝ := Set.Ioo 0 1 ∩
    {t | (1 + borellCurve t) / 2 < α * ((1 + t) / 2)}
  have hopen : IsOpen S := by
    apply isOpen_Ioo.inter
    apply isOpen_lt
    · unfold borellCurve
      fun_prop
    · fun_prop
  have hne : S.Nonempty := ⟨-ρ, ⟨by linarith, by linarith⟩, hgap⟩
  obtain ⟨t, ht⟩ := Rat.denseRange_cast.exists_mem_open hopen hne
  refine ⟨t, ?_, ?_, ht.2⟩
  · exact_mod_cast ht.1.1
  · exact_mod_cast ht.1.2

/-- Final numerical parameter selection in the proof of `thm:main`.
The eps below is used independently for the weighted gap and the unweighting
error. The YES threshold is rational exactly, and the NO threshold is chosen
strictly above the analytic upper bound and below alpha times the YES bound.
This is NOT a hardness theorem or an assumed reduction. -/
theorem exists_main_gap_parameters (α : ℝ) (hα : alphaGW < α) (hα1 : α ≤ 1) :
    ∃ t ε y n : ℚ, 0 < t ∧ t < 1 ∧ 0 < ε ∧
      (ε : ℝ) < ((t : ℝ) - borellCurve t) / 4 ∧
      y = (1 + t) / 2 - 2 * ε ∧ 0 < y ∧ 0 ≤ n ∧
      (1 + borellCurve t) / 2 + 2 * ε < (n : ℝ) ∧
      (n : ℝ) < α * (y : ℝ) := by
  obtain ⟨t, ht, ht1, hgap⟩ := exists_rational_test_correlation α hα
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hαpos : 0 < α := lt_trans alphaGW_pos hα
  have hb : 0 ≤ borellCurve t := by
    unfold borellCurve
    exact mul_nonneg (by positivity) (Real.arcsin_nonneg.mpr htR.le)
  have htb : borellCurve t < (t : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hα1 (show 0 ≤ (1 + (t : ℝ)) / 2 by positivity)
    linarith
  let d : ℝ := α * ((1 + (t : ℝ)) / 2) - (1 + borellCurve t) / 2
  have hd : 0 < d := sub_pos.mpr hgap
  obtain ⟨ε, hε0, hε⟩ := exists_rat_btwn
    (show (0 : ℝ) < min (((t : ℝ) - borellCurve t) / 4) (d / 4) by
      exact lt_min (by linarith) (by positivity))
  have hεr : 0 < ε := by exact_mod_cast hε0
  have hεb : (ε : ℝ) < ((t : ℝ) - borellCurve t) / 4 := lt_of_lt_of_le hε (min_le_left _ _)
  have hεd : (ε : ℝ) < d / 4 := lt_of_lt_of_le hε (min_le_right _ _)
  let y : ℚ := (1 + t) / 2 - 2 * ε
  have hy : (y : ℝ) = (1 + (t : ℝ)) / 2 - 2 * ε := by
    simp [y]
  have hstrict : (1 + borellCurve t) / 2 + 2 * ε < α * (y : ℝ) := by
    rw [hy]
    dsimp [d] at hεd
    nlinarith
  have hypos : 0 < y := by
    have : 0 < (y : ℝ) := by
      have hprod : 0 < α * (y : ℝ) := by linarith
      exact (mul_pos_iff.mp hprod).elim (fun h => h.2) (fun h => False.elim ((not_lt.mpr hαpos.le) h.1))
    exact_mod_cast this
  obtain ⟨n, hnlo, hnhi⟩ := exists_rat_btwn hstrict
  have hn : 0 ≤ n := by
    have : 0 ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  exact ⟨t, ε, y, n, ht, ht1, hεr, hεb, rfl, hypos, hn, hnlo, hnhi⟩

end OptimalMaxCut

end -- noncomputable Walsh/analytic section

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Gadgets_Polynomial
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.BooleanFourthMoment
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad

 theorem walsh_cons {n : ℕ} (s x : Cube (Fin n)) (a b : Bool) :
    walsh (Fin.cons a s) (Fin.cons b x) = (if a then bitSign b else 1) * walsh s x := by
  cases a <;> simp [walsh, Fin.prod_univ_succ, bitSign]

end OptimalMaxCut.BooleanFourthMoment

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Clip
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.MISProof
open scoped BigOperators
open Finset Set MaxCutGames.Foundations.Hastad Analytic BooleanFourthMoment GaussianBellman

 theorem degree_cons {n : ℕ} (a : Bool) (s : Cube (Fin n)) :
    degree (Fin.cons a s) = degree s + if a then 1 else 0 := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  cases a <;> simp [Nat.add_comm]

 theorem corrAverage_walsh (t : ℝ) (n : ℕ) (s r : Cube (Fin n)) :
    corrAverage t n (fun x y => walsh s x * walsh r y) =
      if s = r then t ^ degree s else 0 := by
  induction n with
  | zero => simp [corrAverage, walsh, degree, Subsingleton.elim s r]
  | succ n ih =>
    obtain ⟨⟨a, s⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective s
    obtain ⟨⟨b, r⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective r
    change corrAverage t (n + 1) (fun x y => walsh (Fin.cons a s) x * walsh (Fin.cons b r) y) =
      if (Fin.cons a s : Cube (Fin (n + 1))) = Fin.cons b r then t ^ degree (Fin.cons a s) else 0
    have hp (x y : Cube (Fin n)) :
        (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f *
          (walsh (Fin.cons a s) (Fin.cons e x) * walsh (Fin.cons b r) (Fin.cons f y))) =
        (if a = b then (if a then t else 1) else 0) * (walsh s x * walsh r y) := by
      cases a <;> cases b <;>
        simp only [Fintype.sum_bool, bitPairWeight, sign, walsh_cons, bitSign,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
    simp only [corrAverage, hp, corrAverage_const_mul, ih, Fin.cons_inj, degree_cons]
    cases a <;> cases b <;> by_cases h : s = r <;> simp [h, pow_succ, mul_comm]

end OptimalMaxCut.MISProof

namespace OptimalMaxCut.LongCode

open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

theorem weight_nonneg (p : Law I) (i : I) : 0 ≤ (p.weight i : ℝ) := by
  exact_mod_cast p.nonneg i

theorem total_real (p : Law I) : ∑ i, (p.weight i : ℝ) = 1 := by
  exact_mod_cast p.total

@[simp] theorem avg_const (p : Law I) (a : ℝ) : p.avg (fun _ => a) = a := by
  simp [avg, ← sum_mul, total_real]

theorem avg_mono (p : Law I) {f g : I → ℝ} (h : ∀ i, f i ≤ g i) : p.avg f ≤ p.avg g :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (p.weight_nonneg i)

end Law

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Graphs_TestCut
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem corrAverage_sub (t : ℝ) (n : ℕ) (F G : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y - G x y) = corrAverage t n F - corrAverage t n G := by
  have he (x y : BitCube n) : F x y - G x y = F x y + G x y * (-1) := by ring
  simp_rw [he, corrAverage_add, corrAverage_mul_const]
  ring

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitPairWeightQ
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem jointLaw_average (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1) (n : ℕ)
    (F : Cube (Fin n) → Cube (Fin n) → ℝ) :
    (jointLaw t ht n).avg (fun p => F p.1 p.2) = corrAverage t n F := by
  unfold Law.avg jointLaw
  simp only [corrAverageQ_cast, apply_ite Rat.cast, Rat.cast_one, Rat.cast_zero]
  calc
    _ = ∑ p : Cube (Fin n) × Cube (Fin n), corrAverage t n (fun x y =>
        (if (x, y) = p then (1 : ℝ) else 0) * F p.1 p.2) := by
      simp only [corrAverage_mul_const]
    _ = corrAverage t n (fun x y => ∑ p : Cube (Fin n) × Cube (Fin n),
        (if (x, y) = p then (1 : ℝ) else 0) * F p.1 p.2) := (corrAverage_sum _ _ _ _).symm
    _ = _ := by simp

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

 theorem bind_average (p : Law I) (q : I → Law J) (F : I × J → ℝ) :
    (p.bind q).avg F = p.avg (fun i => (q i).avg (fun j => F (i,j))) := by
  simp only [avg, bind, Rat.cast_mul, Fintype.sum_prod_type, mul_sum, mul_assoc]

 theorem corrAverage_avg (p : Law I) (t : ℝ) (n : ℕ)
    (F : I → Cube (Fin n) → Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => p.avg (fun i => F i x y)) = p.avg (fun i => corrAverage t n (F i)) := by
  simp only [avg, corrAverage_sum, corrAverage_const_mul]

end Law

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

 theorem testCut_expanded (G : Game X Y E q) (t : ℝ) (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
      (G.edgeLaw y).avg (fun e' => corrAverage t q (fun z z' =>
        (1 - f (G.source e) (cubePerm (G.permutation e) z) *
          f (G.source e') (cubePerm (G.permutation e') (antipode z'))) / 2)))) := by
  have hp : ∀ y z z', G.averageCode f y z * G.averageCode f y (antipode z') =
      (G.edgeLaw y).avg (fun e => (G.edgeLaw y).avg (fun e' =>
      f (G.source e) (cubePerm (G.permutation e) z) *
        f (G.source e') (cubePerm (G.permutation e') (antipode z')))) := by
    intro y z z'
    simp only [averageCode, reindex, Law.avg_mul, Law.avg_smul]
  unfold testCut
  simp_rw [hp, Law.corrAverage_avg]
  simp_rw [div_eq_mul_inv, corrAverage_mul_const, corrAverage_sub,
    corrAverage_fst, Fintype.expect_const, Law.avg_mul, Law.avg_sub, Law.avg_const]

/-- The analytic test value is exactly the expectation over explicit rational
atoms. This identity will be used to aggregate a genuine finite graph. -/
 theorem testCut_sampleLaw (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = (G.sampleLaw t ht).avg (fun a =>
      (1 - f (G.queries a).1.1 (G.queries a).1.2 *
        f (G.queries a).2.1 (G.queries a).2.2) / 2) := by
  rw [testCut_expanded]
  simp only [sampleLaw, Law.bind_average, queries]
  congr 1; funext y
  congr 1; funext e
  congr 1; funext e'
  exact (jointLaw_average t ht q _).symm

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Vec
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace OptimalMaxCut.Unweighted

open Finset
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

theorem dotChar_ne_one (h : ZMod p) (hh : h ≠ 0) (x : Vec p) (hx : x ≠ 0) :
    dotChar h x ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! hn
    exact hx (funext hn)
  apply AddChar.ne_one_iff.mpr
  refine ⟨Pi.single i 1, ?_⟩
  change ZMod.stdAddChar (h * dot x (Pi.single i 1)) ≠ 1
  have hd : dot x (Pi.single i 1) = x i := by simp [dot, Pi.single_apply]
  rw [hd, ← (ZMod.stdAddChar (N := p)).map_zero_eq_one]
  exact fun he => (mul_ne_zero hh hi) (ZMod.injective_stdAddChar he)

theorem sum_dotChar (h : ZMod p) (hh : h ≠ 0) (x : Vec p) :
    ∑ y : Vec p, ZMod.stdAddChar (h * dot x y) =
      if x = 0 then (p : ℂ) ^ 6 else 0 := by
  split_ifs with hx
  · subst x
    simp [dot]
  · exact AddChar.sum_eq_zero_of_ne_one (dotChar_ne_one h hh x hx)

theorem orthogonality (h : ZMod p) (hh : h ≠ 0) (x z : Vec p) :
    ∑ y : Vec p, ZMod.stdAddChar (h * dot x y) *
      conj (ZMod.stdAddChar (h * dot z y)) =
      if x = z then (p : ℂ) ^ 6 else 0 := by
  simp_rw [conj_stdChar, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg,
    ← mul_sub, ← dot_sub_left]
  rw [sum_dotChar h hh]
  simp only [sub_eq_zero]

theorem rectangle_energy (h : ZMod p) (hh : h ≠ 0) (T : Finset (Vec p)) :
    ∑ x : Vec p, ‖∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ^ 2 =
      (p : ℝ) ^ 6 * T.card := by
  have he : (∑ x : Vec p, (‖∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ^ 2 : ℝ) : ℂ) =
      (p : ℂ) ^ 6 * T.card := by
    push_cast
    simp_rw [← Complex.mul_conj', map_sum, sum_mul, mul_sum]
    rw [sum_comm]
    apply Eq.trans (sum_congr rfl (fun y hy => sum_comm ..))
    simp_rw [dot_comm (_ : Vec p), orthogonality h hh]
    simp [mul_comm]
  exact_mod_cast he

theorem rectangle_character_bound (h : ZMod p) (hh : h ≠ 0)
    (S T : Finset (Vec p)) :
    ‖∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ≤ (p : ℝ) ^ 9 := by
  let f (x : Vec p) := ‖∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖
  have htriangle : ‖∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ≤ ∑ x ∈ S, f x :=
    norm_sum_le _ _
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := f)
  have henergy : ∑ x ∈ S, f x ^ 2 ≤ (p : ℝ) ^ 6 * T.card := by
    rw [← rectangle_energy h hh T]
    exact sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have hS : (S.card : ℝ) ≤ (p : ℝ) ^ 6 := by
    exact_mod_cast (S.card_le_univ.trans_eq card_vec)
  have hT : (T.card : ℝ) ≤ (p : ℝ) ^ 6 := by
    exact_mod_cast (T.card_le_univ.trans_eq card_vec)
  have hbound : (∑ x ∈ S, f x) ^ 2 ≤ (p : ℝ) ^ 18 := by
    calc
      _ ≤ S.card * ∑ x ∈ S, f x ^ 2 := hcs
      _ ≤ S.card * ((p : ℝ) ^ 6 * T.card) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ ≤ (p : ℝ) ^ 6 * ((p : ℝ) ^ 6 * (p : ℝ) ^ 6) :=
        mul_le_mul hS (mul_le_mul_of_nonneg_left hT (by positivity))
          (by positivity) (by positivity)
      _ = _ := by ring
  have hnonneg : 0 ≤ ∑ x ∈ S, f x := sum_nonneg (fun _ _ => norm_nonneg _)
  have hpower : (p : ℝ) ^ 18 = ((p : ℝ) ^ 9) ^ 2 := by ring
  rw [hpower] at hbound
  have happ : ∑ x ∈ S, f x ≤ (p : ℝ) ^ 9 :=
    (sq_le_sq₀ hnonneg (by positivity)).mp hbound
  exact htriangle.trans happ

theorem beta_norm_le_one (I : Finset (ZMod p)) (h : ZMod p) : ‖beta I h‖ ≤ 1 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : (I.card : ℝ) ≤ p := by
    exact_mod_cast (show I.card ≤ p by simpa using I.card_le_univ)
  calc
    _ = (p : ℝ)⁻¹ * ‖∑ a ∈ I, ZMod.stdAddChar (-(h * a))‖ := by
      simp [beta]
    _ ≤ (p : ℝ)⁻¹ * ∑ a ∈ I, ‖ZMod.stdAddChar (-(h * a))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (p : ℝ)⁻¹ * I.card := by simp
    _ ≤ (p : ℝ)⁻¹ * p := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 1 := inv_mul_cancel₀ hp.ne'

theorem residue_fourier (I : Finset (ZMod p)) (a : ZMod p) :
    (if a ∈ I then (1 : ℂ) else 0) =
      ∑ h : ZMod p, beta I h * ZMod.stdAddChar (h * a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  symm
  simp_rw [beta, mul_assoc, sum_mul, ← AddChar.map_add_eq_mul]
  rw [← mul_sum, sum_comm]
  have hin (b : ZMod p) :
      ∑ h : ZMod p, ZMod.stdAddChar (-(h * b) + h * a) =
        if a = b then (p : ℂ) else 0 := by
    simp_rw [show ∀ h : ZMod p, -(h * b) + h * a = h * (a - b) by intro; ring]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
    simp [sub_eq_zero]
  simp_rw [hin]
  by_cases ha : a ∈ I
  · simp [ha, inv_mul_cancel₀ hp]
  · simp [ha]

/-- Isolate the zero frequency in the rectangle count. -/
theorem rectangle_fourier (I : Finset (ZMod p)) (S T : Finset (Vec p)) :
    (rectangleCount I S T : ℂ) - (I.card : ℂ) / p * S.card * T.card =
      ∑ h ∈ (univ : Finset (ZMod p)).erase 0,
        beta I h * ∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y) := by
  have hfull : (rectangleCount I S T : ℂ) =
      ∑ h : ZMod p, beta I h * ∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y) := by
    simp only [rectangleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    simp_rw [residue_fourier]
    calc
      _ = ∑ x ∈ S, ∑ h : ZMod p, ∑ y ∈ T,
          beta I h * ZMod.stdAddChar (h * dot x y) := by
        apply sum_congr rfl
        intro x hx
        rw [sum_comm]
      _ = ∑ h : ZMod p, ∑ x ∈ S, ∑ y ∈ T,
          beta I h * ZMod.stdAddChar (h * dot x y) := by rw [sum_comm]
      _ = _ := by simp_rw [mul_sum]
  rw [hfull, ← sum_erase_add _ _ (mem_univ (0 : ZMod p))]
  simp [mul_assoc]

/-- Absolute discrepancy in edge counts before dividing by Q=p^12. -/
theorem rectangle_discrepancy_count (I : Finset (ZMod p)) (S T : Finset (Vec p)) :
    |(rectangleCount I S T : ℝ) - (I.card : ℝ) / p * S.card * T.card| ≤ (p : ℝ) ^ 10 := by
  have hr : (rectangleCount I S T : ℂ) - (I.card : ℂ) / p * S.card * T.card =
      ((rectangleCount I S T : ℝ) - (I.card : ℝ) / p * S.card * T.card : ℝ) := by
    push_cast
    rfl
  have hbound : ‖(rectangleCount I S T : ℂ) - (I.card : ℂ) / p * S.card * T.card‖ ≤
      (p : ℝ) ^ 10 := by
    rw [rectangle_fourier]
    calc
      _ ≤ ∑ h ∈ (univ : Finset (ZMod p)).erase 0,
          ‖beta I h * ∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ (univ : Finset (ZMod p)).erase 0, (p : ℝ) ^ 9 := by
        apply sum_le_sum
        intro h hh
        rw [norm_mul]
        exact (mul_le_mul (beta_norm_le_one I h)
          (rectangle_character_bound h (mem_erase.mp hh).1 S T)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ ≤ ∑ _ : ZMod p, (p : ℝ) ^ 9 :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
      _ = (p : ℝ) ^ 10 := by simp [pow_succ, mul_comm]
  rw [hr, Complex.norm_real, Real.norm_eq_abs] at hbound
  exact hbound

theorem card_residueSet (w : ℚ) (_hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (residueSet (p := p) w).card = ⌊(p : ℚ) * w⌋₊ := by
  have hn : ⌊(p : ℚ) * w⌋₊ ≤ p :=
    Nat.floor_le_of_le (by nlinarith [show (0 : ℚ) ≤ p by positivity])
  rw [residueSet, card_image_of_injOn]
  · exact card_range _
  · intro a ha b hb hab
    have ha' : a < p := (mem_range.mp ha).trans_le hn
    have hb' : b < p := (mem_range.mp hb).trans_le hn
    have h := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using h

/-- The exact rounding loss uses the original rational weight, not a renormalized one. -/
theorem residue_density_error (w : ℚ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    |((residueSet (p := p) w).card : ℝ) / p - w| ≤ 1 / (p : ℝ) := by
  rw [card_residueSet w hw hw1]
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hfloor : ((⌊(p : ℚ) * w⌋₊ : ℕ) : ℝ) ≤ (p : ℝ) * (w : ℝ) := by
    exact_mod_cast (Nat.floor_le (show 0 ≤ (p : ℚ) * w by positivity))
  have hfloor' : (p : ℝ) * (w : ℝ) < (⌊(p : ℚ) * w⌋₊ : ℕ) + (1 : ℝ) := by
    exact_mod_cast (Nat.lt_floor_add_one ((p : ℚ) * w))
  have hlo : (⌊(p : ℚ) * w⌋₊ : ℝ) / p ≤ (w : ℝ) :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  have hhi : (w : ℝ) < ((⌊(p : ℚ) * w⌋₊ : ℝ) + 1) / p :=
    (lt_div_iff₀ hp).mpr (by nlinarith)
  rw [add_div] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith [show (0 : ℝ) ≤ 1 / p by positivity]⟩

theorem rectangle_discrepancy (w : ℚ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (S T : Finset (Vec p)) :
    |(rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
      w * ((S.card : ℝ) / (p : ℝ) ^ 6) * ((T.card : ℝ) / (p : ℝ) ^ 6)| ≤
      1 / (p : ℝ) + 1 / (p : ℝ) ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  let q : ℝ := (p : ℝ) ^ 6
  have hq : 0 < q := by dsimp [q]; positivity
  have hS : (S.card : ℝ) / q ≤ 1 := by
    apply (div_le_one hq).mpr
    dsimp [q]
    exact_mod_cast (S.card_le_univ.trans_eq card_vec)
  have hT : (T.card : ℝ) / q ≤ 1 := by
    apply (div_le_one hq).mpr
    dsimp [q]
    exact_mod_cast (T.card_le_univ.trans_eq card_vec)
  have hfrac : 0 ≤ (S.card : ℝ) / q * ((T.card : ℝ) / q) := by positivity
  have hfrac1 : (S.card : ℝ) / q * ((T.card : ℝ) / q) ≤ 1 := by
    nlinarith [show (0 : ℝ) ≤ S.card / q by positivity,
      show (0 : ℝ) ≤ T.card / q by positivity]
  have hfirst : |(rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
      ((residueSet (p := p) w).card : ℝ) / p * (S.card / q) * (T.card / q)| ≤
      1 / (p : ℝ) ^ 2 := by
    have heq : (rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
        ((residueSet (p := p) w).card : ℝ) / p * (S.card / q) * (T.card / q) =
        ((rectangleCount (residueSet w) S T : ℝ) -
          ((residueSet (p := p) w).card : ℝ) / p * S.card * T.card) / (p : ℝ) ^ 12 := by
      dsimp [q]
      field_simp

    rw [heq, abs_div, abs_of_pos (pow_pos hp _)]
    apply (div_le_iff₀ (pow_pos hp _)).mpr
    calc
      _ ≤ (p : ℝ) ^ 10 := rectangle_discrepancy_count _ S T
      _ = 1 / (p : ℝ) ^ 2 * (p : ℝ) ^ 12 := by field_simp
  have hsecond : |(((residueSet (p := p) w).card : ℝ) / p - w) *
      (S.card / q * (T.card / q))| ≤ 1 / (p : ℝ) := by
    rw [abs_mul, abs_of_nonneg hfrac]
    exact (mul_le_mul (residue_density_error w hw hw1) hfrac1 hfrac (by positivity)).trans_eq
      (mul_one _)
  have heq : (rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
      w * ((S.card : ℝ) / (p : ℝ) ^ 6) * ((T.card : ℝ) / (p : ℝ) ^ 6) =
      ((rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
        ((residueSet (p := p) w).card : ℝ) / p * (S.card / q) * (T.card / q)) +
        (((residueSet (p := p) w).card : ℝ) / p - w) * (S.card / q * (T.card / q)) := by
    dsimp [q]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (add_comm _ _))

section Rounding

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem cutMass_nonneg (a : V → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (σ : V → Bool) :
    0 ≤ cutMass a σ := by
  apply prod_nonneg
  intro i hi
  exact ite_nonneg (ha i).1 (sub_nonneg.mpr (ha i).2)

/-- Two distinct coordinates of a product law, proved by finite product expansion. -/
theorem independent_pair (f : V → Bool → ℝ) (hf : ∀ i, ∑ b : Bool, f i b = 1)
    (u v : V) (huv : u ≠ v) (g k : Bool → ℝ) :
    ∑ σ : V → Bool, (∏ i, f i (σ i)) * g (σ u) * k (σ v) =
      (∑ b : Bool, f u b * g b) * (∑ b : Bool, f v b * k b) := by
  let F (i : V) (b : Bool) := f i b * (if i = u then g b else 1) *
    (if i = v then k b else 1)
  have hmul (σ : V → Bool) : (∏ i, f i (σ i)) * g (σ u) * k (σ v) = ∏ i, F i (σ i) := by
    dsimp only [F]
    simp only [prod_mul_distrib]
    simp
  simp_rw [hmul]
  rw [← Fintype.prod_sum]
  have hF (i : V) : (∑ b : Bool, F i b) =
      (if i = u then (∑ b : Bool, f u b * g b) else 1) *
      (if i = v then (∑ b : Bool, f v b * k b) else 1) := by
    by_cases hiu : i = u
    · subst i
      simp [F, huv]
    · by_cases hiv : i = v
      · subst i
        simp [F, Ne.symm huv]
      · simpa [F, hiu, hiv] using hf i
  simp_rw [hF]
  rw [prod_mul_distrib]
  simp

/-- Probability that two distinct vertices receive different cut signs. -/
theorem cutMass_crossing (a : V → ℝ) (u v : V) (huv : u ≠ v) :
    ∑ σ : V → Bool, cutMass a σ * (if σ u ≠ σ v then 1 else 0) =
      a u * (1 - a v) + (1 - a u) * a v := by
  let f (i : V) (b : Bool) : ℝ := if b then a i else 1 - a i
  let g (b : Bool) : ℝ := if b then 1 else 0
  let k (b : Bool) : ℝ := if b then 0 else 1
  have hf (i : V) : ∑ b : Bool, f i b = 1 := by simp [f]
  have hcross (σ : V → Bool) : (if σ u ≠ σ v then (1 : ℝ) else 0) =
      g (σ u) * k (σ v) + k (σ u) * g (σ v) := by
    cases hu : σ u <;> cases hv : σ v <;> simp [g, k]
  simp_rw [hcross, mul_add, ← mul_assoc]
  rw [sum_add_distrib]
  change (∑ σ : V → Bool, (∏ i, f i (σ i)) * g (σ u) * k (σ v)) +
    (∑ σ : V → Bool, (∏ i, f i (σ i)) * k (σ u) * g (σ v)) = _
  rw [independent_pair f hf u v huv, independent_pair f hf u v huv]
  simp [f, g, k]

end Rounding

theorem weightedCut_le_max {N : ℕ} (w : Fin N → Fin N → ℝ) (σ : Fin N → Bool) :
    weightedCut w σ ≤ weightedMax w := by
  exact (univ.image (weightedCut w)).le_max' _ (mem_image.mpr ⟨σ, mem_univ _, rfl⟩)

theorem weightedMax_attained {N : ℕ} (w : Fin N → Fin N → ℝ) :
    ∃ σ : Fin N → Bool, weightedCut w σ = weightedMax w := by
  have hm := (univ.image (weightedCut w)).max'_mem (univ_nonempty.image _)
  obtain ⟨σ, hσ, he⟩ := mem_image.mp hm
  exact ⟨σ, he⟩

theorem fractionalCut_expectation {N : ℕ} (w : Fin N → Fin N → ℝ) (a : Fin N → ℝ) :
    fractionalCut w a = ∑ σ : Fin N → Bool, cutMass a σ * weightedCut w σ := by
  unfold fractionalCut weightedCut
  symm
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  by_cases huv : u < v
  · simp only [huv, true_and, ite_true, if_true]
    have h (σ : Fin N → Bool) : cutMass a σ * (if σ u ≠ σ v then w u v else 0) =
        w u v * (cutMass a σ * (if σ u ≠ σ v then 1 else 0)) := by
      split_ifs <;> ring
    simp_rw [h]
    rw [← mul_sum, cutMass_crossing a u v (ne_of_lt huv)]
  · simp [huv]

/-- Rounding cannot exceed an actual integral maximum cut. -/
theorem fractionalCut_le_max {N : ℕ} (w : Fin N → Fin N → ℝ) (a : Fin N → ℝ)
    (ha : ∀ u, 0 ≤ a u ∧ a u ≤ 1) : fractionalCut w a ≤ weightedMax w := by
  rw [fractionalCut_expectation]
  calc
    _ ≤ ∑ σ : Fin N → Bool, cutMass a σ * weightedMax w :=
      sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (weightedCut_le_max w σ)
        (cutMass_nonneg a ha σ))
    _ = weightedMax w := by rw [← sum_mul, sum_cutMass, one_mul]

theorem vertexEquiv_lt_of_lt {N : ℕ} (u v : Fin N) (x y : Vec p) (huv : u < v) :
    vertexEquiv N (u, x) < vertexEquiv N (v, y) := by
  change (vecEquiv x : ℕ) + p ^ 6 * (u : ℕ) < (vecEquiv y : ℕ) + p ^ 6 * (v : ℕ)
  have h := Nat.mul_le_mul_left (p ^ 6) (show (u : ℕ) + 1 ≤ (v : ℕ) from huv)
  have hx := (vecEquiv x).isLt
  nlinarith

theorem vertexEquiv_lt_iff_of_ne {N : ℕ} (u v : Fin N) (x y : Vec p) (huv : u ≠ v) :
    vertexEquiv N (u, x) < vertexEquiv N (v, y) ↔ u < v := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · exact huv'
    · exact False.elim (lt_asymm h (vertexEquiv_lt_of_lt v u y x hvu'))
  · exact vertexEquiv_lt_of_lt u v x y

theorem blowup_cutSize {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u) (cut : Fin (N * p ^ 6) → Bool) :
    (blowupGraph w hw).cutSize cut =
      clusterCutCount w (fun u x => cut (vertexEquiv N (u, x))) := by
  change (∑ u : Fin (N * p ^ 6), ∑ v : Fin (N * p ^ 6),
    if u < v ∧ (blowupGraph (p := p) w hw).adj u v = true ∧ cut u ≠ cut v
      then (1 : ℕ) else 0) = _
  rw [← Equiv.sum_comp (vertexEquiv N)]
  simp_rw [← Equiv.sum_comp (vertexEquiv N)]
  simp only [Fintype.sum_prod_type]
  unfold clusterCutCount
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  by_cases huv : u < v
  · simp only [huv, ite_true, if_true]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    simp [blowup_adj, vertexEquiv_lt_of_lt u v x y huv, ne_of_lt huv]
  · simp only [huv, ite_false]
    apply sum_eq_zero
    intro x hx
    apply sum_eq_zero
    intro y hy
    by_cases heq : u = v
    · subst v
      simp
    · have hn : ¬ vertexEquiv N (u, x) < vertexEquiv N (v, y) :=
        fun h => huv ((vertexEquiv_lt_iff_of_ne u v x y heq).mp h)
      simp [hn]

theorem cutSet_card_partition (σ : Vec p → Bool) :
    (cutSet σ true).card + (cutSet σ false).card = p ^ 6 := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Vec p)))
    (fun x => σ x = true)
  simpa [cutSet] using h

theorem cutFraction_mem (σ : Vec p → Bool) :
    0 ≤ cutFraction σ ∧ cutFraction σ ≤ 1 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  constructor
  · unfold cutFraction; positivity
  · unfold cutFraction
    apply (div_le_one (pow_pos hp _)).mpr
    exact_mod_cast ((cutSet σ true).card_le_univ.trans_eq card_vec)

theorem cutFraction_false (σ : Vec p → Bool) :
    ((cutSet σ false).card : ℝ) / (p : ℝ) ^ 6 = 1 - cutFraction σ := by
  have hp : (p : ℝ) ^ 6 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hc : ((cutSet σ true).card : ℝ) + (cutSet σ false).card = (p : ℝ) ^ 6 := by
    exact_mod_cast cutSet_card_partition σ
  have h : cutFraction σ + ((cutSet σ false).card : ℝ) / (p : ℝ) ^ 6 = 1 := by
    rw [cutFraction, ← add_div, hc, div_self hp]
  linarith

theorem rectangle_cutSet (I : Finset (ZMod p)) (σ τ : Vec p → Bool) (b c : Bool) :
    rectangleCount I (cutSet σ b) (cutSet τ c) =
      ∑ x, ∑ y, if σ x = b ∧ τ y = c ∧ dot x y ∈ I then 1 else 0 := by
  simp only [rectangleCount, cutSet, sum_filter]
  apply sum_congr rfl
  intro x hx
  by_cases hb : σ x = b
  · simp only [hb, ite_true, if_true, true_and]
    apply sum_congr rfl
    intro y hy
    by_cases hc : τ y = c <;> simp [hc]
  · simp [hb]

theorem pairCutCount_rectangles (w : ℚ) (σ τ : Vec p → Bool) :
    pairCutCount w σ τ =
      rectangleCount (residueSet w) (cutSet σ true) (cutSet τ false) +
      rectangleCount (residueSet w) (cutSet σ false) (cutSet τ true) := by
  rw [rectangle_cutSet, rectangle_cutSet, ← sum_add_distrib]
  unfold pairCutCount
  apply sum_congr rfl
  intro x hx
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro y hy
  cases hσ : σ x <;> cases hτ : τ y <;> simp []

theorem pairCutCount_discrepancy (w : ℚ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (σ τ : Vec p → Bool) :
    |(pairCutCount w σ τ : ℝ) / (p : ℝ) ^ 12 -
      w * (cutFraction σ * (1 - cutFraction τ) + (1 - cutFraction σ) * cutFraction τ)| ≤
      2 * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
  have h₁ := rectangle_discrepancy w hw hw1 (cutSet σ true) (cutSet τ false)
  have h₂ := rectangle_discrepancy w hw hw1 (cutSet σ false) (cutSet τ true)
  rw [cutFraction_false] at h₁ h₂
  change |(rectangleCount _ _ _ : ℝ) / (p : ℝ) ^ 12 -
    w * cutFraction σ * (1 - cutFraction τ)| ≤ _ at h₁
  change |(rectangleCount _ _ _ : ℝ) / (p : ℝ) ^ 12 -
    w * (1 - cutFraction σ) * cutFraction τ| ≤ _ at h₂
  rw [pairCutCount_rectangles, Nat.cast_add, add_div]
  calc
    _ = |((rectangleCount (residueSet w) (cutSet σ true) (cutSet τ false) : ℝ) /
          (p : ℝ) ^ 12 - w * cutFraction σ * (1 - cutFraction τ)) +
        ((rectangleCount (residueSet w) (cutSet σ false) (cutSet τ true) : ℝ) /
          (p : ℝ) ^ 12 - w * (1 - cutFraction σ) * cutFraction τ)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- Twice the number of unordered distinct pairs, including N=0 and N=1. -/
theorem twice_pair_count (N : ℕ) :
    (∑ u : Fin N, ∑ v : Fin N, if u < v then (2 : ℝ) else 0) =
      (N : ℝ) * ((N : ℝ) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Fin.sum_univ_succ, Fin.not_lt_zero, ite_false, Fin.succ_pos,
      ite_true, if_true, sum_const, card_fin, nsmul_eq_mul, zero_add, Fin.succ_lt_succ_iff,
      ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Summing the exact pair loss on the common unnormalized scale. -/
theorem clusterCutCount_discrepancy {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hbound : ∀ u v, u < v → 0 ≤ w u v ∧ w u v ≤ 1)
    (σ : Fin N → Vec p → Bool) :
    |(clusterCutCount w σ : ℝ) / (p : ℝ) ^ 12 -
      fractionalCut (fun u v => (w u v : ℝ)) (fun u => cutFraction (σ u))| ≤
      (N : ℝ) * ((N : ℝ) - 1) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
  change |((∑ u, ∑ v, if u < v then pairCutCount (w u v) (σ u) (σ v) else 0 : ℕ) : ℝ) /
    (p : ℝ) ^ 12 - ∑ u, ∑ v, if u < v then
      (w u v : ℝ) * (cutFraction (σ u) * (1 - cutFraction (σ v)) +
        (1 - cutFraction (σ u)) * cutFraction (σ v)) else 0| ≤ _
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, sum_div]
  rw [← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ u, ∑ v,
        |(if u < v then (pairCutCount (w u v) (σ u) (σ v) : ℝ) else 0) /
          (p : ℝ) ^ 12 - (if u < v then
          (w u v : ℝ) * (cutFraction (σ u) * (1 - cutFraction (σ v)) +
            (1 - cutFraction (σ u)) * cutFraction (σ v)) else 0)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun u _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ u, ∑ v, if u < v then 2 * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) else 0 := by
      apply sum_le_sum
      intro u hu
      apply sum_le_sum
      intro v hv
      by_cases huv : u < v
      · simpa only [huv, ite_true, if_true] using
          pairCutCount_discrepancy (w u v) (hbound u v huv).1 (hbound u v huv).2 (σ u) (σ v)
      · simp [huv]
    _ = _ := by
      have he (u v : Fin N) :
          (if u < v then 2 * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) else 0) =
          (if u < v then (2 : ℝ) else 0) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
        split_ifs <;> ring
      simp_rw [he, ← sum_mul]
      rw [twice_pair_count]

/-- Every cut lies below the finite unweighted optimum. -/
theorem graph_cut_le_max (G : Graph) (σ : Fin G.vertices → Bool) :
    G.cutSize σ ≤ G.maxCut := by
  unfold Graph.maxCut
  exact le_sup (s := univ.image G.cutSize) (f := id) (mem_image.mpr ⟨σ, mem_univ _, rfl⟩)

/-- The finite unweighted optimum is attained by an actual cut. -/
theorem graph_max_attained (G : Graph) : ∃ σ, G.cutSize σ = G.maxCut := by
  have h := sup_mem_of_nonempty (s := (univ : Finset (Fin G.vertices → Bool)))
    (f := G.cutSize) univ_nonempty
  obtain ⟨σ, hσ, he⟩ := h
  refine ⟨σ, ?_⟩
  simpa [Graph.maxCut, sup_image, Function.comp_def] using he

theorem fractionalCut_integral {N : ℕ} (w : Fin N → Fin N → ℝ) (σ : Fin N → Bool) :
    fractionalCut w (fun u => if σ u then 1 else 0) = weightedCut w σ := by
  unfold fractionalCut weightedCut
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  cases hσ : σ u <;> cases hτ : σ v <;> simp [hσ, hτ]

/-- Full optimum comparison for the actual simple finite graph.
No complexity certificate is asserted in this analytic/combinatorial theorem. -/
theorem blowup_maxCut_error {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u)
    (hbound : ∀ u v, u < v → 0 ≤ w u v ∧ w u v ≤ 1) :
    |((blowupGraph (p := p) w hw).maxCut : ℝ) / (p : ℝ) ^ 12 -
      weightedMax (fun u v => (w u v : ℝ))| ≤
      (N : ℝ) * ((N : ℝ) - 1) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  apply abs_le.mpr
  constructor
  · obtain ⟨σ, hσ⟩ := weightedMax_attained (fun u v => (w u v : ℝ))
    let cut : Fin (N * p ^ 6) → Bool := fun i => σ ((vertexEquiv N).symm i).1
    have he : (blowupGraph (p := p) w hw).cutSize cut =
        clusterCutCount w (fun u (_ : Vec p) => σ u) := by
      rw [blowup_cutSize]
      simp only [cut, Equiv.symm_apply_apply]
    have hc := clusterCutCount_discrepancy w hbound (fun u (_ : Vec p) => σ u)
    simp only [cutFraction_const, fractionalCut_integral, hσ] at hc
    have hmax := div_le_div_of_nonneg_right
      (show ((blowupGraph (p := p) w hw).cutSize cut : ℝ) ≤
        (blowupGraph (p := p) w hw).maxCut from by exact_mod_cast graph_cut_le_max (blowupGraph (p := p) w hw) cut)
      (le_of_lt (pow_pos hp 12))
    rw [he] at hmax
    linarith [(abs_le.mp hc).1]
  · obtain ⟨cut, hcut⟩ := graph_max_attained (blowupGraph (p := p) w hw)
    have hc := clusterCutCount_discrepancy w hbound
      (fun u x => cut (vertexEquiv N (u, x)))
    rw [← blowup_cutSize w hw cut, hcut] at hc
    have hf := fractionalCut_le_max (fun u v => (w u v : ℝ))
      (fun u => cutFraction (fun x => cut (vertexEquiv N (u, x))))
      (fun u => cutFraction_mem _)
    linarith [(abs_le.mp hc).2]

theorem normalized_pair_bound {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hnonneg : ∀ u v, u < v → 0 ≤ w u v) (hscale : totalWeight w ≤ 1) :
    ∀ u v, u < v → 0 ≤ w u v ∧ w u v ≤ 1 := by
  intro u v huv
  refine ⟨hnonneg u v huv, ?_⟩
  have hx (u v : Fin N) : 0 ≤ (if u < v then w u v else 0) := by
    split_ifs with h
    · exact hnonneg u v h
    · exact le_rfl
  have h₁ := single_le_sum (fun v (_ : v ∈ (univ : Finset (Fin N))) => hx u v) (mem_univ v)
  have h₂ : (∑ v, if u < v then w u v else 0) ≤ totalWeight w := by
    unfold totalWeight
    apply single_le_sum (s := univ) (a := u)
    · intro u hu
      exact sum_nonneg (fun v _ => hx u v)
    · exact mem_univ _
  have h₁' : w u v ≤ ∑ v, if u < v then w u v else 0 := by
    simpa only [huv, ite_true, if_true] using h₁
  exact h₁'.trans (h₂.trans hscale)

theorem selected_prime_error (N K : ℕ) (hK : 0 < K) :
    let p := searchPrime (K * (N + 1) ^ 2)
    (N : ℝ) * ((N : ℝ) - 1) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) ≤ 2 / (K : ℝ) := by
  dsimp only
  let p := searchPrime (K * (N + 1) ^ 2)
  have hp : 0 < (p : ℝ) := by exact_mod_cast (searchPrime_spec _).1.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (searchPrime_spec _).1.one_lt.le
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hlarge : (K : ℝ) * ((N : ℝ) + 1) ^ 2 ≤ (p : ℝ) := by
    exact_mod_cast (searchPrime_spec (K * (N + 1) ^ 2)).2.1.le
  have hpair : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := by
    rw [← twice_pair_count]
    apply sum_nonneg
    intro u hu
    apply sum_nonneg
    intro v hv
    split_ifs <;> norm_num
  have hr : 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ) := by
    have hh := one_div_le_one_div_of_le hp (show (p : ℝ) ≤ (p : ℝ) ^ 2 by nlinarith)
    calc
      _ ≤ 1 / (p : ℝ) + 1 / (p : ℝ) := add_le_add (le_refl _) hh
      _ = 2 / (p : ℝ) := by ring
  calc
    _ ≤ (N : ℝ) * ((N : ℝ) - 1) * (2 / (p : ℝ)) := mul_le_mul_of_nonneg_left hr hpair
    _ ≤ ((N : ℝ) + 1) ^ 2 * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ ≤ 2 / (K : ℝ) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hp hK').mpr
      nlinarith

theorem deterministicOutput_error {N : ℕ} (K : ℕ) (hK : 0 < K)
    (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u)
    (hnonneg : ∀ u v, u < v → 0 ≤ w u v) (hscale : totalWeight w ≤ 1) :
    |((deterministicOutput K w hw).graph.maxCut : ℝ) / (deterministicOutput K w hw).scale -
      weightedMax (fun u v => (w u v : ℝ))| ≤ 2 / (K : ℝ) := by
  let p := searchPrime (K * (N + 1) ^ 2)
  have : Fact p.Prime := ⟨(searchPrime_spec _).1⟩
  have h := blowup_maxCut_error (p := p) w hw (normalized_pair_bound w hnonneg hscale)
  have he := h.trans (selected_prime_error N K hK)
  simpa only [deterministicOutput, blowupOutput, Nat.cast_pow] using he

end OptimalMaxCut.Unweighted

/-! Exact tree gate and slice symmetry. Sign values are encoded in ZMod 2:
b encodes (-1)^b. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Dictator
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

 theorem corrAverage_coordinate (t : ℝ) {n : ℕ} (i : Fin n) :
    corrAverage t n (fun x y => bitSign (x i) * bitSign (y i)) = t := by
  classical
  let s : Cube (Fin n) := fun j => decide (j = i)
  have hw (x : Cube (Fin n)) : walsh s x = bitSign (x i) := by
    have he (j : Fin n) : bitSign (s j && x j) = if j = i then bitSign (x i) else 1 := by
      by_cases h : j = i <;> simp [s, h, bitSign]
    simp only [walsh, he]
    simp
  have hd : Analytic.degree s = 1 := by
    have hs : univ.filter (fun j => s j = true) = {i} := by ext j; simp [s]
    rw [Analytic.degree, hs, card_singleton]
  simpa [hw, hd] using corrAverage_walsh t n s s

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

 theorem testCut_complete (G : Game X Y E q) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (lx : X → Fin q) (ly : Y → Fin q) :
    (1 + t) / 2 - 2 * (1 - G.satisfied lx ly) ≤ G.testCut t (dictator lx) := by
  classical
  let P (e e' : E) := corrAverage t q (fun z z' =>
      (1 - dictator lx (G.source e) (cubePerm (G.permutation e) z) *
        dictator lx (G.source e') (cubePerm (G.permutation e') (antipode z'))) / 2)
  let bad (y : Y) (e : E) : ℝ := if G.permutation e (lx (G.source e)) = ly y then 0 else 1
  have hP (e e' : E) : 0 ≤ P e e' := by
    have h := corrAverage_mono ht q (F := fun _ _ => 0)
      (G := fun z z' => (1 - dictator lx (G.source e) (cubePerm (G.permutation e) z) *
        dictator lx (G.source e') (cubePerm (G.permutation e') (antipode z'))) / 2)
      (fun z z' => by
        dsimp [dictator, cubePerm, antipode, bitSign]
        split_ifs <;> norm_num)
    simpa only [corrAverage_fst, Fintype.expect_const] using h
  have hgood (y : Y) (e e' : E)
      (he : G.permutation e (lx (G.source e)) = ly y)
      (he' : G.permutation e' (lx (G.source e')) = ly y) : P e e' = (1 + t) / 2 := by
    dsimp [P, dictator, cubePerm, antipode]
    simp only [he, he', bitSign_not, mul_neg, sub_neg_eq_add, div_eq_mul_inv,
      corrAverage_mul_const, corrAverage_add, corrAverage_fst, Fintype.expect_const,
      corrAverage_coordinate]
  have hp (y : Y) (e e' : E) : (1 + t) / 2 - bad y e - bad y e' ≤ P e e' := by
    by_cases he : G.permutation e (lx (G.source e)) = ly y
    · by_cases he' : G.permutation e' (lx (G.source e')) = ly y
      · simp only [bad, ite_eq_left he, ite_eq_left he', sub_zero, hgood y e e' he he', le_refl]
      · simp only [bad, ite_eq_left he, ite_eq_right he', sub_zero]
        linarith [hP e e', ht.2]
    · by_cases he' : G.permutation e' (lx (G.source e')) = ly y
      · simp only [bad, ite_eq_right he, ite_eq_left he', sub_zero]
        linarith [hP e e', ht.2]
      · simp only [bad, ite_eq_right he, ite_eq_right he']
        linarith [hP e e', ht.2]
  have hbad : G.rightLaw.avg (fun y => (G.edgeLaw y).avg (bad y)) = 1 - G.satisfied lx ly := by
    have hh (y : Y) (e : E) : bad y e = 1 -
      (if G.permutation e (lx (G.source e)) = ly y then (1 : ℝ) else 0) := by
      dsimp [bad]; split_ifs <;> norm_num
    change G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e => bad y e)) = _
    simp only [hh, Law.avg_sub, Law.avg_const, satisfied]
  rw [testCut_expanded]
  have h := G.rightLaw.avg_mono (fun y => (G.edgeLaw y).avg_mono (fun e =>
    (G.edgeLaw y).avg_mono (fun e' => hp y e e')))
  simp only [Law.avg_sub, Law.avg_const, hbad] at h
  dsimp only [P] at h
  linarith

end Game
end OptimalMaxCut.LongCode
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

 theorem push_average (p : Law I) (f : I → J) (g : J → ℝ) :
    (p.push f).avg g = p.avg (fun i => g (f i)) := by
  simp only [avg, push, Rat.cast_sum, apply_ite Rat.cast, Rat.cast_zero, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul]

end Law

 theorem aggregate_nonneg {N : ℕ} (p : Law (Fin N × Fin N)) (u v : Fin N) :
    0 ≤ aggregate p u v := by
  unfold aggregate
  split_ifs
  · exact le_refl 0
  · exact add_nonneg (p.nonneg _) (p.nonneg _)

 theorem upper_triangle_symmetrize {N : ℕ} (a : Fin N → Fin N → ℝ) :
    (∑ u, ∑ v, if u < v then a u v + a v u else 0) =
      ∑ u, ∑ v, if u ≠ v then a u v else 0 := by
  have he (u v : Fin N) : (if u ≠ v then a u v else 0) =
      (if u < v then a u v else 0) + (if v < u then a u v else 0) := by
    rcases lt_trichotomy u v with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hs (u v : Fin N) : (if u < v then a u v + a v u else 0) =
      (if u < v then a u v else 0) + (if u < v then a v u else 0) := by
    split_ifs <;> ring
  conv_lhs => simp only [hs, sum_add_distrib]
  conv_rhs => simp only [he, sum_add_distrib]
  congr 1
  rw [sum_comm]

 theorem aggregate_cut {N : ℕ} (p : Law (Fin N × Fin N)) (σ : Fin N → Bool) :
    weightedCut (fun u v => (aggregate p u v : ℝ)) σ =
      p.avg (fun e => if σ e.1 ≠ σ e.2 then 1 else 0) := by
  have h (u v : Fin N) :
      (if u < v ∧ σ u ≠ σ v then (aggregate p u v : ℝ) else 0) =
      (if u < v then (if σ u ≠ σ v then (p.weight (u,v) : ℝ) else 0) +
        (if σ v ≠ σ u then (p.weight (v,u) : ℝ) else 0) else 0) := by
    by_cases hlt : u < v <;> by_cases hs : σ u = σ v <;>
      simp [aggregate, hlt, hs, eq_comm, ne_of_lt, Rat.cast_add]
  simp only [weightedCut, h, upper_triangle_symmetrize, Law.avg, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases huv : u = v <;> by_cases hs : σ u = σ v <;> simp [huv, hs]

 theorem aggregate_total {N : ℕ} (p : Law (Fin N × Fin N)) : totalWeight (aggregate p) ≤ 1 := by
  have he : ((totalWeight (aggregate p) : ℚ) : ℝ) =
      ∑ u, ∑ v, if u ≠ v then (p.weight (u,v) : ℝ) else 0 := by
    simp only [totalWeight, Rat.cast_sum, apply_ite Rat.cast, Rat.cast_zero]
    have hh (u v : Fin N) : (if u < v then (aggregate p u v : ℝ) else 0) =
        if u < v then (p.weight (u,v) : ℝ) + (p.weight (v,u) : ℝ) else 0 := by
      by_cases h : u < v
      · simp [h, aggregate, ne_of_lt h]
      · simp [h]
    simp only [hh, upper_triangle_symmetrize]
  have hle : (∑ u, ∑ v, if u ≠ v then (p.weight (u,v) : ℝ) else 0) ≤ 1 := by
    calc
      _ ≤ ∑ u, ∑ v, (p.weight (u,v) : ℝ) := by
        apply sum_le_sum; intro u _
        apply sum_le_sum; intro v _
        split_ifs
        · exact le_refl _
        · exact p.weight_nonneg _
      _ = 1 := by simpa only [Fintype.sum_prod_type] using p.total_real
  rw [← he] at hle
  exact_mod_cast hle

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

 theorem weightedCut_testCut (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (σ : Fin N → Bool) :
    weightedCut (fun u v => (G.weights t ht enum u v : ℝ)) σ =
      G.testCut t (fun x z => bitSign (σ (enum (x,z)))) := by
  rw [weights, aggregate_cut, edgeDistribution, Law.push_average, G.testCut_sampleLaw t ht]
  congr 1
  funext a
  cases h : σ (enum (G.queries a).1) <;> cases h' : σ (enum (G.queries a).2) <;>
    norm_num [bitSign, h, h']

 theorem weightedMax_complete (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (lx : X → Fin q) (ly : Y → Fin q) :
    (1 + (t : ℝ)) / 2 - 2 * (1 - G.satisfied lx ly) ≤
      weightedMax (fun u v => (G.weights t ht enum u v : ℝ)) := by
  let σ : Fin N → Bool := fun u => (enum.symm u).2 (lx (enum.symm u).1)
  have ht' : (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  have h := G.testCut_complete (t : ℝ) ht' lx ly
  have he : (fun x z => bitSign (σ (enum (x,z)))) = dictator lx := by
    funext x z; simp [σ, dictator]
  rw [← he, ← G.weightedCut_testCut t ht enum σ] at h
  exact h.trans (weightedCut_le_max _ _)

end Game
end OptimalMaxCut.LongCode

namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset
namespace Law
attribute [local instance] Classical.propDecidable
variable {E Y : Type} [Fintype E] [Fintype Y] [Nonempty E]

omit [Fintype Y] [Nonempty E] in
 theorem fiberSize_pos (r : E → Y) (e : E) : 0 < fiberSize r (r e) := by
  classical
  exact card_pos.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

 theorem fiber_joint (r : E → Y) (y : Y) (e : E) :
    (fiberMarginal r).weight y * (fiberConditional r y).weight e =
      if r e = y then 1 / (Fintype.card E : ℚ) else 0 := by
  classical
  dsimp [fiberMarginal, fiberConditional]
  by_cases h : fiberSize r y = 0
  · have hx : r e ≠ y := by
      intro he
      have hp := fiberSize_pos r e
      rw [he, h] at hp
      omega
    simp [h, hx]
  · have hr : (fiberSize r y : ℚ) ≠ 0 := by exact_mod_cast h
    split_ifs <;> field_simp ; simp_all

 theorem fiber_average (r : E → Y) (f : Y → E → ℝ) :
    (fiberMarginal r).avg (fun y => (fiberConditional r y).avg (f y)) =
      (∑ e, f (r e) e) / Fintype.card E := by
  classical
  simp only [avg, mul_sum, ← mul_assoc, ← Rat.cast_mul, fiber_joint]
  rw [sum_comm]
  simp only [apply_ite (fun z : ℚ => (z : ℝ)), Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast, Rat.cast_zero, ite_mul, zero_mul]
  simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← mul_sum]
  ring
end Law
end OptimalMaxCut.LongCode

namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target
open MaxCutGames.Explicit.MachineOutputContract
attribute [local instance] Classical.propDecidable

variable {q : ℕ}

 theorem satisfaction_formula (g : Instance q) (lx ly : Fin g.vertices → Fin q) :
    (ofInstance g).satisfied lx ly =
      (∑ e : Fin g.constraints.length,
        if g.constraints[e].permutation.images[lx g.constraints[e].source] =
          ly g.constraints[e].target then (1 : ℝ) else 0) / g.constraints.length := by
  let : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  unfold Game.satisfied ofInstance
  rw [Law.fiber_average]
  simp only [Fintype.card_fin, permutationEquiv, Equiv.coe_fn_mk]
  congr 1

/-- Occurrences retain their list identity: no parallel edge or denominator is
silently discarded in the adapter. -/
 theorem count_as_sum {n : ℕ} (cs : List (Constraint n q)) (l : Fin n → Fin q) :
    (countSatisfied l cs : ℝ) =
      ∑ e : Fin cs.length, if cs[e].permutation.images[l cs[e].source] =
        l cs[e].target then (1 : ℝ) else 0 := by
  induction cs with
  | nil => simp [countSatisfied]
  | cons c cs ih =>
    simp only [List.length_cons, Fin.sum_univ_succ]
    simp only [countSatisfied, Nat.cast_add, ih, Constraint.satisfied,

      ]
    congr 1
    split_ifs <;> simp_all

 theorem satisfaction_diagonal (g : Instance q) (l : Fin g.vertices → Fin q) :
    (ofInstance g).satisfied l l = (countSatisfied l g.constraints : ℝ) / g.constraints.length := by
  rw [satisfaction_formula, count_as_sum]

 theorem satisfaction_merge (g : Instance q) (b : SimpleBipartite g)
    (lx ly : Fin g.vertices → Fin q) :
    (ofInstance g).satisfied lx ly =
      (countSatisfied (merge g b lx ly) g.constraints : ℝ) / g.constraints.length := by
  rw [satisfaction_formula, count_as_sum]
  congr 1
  apply sum_congr rfl
  intro e _
  simp only [merge, b.sourceSide, b.targetSide, Bool.false_eq_true, ↓reduceIte]

 theorem complete (g : Instance q) (ε : ℝ)
    (h : ∃ l, 1 - ε ≤ (countSatisfied l g.constraints : ℝ) / g.constraints.length) :
    ∃ lx ly, 1 - ε ≤ (ofInstance g).satisfied lx ly := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, l, (satisfaction_diagonal g l).symm ▸ hl⟩

 theorem sound (g : Instance q) (b : SimpleBipartite g) (δ : ℝ)
    (h : ∀ l, (countSatisfied l g.constraints : ℝ) / g.constraints.length ≤ δ) :
    (ofInstance g).Sound δ := by
  intro lx ly
  rw [satisfaction_merge g b lx ly]
  exact h _
end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Arithmetic_GridWeight
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset OptimalMaxCut.Unweighted

namespace Law
variable {I : Type} [Fintype I]

 theorem gridWeight_error (P : ℕ) (hP : 0 < P) (a : ℚ) :
    a - gridWeight P a ≤ 1 / (P : ℚ) := by
  have hPr : (0 : ℚ) < P := by exact_mod_cast hP
  have h := Nat.lt_floor_add_one ((P : ℚ) * a)
  unfold gridWeight
  apply (le_div_iff₀ hPr).mpr
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hPr)]
  nlinarith

 theorem grid_average (p : Law I) (P : ℕ) (hP : 0 < P) (f : Option I → ℝ)
    (hzero : f none = 0) :
    (p.grid P hP).avg f = ∑ i, (gridWeight P (p.weight i) : ℝ) * f (some i) := by
  simp only [avg, Fintype.sum_option, grid, hzero, mul_zero, zero_add]

 theorem grid_average_bounds (p : Law I) (P : ℕ) (hP : 0 < P) (f : I → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    let rounded := ∑ i, (gridWeight P (p.weight i) : ℝ) * f i
    rounded ≤ p.avg f ∧ p.avg f - rounded ≤ Fintype.card I / (P : ℝ) := by
  dsimp only
  have hw (i : I) : (gridWeight P (p.weight i) : ℝ) ≤ (p.weight i : ℝ) := by
    exact_mod_cast gridWeight_le P hP _ (p.nonneg i)
  have he (i : I) : (p.weight i : ℝ) - (gridWeight P (p.weight i) : ℝ) ≤ 1 / (P : ℝ) := by
    have hh : ((p.weight i - gridWeight P (p.weight i) : ℚ) : ℝ) ≤
        ((1 / (P : ℚ) : ℚ) : ℝ) := by exact_mod_cast gridWeight_error P hP (p.weight i)
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hh
  constructor
  · exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (hf0 i))
  · rw [avg, ← sum_sub_distrib]
    calc
      _ ≤ ∑ _ : I, 1 / (P : ℝ) := sum_le_sum (fun i _ => by
        have h := mul_le_of_le_one_right (sub_nonneg.mpr (hw i)) (hf1 i)
        nlinarith [he i])
      _ = _ := by simp [div_eq_mul_inv]

end Law

 theorem roundedWeights_cut_error {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (query : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) (σ : Fin N → Bool) :
    let w := aggregate (p.push query)
    let w' := roundedWeights p query v0 P hP
    weightedCut (fun u v => (w' u v : ℝ)) σ ≤ weightedCut (fun u v => (w u v : ℝ)) σ ∧
      weightedCut (fun u v => (w u v : ℝ)) σ -
        weightedCut (fun u v => (w' u v : ℝ)) σ ≤ Fintype.card I / (P : ℝ) := by
  dsimp only
  rw [aggregate_cut, Law.push_average, roundedWeights, aggregate_cut, Law.push_average,
    Law.grid_average _ _ _ _ (by simp)]
  exact Law.grid_average_bounds p P hP (fun i => if σ (query i).1 ≠ σ (query i).2 then 1 else 0)
    (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num)

 theorem roundedWeights_max_error {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (query : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) :
    let w := aggregate (p.push query)
    let w' := roundedWeights p query v0 P hP
    weightedMax (fun u v => (w' u v : ℝ)) ≤ weightedMax (fun u v => (w u v : ℝ)) ∧
      weightedMax (fun u v => (w u v : ℝ)) -
        weightedMax (fun u v => (w' u v : ℝ)) ≤ Fintype.card I / (P : ℝ) := by
  dsimp only
  obtain ⟨σ, hσ⟩ := weightedMax_attained (fun u v =>
    (roundedWeights p query v0 P hP u v : ℝ))
  obtain ⟨τ, hτ⟩ := weightedMax_attained (fun u v => (aggregate (p.push query) u v : ℝ))
  constructor
  · have h := (roundedWeights_cut_error p query v0 P hP σ).1
    exact hσ.symm.trans_le (h.trans (weightedCut_le_max _ _))
  · have h := (roundedWeights_cut_error p query v0 P hP τ).2
    have h' := weightedCut_le_max (fun u v => (roundedWeights p query v0 P hP u v : ℝ)) τ
    rw [hτ] at h
    linarith

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Sample
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.Game
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted
variable {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

 theorem gridWeights_error (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) :
    weightedMax (fun u v => (G.gridWeights t ht enum anchor K u v : ℝ)) ≤
      weightedMax (fun u v => (G.weights t ht enum u v : ℝ)) ∧
    weightedMax (fun u v => (G.weights t ht enum u v : ℝ)) -
      weightedMax (fun u v => (G.gridWeights t ht enum anchor K u v : ℝ)) ≤ 1/(K+1 : ℝ) := by
  have h := roundedWeights_max_error (G.sampleLaw t ht)
    (fun a => (enum (G.queries a).1, enum (G.queries a).2)) anchor
    (gridSize Y E q K) (gridSize_pos K)
  have hb : (Fintype.card (Sample Y E q) : ℝ) / gridSize Y E q K ≤ 1/(K+1 : ℝ) := by
    have hK : (0 : ℝ) < K+1 := by positivity
    have hC : (0 : ℝ) < Fintype.card (Sample Y E q)+1 := by positivity
    rw [gridSize, Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    apply (div_le_div_iff₀ (mul_pos hK hC) hK).mpr
    nlinarith
  exact ⟨h.1, h.2.trans hb⟩

 theorem gridOutput_error (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) :
    |((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) / (G.gridOutput t ht enum anchor K).scale -
      weightedMax (fun u v => (G.gridWeights t ht enum anchor K u v : ℝ))| ≤ 2/(K+1 : ℝ) := by
  simpa only [gridOutput, gridWeights, roundedWeights, Nat.cast_add, Nat.cast_one] using
    deterministicOutput_error (K+1) (by omega) _ (aggregate_symm _)
      (fun u v _ => aggregate_nonneg _ u v) (aggregate_total _)

 theorem gridOutput_complete (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ)
    (lx : X → Fin q) (ly : Y → Fin q) :
    (1+(t:ℝ))/2 - 2*(1-G.satisfied lx ly) - 3/(K+1 : ℝ) ≤
      ((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) / (G.gridOutput t ht enum anchor K).scale := by
  have hc := G.weightedMax_complete t ht enum lx ly
  have he := G.gridWeights_error t ht enum anchor K
  have hg := abs_le.mp (G.gridOutput_error t ht enum anchor K)
  linarith [show (3 : ℝ)/(K+1) = 1/(K+1) + 2/(K+1) by ring]

/-- All game-independent constants for the rounded, executable-integer target.
This is the mathematical gap; the polynomial TM printer is still separate. -/
 theorem exists_grid_gap_parameters (α : ℝ) (hα : alphaGW < α) (hα1 : α ≤ 1) :
    ∃ (t ε y n : ℚ) (δ : ℝ) (K : ℕ) (ht : t ∈ Set.Icc (-1 : ℚ) 1),
      0 < t ∧ t < 1 ∧ 0 < ε ∧ (ε:ℝ) < 1/2 ∧ 0 < δ ∧ δ < 1/2 ∧
      0 < y ∧ 0 ≤ n ∧ (n:ℝ) < α*(y:ℝ) ∧
      (∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}
        (G : Game X Y E q) (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N),
        (∃ lx ly, 1-(ε:ℝ) ≤ G.satisfied lx ly) →
        (y:ℝ) ≤ ((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) /
          (G.gridOutput t ht enum anchor K).scale) ∧
      (∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}
        (_hq : 0 < q) (G : Game X Y E q) (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N),
        G.Sound δ → ((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) /
          (G.gridOutput t ht enum anchor K).scale ≤ (n:ℝ)) := by
  obtain ⟨t, η, y, n, ht0, ht1, hη, hηb, hy, hypos, hn, hnlo, hgap⟩ :=
    exists_main_gap_parameters α hα hα1
  have hηr : 0 < (η:ℝ) := by exact_mod_cast hη
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht0
  have htR1 : (t:ℝ) < 1 := by exact_mod_cast ht1
  have hb : 0 ≤ borellCurve t := mul_nonneg (by positivity) (Real.arcsin_nonneg.mpr htR.le)
  have hηsmall : (η:ℝ) < 1/4 := by linarith
  obtain ⟨δ,hδ,hsound⟩ := exists_weighted_soundness t ht0 ht1 (η:ℝ) hηr
  obtain ⟨K,hlarge⟩ := exists_nat_gt (3/(η:ℝ))
  have hK : (0:ℝ) < K+1 := by positivity
  have hsmall : 3/(K+1:ℝ) ≤ (η:ℝ) := by
    have hm := (div_lt_iff₀ hηr).mp hlarge
    apply (div_le_iff₀ hK).mpr; nlinarith
  have hsmaller : 2/(K+1:ℝ) ≤ (η:ℝ) := by
    exact (div_le_div_of_nonneg_right (by norm_num) hK.le).trans hsmall
  let ht : t ∈ Set.Icc (-1:ℚ) 1 := ⟨by linarith, ht1.le⟩
  refine ⟨t,η/4,y,n,min δ (1/4),K,ht,ht0,ht1,by positivity,?_,
    lt_min hδ (by norm_num),?_,hypos,hn,hgap,?_,?_⟩
  · push_cast; linarith
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro X Y E _ _ _ q N G enum anchor hyes
    obtain ⟨lx,ly,hsat⟩ := hyes
    have hc := G.gridOutput_complete t ht enum anchor K lx ly
    have hyR : (y:ℝ) = (1+(t:ℝ))/2-2*(η:ℝ) := by exact_mod_cast hy
    push_cast at hsat; linarith
  · intro X Y E _ _ _ q N hq G enum anchor hs
    have hs' : G.Sound δ := fun lx ly => (hs lx ly).trans (min_le_left _ _)
    have h := hsound hq G enum hs'
    have he := G.gridWeights_error t ht enum anchor K
    have hg := abs_le.mp (G.gridOutput_error t ht enum anchor K)
    change (1+2/Real.pi*Real.arcsin (t:ℝ))/2+2*(η:ℝ) < (n:ℝ) at hnlo
    linarith

end OptimalMaxCut.LongCode.Game

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace OptimalMaxCut
open LongCode LongCode.InstanceAdapter
open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

/-- Optimal Max-Cut approximation hardness: for EVERY fixed real alpha above
the exact Goemans--Williamson constant, an ordinary binary polynomial reduction
prints a full finite SIMPLE UNWEIGHTED graph and a strict YES/NO optimum gap.
The construction uses an analytic inequality, rational long-code construction,
integer rounding, finite-field derandomization and a graph-printer TM. -/
theorem main_oai : MainStatement := by
  intro α ha ha1
  obtain ⟨t,ε,y,n,δ,K,ht,ht0,ht1,hε,hεhalf,hδ,hδhalf,hy,hn,hgap,hcomplete,hsound⟩ :=
    Game.exists_grid_gap_parameters α ha ha1
  obtain ⟨ug⟩ := MaxCutGames.theorem11 (ε : ℝ) δ (by exact_mod_cast hε)
    hεhalf hδ hδhalf
  obtain ⟨pc,hpc⟩ := exists_encoded_gridComputer ug.alphabet t ht K
  refine ⟨{
    yesBound := y
    noBound := n
    yes_pos := hy
    no_nonneg := hn
    gap := hgap
    construct := fun input => gridGraph (ug.construct input) t ht K
    computation := MachineSequential.composeBits ug.computation pc
    finiteAlphabet := MachineFiniteAlphabet.composeBits ug.computation pc ug.finiteAlphabet hpc
    completeness := ?_
    soundness := ?_ }⟩
  · intro input hin
    exact hcomplete (ofInstance (ug.construct input)) (vertexEquiv _ _) (anchor _)
      (InstanceAdapter.complete _ _ (ug.completeness input hin))
  · intro input hin
    exact hsound (by have := ug.alphabetAtLeastTwo; omega)
      (ofInstance (ug.construct input)) (vertexEquiv _ _) (anchor _)
      (InstanceAdapter.sound _ (ug.simpleBipartite input) _ (ug.soundness input hin))

end OptimalMaxCut

end

end OAI
end

theorem solution : type_of% @OAI.OptimalMaxCut.main_oai := @OAI.OptimalMaxCut.main_oai
