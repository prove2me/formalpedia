-- Prove2me | solution 1 for MastSail.Monotone.hazard_le_density
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:48:33.495179+00:00
-- url     : https://prove2.me/submissions/541489fd-904b-497b-ab4a-5915d456f402

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone

open MeasureTheory

lemma hazard_aux (M : Model) (hM : M.Standing) (i : ℝ) (hi : i ∈ Set.Icc 0 M.Ibar) :
    (1 - cdf M.gL i) / (1 - cdf M.gH i) ≤ M.gL i / M.gH i ∧
    (M.StrictMLRPg → (1 - cdf M.gL i) / (1 - cdf M.gH i) < M.gL i / M.gH i) := by
  obtain ⟨hI0, hIQ, -, -, ⟨hgLc, hgLp, hgL1⟩, ⟨hgHc, hgHp, hgH1⟩, -, hg⟩ := hM
  have hQ : 0 ≤ M.Qbar := by linarith
  have hi0 : 0 ≤ i := hi.1
  have hiQ : i < M.Qbar := by linarith [hi.2]
  have intL : IntervalIntegrable M.gL volume 0 M.Qbar :=
    hgLc.intervalIntegrable_of_Icc hQ
  have intH : IntervalIntegrable M.gH volume 0 M.Qbar :=
    hgHc.intervalIntegrable_of_Icc hQ
  have sub : Set.uIcc i M.Qbar ⊆ Set.uIcc 0 M.Qbar := by
    rw [Set.uIcc_of_le hiQ.le, Set.uIcc_of_le hQ]
    exact Set.Icc_subset_Icc hi0 le_rfl
  have sub' : Set.uIcc 0 i ⊆ Set.uIcc 0 M.Qbar := by
    rw [Set.uIcc_of_le hi0, Set.uIcc_of_le hQ]
    exact Set.Icc_subset_Icc le_rfl hiQ.le
  have eL : 1 - cdf M.gL i = ∫ x in i..M.Qbar, M.gL x := by
    unfold cdf; rw [← hgL1]
    exact intervalIntegral.integral_interval_sub_left intL (intL.mono_set sub')
  have eH : 1 - cdf M.gH i = ∫ x in i..M.Qbar, M.gH x := by
    unfold cdf; rw [← hgH1]
    exact intervalIntegral.integral_interval_sub_left intH (intH.mono_set sub')
  have posH : 0 < ∫ x in i..M.Qbar, M.gH x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (intH.mono_set sub) _ hiQ
    intro x hx
    exact hgHp x ⟨by linarith [hx.1], hx.2.le⟩
  have hiQ' : i ∈ Set.Icc 0 M.Qbar := ⟨hi0, hiQ.le⟩
  set r := M.gL i / M.gH i
  have iL := intL.mono_set sub
  have iH := (intH.mono_set sub).const_mul r
  rw [eL, eH, div_le_iff₀ posH, div_lt_iff₀ posH]
  constructor
  · have hle : ∫ x in i..M.Qbar, M.gL x ≤ ∫ x in i..M.Qbar, r * M.gH x := by
      apply intervalIntegral.integral_mono_on hiQ.le iL iH
      intro x hx
      have hx0 : x ∈ Set.Icc 0 M.Qbar := ⟨by linarith [hx.1], hx.2⟩
      have hpos := hgHp x hx0
      have : M.gL x / M.gH x ≤ r := hg hiQ' hx0 hx.1
      rw [div_le_iff₀ hpos] at this
      linarith
    rw [intervalIntegral.integral_const_mul] at hle
    linarith
  · intro hs
    have hlt : 0 < ∫ x in i..M.Qbar, (r * M.gH x - M.gL x) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on (iH.sub iL) _ hiQ
      intro x hx
      have hx0 : x ∈ Set.Icc 0 M.Qbar := ⟨by linarith [hx.1], hx.2.le⟩
      have hpos := hgHp x hx0
      have : M.gL x / M.gH x < r := hs hiQ' hx0 hx.1
      rw [div_lt_iff₀ hpos] at this
      linarith
    rw [intervalIntegral.integral_sub iH iL, intervalIntegral.integral_const_mul] at hlt
    linarith

end MastSail.Monotone

open MastSail.Monotone in
theorem solution (M : Model) (hM : M.Standing) :
    (∀ i ∈ Set.Icc 0 M.Ibar, (1 - cdf M.gL i) / (1 - cdf M.gH i) ≤ M.gL i / M.gH i) ∧
    (M.StrictMLRPg →
      ∀ i ∈ Set.Icc 0 M.Ibar, (1 - cdf M.gL i) / (1 - cdf M.gH i) < M.gL i / M.gH i) :=
  ⟨fun i hi => (hazard_aux M hM i hi).1, fun hs i hi => (hazard_aux M hM i hi).2 hs⟩
