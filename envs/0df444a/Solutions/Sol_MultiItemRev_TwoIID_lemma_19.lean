-- Prove2me | solution 1 for MultiItemRev.TwoIID.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:13:07.921582+00:00
-- url     : https://prove2.me/submissions/04ee0689-46bb-4a6d-a11f-5a5a2f55d212

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory Set
open scoped NNReal ENNReal

namespace TwoIIDL19

open MultiItemRev.Decomp

theorem one_good_bound (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (Q S : ℝ≥0 → ℝ) (lam : ℝ)
    (hQ : ∀ y, 0 ≤ Q y ∧ Q y ≤ lam)
    (hIC : ∀ y y', Q y' * y - S y' ≤ Q y * y - S y) (hIR : ∀ y, 0 ≤ Q y * y - S y)
    (hS0 : ∀ y, 0 ≤ S y) (hSm : Measurable S) :
    ∫⁻ y, ENNReal.ofReal (S y) ∂ν ≤ ENNReal.ofReal lam * Rev1 ν := by
  have hlam0 : 0 ≤ lam := le_trans (hQ 0).1 (hQ 0).2
  rcases hlam0.eq_or_lt with h0 | hpos
  · have hS : ∀ y, S y = 0 := by
      intro y
      have hq : Q y = 0 := le_antisymm (h0 ▸ (hQ y).2) (hQ y).1
      have := hIR y
      rw [hq] at this
      linarith [hS0 y]
    simp [hS]
  · let M : Mechanism Unit := ⟨fun x _ => Q (x ()) / lam, fun x => S (x ()) / lam⟩
    have hadm : IsAdmissible M := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x i
        exact ⟨div_nonneg (hQ _).1 hpos.le, (div_le_one hpos).mpr (hQ _).2⟩
      · intro x x'
        simp only [buyerPayoff, Finset.univ_unique, Finset.sum_singleton, M]
        have := hIC (x default) (x' default)
        have e : ∀ a c : ℝ, a / lam * (x default : ℝ) - c / lam = (a * x default - c) / lam := by
          intro a c; field_simp
        rw [e, e]
        exact div_le_div_of_nonneg_right this hpos.le
      · intro x
        simp only [buyerPayoff, Finset.univ_unique, Finset.sum_singleton, M]
        have e : ∀ a c : ℝ, a / lam * (x default : ℝ) - c / lam = (a * x default - c) / lam := by
          intro a c; field_simp
        rw [e]
        exact div_nonneg (hIR _) hpos.le
      · exact (hSm.comp (measurable_pi_apply ())).div_const lam
    have hrev : (expRevenue (oneGood ν) M).toENNReal ≤ Rev1 ν :=
      le_iSup₂ (f := fun (M : Mechanism Unit) (_ : IsAdmissible M) =>
        (expRevenue (oneGood ν) M).toENNReal) M hadm
    have hmf : Measurable (fun t : ℝ≥0 => (fun _ : Unit => t)) := measurable_pi_lambda _
      (fun _ => measurable_id)
    have hexp : expRevenue (oneGood ν) M =
        ((∫⁻ y, ENNReal.ofReal (S y / lam) ∂ν : ℝ≥0∞) : EReal) := by
      unfold expRevenue oneGood
      have hs : Measurable M.s := (hSm.comp (measurable_pi_apply ())).div_const lam
      have h1 : Measurable (fun x : Unit → ℝ≥0 => ENNReal.ofReal (M.s x)) :=
        ENNReal.measurable_ofReal.comp hs
      have h2 : Measurable (fun x : Unit → ℝ≥0 => ENNReal.ofReal (-M.s x)) :=
        ENNReal.measurable_ofReal.comp hs.neg
      rw [lintegral_map h1 hmf, lintegral_map h2 hmf]
      have : ∫⁻ a, ENNReal.ofReal (-M.s (fun _ => a)) ∂ν = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        · apply ae_of_all
          intro a
          apply ENNReal.ofReal_of_nonpos
          simp only [M, neg_nonpos]
          exact div_nonneg (hS0 a) hpos.le
      rw [this]
      simp [M]
    rw [hexp, EReal.toENNReal_coe] at hrev
    calc ∫⁻ y, ENNReal.ofReal (S y) ∂ν
        = ∫⁻ y, ENNReal.ofReal lam * ENNReal.ofReal (S y / lam) ∂ν := by
          apply lintegral_congr
          intro y
          rw [← ENNReal.ofReal_mul hpos.le]
          congr 1
          field_simp
      _ = ENNReal.ofReal lam * ∫⁻ y, ENNReal.ofReal (S y / lam) ∂ν :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hSm.div_const lam))
      _ ≤ _ := by gcongr

end TwoIIDL19

open MultiItemRev.Decomp in
theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (x₀ : ℝ≥0) (hx₀ : ν {t | t < x₀} = 0)
    (M : MultiItemRev.Decomp.Mechanism Unit) (hM : MultiItemRev.TwoIID.IsAdmissible M) :
    MultiItemRev.TwoIID.expRevenue (MultiItemRev.Decomp.oneGood ν) M ≤
      ((1 - M.q (fun _ => x₀) () : ℝ) : EReal) * (MultiItemRev.Decomp.Rev1 ν : EReal) +
        (M.s (fun _ => x₀) : EReal) := by
  obtain ⟨hF, hIC, hIR, hsm⟩ := hM
  set qf : ℝ≥0 → ℝ := fun y => M.q (fun _ => y) () with hqf
  set sf : ℝ≥0 → ℝ := fun y => M.s (fun _ => y) with hsf
  set q0 := qf x₀ with hq0
  set c := sf x₀ with hc
  have hmf : Measurable (fun t : ℝ≥0 => (fun _ : Unit => t)) :=
    measurable_pi_lambda _ (fun _ => measurable_id)
  have hsfm : Measurable sf := hsm.comp hmf
  have ic : ∀ y y', qf y' * y - sf y' ≤ qf y * y - sf y := by
    intro y y'
    have h := hIC (fun _ => y) (fun _ => y')
    simpa only [buyerPayoff, Finset.univ_unique, Finset.sum_singleton] using h
  have hmono : Monotone qf := by
    intro y y' hyy
    have h1 := ic y' y
    have h2 := ic y y'
    have hyy' : (y : ℝ) ≤ y' := hyy
    rcases eq_or_lt_of_le hyy' with h | h
    · have : y = y' := by exact_mod_cast h
      rw [this]
    · by_contra hcon
      push_neg at hcon
      nlinarith [mul_pos (sub_pos.mpr hcon) (sub_pos.mpr h)]
  have hq01 : ∀ y, 0 ≤ qf y ∧ qf y ≤ 1 := fun y => hF _ ()
  set T : Set ℝ≥0 := {y | x₀ ≤ y} with hT
  have hTm : MeasurableSet T := measurableSet_Ici
  set lam := 1 - q0 with hlam
  set S : ℝ≥0 → ℝ := fun y => T.indicator (fun y => sf y - c) y with hS
  have hSlow : ∀ y, (qf y - q0) * x₀ ≤ sf y - c := by
    intro y
    have := ic x₀ y
    linarith
  have hbound := TwoIIDL19.one_good_bound ν (fun y => T.indicator (fun y => qf y - q0) y) S lam
    (by
      intro y
      by_cases hy : y ∈ T
      · simp only [indicator_of_mem hy]
        have := hmono (show x₀ ≤ y from hy)
        constructor <;> linarith [(hq01 y).2]
      · simp only [indicator_of_notMem hy]
        constructor <;> linarith [(hq01 x₀).2])
    (by
      intro y y'
      by_cases hy : y ∈ T <;> by_cases hy' : y' ∈ T
      · simp only [hS, indicator_of_mem hy, indicator_of_mem hy']
        linarith [ic y y']
      · simp only [hS, indicator_of_mem hy, indicator_of_notMem hy']
        linarith [ic y x₀]
      · simp only [hS, indicator_of_notMem hy, indicator_of_mem hy']
        have h1 := hmono (show x₀ ≤ y' from hy')
        have h2 : (y : ℝ) ≤ x₀ := le_of_lt (not_le.mp hy)
        nlinarith [mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr h1), hSlow y']
      · simp only [hS, indicator_of_notMem hy, indicator_of_notMem hy']
        linarith)
    (by
      intro y
      by_cases hy : y ∈ T
      · simp only [hS, indicator_of_mem hy]
        linarith [ic y x₀]
      · simp only [hS, indicator_of_notMem hy]
        linarith)
    (by
      intro y
      by_cases hy : y ∈ T
      · simp only [hS, indicator_of_mem hy]
        have := hmono (show x₀ ≤ y from hy)
        nlinarith [hSlow y, mul_nonneg (sub_nonneg.mpr this) x₀.2]
      · simp only [hS, indicator_of_notMem hy]
        exact le_rfl)
    ((hsfm.sub_const c).indicator hTm)
  have hS0 : ∀ y, 0 ≤ S y := by
    intro y
    by_cases hy : y ∈ T
    · simp only [hS, indicator_of_mem hy]
      have := hmono (show x₀ ≤ y from hy)
      nlinarith [hSlow y, mul_nonneg (sub_nonneg.mpr this) x₀.2]
    · simp only [hS, indicator_of_notMem hy]
      exact le_rfl
  have hSm : Measurable S := (hsfm.sub_const c).indicator hTm
  -- a.e. `s = S + c`
  have hae : ∀ᵐ y ∂ν, sf y = S y + c := by
    have : ∀ᵐ y ∂ν, y ∈ T := by
      rw [ae_iff]
      have e : {a | ¬ a ∈ T} = {t | t < x₀} := by
        ext a; simp [hT]
      rw [e]; exact hx₀
    filter_upwards [this] with y hy
    simp only [hS, indicator_of_mem hy]
    ring
  -- expected revenue as integrals over ν
  have hexp : MultiItemRev.TwoIID.expRevenue (oneGood ν) M =
      ((∫⁻ y, ENNReal.ofReal (sf y) ∂ν : ℝ≥0∞) : EReal) -
        ((∫⁻ y, ENNReal.ofReal (-sf y) ∂ν : ℝ≥0∞) : EReal) := by
    unfold MultiItemRev.TwoIID.expRevenue oneGood
    have h1 : Measurable (fun x : Unit → ℝ≥0 => ENNReal.ofReal (M.s x)) :=
      ENNReal.measurable_ofReal.comp hsm
    have h2 : Measurable (fun x : Unit → ℝ≥0 => ENNReal.ofReal (-M.s x)) :=
      ENNReal.measurable_ofReal.comp hsm.neg
    rw [lintegral_map h1 hmf, lintegral_map h2 hmf]
  rw [hexp]
  set K := ∫⁻ y, ENNReal.ofReal (S y) ∂ν with hK
  have hlam0 : 0 ≤ lam := by linarith [(hq01 x₀).2]
  by_cases htop : ENNReal.ofReal lam * Rev1 ν = ⊤
  · -- right-hand side is `⊤`
    have hR : Rev1 ν = ⊤ := by
      by_contra h
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h htop
    have hlpos : 0 < lam := by
      by_contra h
      push_neg at h
      have : lam = 0 := le_antisymm h hlam0
      rw [this, ENNReal.ofReal_zero, zero_mul] at htop
      exact ENNReal.zero_ne_top htop
    rw [hR, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos hlpos, EReal.top_add_coe]
    exact le_top
  have hKne : K ≠ ⊤ := ne_top_of_le_ne_top htop hbound
  have hSint : Integrable S ν := by
    have h := integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hSm).aemeasurable hKne
    refine h.congr (ae_of_all _ (fun y => ?_))
    simp only [Function.comp, ENNReal.toReal_ofReal (hS0 y)]
  have hsint : Integrable sf ν := (hSint.add (integrable_const c)).congr
    (by filter_upwards [hae] with y hy; rw [hy]; rfl)
  have hp := hsint.lintegral_lt_top
  have hn : ∫⁻ y, ENNReal.ofReal (-sf y) ∂ν < ⊤ := hsint.neg.lintegral_lt_top
  rw [← EReal.coe_ennreal_toReal hp.ne, ← EReal.coe_ennreal_toReal hn.ne, ← EReal.coe_sub]
  have hI : (∫⁻ y, ENNReal.ofReal (sf y) ∂ν).toReal - (∫⁻ y, ENNReal.ofReal (-sf y) ∂ν).toReal =
      K.toReal + c := by
    have := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hsint
    rw [← this, integral_congr_ae hae, integral_add hSint (integrable_const c), integral_const,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hS0) hSm.aestronglyMeasurable]
    simp
    rfl
  rw [hI, EReal.coe_add]
  have hKle : ((K.toReal : ℝ) : EReal) ≤ ((lam : ℝ) : EReal) * ((Rev1 ν : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_toReal hKne]
    have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hbound
    rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hlam0] at h
    exact h
  exact add_le_add_left hKle _
