-- Prove2me | solution 1 for MultiItemRev.TwoIID.display_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:09:47.226884+00:00
-- url     : https://prove2.me/submissions/0a3a9577-109b-41a5-a279-a62f08917430

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model
import Theorems.Thm_MultiItemRev_TwoIID_diagonal_allocation_monotone

open MeasureTheory Set
open scoped NNReal ENNReal

namespace TwoIIDD12

open MultiItemRev.Decomp

/-- The valuation `(y, z)`. -/
def pt (y z : ℝ≥0) : Fin 2 → ℝ≥0 := ![y, z]

@[simp] lemma pt0 (y z : ℝ≥0) : pt y z 0 = y := rfl
@[simp] lemma pt1 (y z : ℝ≥0) : pt y z 1 = z := rfl

lemma diag_eq (t : ℝ≥0) : MultiItemRev.TwoIID.diag t = pt t t := by
  funext i; fin_cases i <;> rfl

lemma swap_pt (y z : ℝ≥0) : MultiItemRev.TwoIID.swap2 (pt y z) = pt z y := by
  funext i; fin_cases i <;> rfl

lemma measurable_pt : Measurable (fun p : ℝ≥0 × ℝ≥0 => pt p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact measurable_fst
  · exact measurable_snd

/-- IC written in coordinates. -/
lemma ic_pt (M : Mechanism (Fin 2)) (hIC : IsIC M) (a b c d : ℝ≥0) :
    M.q (pt c d) 0 * a + M.q (pt c d) 1 * b - M.s (pt c d) ≤
      M.q (pt a b) 0 * a + M.q (pt a b) 1 * b - M.s (pt a b) := by
  have h := hIC (pt a b) (pt c d)
  simpa only [buyerPayoff, Fin.sum_univ_two, pt0, pt1] using h

lemma payoff_pt (M : Mechanism (Fin 2)) (a b : ℝ≥0) :
    buyerPayoff M (pt a b) = M.q (pt a b) 0 * a + M.q (pt a b) 1 * b - M.s (pt a b) := by
  simp only [buyerPayoff, Fin.sum_univ_two, pt0, pt1]

/-- A one-good mechanism (given by `Q, S` on `ℝ≥0`) that is IC, IR, NPT, measurable, with
allocation in `[0, λ]`, earns at most `λ · Rev(ν)`. -/
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


lemma q2_diag (M : Mechanism (Fin 2)) (hSym : MultiItemRev.TwoIID.IsSymmetric M) (t : ℝ≥0) :
    M.q (pt t t) 1 = M.q (pt t t) 0 := by
  have := (hSym (pt t t)).1
  rw [swap_pt] at this
  exact this.symm

lemma s_symm (M : Mechanism (Fin 2)) (hSym : MultiItemRev.TwoIID.IsSymmetric M) (y z : ℝ≥0) :
    M.s (pt y z) = M.s (pt z y) := by
  have := (hSym (pt y z)).2
  rwa [swap_pt] at this

/-- `D_z(y) = s^z(y) - s^z(z)` where `s^z(y) = s(y,z) - q₂(y,z) z`. -/
noncomputable def Dfun (M : Mechanism (Fin 2)) (z y : ℝ≥0) : ℝ :=
  M.s (pt y z) - M.q (pt y z) 1 * z - (M.s (pt z z) - z * M.q (pt z z) 0)

lemma q1_mono (M : Mechanism (Fin 2)) (hIC : IsIC M) (z : ℝ≥0) :
    Monotone (fun y => M.q (pt y z) 0) := by
  intro y y' hyy
  have h1 := ic_pt M hIC y' z y z
  have h2 := ic_pt M hIC y z y' z
  have hyy' : (y : ℝ) ≤ y' := hyy
  rcases eq_or_lt_of_le hyy' with h | h
  · have : y = y' := by exact_mod_cast h
    rw [this]
  · by_contra hc
    push_neg at hc
    nlinarith [mul_pos (sub_pos.mpr hc) (sub_pos.mpr h)]

lemma D_lower (M : Mechanism (Fin 2)) (hIC : IsIC M) (hSym : MultiItemRev.TwoIID.IsSymmetric M)
    (z y : ℝ≥0) : (M.q (pt y z) 0 - M.q (pt z z) 0) * z ≤ Dfun M z y := by
  have h := ic_pt M hIC z z y z
  have e := q2_diag M hSym z
  unfold Dfun
  rw [e] at h
  nlinarith

lemma D_measurable (M : Mechanism (Fin 2)) (hF : IsFeasible M) (hIC : IsIC M) (z : ℝ≥0) :
    Measurable (fun y => Dfun M z y) := by
  set bz : ℝ≥0 → ℝ := fun y => M.q (pt y z) 0 * y + M.q (pt y z) 1 * z - M.s (pt y z) with hbz
  have hq1 : Measurable (fun y => M.q (pt y z) 0) := (q1_mono M hIC z).measurable
  have hlip : LipschitzWith 1 bz := by
    apply LipschitzWith.mk_one
    intro y y'
    rw [Real.dist_eq, NNReal.dist_eq]
    have h1 := ic_pt M hIC y' z y z
    have h2 := ic_pt M hIC y z y' z
    have f1 := hF (pt y z) 0
    have f2 := hF (pt y' z) 0
    simp only [hbz]
    rw [abs_le]
    rcases le_total (y : ℝ) y' with h | h
    · rw [abs_of_nonpos (by linarith)]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right f1.2 (sub_nonneg.mpr h),
        mul_le_mul_of_nonneg_right f2.2 (sub_nonneg.mpr h),
        mul_nonneg f1.1 (sub_nonneg.mpr h), mul_nonneg f2.1 (sub_nonneg.mpr h)]
    · rw [abs_of_nonneg (by linarith)]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right f1.2 (sub_nonneg.mpr h),
        mul_le_mul_of_nonneg_right f2.2 (sub_nonneg.mpr h),
        mul_nonneg f1.1 (sub_nonneg.mpr h), mul_nonneg f2.1 (sub_nonneg.mpr h)]
  have hb : Measurable bz := hlip.continuous.measurable
  have e : (fun y => Dfun M z y) = fun y =>
      M.q (pt y z) 0 * y - bz y - (M.s (pt z z) - z * M.q (pt z z) 0) := by
    funext y; simp only [Dfun, hbz]; ring
  rw [e]
  exact ((hq1.mul measurable_coe_nnreal_real).sub hb).sub_const _

/-- For fixed `z`, the bound `E[(s^z(Y) - s^z(z)) 1_{Y ∈ T}] ≤ (1 - φ(z)) Rev(Y)`
(Lemma 19 combined with `Rev(Y^z) ≤ r / P[Y ≥ z]`). -/
theorem per_z (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (M : Mechanism (Fin 2))
    (hF : IsFeasible M) (hIC : IsIC M) (hSym : MultiItemRev.TwoIID.IsSymmetric M)
    (z : ℝ≥0) (T : Set ℝ≥0) (hTm : MeasurableSet T) (hT1 : ∀ y ∈ T, z ≤ y)
    (hT2 : ∀ y ∉ T, y ≤ z) :
    ∫⁻ y, T.indicator (fun y => ENNReal.ofReal (Dfun M z y)) y ∂ν ≤
      ENNReal.ofReal (1 - M.q (pt z z) 0) * Rev1 ν := by
  set φz := M.q (pt z z) 0 with hφz
  have hmono := q1_mono M hIC z
  have e2 := q2_diag M hSym z
  have hφz1 : φz ≤ 1 := (hF (pt z z) 0).2
  have hconv : ∀ y, T.indicator (fun y => ENNReal.ofReal (Dfun M z y)) y =
      ENNReal.ofReal (T.indicator (fun y => Dfun M z y) y) := by
    intro y
    by_cases hy : y ∈ T
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, ENNReal.ofReal_zero]
  simp_rw [hconv]
  apply one_good_bound ν (fun y => T.indicator (fun y => M.q (pt y z) 0 - φz) y)
    (fun y => T.indicator (fun y => Dfun M z y) y) (1 - φz)
  · intro y
    by_cases hy : y ∈ T
    · simp only [indicator_of_mem hy]
      have := hmono (hT1 y hy)
      have := (hF (pt y z) 0).2
      simp only at *
      constructor <;> linarith
    · simp only [indicator_of_notMem hy]
      constructor <;> linarith
  · intro y y'
    have hD := D_lower M hIC hSym z y'
    by_cases hy : y ∈ T <;> by_cases hy' : y' ∈ T
    · simp only [indicator_of_mem hy, indicator_of_mem hy', Dfun]
      have := ic_pt M hIC y z y' z
      linarith
    · simp only [indicator_of_mem hy, indicator_of_notMem hy', Dfun]
      have := ic_pt M hIC y z z z
      rw [e2] at this
      linarith
    · simp only [indicator_of_notMem hy, indicator_of_mem hy']
      have h1 := hmono (hT1 y' hy')
      have h2 := hT2 y hy
      simp only at h1
      have h2' : (y : ℝ) ≤ z := h2
      nlinarith [mul_le_mul_of_nonneg_left h2' (sub_nonneg.mpr h1)]
    · simp only [indicator_of_notMem hy, indicator_of_notMem hy']
      linarith
  · intro y
    by_cases hy : y ∈ T
    · simp only [indicator_of_mem hy, Dfun]
      have := ic_pt M hIC y z z z
      rw [e2] at this
      linarith
    · simp only [indicator_of_notMem hy]
      linarith
  · intro y
    by_cases hy : y ∈ T
    · simp only [indicator_of_mem hy]
      have hD := D_lower M hIC hSym z y
      have h1 := hmono (hT1 y hy)
      simp only at h1
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) z.2]
    · simp only [indicator_of_notMem hy]
      exact le_rfl
  · exact (D_measurable M hF hIC z).indicator hTm

/-- Pointwise: on the region `z ≤ y`, `s(y,z) ≤ D_z(y) + V(y,z)`. -/
theorem s_le_D_add_V (M : Mechanism (Fin 2)) (hIC : IsIC M)
    (hSym : MultiItemRev.TwoIID.IsSymmetric M) (y z : ℝ≥0) (hzy : z ≤ y) :
    M.s (pt y z) ≤ Dfun M z y +
      (((min y z : ℝ≥0) : ℝ) * M.q (pt y y) 0 + ((min y z : ℝ≥0) : ℝ) * M.q (pt z z) 0 -
        buyerPayoff M (pt (min y z) (min y z))) := by
  rw [min_eq_right hzy, payoff_pt, q2_diag M hSym z]
  unfold Dfun
  have h1 := ic_pt M hIC y y y z
  have h2 := ic_pt M hIC y z y y
  have e := q2_diag M hSym y
  rw [e] at h1 h2
  have hzy' : (z : ℝ) ≤ y := hzy
  have key : M.q (pt y z) 1 * z ≤ M.q (pt y y) 0 * z := by
    rcases eq_or_lt_of_le hzy' with h | h
    · have : z = y := by exact_mod_cast h
      rw [this]
      rw [e]
    · have : M.q (pt y z) 1 ≤ M.q (pt y y) 0 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos (sub_pos.mpr hc) (sub_pos.mpr h)]
      exact mul_le_mul_of_nonneg_right this z.2
  linarith


end TwoIIDD12

open MultiItemRev.Decomp TwoIIDD12 in
theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (M : MultiItemRev.Decomp.Mechanism (Fin 2))
    (hM : MultiItemRev.TwoIID.IsAdmissible M ∧ MultiItemRev.Decomp.IsNPT M)
    (hSym : MultiItemRev.TwoIID.IsSymmetric M) (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) :
    let μ := Measure.pi (fun _ : Fin 2 => ν)
    let r := (MultiItemRev.Decomp.Rev1 ν).toReal
    MultiItemRev.TwoIID.expRevenue μ M ≤
      ((2 * r - 2 * r * ∫ t, M.q (MultiItemRev.TwoIID.diag t) 0 ∂ν : ℝ) : EReal) +
        2 * ((∫⁻ x, ENNReal.ofReal
          (((min (x 0) (x 1) : ℝ≥0) : ℝ) * M.q (MultiItemRev.TwoIID.diag (x 0)) 0 -
            MultiItemRev.Decomp.buyerPayoff M
              (MultiItemRev.TwoIID.diag (min (x 0) (x 1))) / 2) ∂μ : ℝ≥0∞) : EReal) := by
  intro μ r
  obtain ⟨⟨hF, hIC, hIR, hsm⟩, hNPT⟩ := hM
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  set φ : ℝ≥0 → ℝ := fun t => M.q (pt t t) 0 with hφdef
  have hφdiag : ∀ t, M.q (MultiItemRev.TwoIID.diag t) 0 = φ t := fun t => by
    rw [diag_eq]
  have hφmono : Monotone φ := by
    have := (MultiItemRev.TwoIID.diagonal_allocation_monotone M hF hIC hSym).1
    intro a b hab
    have h := this hab
    simp only [hφdiag] at h
    exact h
  have hφ01 : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1 := fun t => hF _ 0
  have hφm : Measurable φ := hφmono.measurable
  set P := ν.prod ν with hP
  -- change of variables `μ ↔ ν ⊗ ν`
  have hconv : ∀ f : (Fin 2 → ℝ≥0) → ℝ≥0∞, ∫⁻ x, f x ∂μ = ∫⁻ p, f (pt p.1 p.2) ∂P := by
    intro f
    have hmp := measurePreserving_finTwoArrow ν
    rw [MeasurePreserving.lintegral_map_equiv f MeasurableEquiv.finTwoArrow.symm hmp.symm]
    apply lintegral_congr
    intro a
    rfl
  have hswap : ∀ g : ℝ≥0 × ℝ≥0 → ℝ≥0∞, ∫⁻ p, g p ∂P = ∫⁻ p, g p.swap ∂P := by
    intro g
    exact MeasurePreserving.lintegral_map_equiv g MeasurableEquiv.prodComm
      (Measure.measurePreserving_swap)
  -- measurability
  have hptm := measurable_pt
  have hsP : Measurable (fun p : ℝ≥0 × ℝ≥0 => M.s (pt p.1 p.2)) := hsm.comp hptm
  have hgm : Measurable (fun t : ℝ≥0 => buyerPayoff M (pt t t)) := by
    have e : (fun t : ℝ≥0 => buyerPayoff M (pt t t)) =
        fun t => φ t * t + φ t * t - M.s (pt t t) := by
      funext t; rw [payoff_pt, q2_diag M hSym]
    rw [e]
    have hst : Measurable (fun t : ℝ≥0 => M.s (pt t t)) :=
      hsm.comp (hptm.comp (measurable_id.prodMk measurable_id))
    exact ((hφm.mul measurable_coe_nnreal_real).add (hφm.mul measurable_coe_nnreal_real)).sub hst
  set mn : ℝ≥0 × ℝ≥0 → ℝ≥0 := fun p => min p.1 p.2 with hmn
  have hmnm : Measurable mn := measurable_fst.min measurable_snd
  set V : ℝ≥0 × ℝ≥0 → ℝ := fun p => ((mn p : ℝ≥0) : ℝ) * φ p.1 + ((mn p : ℝ≥0) : ℝ) * φ p.2 -
    buyerPayoff M (pt (mn p) (mn p)) with hV
  set W : ℝ≥0 × ℝ≥0 → ℝ := fun p => ((mn p : ℝ≥0) : ℝ) * φ p.1 -
    buyerPayoff M (pt (mn p) (mn p)) / 2 with hW
  have hVm : Measurable V := by
    have h1 : Measurable (fun p : ℝ≥0 × ℝ≥0 => ((mn p : ℝ≥0) : ℝ)) := hmnm.coe_nnreal_real
    exact ((h1.mul (hφm.comp measurable_fst)).add (h1.mul (hφm.comp measurable_snd))).sub
      (hgm.comp hmnm)
  have hWm : Measurable W := by
    have h1 : Measurable (fun p : ℝ≥0 × ℝ≥0 => ((mn p : ℝ≥0) : ℝ)) := hmnm.coe_nnreal_real
    exact (h1.mul (hφm.comp measurable_fst)).sub ((hgm.comp hmnm).div_const 2)
  have hVsym : ∀ p : ℝ≥0 × ℝ≥0, V p.swap = V p := by
    intro p
    simp only [hV, hmn, Prod.fst_swap, Prod.snd_swap, min_comm p.2 p.1]
    ring
  have hVW : ∀ p : ℝ≥0 × ℝ≥0, V p = W p + W p.swap := by
    intro p
    simp only [hV, hW, hmn, Prod.fst_swap, Prod.snd_swap, min_comm p.2 p.1]
    ring
  set A : Set (ℝ≥0 × ℝ≥0) := {p | p.2 ≤ p.1} with hA
  set B : Set (ℝ≥0 × ℝ≥0) := {p | p.2 < p.1} with hB
  have hAm : MeasurableSet A := measurableSet_le measurable_snd measurable_fst
  have hBm : MeasurableSet B := measurableSet_lt measurable_snd measurable_fst
  set oS : ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (M.s (pt p.1 p.2)) with hoS
  set oD : ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (Dfun M p.2 p.1) with hoD
  set oV : ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (V p) with hoV
  set oW : ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (W p) with hoW
  have hoVm : Measurable oV := ENNReal.measurable_ofReal.comp hVm
  have hoWm : Measurable oW := ENNReal.measurable_ofReal.comp hWm
  have hoSm : Measurable oS := ENNReal.measurable_ofReal.comp hsP
  -- S1 + S2: split into the two regions
  have hS12 : ∫⁻ p, oS p ∂P = ∫⁻ p, A.indicator oS p ∂P + ∫⁻ p, B.indicator oS p ∂P := by
    rw [← lintegral_add_compl oS hAm, lintegral_indicator hAm]
    congr 1
    rw [← lintegral_indicator hAm.compl, hswap]
    apply lintegral_congr
    intro p
    by_cases hp : p.2 < p.1
    · have h1 : p.swap ∈ Aᶜ := by simp [hA, hp]
      rw [indicator_of_mem h1, indicator_of_mem (show p ∈ B from hp)]
      simp only [hoS, Prod.fst_swap, Prod.snd_swap]
      rw [s_symm M hSym]
    · have h1 : p.swap ∉ Aᶜ := by simp [hA]; push_neg at hp; exact hp
      rw [indicator_of_notMem h1, indicator_of_notMem (show p ∉ B from hp)]
  -- S3: pointwise bound on a region inside `A`
  have hS3 : ∀ X : Set (ℝ≥0 × ℝ≥0), MeasurableSet X → X ⊆ A →
      ∫⁻ p, X.indicator oS p ∂P ≤ ∫⁻ p, X.indicator oD p ∂P + ∫⁻ p, X.indicator oV p ∂P := by
    intro X hXm hXA
    rw [← lintegral_add_right _ (hoVm.indicator hXm)]
    apply lintegral_mono
    intro p
    by_cases hp : p ∈ X
    · simp only [indicator_of_mem hp, hoS, hoD, hoV]
      have h := s_le_D_add_V M hIC hSym p.1 p.2 (hXA hp)
      calc ENNReal.ofReal (M.s (pt p.1 p.2)) ≤ ENNReal.ofReal (Dfun M p.2 p.1 + V p) :=
            ENNReal.ofReal_le_ofReal h
        _ ≤ _ := ENNReal.ofReal_add_le
    · simp only [indicator_of_notMem hp]
      simp
  -- S4: the `D` part
  have hint1 : ∫ z, φ z ∂ν ≤ 1 := by
    calc ∫ z, φ z ∂ν ≤ ∫ _z, (1 : ℝ) ∂ν :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => (hφ01 z).1)) (integrable_const _)
            (ae_of_all _ (fun z => (hφ01 z).2))
      _ = 1 := by simp
  have hφint : Integrable φ ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hφm.aestronglyMeasurable ?_
    apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 t).1]
    exact (hφ01 t).2
  have hS4 : ∀ (X : Set (ℝ≥0 × ℝ≥0)) (T : ℝ≥0 → Set ℝ≥0), (∀ z, MeasurableSet (T z)) →
      (∀ z y, (y, z) ∈ X ↔ y ∈ T z) → (∀ z, ∀ y ∈ T z, z ≤ y) → (∀ z, ∀ y ∉ T z, y ≤ z) →
      ∫⁻ p, X.indicator oD p ∂P ≤ ENNReal.ofReal (r - r * ∫ z, φ z ∂ν) := by
    intro X T hTm hXT hT1 hT2
    rw [hswap]
    calc ∫⁻ p, X.indicator oD p.swap ∂P
        ≤ ∫⁻ z, ∫⁻ y, X.indicator oD (z, y).swap ∂ν ∂ν :=
          lintegral_prod_le (fun p => X.indicator oD p.swap)
      _ = ∫⁻ z, ∫⁻ y, (T z).indicator (fun y => ENNReal.ofReal (Dfun M z y)) y ∂ν ∂ν := by
          apply lintegral_congr; intro z
          apply lintegral_congr; intro y
          simp only [Prod.swap_prod_mk]
          by_cases hy : y ∈ T z
          · rw [indicator_of_mem ((hXT z y).mpr hy), indicator_of_mem hy]
          · rw [indicator_of_notMem (fun h => hy ((hXT z y).mp h)), indicator_of_notMem hy]
      _ ≤ ∫⁻ z, ENNReal.ofReal (1 - M.q (pt z z) 0) * Rev1 ν ∂ν := by
          apply lintegral_mono; intro z
          exact per_z ν M hF hIC hSym z (T z) (hTm z) (hT1 z) (hT2 z)
      _ = ∫⁻ z, ENNReal.ofReal ((1 - φ z) * r) ∂ν := by
          apply lintegral_congr; intro z
          rw [ENNReal.ofReal_mul (by linarith [(hφ01 z).2]), ENNReal.ofReal_toReal hr]
      _ = ENNReal.ofReal (∫ z, (1 - φ z) * r ∂ν) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact ((integrable_const 1).sub hφint).mul_const r
          · exact ae_of_all _ (fun z => mul_nonneg (by linarith [(hφ01 z).2]) hr0)
      _ = ENNReal.ofReal (r - r * ∫ z, φ z ∂ν) := by
          congr 1
          rw [integral_mul_const, integral_sub (integrable_const 1) hφint]
          simp
          ring
  -- S5: the `V` part
  have hS5 : ∫⁻ p, A.indicator oV p ∂P + ∫⁻ p, B.indicator oV p ∂P ≤ 2 * ∫⁻ p, oW p ∂P := by
    have e1 : ∫⁻ p, B.indicator oV p ∂P = ∫⁻ p, Aᶜ.indicator oV p ∂P := by
      rw [hswap]
      apply lintegral_congr
      intro p
      by_cases hp : p.1 < p.2
      · have h1 : p.swap ∈ B := by simp [hB, hp]
        have h2 : p ∈ Aᶜ := by simp [hA, hp]
        rw [indicator_of_mem h1, indicator_of_mem h2]
        simp only [hoV]
        rw [hVsym]
      · have h1 : p.swap ∉ B := by simpa [hB] using hp
        have h2 : p ∉ Aᶜ := by simp [hA]; push_neg at hp; exact hp
        rw [indicator_of_notMem h1, indicator_of_notMem h2]
    rw [e1, lintegral_indicator hAm, lintegral_indicator hAm.compl, lintegral_add_compl _ hAm]
    calc ∫⁻ p, oV p ∂P ≤ ∫⁻ p, (oW p + oW p.swap) ∂P := by
          apply lintegral_mono
          intro p
          simp only [hoV, hoW]
          rw [hVW]
          exact ENNReal.ofReal_add_le
      _ = ∫⁻ p, oW p ∂P + ∫⁻ p, oW p.swap ∂P := lintegral_add_left hoWm _
      _ = 2 * ∫⁻ p, oW p ∂P := by rw [← hswap, two_mul]
  -- S6: combine
  have hT_A : ∀ z y, (y, z) ∈ A ↔ y ∈ {y : ℝ≥0 | z ≤ y} := fun z y => Iff.rfl
  have hT_B : ∀ z y, (y, z) ∈ B ↔ y ∈ {y : ℝ≥0 | z < y} := fun z y => Iff.rfl
  have hDA := hS4 A (fun z => {y | z ≤ y}) (fun z => measurableSet_Ici) hT_A
    (fun z y hy => hy) (fun z y hy => le_of_lt (not_le.mp hy))
  have hDB := hS4 B (fun z => {y | z < y}) (fun z => measurableSet_Ioi) hT_B
    (fun z y hy => le_of_lt hy) (fun z y hy => not_lt.mp hy)
  have hA3 := hS3 A hAm subset_rfl
  have hB3 := hS3 B hBm (fun p (hp : p.2 < p.1) => (le_of_lt hp : p.2 ≤ p.1))
  have hE : ∫⁻ p, oS p ∂P ≤ ENNReal.ofReal (2 * r - 2 * r * ∫ z, φ z ∂ν) + 2 * ∫⁻ p, oW p ∂P := by
    have hnn : 0 ≤ r - r * ∫ z, φ z ∂ν := by nlinarith
    have e2 : ENNReal.ofReal (2 * r - 2 * r * ∫ z, φ z ∂ν) =
        ENNReal.ofReal (r - r * ∫ z, φ z ∂ν) + ENNReal.ofReal (r - r * ∫ z, φ z ∂ν) := by
      rw [← ENNReal.ofReal_add hnn hnn]; congr 1; ring
    rw [hS12, e2]
    calc ∫⁻ p, A.indicator oS p ∂P + ∫⁻ p, B.indicator oS p ∂P
        ≤ (∫⁻ p, A.indicator oD p ∂P + ∫⁻ p, A.indicator oV p ∂P) +
            (∫⁻ p, B.indicator oD p ∂P + ∫⁻ p, B.indicator oV p ∂P) := add_le_add hA3 hB3
      _ = (∫⁻ p, A.indicator oD p ∂P + ∫⁻ p, B.indicator oD p ∂P) +
            (∫⁻ p, A.indicator oV p ∂P + ∫⁻ p, B.indicator oV p ∂P) := by ring
      _ ≤ _ := add_le_add (add_le_add hDA hDB) hS5
  -- back to the statement
  have hLHS : MultiItemRev.TwoIID.expRevenue μ M = ((∫⁻ p, oS p ∂P : ℝ≥0∞) : EReal) := by
    unfold MultiItemRev.TwoIID.expRevenue
    have h0 : ∫⁻ x, ENNReal.ofReal (-M.s x) ∂μ = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      apply ae_of_all
      intro x
      apply ENNReal.ofReal_of_nonpos
      linarith [hNPT x]
    rw [h0, hconv]
    simp [hoS]
  have hRHS : ∫⁻ x, ENNReal.ofReal
          (((min (x 0) (x 1) : ℝ≥0) : ℝ) * M.q (MultiItemRev.TwoIID.diag (x 0)) 0 -
            MultiItemRev.Decomp.buyerPayoff M
              (MultiItemRev.TwoIID.diag (min (x 0) (x 1))) / 2) ∂μ = ∫⁻ p, oW p ∂P := by
    rw [hconv]
    apply lintegral_congr
    intro p
    simp only [hoW, hW, hmn, pt0, pt1, diag_eq]
    rfl
  have hint_eq : ∫ t, M.q (MultiItemRev.TwoIID.diag t) 0 ∂ν = ∫ t, φ t ∂ν := by
    congr 1; funext t; exact hφdiag t
  rw [hLHS, hRHS, hint_eq]
  have ha : 0 ≤ 2 * r - 2 * r * ∫ z, φ z ∂ν := by nlinarith
  have key : ((∫⁻ p, oS p ∂P : ℝ≥0∞) : EReal) ≤
      ((ENNReal.ofReal (2 * r - 2 * r * ∫ z, φ z ∂ν) + 2 * ∫⁻ p, oW p ∂P : ℝ≥0∞) : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr hE
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left ha]
    at key
  exact key
