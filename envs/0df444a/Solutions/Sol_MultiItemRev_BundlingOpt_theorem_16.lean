-- Prove2me | solution 1 for MultiItemRev.BundlingOpt.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:44:08.951269+00:00
-- url     : https://prove2.me/submissions/12c10b91-cfae-418d-b275-396d9a21e723

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
import Theorems.Thm_MultiItemRev_BundlingOpt_proposition_6_iii
import Theorems.Thm_MultiItemRev_BundlingOpt_symmetrization
import Theorems.Thm_MultiItemRev_BundlingOpt_bundled_majorant_ic_ir
import Theorems.Thm_MultiItemRev_BundlingOpt_revenue_le_majorant
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt.T16Red

open MultiItemRev.BundlingOpt

/-- One-good mechanism on `Unit` given by functions of the (single) value. -/
noncomputable def oneMech (qq ss : ℝ≥0 → ℝ) : Mechanism Unit where
  q v _ := qq (v ())
  s v := ss (v ())

lemma oneMech_admissible (qq ss : ℝ≥0 → ℝ) (hq : ∀ u, 0 ≤ qq u ∧ qq u ≤ 1)
    (hic : ∀ u v : ℝ≥0, qq v * u - ss v ≤ qq u * u - ss u)
    (hir : ∀ u : ℝ≥0, 0 ≤ qq u * u - ss u) (hs : Measurable ss) :
    IsAdmissible (oneMech qq ss) := by
  refine ⟨fun x i => hq (x ()), fun x x' => ?_, fun x => ?_, ?_⟩
  · simpa [buyerPayoff, oneMech] using hic (x ()) (x' ())
  · simpa [buyerPayoff, oneMech] using hir (x ())
  · exact hs.comp (measurable_pi_apply ())

/-- Revenue of a one-good mechanism against `oneGood (μ.map T)`. -/
lemma expRevenue_oneGood_map (μ : Measure (Fin 2 → ℝ≥0)) (N : Mechanism Unit)
    (hN : Measurable N.s) :
    expRevenue (oneGood (μ.map (fun x => ∑ i, x i))) N =
      ((∫⁻ x, ENNReal.ofReal (N.s (fun _ => ∑ i, x i)) ∂μ : ℝ≥0∞) : EReal) -
        ((∫⁻ x, ENNReal.ofReal (-N.s (fun _ => ∑ i, x i)) ∂μ : ℝ≥0∞) : EReal) := by
  have hg : Measurable (fun t : ℝ≥0 => (fun _ : Unit => t)) := measurable_pi_lambda _ (fun _ => measurable_id)
  have hS : Measurable (fun x : Fin 2 → ℝ≥0 => ∑ i, x i) := by fun_prop
  have h1 : Measurable (fun v : Unit → ℝ≥0 => ENNReal.ofReal (N.s v)) :=
    ENNReal.measurable_ofReal.comp hN
  have h2 : Measurable (fun v : Unit → ℝ≥0 => ENNReal.ofReal (-N.s v)) :=
    ENNReal.measurable_ofReal.comp hN.neg
  unfold expRevenue oneGood
  have h3 : Measurable (fun t : ℝ≥0 => ENNReal.ofReal (N.s (fun _ => t))) := h1.comp hg
  have h4 : Measurable (fun t : ℝ≥0 => ENNReal.ofReal (-N.s (fun _ => t))) := h2.comp hg
  rw [lintegral_map h1 hg, lintegral_map h2 hg, lintegral_map h3 hS, lintegral_map h4 hS]

/-- `BRev ≤ Rev` for two goods: every one-good mechanism for the sum lifts to a bundled
two-good mechanism with the same revenue. -/
lemma brev_le_rev (μ : Measure (Fin 2 → ℝ≥0)) : BRev μ ≤ Rev μ := by
  unfold BRev Rev1
  conv_lhs => unfold Rev
  refine iSup₂_le fun N hN => ?_
  let M2 : Mechanism (Fin 2) :=
    { q := fun x _ => N.q (fun _ => ∑ i, x i) (), s := fun x => N.s (fun _ => ∑ i, x i) }
  have hM2 : IsAdmissible M2 := by
    obtain ⟨hF, hIC, hIR, hMs⟩ := hN
    refine ⟨fun x i => hF _ (), fun x x' => ?_, fun x => ?_, ?_⟩
    · have h := hIC (fun _ => ∑ i, x i) (fun _ => ∑ i, x' i)
      simp only [buyerPayoff, Finset.univ_unique, Finset.sum_singleton, M2] at h ⊢
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      push_cast at h
      simpa using h
    · have h := hIR (fun _ => ∑ i, x i)
      simp only [buyerPayoff, Finset.univ_unique, Finset.sum_singleton, M2] at h ⊢
      rw [← Finset.mul_sum]
      push_cast at h
      simpa using h
    · exact hMs.comp (measurable_pi_lambda _ (fun _ => by fun_prop))
  refine le_iSup₂_of_le M2 hM2 (le_of_eq ?_)
  rw [expRevenue_oneGood_map μ N hN.2.2.2]
  rfl

/-- Core one-good construction: options `(Q t, S t)` for `t ≥ c` that are IC/IR among themselves
extend to a globally IC, IR one-good mechanism, by offering the option `c` or nothing below `c`. -/
lemma extend_one_good (Q S : ℝ≥0 → ℝ) (c : ℝ≥0)
    (hq : ∀ t, 0 ≤ Q t ∧ Q t ≤ 1)
    (hic : ∀ t t' : ℝ≥0, c ≤ t → c ≤ t' → Q t' * t - S t' ≤ Q t * t - S t)
    (hir : ∀ t : ℝ≥0, c ≤ t → 0 ≤ Q t * t - S t) :
    ∃ N : Mechanism Unit, IsAdmissible N ∧ ∀ t : ℝ≥0, c ≤ t → N.s (fun _ => t) = S t := by
  -- monotonicity of `Q` and of the payoff on `[c, ∞)`
  have hQmono : ∀ t₁ t₂ : ℝ≥0, c ≤ t₁ → t₁ ≤ t₂ → Q t₁ ≤ Q t₂ := by
    intro t₁ t₂ h1 h12
    rcases eq_or_lt_of_le h12 with h | h
    · rw [h]
    · have a1 := hic t₁ t₂ h1 (h1.trans h12)
      have a2 := hic t₂ t₁ (h1.trans h12) h1
      have hlt : (t₁ : ℝ) < t₂ := h
      by_contra hc
      push Not at hc
      nlinarith
  have hVmono : ∀ t₁ t₂ : ℝ≥0, c ≤ t₁ → t₁ ≤ t₂ → Q t₁ * t₁ - S t₁ ≤ Q t₂ * t₂ - S t₂ := by
    intro t₁ t₂ h1 h12
    have a1 := hic t₂ t₁ (h1.trans h12) h1
    have hle : (t₁ : ℝ) ≤ t₂ := h12
    nlinarith [(hq t₁).1]
  set Q' : ℝ≥0 → ℝ := fun t => Q (max t c) with hQ'
  set V' : ℝ≥0 → ℝ := fun t => Q (max t c) * (max t c : ℝ≥0) - S (max t c) with hV'
  have hQ'm : Measurable Q' := by
    refine Monotone.measurable fun t₁ t₂ h => hQmono _ _ (le_max_right _ _) (max_le_max h le_rfl)
  have hV'm : Measurable V' := by
    refine Monotone.measurable fun t₁ t₂ h => hVmono _ _ (le_max_right _ _) (max_le_max h le_rfl)
  let qq : ℝ≥0 → ℝ := fun u =>
    if c ≤ u then Q u else if 0 ≤ Q c * u - S c then Q c else 0
  let ss : ℝ≥0 → ℝ := fun u =>
    if c ≤ u then S u else if 0 ≤ Q c * u - S c then S c else 0
  have hss : ss = fun u =>
      if c ≤ u then Q' u * u - V' u else if 0 ≤ Q c * u - S c then S c else 0 := by
    funext u
    by_cases h : c ≤ u
    · simp only [ss, h, if_true, hQ', hV', max_eq_left h]; ring
    · simp only [ss, h, if_false]
  have hssm : Measurable ss := by
    rw [hss]
    refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ ?_
    · exact (hQ'm.mul measurable_coe_nnreal_real).sub hV'm
    · refine Measurable.ite (measurableSet_le measurable_const ?_) measurable_const measurable_const
      exact (measurable_const.mul measurable_coe_nnreal_real).sub measurable_const
  -- every option's payoff is dominated by the option `c` below `c`
  have below : ∀ u t' : ℝ≥0, u < c → c ≤ t' → Q t' * u - S t' ≤ Q c * u - S c := by
    intro u t' hu ht'
    have a1 := hic c t' le_rfl ht'
    have hm := hQmono c t' le_rfl ht'
    have hlt : (u : ℝ) < c := hu
    nlinarith
  have hqq : ∀ u, 0 ≤ qq u ∧ qq u ≤ 1 := by
    intro u
    simp only [qq]
    split_ifs
    · exact hq u
    · exact hq c
    · exact ⟨le_rfl, zero_le_one⟩
  -- the payoff of truthful reporting
  have hU : ∀ u : ℝ≥0, (0 ≤ qq u * u - ss u) ∧ ∀ t' : ℝ≥0, c ≤ t' → Q t' * u - S t' ≤ qq u * u - ss u := by
    intro u
    by_cases h : c ≤ u
    · simp only [qq, ss, h, if_true]
      exact ⟨hir u h, fun t' ht' => hic u t' h ht'⟩
    · push Not at h
      by_cases h2 : 0 ≤ Q c * u - S c
      · have e1 : qq u = Q c := by simp only [qq, not_le.2 h, h2, if_true, if_false]
        have e2 : ss u = S c := by simp only [ss, not_le.2 h, h2, if_true, if_false]
        rw [e1, e2]
        exact ⟨h2, fun t' ht' => below u t' h ht'⟩
      · have e1 : qq u = 0 := by simp only [qq, not_le.2 h, h2, if_false]
        have e2 : ss u = 0 := by simp only [ss, not_le.2 h, h2, if_false]
        rw [e1, e2]
        push Not at h2
        refine ⟨by simp, fun t' ht' => ?_⟩
        have := below u t' h ht'
        linarith
  have hic' : ∀ u v : ℝ≥0, qq v * u - ss v ≤ qq u * u - ss u := by
    intro u v
    by_cases h : c ≤ v
    · simp only [qq, ss, h, if_true]
      exact (hU u).2 v h
    · by_cases h2 : 0 ≤ Q c * v - S c
      · simp only [qq, ss, h, h2, if_true, if_false]
        exact (hU u).2 c le_rfl
      · have e1 : qq v = 0 := by simp only [qq, h, h2, if_false]
        have e2 : ss v = 0 := by simp only [ss, h, h2, if_false]
        rw [e1, e2, zero_mul, sub_zero]
        exact (hU u).1
  refine ⟨oneMech qq ss, oneMech_admissible qq ss hqq hic' (fun u => (hU u).1) hssm, ?_⟩
  intro t ht
  simp [oneMech, ss, ht]

/-- The bundled majorant `µ̂` of an admissible symmetric mechanism, which is IC and IR on the
quadrant `[a, ∞)²` and depends only on `y + z`, agrees on that quadrant with an admissible one-good
mechanism for the sum `T = Y + Z`. -/
lemma bundle_one_good (M : Mechanism (Fin 2)) (hM : IsAdmissible M) (hsym : IsSymmetric M)
    (a : ℝ≥0) :
    ∃ N : Mechanism Unit, IsAdmissible N ∧
      ∀ x : Fin 2 → ℝ≥0, a ≤ x 0 → a ≤ x 1 → N.s (fun _ => x 0 + x 1) = (bundledMajorant M a).s x := by
  obtain ⟨hF, hIC, hIR, hdep⟩ := bundled_majorant_ic_ir M hM hsym a
  set B := bundledMajorant M a with hB
  let xh : ℝ≥0 → Fin 2 → ℝ≥0 := fun t => ![t - a, a]
  have quad : ∀ t, a + a ≤ t → ∀ i, a ≤ xh t i := by
    intro t ht i
    fin_cases i
    · exact le_tsub_of_add_le_right ht
    · exact le_rfl
  have sumxh : ∀ t, a ≤ t → xh t 0 + xh t 1 = t := by
    intro t ht
    simp [xh, tsub_add_cancel_of_le ht]
  have pay : ∀ t t', a ≤ t → ∑ i, B.q (xh t') i * ((xh t i : ℝ≥0) : ℝ) = B.q (xh t') 0 * t := by
    intro t t' ht
    rw [Fin.sum_univ_two]
    have e : B.q (xh t') 1 = B.q (xh t') 0 := rfl
    rw [e]
    simp only [xh, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [NNReal.coe_sub ht]
    ring
  let Q : ℝ≥0 → ℝ := fun t => B.q (xh t) 0
  let S : ℝ≥0 → ℝ := fun t => B.s (xh t)
  have hc : ∀ t, a + a ≤ t → a ≤ t := fun t ht => le_trans le_add_self ht
  obtain ⟨N, hN, hNs⟩ := extend_one_good Q S (a + a) (fun t => hF (xh t) 0)
    (fun t t' ht ht' => by
      have h := hIC (xh t) (xh t') (quad t ht) (quad t' ht')
      unfold buyerPayoff at h
      rw [pay t t' (hc t ht), pay t t (hc t ht)] at h
      exact h)
    (fun t ht => by
      have h := hIR (xh t) (quad t ht)
      unfold buyerPayoff at h
      rw [pay t t (hc t ht)] at h
      exact h)
  refine ⟨N, hN, fun x hx0 hx1 => ?_⟩
  have ht : a + a ≤ x 0 + x 1 := add_le_add hx0 hx1
  rw [hNs _ ht]
  exact ((hdep x (xh (x 0 + x 1)) (by rw [sumxh _ (hc _ ht)])).2).symm

lemma le_Rev {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ≥0)) (N : Mechanism ι)
    (hN : IsAdmissible N) : (expRevenue ν N).toENNReal ≤ Rev ν :=
  le_iSup₂ (f := fun (M : Mechanism ι) (_ : IsAdmissible M) => (expRevenue ν M).toENNReal) N hN

lemma densityLaw_prob (f : ℝ → ℝ) (hf_mass : ∫⁻ x, ENNReal.ofReal (f x) = 1) :
    IsProbabilityMeasure (densityLaw f) := by
  constructor
  rw [densityLaw, Measure.map_apply measurable_real_toNNReal MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hf_mass]

lemma densityLaw_ae (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_supp : ∀ x, x < a → f x = 0) :
    ∀ᵐ t ∂(densityLaw f), a.toNNReal ≤ t := by
  rw [ae_iff]
  simp only [not_le]
  change densityLaw f (Set.Iio a.toNNReal) = 0
  rw [densityLaw, Measure.map_apply measurable_real_toNNReal measurableSet_Iio,
    withDensity_apply _ (measurable_real_toNNReal measurableSet_Iio)]
  rw [setLIntegral_congr_fun (measurable_real_toNNReal measurableSet_Iio)
    (g := fun _ => 0) (fun x hx => by
      have hx' : x.toNNReal < a.toNNReal := hx
      simp [hf_supp x ((Real.toNNReal_lt_toNNReal_iff ha).1 hx')])]
  simp

end MultiItemRev.BundlingOpt.T16Red

open MultiItemRev.BundlingOpt MultiItemRev.BundlingOpt.T16Red in
theorem solution (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_supp : ∀ x, x < a → f x = 0)
    (hf_mass : ∫⁻ x, ENNReal.ofReal (f x) = 1)
    (hf_diff : ∀ x, a < x → DifferentiableAt ℝ f x)
    (h9 : ∀ x, a < x → x * deriv f x + 3 / 2 * f x ≤ 0) :
    Rev (Measure.pi (fun _ : Fin 2 => densityLaw f)) =
        BRev (Measure.pi (fun _ : Fin 2 => densityLaw f)) ∧
      BRev (Measure.pi (fun _ : Fin 2 => densityLaw f)) =
        Rev1 ((Measure.pi (fun _ : Fin 2 => densityLaw f)).map (fun x => x 0 + x 1)) := by
  have : IsProbabilityMeasure (densityLaw f) := densityLaw_prob f hf_mass
  set μ := Measure.pi (fun _ : Fin 2 => densityLaw f) with hμ
  have hquad : ∀ᵐ x ∂μ, a.toNNReal ≤ x 0 ∧ a.toNNReal ≤ x 1 :=
    ((Measure.quasiMeasurePreserving_eval (fun _ : Fin 2 => densityLaw f) 0).ae
      (densityLaw_ae a ha f hf_supp)).and
    ((Measure.quasiMeasurePreserving_eval (fun _ : Fin 2 => densityLaw f) 1).ae
      (densityLaw_ae a ha f hf_supp))
  refine ⟨le_antisymm ?_ (brev_le_rev μ), ?_⟩
  · rw [proposition_6_iii μ]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨hA, hNPT, hS, hR⟩ := symmetrization (densityLaw f) M hM
    have h1 := revenue_le_majorant a ha f hf_meas hf_nonneg hf_supp hf_mass hf_diff h9
      (symmetrize M) ⟨hA, hNPT⟩ hS
    obtain ⟨N, hN, hNs⟩ := bundle_one_good (symmetrize M) hA hS a.toNNReal
    have h2 : expRevenue μ (bundledMajorant (symmetrize M) a.toNNReal) =
        expRevenue (oneGood (μ.map (fun x => ∑ i, x i))) N := by
      rw [expRevenue_oneGood_map μ N hN.2.2.2]
      have e1 : ∀ᵐ x ∂μ, ENNReal.ofReal ((bundledMajorant (symmetrize M) a.toNNReal).s x) =
          ENNReal.ofReal (N.s (fun _ => ∑ i, x i)) :=
        hquad.mono fun x hx => by rw [Fin.sum_univ_two, hNs x hx.1 hx.2]
      have e2 : ∀ᵐ x ∂μ, ENNReal.ofReal (-(bundledMajorant (symmetrize M) a.toNNReal).s x) =
          ENNReal.ofReal (-N.s (fun _ => ∑ i, x i)) :=
        hquad.mono fun x hx => by rw [Fin.sum_univ_two, hNs x hx.1 hx.2]
      unfold expRevenue
      rw [lintegral_congr_ae e1, lintegral_congr_ae e2]
    calc (expRevenue μ M).toENNReal = (expRevenue μ (symmetrize M)).toENNReal := by rw [hR]
      _ ≤ (expRevenue μ (bundledMajorant (symmetrize M) a.toNNReal)).toENNReal :=
          EReal.toENNReal_le_toENNReal h1
      _ = (expRevenue (oneGood (μ.map (fun x => ∑ i, x i))) N).toENNReal := by rw [h2]
      _ ≤ BRev μ := by
          exact le_Rev _ N hN
  · have e : (fun x : Fin 2 → ℝ≥0 => ∑ i, x i) = (fun x => x 0 + x 1) :=
      funext fun x => Fin.sum_univ_two _
    unfold BRev
    rw [e]
