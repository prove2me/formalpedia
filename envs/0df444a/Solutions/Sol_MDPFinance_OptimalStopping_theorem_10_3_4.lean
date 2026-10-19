-- Prove2me | solution 1 for MDPFinance.OptimalStopping.theorem_10_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:11:05.674721+00:00
-- url     : https://prove2.me/submissions/e7ad9af2-fbe6-4dc4-8d23-ff5cffb2c284

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory
open scoped ENNReal

namespace MTPAux
open MDPFinance.OptimalStopping

lemma lr_upper {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : LikelihoodRatioLe μ ν) {U : Set ℝ} (hU : IsUpperSet U) : μ U ≤ ν U := by
  obtain ⟨lam, f, g, hf0, hg0, hf, hg, hμ, hν, hfg⟩ := h
  have hUm : MeasurableSet U := hU.ordConnected.measurableSet
  have hμU : ∀ s, MeasurableSet s → μ s = ∫⁻ θ in s, ENNReal.ofReal (f θ) ∂lam := by
    intro s hs; rw [hμ, withDensity_apply _ hs]
  have hνU : ∀ s, MeasurableSet s → ν s = ∫⁻ θ in s, ENNReal.ofReal (g θ) ∂lam := by
    intro s hs; rw [hν, withDensity_apply _ hs]
  have hpt : ∀ θ ∈ Uᶜ, μ U * ENNReal.ofReal (g θ) ≤ ENNReal.ofReal (f θ) * ν U := by
    intro θ hθ
    rw [hμU U hUm, hνU U hUm, ← lintegral_mul_const _ hf.ennreal_ofReal,
      ← lintegral_const_mul _ hg.ennreal_ofReal]
    apply setLIntegral_mono' hUm
    intro θ' hθ'
    have hle : θ ≤ θ' := by
      by_contra hc
      exact hθ (hU (le_of_lt (not_le.mp hc)) hθ')
    rw [← ENNReal.ofReal_mul (hf0 _), ← ENNReal.ofReal_mul (hf0 _)]
    exact ENNReal.ofReal_le_ofReal (hfg θ θ' hle)
  have hint : μ U * ν Uᶜ ≤ μ Uᶜ * ν U := by
    rw [hνU _ hUm.compl, hμU _ hUm.compl, ← lintegral_const_mul _ hg.ennreal_ofReal,
      ← lintegral_mul_const _ hf.ennreal_ofReal]
    exact setLIntegral_mono' hUm.compl hpt
  rw [prob_compl_eq_one_sub hUm, prob_compl_eq_one_sub hUm] at hint
  have ha : μ U ≠ ⊤ := measure_ne_top _ _
  have hb : ν U ≠ ⊤ := measure_ne_top _ _
  have ha1 : μ U ≤ 1 := prob_le_one
  have hb1 : ν U ≤ 1 := prob_le_one
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) (by finiteness)) hint
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hb1 (by simp),
    ENNReal.toReal_sub_of_le ha1 (by simp)] at this
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb]
  apply ENNReal.ofReal_le_ofReal
  simp only [ENNReal.toReal_one] at this
  nlinarith

lemma lr_lower {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : LikelihoodRatioLe μ ν) {L : Set ℝ} (hL : IsLowerSet L) : ν L ≤ μ L := by
  have hLm : MeasurableSet L := hL.ordConnected.measurableSet
  have h1 := lr_upper h hL.compl
  have e1 := measure_add_measure_compl (μ := μ) hLm
  have e2 := measure_add_measure_compl (μ := ν) hLm
  have : ν L + ν Lᶜ ≤ μ L + ν Lᶜ := by
    rw [e2, measure_univ, ← measure_univ (μ := μ), ← e1]; gcongr
  exact (ENNReal.add_le_add_iff_right (measure_ne_top _ _)).mp this

lemma lint_cmp {μ ν : Measure ℝ} (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ)
    (h : ∀ t : ℝ≥0∞, μ {x | t < ψ x} ≤ ν {x | t < ψ x}) :
    ∫⁻ x, ψ x ∂μ ≤ ∫⁻ x, ψ x ∂ν := by
  have key : ∀ N : ℕ, ∫⁻ x, min (ψ x) N ∂μ ≤ ∫⁻ x, min (ψ x) N ∂ν := by
    intro N
    have hfin : ∀ x, min (ψ x) N ≠ ⊤ := fun x =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
    have e : ∀ x, min (ψ x) N = ENNReal.ofReal ((min (ψ x) N).toReal) := fun x =>
      (ENNReal.ofReal_toReal (hfin x)).symm
    rw [lintegral_congr e, lintegral_congr e]
    have hm : Measurable fun x => (min (ψ x) (N : ℝ≥0∞)).toReal :=
      (hψ.min measurable_const).ennreal_toReal
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ fun _ => ENNReal.toReal_nonneg) hm.aemeasurable,
      lintegral_eq_lintegral_meas_lt ν (ae_of_all _ fun _ => ENNReal.toReal_nonneg) hm.aemeasurable]
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    have hset : {a | t < (min (ψ a) (N : ℝ≥0∞)).toReal} =
        {a | ENNReal.ofReal t < min (ψ a) N} := by
      ext a
      simp only [Set.mem_setOf_eq]
      rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hfin a)]
    rw [hset]
    by_cases hN : ENNReal.ofReal t < N
    · have : {a | ENNReal.ofReal t < min (ψ a) N} = {a | ENNReal.ofReal t < ψ a} := by
        ext a; simp only [Set.mem_setOf_eq, lt_min_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hN⟩⟩
      rw [this]; exact h _
    · have : {a | ENNReal.ofReal t < min (ψ a) N} = ∅ := by
        ext a; simp only [Set.mem_setOf_eq, lt_min_iff, Set.mem_empty_iff_false, iff_false]
        exact fun hh => hN hh.2
      rw [this]; simp
  have eψ : ∀ x, ψ x = ⨆ N : ℕ, min (ψ x) N := by
    intro x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]; exact (inf_top_eq _).symm
  have hmono : Monotone fun (N : ℕ) x => min (ψ x) (N : ℝ≥0∞) := by
    intro a b hab x
    exact min_le_min le_rfl (by exact_mod_cast hab)
  calc ∫⁻ x, ψ x ∂μ = ∫⁻ x, ⨆ N : ℕ, min (ψ x) N ∂μ := lintegral_congr eψ
    _ = ⨆ N : ℕ, ∫⁻ x, min (ψ x) N ∂μ :=
        lintegral_iSup (fun N => hψ.min measurable_const) hmono
    _ ≤ ⨆ N : ℕ, ∫⁻ x, min (ψ x) N ∂ν := iSup_mono key
    _ = ∫⁻ x, ⨆ N : ℕ, min (ψ x) N ∂ν :=
        (lintegral_iSup (fun N => hψ.min measurable_const) hmono).symm
    _ = ∫⁻ x, ψ x ∂ν := (lintegral_congr eψ).symm

lemma toENNReal_sup (v : EReal) : (v ⊔ 0).toENNReal = v.toENNReal := by
  rcases le_total v 0 with h | h
  · rw [sup_eq_right.mpr h, EReal.toENNReal_of_nonpos h]; simp
  · rw [sup_eq_left.mpr h]

lemma ereal_cmp {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : LikelihoodRatioLe μ ν) {φ : ℝ → EReal} (hφ : Monotone φ) :
    erealIntegral μ φ ≤ erealIntegral ν φ := by
  unfold erealIntegral
  have hm1 : Monotone fun a => (φ a ⊔ 0).toENNReal := fun a b hab =>
    EReal.toENNReal_le_toENNReal (sup_le_sup_right (hφ hab) 0)
  have hm2 : Antitone fun a => ((-φ a) ⊔ 0).toENNReal := fun a b hab =>
    EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.mpr (hφ hab)) 0)
  have h1 : ∫⁻ a, (φ a ⊔ 0).toENNReal ∂μ ≤ ∫⁻ a, (φ a ⊔ 0).toENNReal ∂ν :=
    lint_cmp _ hm1.measurable fun t => lr_upper h fun a b hab ha =>
      lt_of_lt_of_le ha (hm1 hab)
  have h2 : ∫⁻ a, ((-φ a) ⊔ 0).toENNReal ∂ν ≤ ∫⁻ a, ((-φ a) ⊔ 0).toENNReal ∂μ :=
    lint_cmp _ hm2.measurable fun t => lr_lower h fun a b hab ha =>
      lt_of_lt_of_le ha (hm2 hab)
  exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1)
    (EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h2))

lemma ereal_mono_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : ∀ᵐ a ∂μ, v a ≤ w a) : erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  have h1 : ∫⁻ a, (v a ⊔ 0).toENNReal ∂μ ≤ ∫⁻ a, (w a ⊔ 0).toENNReal ∂μ :=
    lintegral_mono_ae (h.mono fun a ha => EReal.toENNReal_le_toENNReal (sup_le_sup_right ha 0))
  have h2 : ∫⁻ a, ((-w a) ⊔ 0).toENNReal ∂μ ≤ ∫⁻ a, ((-v a) ⊔ 0).toENNReal ∂μ :=
    lintegral_mono_ae (h.mono fun a ha =>
      EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.mpr ha) 0))
  exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1)
    (EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h2))

lemma ereal_congr_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : ∀ᵐ a ∂μ, v a = w a) : erealIntegral μ v = erealIntegral μ w :=
  le_antisymm (ereal_mono_ae μ (h.mono fun a ha => ha.le))
    (ereal_mono_ae μ (h.mono fun a ha => ha.ge))

lemma ereal_wd (φ : ℝ → EReal) (hφ : Measurable φ) (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) :
    erealIntegral volume (fun z => φ z * (ρ z : EReal)) =
      erealIntegral (volume.withDensity fun z => ENNReal.ofReal (ρ z)) φ := by
  unfold erealIntegral
  have hρm : Measurable fun z => ENNReal.ofReal (ρ z) := ENNReal.measurable_ofReal.comp hρ
  have e1 : ∀ z, ((φ z * (ρ z : EReal)) ⊔ 0).toENNReal =
      ENNReal.ofReal (ρ z) * (φ z ⊔ 0).toENNReal := by
    intro z
    rw [toENNReal_sup, toENNReal_sup, EReal.toENNReal_mul' (EReal.coe_nonneg.mpr (hρ0 z)),
      EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe, mul_comm]
  have e2 : ∀ z, ((-(φ z * (ρ z : EReal))) ⊔ 0).toENNReal =
      ENNReal.ofReal (ρ z) * ((-φ z) ⊔ 0).toENNReal := by
    intro z
    rw [toENNReal_sup, toENNReal_sup, ← EReal.neg_mul,
      EReal.toENNReal_mul' (EReal.coe_nonneg.mpr (hρ0 z)), EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe, mul_comm]
  simp_rw [e1, e2]
  rw [lintegral_withDensity_eq_lintegral_mul _ hρm
      (show Measurable fun a => (max (φ a) 0).toENNReal from
        (hφ.max measurable_const).ereal_toENNReal),
    lintegral_withDensity_eq_lintegral_mul _ hρm
      (show Measurable fun a => (max (-φ a) 0).toENNReal from
        (hφ.neg.max measurable_const).ereal_toENNReal)]
  rfl

end MTPAux

open MeasureTheory
open scoped ENNReal

namespace MTPAux
open MDPFinance.OptimalStopping

variable {I : Type*} [MeasurableSpace I]

noncomputable def pred (M : GenBayesStopping I) (i : I) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (M.q z θ) ∂(M.muhat i)

lemma q_meas2 (M : GenBayesStopping I) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (M.q p.1 p.2) :=
  M.q_meas.ennreal_ofReal

lemma pred_meas (M : GenBayesStopping I) (i : I) : Measurable (pred M i) := by
  have := M.muhat_prob i
  exact (q_meas2 M).lintegral_prod_right'

lemma q_meas_θ (M : GenBayesStopping I) (z : ℝ) : Measurable fun θ => ENNReal.ofReal (M.q z θ) :=
  (M.q_meas.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal

lemma q_meas_z (M : GenBayesStopping I) (θ : ℝ) : Measurable fun z => M.q z θ :=
  M.q_meas.comp (measurable_id.prodMk measurable_const)

/-- For `μ̂_i`-a.e. `θ`, Lebesgue-a.e. `z` has `q(z|θ) = 0` or positive predictive density. -/
lemma null_pred (M : GenBayesStopping I) (i : I) :
    ∀ᵐ θ ∂(M.muhat i), ∀ᵐ z ∂(volume : Measure ℝ), M.q z θ = 0 ∨ 0 < pred M i z := by
  have := M.muhat_prob i
  set N := {z | pred M i z = 0} with hN
  have hNm : MeasurableSet N := pred_meas M i (measurableSet_singleton 0)
  let F : ℝ → ℝ → ℝ≥0∞ := fun θ z => N.indicator (fun _ => (1 : ℝ≥0∞)) z * ENNReal.ofReal (M.q z θ)
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.mul
    · exact (measurable_const.indicator hNm).comp measurable_snd
    · exact (q_meas2 M).comp (measurable_snd.prodMk measurable_fst)
  have hzero : ∫⁻ θ, ∫⁻ z, F θ z ∂volume ∂(M.muhat i) = 0 := by
    rw [lintegral_lintegral_swap hF.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    -- wait
    refine ae_of_all _ fun z => ?_
    simp only [F]
    by_cases hz : z ∈ N
    · simp only [Set.indicator_of_mem hz, one_mul, Pi.zero_apply]
      exact hz
    · simp [Set.indicator_of_notMem hz]
  have hmeasθ : Measurable fun θ => ∫⁻ z, F θ z ∂volume := hF.lintegral_prod_right'
  rw [lintegral_eq_zero_iff hmeasθ] at hzero
  filter_upwards [hzero] with θ hθ
  have hmz : Measurable fun z => F θ z := hF.comp (measurable_const.prodMk measurable_id)
  rw [Pi.zero_apply, lintegral_eq_zero_iff hmz] at hθ
  filter_upwards [hθ] with z hz
  by_cases hzN : z ∈ N
  · left
    simp only [F, Set.indicator_of_mem hzN, one_mul, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
    exact le_antisymm hz (M.q_nonneg z θ)
  · right
    exact pos_iff_ne_zero.mpr hzN

lemma ile_refl (M : GenBayesStopping I) (i : I) : M.Ile i i := by
  refine ⟨M.muhat i, fun _ => 1, fun _ => 1, fun _ => zero_le_one, fun _ => zero_le_one,
    measurable_const, measurable_const, ?_, ?_, fun _ _ _ => le_rfl⟩ <;>
  · simp only [ENNReal.ofReal_one]
    exact (withDensity_one).symm

lemma pred_ne_top (M : GenBayesStopping I) (i : I) (z : ℝ) (hp : 0 < pred M i z) :
    pred M i z ≠ ⊤ := by
  intro htop
  have e := M.hbayes i z hp
  have hp1 := M.muhat_prob (M.Phi i z)
  have : M.muhat (M.Phi i z) Set.univ = 0 := by
    rw [e]; unfold pred at htop; rw [htop]; simp
  simp at this

lemma post_repr (M : GenBayesStopping I) {i : I} {lam : Measure ℝ} {f : ℝ → ℝ}
    (hf0 : ∀ θ, 0 ≤ f θ) (hf : Measurable f)
    (hμ : M.muhat i = lam.withDensity fun θ => ENNReal.ofReal (f θ)) {z : ℝ}
    (hp : 0 < pred M i z) :
    M.muhat (M.Phi i z) = lam.withDensity fun θ =>
      ENNReal.ofReal ((pred M i z)⁻¹.toReal * f θ * M.q z θ) := by
  have e := M.hbayes i z hp
  have hpt := pred_ne_top M i z hp
  rw [e]
  change _ = lam.withDensity fun θ => ENNReal.ofReal ((pred M i z)⁻¹.toReal * f θ * M.q z θ)
  have hfun : (fun θ => ENNReal.ofReal ((pred M i z)⁻¹.toReal * f θ * M.q z θ)) =
      (pred M i z)⁻¹ • ((fun θ => ENNReal.ofReal (f θ)) * fun θ => ENNReal.ofReal (M.q z θ)) := by
    funext θ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (hf0 θ)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hp.ne'),
      mul_assoc]
  rw [hfun, withDensity_smul _ (hf.ennreal_ofReal.mul (q_meas_θ M z)),
    withDensity_mul _ hf.ennreal_ofReal (q_meas_θ M z), ← hμ]
  rfl

lemma post (M : GenBayesStopping I) (hmtp : IsMTP2 M.q) {i i' : I} (h : M.Ile i i')
    {z z' : ℝ} (hz : z ≤ z') (hp : 0 < pred M i z) (hp' : 0 < pred M i' z') :
    M.Ile (M.Phi i z) (M.Phi i' z') := by
  obtain ⟨lam, f, g, hf0, hg0, hf, hg, hμ, hν, hfg⟩ := h
  set a := (pred M i z)⁻¹.toReal
  set b := (pred M i' z')⁻¹.toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  refine ⟨lam, fun θ => a * f θ * M.q z θ, fun θ => b * g θ * M.q z' θ,
    fun θ => mul_nonneg (mul_nonneg ha (hf0 θ)) (M.q_nonneg _ _),
    fun θ => mul_nonneg (mul_nonneg hb (hg0 θ)) (M.q_nonneg _ _),
    (measurable_const.mul hf).mul (q_meas_z' M z), (measurable_const.mul hg).mul (q_meas_z' M z'),
    post_repr M hf0 hf hμ hp, post_repr M hg0 hg hν hp', ?_⟩
  intro θ θ' hθ
  have h1 := hfg θ θ' hθ
  have h2 : M.q z' θ * M.q z θ' ≤ M.q z' θ' * M.q z θ := by
    have := hmtp z' z θ θ'
    rwa [max_eq_left hz, min_eq_right hz, max_eq_right hθ, min_eq_left hθ] at this
  have hq := M.q_nonneg
  calc a * f θ' * M.q z θ' * (b * g θ * M.q z' θ)
      = (a * b) * ((f θ' * g θ) * (M.q z' θ * M.q z θ')) := by ring
    _ ≤ (a * b) * ((f θ * g θ') * (M.q z' θ' * M.q z θ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg ha hb)
        exact mul_le_mul h1 h2 (mul_nonneg (hq _ _) (hq _ _))
          (mul_nonneg (hf0 _) (hg0 _))
    _ = a * f θ * M.q z θ * (b * g θ' * M.q z' θ') := by ring
where
  q_meas_z' (M : GenBayesStopping I) (z : ℝ) : Measurable fun θ => M.q z θ :=
    M.q_meas.comp (measurable_const.prodMk measurable_id)

/-- Core monotonicity step: `i ↦ ∫∫ h(z, Φ(i,z)) q(z|θ) dz μ̂(dθ|i)` is increasing. -/
lemma core (M : GenBayesStopping I) (hmtp : IsMTP2 M.q) (h : ℝ → I → EReal)
    (hmono : ∀ x x' j j', x ≤ x' → M.Ile j j' → h x j ≤ h x' j') {i i' : I}
    (hii : M.Ile i i') :
    erealIntegral (M.muhat i) (fun θ => erealIntegral volume
        (fun z => h z (M.Phi i z) * (M.q z θ : EReal))) ≤
      erealIntegral (M.muhat i') (fun θ => erealIntegral volume
        (fun z => h z (M.Phi i' z) * (M.q z θ : EReal))) := by
  have := M.muhat_prob i
  have := M.muhat_prob i'
  let S' := {s | 0 < pred M i' s}
  let uc : ℝ → EReal := fun z => ⨅ (s : ℝ) (_ : s ∈ S' ∧ z ≤ s), h s (M.Phi i' s)
  have huc_mono : Monotone uc := fun z z' hzz =>
    le_iInf₂ fun s hs => iInf₂_le s ⟨hs.1, le_trans hzz hs.2⟩
  have huc_eq : ∀ s ∈ S', uc s = h s (M.Phi i' s) := by
    intro s hs
    apply le_antisymm (iInf₂_le s ⟨hs, le_rfl⟩)
    exact le_iInf₂ fun s' hs' => hmono _ _ _ _ hs'.2
      (post M hmtp (ile_refl M i') hs'.2 hs hs'.1)
  have huc_le : ∀ z, 0 < pred M i z → h z (M.Phi i z) ≤ uc z := by
    intro z hz
    exact le_iInf₂ fun s hs => hmono _ _ _ _ hs.2 (post M hmtp hii hs.2 hz hs.1)
  let U : ℝ → EReal := fun θ => erealIntegral volume (fun z => uc z * (M.q z θ : EReal))
  have hU_mono : Monotone U := by
    intro θ θ' hθ
    simp only [U]
    rw [ereal_wd uc huc_mono.measurable _ (q_meas_z M θ) (fun z => M.q_nonneg z θ),
      ereal_wd uc huc_mono.measurable _ (q_meas_z M θ') (fun z => M.q_nonneg z θ')]
    have : IsProbabilityMeasure (volume.withDensity fun z => ENNReal.ofReal (M.q z θ)) :=
      ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact M.q_density θ⟩
    have : IsProbabilityMeasure (volume.withDensity fun z => ENNReal.ofReal (M.q z θ')) :=
      ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact M.q_density θ'⟩
    refine ereal_cmp ?_ huc_mono
    refine ⟨volume, fun z => M.q z θ, fun z => M.q z θ', fun z => M.q_nonneg z θ,
      fun z => M.q_nonneg z θ', q_meas_z M θ, q_meas_z M θ', rfl, rfl, ?_⟩
    intro z z' hz
    have := hmtp z' z θ θ'
    rw [max_eq_left hz, min_eq_right hz, max_eq_right hθ, min_eq_left hθ] at this
    simp only
    linarith [mul_comm (M.q z' θ') (M.q z θ)]
  calc erealIntegral (M.muhat i) (fun θ => erealIntegral volume
        (fun z => h z (M.Phi i z) * (M.q z θ : EReal)))
      ≤ erealIntegral (M.muhat i) U := by
        apply ereal_mono_ae
        filter_upwards [null_pred M i] with θ hθ
        apply ereal_mono_ae
        filter_upwards [hθ] with z hz
        rcases hz with h0 | hp
        · simp [h0]
        · exact mul_le_mul_of_nonneg_right (huc_le z hp) (EReal.coe_nonneg.mpr (M.q_nonneg z θ))
    _ ≤ erealIntegral (M.muhat i') U := ereal_cmp hii hU_mono
    _ = erealIntegral (M.muhat i') (fun θ => erealIntegral volume
        (fun z => h z (M.Phi i' z) * (M.q z θ : EReal))) := by
        apply ereal_congr_ae
        filter_upwards [null_pred M i'] with θ hθ
        apply ereal_congr_ae
        filter_upwards [hθ] with z hz
        rcases hz with h0 | hp
        · simp [h0]
        · rw [huc_eq z hp]

end MTPAux

open MDPFinance.OptimalStopping in
theorem solution {I : Type*} [MeasurableSpace I] (M : GenBayesStopping I)
    (hMTP2 : IsMTP2 M.q) :
    (∀ (n : ℕ) (p p' : ℝ × I), M.Ele p p' → M.J n p.1 p.2 ≤ M.J n p'.1 p'.2) ∧
    (∀ (n : ℕ) (i i' : I), 1 ≤ n → M.Ile i i' → M.cfun n i ≤ M.cfun n i') := by
  have key : ∀ n x x' i i', x ≤ x' → M.Ile i i' → M.J n x i ≤ M.J n x' i' := by
    intro n
    induction n with
    | zero => intro x x' i i' hx _; exact EReal.coe_le_coe_iff.mpr hx
    | succ k ih =>
      intro x x' i i' hx hii
      simp only [GenBayesStopping.J]
      exact max_le_max (EReal.coe_le_coe_iff.mpr hx)
        (add_le_add le_rfl (MTPAux.core M hMTP2 (M.J k) ih hii))
  refine ⟨fun n p p' hp => key n _ _ _ _ hp.1 hp.2, fun n i i' _ hii => ?_⟩
  unfold GenBayesStopping.cfun
  exact add_le_add le_rfl (MTPAux.core M hMTP2 (M.J (n - 1)) (key _) hii)
