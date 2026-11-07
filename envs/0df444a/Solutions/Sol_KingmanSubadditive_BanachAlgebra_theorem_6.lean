-- Prove2me | solution 1 for KingmanSubadditive.BanachAlgebra.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:48:45.497137+00:00
-- url     : https://prove2.me/submissions/5a8e6d55-ffc2-4478-8f94-b9ae1b20edba

import Mathlib
import Theorems.Thm_KingmanSubadditive_Ergodic_theorem_1
import Theorems.Thm_KingmanSubadditive_BanachAlgebra_logNormProcess_conditions
import Theorems.Thm_KingmanSubadditive_BanachAlgebra_truncation_isSubadditive
open MeasureTheory Filter Topology
open KingmanSubadditive.BanachAlgebra

namespace K6aux

lemma eMean_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → EReal}
    (h : ∀ᵐ ω ∂P, f ω ≤ g ω) : eMean P f ≤ eMean P g := by
  unfold eMean
  apply EReal.sub_le_sub
  · exact_mod_cast lintegral_mono_ae (h.mono fun ω hω => EReal.toENNReal_le_toENNReal hω)
  · exact_mod_cast lintegral_mono_ae (h.mono fun ω hω =>
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 hω))

lemma toENNReal_coe_real (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

lemma eMean_coe {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {g : Ω → ℝ}
    (hg : Integrable g P) : eMean P (fun ω => (g ω : EReal)) = ((∫ ω, g ω ∂P : ℝ) : EReal) := by
  unfold eMean
  have h1 : (fun ω => ((g ω : EReal)).toENNReal) = fun ω => ENNReal.ofReal (g ω) := by
    funext ω; exact toENNReal_coe_real _
  have h2 : (fun ω => (-(g ω : EReal)).toENNReal) = fun ω => ENNReal.ofReal (-g ω) := by
    funext ω; rw [← EReal.coe_neg]; exact toENNReal_coe_real _
  rw [h1, h2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  have hA : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P ≠ ⊤ := hg.lintegral_lt_top.ne
  have hB : ∫⁻ ω, ENNReal.ofReal (-g ω) ∂P ≠ ⊤ := hg.neg.lintegral_lt_top.ne
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal hA, EReal.coe_ennreal_toReal hB]

lemma eMean_tendsto_iInf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → EReal) (hm : ∀ N, Measurable (f N))
    (hanti : ∀ N M, N ≤ M → ∀ᵐ ω ∂P, f M ω ≤ f N ω)
    (h0 : ∫⁻ ω, (f 0 ω).toENNReal ∂P < ⊤) :
    Tendsto (fun N => eMean P (f N)) atTop (𝓝 (eMean P (fun ω => ⨅ N, f N ω))) := by
  have hae : ∀ᵐ ω ∂P, Antitone (fun N => f N ω) := by
    have : ∀ᵐ ω ∂P, ∀ N M, N ≤ M → f M ω ≤ f N ω := by
      rw [ae_all_iff]; intro N; rw [ae_all_iff]; intro M
      by_cases hNM : N ≤ M
      · exact (hanti N M hNM).mono fun ω h _ => h
      · exact Filter.Eventually.of_forall fun ω h => absurd h hNM
    filter_upwards [this] with ω h
    intro N M hNM; exact h N M hNM
  -- positive parts
  have hpos_eq : ∀ ω, (⨅ N, f N ω).toENNReal = ⨅ N, (f N ω).toENNReal := by
    intro ω
    have := Monotone.map_iInf_of_continuousAt (f := EReal.toENNReal) (g := fun N => f N ω)
      EReal.continuous_toENNReal.continuousAt (fun a b h => EReal.toENNReal_le_toENNReal h) rfl
    exact this
  have hposint : ∫⁻ ω, (⨅ N, f N ω).toENNReal ∂P = ⨅ N, ∫⁻ ω, (f N ω).toENNReal ∂P := by
    simp_rw [hpos_eq]
    apply lintegral_iInf_ae (fun N => (hm N).ereal_toENNReal)
    · intro N
      filter_upwards [hae] with ω h
      exact EReal.toENNReal_le_toENNReal (h (Nat.le_succ N))
    · exact h0.ne
  have hposanti : Antitone (fun N => ∫⁻ ω, (f N ω).toENNReal ∂P) := by
    intro N M hNM
    apply lintegral_mono_ae
    filter_upwards [hae] with ω h
    exact EReal.toENNReal_le_toENNReal (h hNM)
  have hposT : Tendsto (fun N => ∫⁻ ω, (f N ω).toENNReal ∂P) atTop
      (𝓝 (∫⁻ ω, (⨅ N, f N ω).toENNReal ∂P)) := by
    rw [hposint]; exact tendsto_atTop_iInf hposanti
  -- negative parts
  have hneg_eq : ∀ ω, (-(⨅ N, f N ω)).toENNReal = ⨆ N, (-(f N ω)).toENNReal := by
    intro ω
    have := Antitone.map_iInf_of_continuousAt (f := fun y : EReal => (-y).toENNReal)
      (g := fun N => f N ω)
      (EReal.continuous_toENNReal.comp continuous_neg).continuousAt
      (fun a b h => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 h)) (by simp)
    exact this
  have hnegint : ∫⁻ ω, (-(⨅ N, f N ω)).toENNReal ∂P = ⨆ N, ∫⁻ ω, (-(f N ω)).toENNReal ∂P := by
    simp_rw [hneg_eq]
    apply lintegral_iSup' (fun N => ((hm N).neg.ereal_toENNReal).aemeasurable)
    filter_upwards [hae] with ω h
    intro N M hNM
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h hNM))
  have hnegmono : Monotone (fun N => ∫⁻ ω, (-(f N ω)).toENNReal ∂P) := by
    intro N M hNM
    apply lintegral_mono_ae
    filter_upwards [hae] with ω h
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h hNM))
  have hnegT : Tendsto (fun N => ∫⁻ ω, (-(f N ω)).toENNReal ∂P) atTop
      (𝓝 (∫⁻ ω, (-(⨅ N, f N ω)).toENNReal ∂P)) := by
    rw [hnegint]; exact tendsto_atTop_iSup hnegmono
  -- combine
  set a := ∫⁻ ω, (⨅ N, f N ω).toENNReal ∂P
  set b := ∫⁻ ω, (-(⨅ N, f N ω)).toENNReal ∂P
  have ha : a ≠ ⊤ := by
    have : a ≤ ∫⁻ ω, (f 0 ω).toENNReal ∂P := by rw [hposint]; exact iInf_le _ 0
    exact ne_top_of_le_ne_top h0.ne this
  have hA : Tendsto (fun N => ((∫⁻ ω, (f N ω).toENNReal ∂P : ENNReal) : EReal)) atTop
      (𝓝 (a : EReal)) := (continuous_coe_ennreal_ereal.tendsto _).comp hposT
  have hB : Tendsto (fun N => -((∫⁻ ω, (-(f N ω)).toENNReal ∂P : ENNReal) : EReal)) atTop
      (𝓝 (-(b : EReal))) :=
    (continuous_neg.tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp hnegT)
  have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) ((a : EReal), -(b : EReal)) := by
    apply EReal.continuousAt_add
    · left; simpa using ha
    · left; simp
  have := hcont.tendsto.comp (hA.prodMk_nhds hB)
  unfold eMean
  simp only [sub_eq_add_neg]
  exact this


lemma logNorm_ne_top {𝔅 : Type*} [Norm 𝔅] (a : 𝔅) : logNorm a ≠ ⊤ := by
  unfold logNorm
  exact (ENNReal.log_lt_top_iff.2 ENNReal.ofReal_lt_top).ne

/-- truncation level `-(N+1)(t-s)` -/
noncomputable def cc (N s t : ℕ) : ℝ := -((N : ℝ) + 1) * ((t : ℝ) - (s : ℝ))

noncomputable def zE {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (N s t : ℕ) (ω : Ω) : EReal :=
  max (x s t ω) ((cc N s t : ℝ) : EReal)

noncomputable def zz {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (N : ℕ) : ℕ → ℕ → Ω → ℝ :=
  fun s t ω => (zE x N s t ω).toReal

lemma zE_ne_top {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (hx : ∀ s t ω, x s t ω ≠ ⊤)
    (N s t : ℕ) (ω : Ω) : zE x N s t ω ≠ ⊤ := by
  unfold zE
  exact (max_lt (lt_top_iff_ne_top.2 (hx s t ω)) (EReal.coe_lt_top _)).ne

lemma zE_ne_bot {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (N s t : ℕ) (ω : Ω) :
    zE x N s t ω ≠ ⊥ := by
  unfold zE
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)

lemma coe_zz {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (hx : ∀ s t ω, x s t ω ≠ ⊤)
    (N s t : ℕ) (ω : Ω) : ((zz x N s t ω : ℝ) : EReal) = zE x N s t ω :=
  EReal.coe_toReal (zE_ne_top x hx N s t ω) (zE_ne_bot x N s t ω)

lemma cc_le_zz {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (hx : ∀ s t ω, x s t ω ≠ ⊤)
    (N s t : ℕ) (ω : Ω) : cc N s t ≤ zz x N s t ω := by
  have : ((cc N s t : ℝ) : EReal) ≤ ((zz x N s t ω : ℝ) : EReal) := by
    rw [coe_zz x hx]; exact le_max_right _ _
  exact_mod_cast this

lemma x_le_zz {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (hx : ∀ s t ω, x s t ω ≠ ⊤)
    (N s t : ℕ) (ω : Ω) : x s t ω ≤ ((zz x N s t ω : ℝ) : EReal) := by
  rw [coe_zz x hx]; exact le_max_left _ _

lemma zz_anti {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (hx : ∀ s t ω, x s t ω ≠ ⊤)
    (N M s t : ℕ) (hst : s ≤ t) (hNM : N ≤ M) (ω : Ω) : zz x M s t ω ≤ zz x N s t ω := by
  have h1 : cc M s t ≤ cc N s t := by
    unfold cc
    have : (s : ℝ) ≤ t := by exact_mod_cast hst
    have : (N : ℝ) ≤ M := by exact_mod_cast hNM
    nlinarith
  have : ((zz x M s t ω : ℝ) : EReal) ≤ ((zz x N s t ω : ℝ) : EReal) := by
    rw [coe_zz x hx, coe_zz x hx]; unfold zE
    exact max_le_max le_rfl (by exact_mod_cast h1)
  exact_mod_cast this

lemma zz_S1 {Ω : Type*} (x : ℕ → ℕ → Ω → EReal) (hx : ∀ s t ω, x s t ω ≠ ⊤)
    (h1 : ∀ (s t u : ℕ) (ω : Ω), s < t → t < u → x s u ω ≤ x s t ω + x t u ω) (N : ℕ) :
    ∀ (s t u : ℕ) (ω : Ω), s < t → t < u → zz x N s u ω ≤ zz x N s t ω + zz x N t u ω := by
  intro s t u ω hst htu
  have : ((zz x N s u ω : ℝ) : EReal) ≤ ((zz x N s t ω + zz x N t u ω : ℝ) : EReal) := by
    rw [EReal.coe_add, coe_zz x hx, coe_zz x hx, coe_zz x hx]
    unfold zE
    apply max_le
    · exact (h1 s t u ω hst htu).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
    · have hc : cc N s u = cc N s t + cc N t u := by unfold cc; ring
      rw [hc, EReal.coe_add]
      exact add_le_add (le_max_right _ _) (le_max_right _ _)
  exact_mod_cast this

lemma zz_meas {Ω : Type*} [MeasurableSpace Ω] (x : ℕ → ℕ → Ω → EReal)
    (hm : IsMeasurableFamily x) (N : ℕ) : IsMeasurableFamily (zz x N) := by
  intro s t hst
  exact ((hm s t hst).max measurable_const).ereal_toReal

lemma zz_S2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : ℕ → ℕ → Ω → EReal)
    (hm : IsMeasurableFamily x) (h2 : S2 P x) (N : ℕ) : S2 P (zz x N) := by
  let F : (KingmanSubadditive.Ergodic.Interval → EReal) → (KingmanSubadditive.Ergodic.Interval → ℝ) :=
    fun φ p => (max (φ p) ((cc N p.1.1 p.1.2 : ℝ) : EReal)).toReal
  have hF : Measurable F :=
    measurable_pi_lambda _ fun p => ((measurable_pi_apply p).max measurable_const).ereal_toReal
  have hp : Measurable (path x) := measurable_pi_lambda _ fun p => hm _ _ p.2
  have hsp : Measurable (shiftedPath x) :=
    measurable_pi_lambda _ fun p => hm _ _ (by have := p.2; omega)
  have e1 : path (zz x N) = F ∘ path x := by
    funext ω p; rfl
  have e2 : shiftedPath (zz x N) = F ∘ shiftedPath x := by
    funext ω p
    simp only [shiftedPath, zz, zE, F, Function.comp, cc]
    congr 3
    push_cast; ring
  unfold S2 at h2 ⊢
  rw [e1, e2, ← Measure.map_map hF hsp, ← Measure.map_map hF hp, h2]

lemma zz_S3' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : ℕ → ℕ → Ω → EReal)
    (hx : ∀ s t ω, x s t ω ≠ ⊤) (h3 : ∫⁻ ω, (x 0 1 ω).toENNReal ∂P < ⊤) (N : ℕ) :
    S3' P (zz x N) := by
  unfold S3'
  refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) h3
  rw [← toENNReal_coe_real, coe_zz x hx]
  unfold zE
  rw [Monotone.map_max (fun a b h => EReal.toENNReal_le_toENNReal h)]
  have : ((cc N 0 1 : ℝ) : EReal).toENNReal = 0 := by
    apply EReal.toENNReal_of_nonpos
    have : cc N 0 1 ≤ 0 := by unfold cc; push_cast; nlinarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
    exact_mod_cast this
  rw [this]; simp

lemma zz_sub {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : ℕ → ℕ → Ω → EReal)
    (hx : ∀ s t ω, x s t ω ≠ ⊤) (hm : IsMeasurableFamily x)
    (h1 : ∀ (s t u : ℕ) (ω : Ω), s < t → t < u → x s u ω ≤ x s t ω + x t u ω)
    (h2 : S2 P x) (h3 : ∫⁻ ω, (x 0 1 ω).toENNReal ∂P < ⊤) (N : ℕ) :
    KingmanSubadditive.Ergodic.IsSubadditiveProcess P (zz x N) := by
  have hS1 := zz_S1 x hx h1 N
  have hT := KingmanSubadditive.BanachAlgebra.truncation_isSubadditive P (zz x N)
    (zz_meas x hm N) (fun s t u hst htu => Filter.Eventually.of_forall fun ω => hS1 s t u ω hst htu)
    (zz_S2 P x hm h2 N) (zz_S3' P x hx h3 N) (N + 1) (by omega)
  have heq : ∀ t ω, truncate (zz x N) (N + 1) 0 t ω = zz x N 0 t ω := by
    intro t ω
    unfold truncate
    apply max_eq_left
    have := cc_le_zz x hx N 0 t ω
    unfold cc at this
    push_cast at this ⊢
    linarith
  obtain ⟨_, _, _, ⟨hint, A, hA⟩⟩ := hT
  refine ⟨zz_meas x hm N, hS1, zz_S2 P x hm h2 N, ?_, A, ?_⟩
  · intro t ht
    have := hint t ht
    refine this.congr (Filter.Eventually.of_forall fun ω => heq t ω)
  · intro t ht
    have := hA t ht
    unfold KingmanSubadditive.Ergodic.mean at this ⊢
    simp_rw [heq] at this
    exact this

end K6aux

open K6aux in
theorem solution {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (hstat : IsStationarySeq P Y)
    (hlog : ∫⁻ ω, (logNorm (Y 1 ω)).toENNReal ∂P < ⊤) :
    ∃ ξ : Ω → EReal, Measurable ξ ∧
      (∀ᵐ ω ∂P, ξ ω ≠ ⊤ ∧
        Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * logNorm (prodRange Y 0 n ω))
          atTop (𝓝 (ξ ω))) ∧
      ∫⁻ ω, (ξ ω).toENNReal ∂P < ⊤ ∧
      Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
          eMean P (fun ω => logNorm (prodRange Y 0 n ω)))
        atTop (𝓝 (eMean P ξ)) := by
  obtain ⟨hm, h1, h2, h3⟩ :=
    KingmanSubadditive.BanachAlgebra.logNormProcess_conditions (𝕜 := 𝕜) P Y hY hstat hlog
  set x := logNormProcess Y with hxdef
  have hx : ∀ s t ω, x s t ω ≠ ⊤ := fun s t ω => logNorm_ne_top _
  have hsub := zz_sub P x hx hm h1 h2 h3
  have hT := fun N => KingmanSubadditive.Ergodic.theorem_1 P (zz x N) (hsub N)
  choose ξ0 hξint hξae hξL1 hξmean using hT
  set ξN : ℕ → Ω → ℝ := fun N => (hξint N).aemeasurable.mk (ξ0 N) with hξNdef
  have hξNm : ∀ N, Measurable (ξN N) := fun N => (hξint N).aemeasurable.measurable_mk
  have hξNeq : ∀ N, ξ0 N =ᵐ[P] ξN N := fun N => (hξint N).aemeasurable.ae_eq_mk
  have hξNint : ∀ N, Integrable (ξN N) P := fun N => (hξint N).congr (hξNeq N)
  have hgood : ∀ᵐ ω ∂P, ∀ N, Tendsto (fun n : ℕ => zz x N 0 n ω / (n : ℝ)) atTop
      (𝓝 (ξN N ω)) := by
    rw [ae_all_iff]; intro N
    filter_upwards [hξae N, hξNeq N] with ω h e
    rw [← e]; exact h
  set ξ : Ω → EReal := fun ω => ⨅ N, ((ξN N ω : ℝ) : EReal) with hξdef
  -- key pointwise inequality
  have hineq : ∀ (N n : ℕ) (ω : Ω), (((n : ℝ)⁻¹ : ℝ) : EReal) * x 0 n ω ≤
      ((zz x N 0 n ω / (n : ℝ) : ℝ) : EReal) := by
    intro N n ω
    have h0 : (0 : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) := by
      exact_mod_cast inv_nonneg.2 (Nat.cast_nonneg n)
    calc (((n : ℝ)⁻¹ : ℝ) : EReal) * x 0 n ω
        ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) * ((zz x N 0 n ω : ℝ) : EReal) :=
          mul_le_mul_of_nonneg_left (x_le_zz x hx N 0 n ω) h0
      _ = ((zz x N 0 n ω / (n : ℝ) : ℝ) : EReal) := by
          rw [← EReal.coe_mul, div_eq_inv_mul]
  have hpt : ∀ ω, (∀ N, Tendsto (fun n : ℕ => zz x N 0 n ω / (n : ℝ)) atTop
      (𝓝 (ξN N ω))) → Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * x 0 n ω) atTop
        (𝓝 (ξ ω)) := by
    intro ω hω
    by_cases hA : ∃ N : ℕ, -((N : ℝ) + 1) < ξN N ω
    · obtain ⟨N, hN⟩ := hA
      have hev : ∀ᶠ n : ℕ in atTop, (((n : ℝ)⁻¹ : ℝ) : EReal) * x 0 n ω =
          ((zz x N 0 n ω / (n : ℝ) : ℝ) : EReal) := by
        filter_upwards [(hω N).eventually (lt_mem_nhds hN), eventually_ge_atTop 1] with n hn hn1
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hgt : cc N 0 n < zz x N 0 n ω := by
          rw [lt_div_iff₀ hnpos] at hn
          unfold cc; push_cast; linarith
        have hgtE : ((cc N 0 n : ℝ) : EReal) < x 0 n ω := by
          by_contra hle
          push Not at hle
          have : zE x N 0 n ω = ((cc N 0 n : ℝ) : EReal) := max_eq_right hle
          have h' := coe_zz x hx N 0 n ω
          rw [this] at h'
          have := EReal.coe_injective h'
          linarith
        have hz : zE x N 0 n ω = x 0 n ω := max_eq_left hgtE.le
        rw [div_eq_inv_mul, EReal.coe_mul, coe_zz x hx, hz]
      have hlim : Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * x 0 n ω) atTop
          (𝓝 ((ξN N ω : ℝ) : EReal)) :=
        (((continuous_coe_real_ereal.tendsto _).comp (hω N))).congr' (hev.mono fun n h => h.symm)
      have hξω : ξ ω = ((ξN N ω : ℝ) : EReal) := by
        apply le_antisymm (iInf_le (fun M => ((ξN M ω : ℝ) : EReal)) N)
        apply le_iInf
        intro M
        exact le_of_tendsto_of_tendsto' hlim
          ((continuous_coe_real_ereal.tendsto _).comp (hω M)) (fun n => hineq M n ω)
      rw [hξω]; exact hlim
    · push Not at hA
      have hξω : ξ ω = ⊥ := by
        rw [EReal.eq_bot_iff_forall_lt]
        intro y
        obtain ⟨N, hN⟩ := exists_nat_gt (-y)
        calc ξ ω ≤ ((ξN N ω : ℝ) : EReal) := iInf_le (fun M => ((ξN M ω : ℝ) : EReal)) N
          _ < (y : EReal) := by
            have := hA N
            exact_mod_cast (show ξN N ω < y by linarith)
      rw [hξω, EReal.tendsto_nhds_bot_iff_real]
      intro r
      obtain ⟨N, hN⟩ := exists_nat_gt (-r)
      have hlt : ξN N ω < r := by have := hA N; linarith
      filter_upwards [(hω N).eventually (gt_mem_nhds hlt)] with n hn
      exact lt_of_le_of_lt (hineq N n ω) (by exact_mod_cast hn)
  have hξmeas : Measurable ξ := Measurable.iInf (fun N => (hξNm N).coe_real_ereal)
  have hξle0 : ∀ ω, ξ ω ≤ ((ξN 0 ω : ℝ) : EReal) := fun ω =>
    iInf_le (fun M => ((ξN M ω : ℝ) : EReal)) 0
  have hzint : ∀ N n : ℕ, 1 ≤ n → Integrable (zz x N 0 n) P := fun N n hn => (hsub N).2.2.2.1 n hn
  -- L¹ convergence of the means of the truncations
  have hL1' : ∀ N : ℕ, Tendsto (fun n : ℕ => ∫ ω, zz x N 0 n ω / (n : ℝ) ∂P) atTop
      (𝓝 (∫ ω, ξN N ω ∂P)) := by
    intro N
    rw [← integral_congr_ae (hξNeq N), tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ (hξL1 N)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← integral_sub ((hzint N n hn).div_const _) (hξint N)]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [Real.norm_eq_abs]
  have hγle : ∀ N n : ℕ, 1 ≤ n → ∫ ω, ξN N ω ∂P ≤ ∫ ω, zz x N 0 n ω / (n : ℝ) ∂P := by
    intro N n hn
    rw [← integral_congr_ae (hξNeq N), hξmean N, integral_div]
    obtain ⟨A, hA⟩ := (hsub N).2.2.2.2
    have hbdd : BddBelow (Set.range fun t : {t : ℕ // 1 ≤ t} =>
        KingmanSubadditive.Ergodic.mean P (zz x N) t / (t : ℝ)) := by
      refine ⟨-A, ?_⟩
      rintro _ ⟨t, rfl⟩
      have htpos : (0 : ℝ) < (t : ℕ) := by exact_mod_cast t.2
      rw [le_div_iff₀ htpos]
      exact hA t t.2
    exact ciInf_le hbdd ⟨n, hn⟩
  have hantiR : ∀ N M : ℕ, N ≤ M → ∀ᵐ ω ∂P, ξN M ω ≤ ξN N ω := by
    intro N M hNM
    filter_upwards [hgood] with ω hω
    exact le_of_tendsto_of_tendsto' (hω M) (hω N) (fun n =>
      div_le_div_of_nonneg_right (zz_anti x hx N M 0 n (Nat.zero_le n) hNM ω) (Nat.cast_nonneg n))
  have hlimξ0 := eMean_tendsto_iInf P (fun N ω => ((ξN N ω : ℝ) : EReal))
    (fun N => (hξNm N).coe_real_ereal)
    (fun N M hNM => (hantiR N M hNM).mono fun ω h => by exact_mod_cast h)
    (by simp_rw [toENNReal_coe_real]; exact (hξNint 0).lintegral_lt_top)
  have hlimξ : Tendsto (fun N => ((∫ ω, ξN N ω ∂P : ℝ) : EReal)) atTop (𝓝 (eMean P ξ)) := by
    refine hlimξ0.congr (fun N => ?_)
    exact eMean_coe P (hξNint N)
  have hantiI : Antitone (fun N => ((∫ ω, ξN N ω ∂P : ℝ) : EReal)) := by
    intro N M hNM
    show ((∫ ω, ξN M ω ∂P : ℝ) : EReal) ≤ ((∫ ω, ξN N ω ∂P : ℝ) : EReal)
    exact_mod_cast integral_mono_ae (hξNint M) (hξNint N) (hantiR N M hNM)
  have hEξle : ∀ N : ℕ, eMean P ξ ≤ ((∫ ω, ξN N ω ∂P : ℝ) : EReal) :=
    fun N => hantiI.le_of_tendsto hlimξ N
  have hemz : ∀ N n : ℕ, 1 ≤ n → eMean P (fun ω => zE x N 0 n ω) =
      ((∫ ω, zz x N 0 n ω ∂P : ℝ) : EReal) := by
    intro N n hn
    have : (fun ω => zE x N 0 n ω) = fun ω => ((zz x N 0 n ω : ℝ) : EReal) := by
      funext ω; exact (coe_zz x hx N 0 n ω).symm
    rw [this]; exact eMean_coe P (hzint N n hn)
  have hlimx : ∀ n : ℕ, 1 ≤ n → Tendsto (fun N => ((∫ ω, zz x N 0 n ω ∂P : ℝ) : EReal)) atTop
      (𝓝 (eMean P (fun ω => x 0 n ω))) := by
    intro n hn
    have hinf : ∀ ω, (⨅ N, zE x N 0 n ω) = x 0 n ω := by
      intro ω
      apply le_antisymm
      · by_contra hlt
        push Not at hlt
        obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
        obtain ⟨N, hN⟩ := exists_nat_gt (-r)
        have hc : cc N 0 n < r := by
          unfold cc
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          push_cast
          nlinarith
        have h1' : zE x N 0 n ω < (r : EReal) :=
          max_lt hr1 (by exact_mod_cast hc)
        exact absurd (lt_of_lt_of_le hr2 (iInf_le _ N)) (not_lt.2 h1'.le)
      · exact le_iInf fun N => le_max_left _ _
    have := eMean_tendsto_iInf P (fun N ω => zE x N 0 n ω)
      (fun N => (hm 0 n (by omega)).max measurable_const)
      (fun N M hNM => Filter.Eventually.of_forall fun ω => by
        rw [← coe_zz x hx, ← coe_zz x hx]
        exact_mod_cast zz_anti x hx N M 0 n (Nat.zero_le n) hNM ω)
      (by
        simp_rw [← coe_zz x hx, toENNReal_coe_real]
        exact (hzint 0 n hn).lintegral_lt_top)
    simp_rw [hinf] at this
    exact this.congr (fun N => hemz N n hn)
  have hinvc : ∀ n : ℕ, (0 : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) := fun n => by
    exact_mod_cast inv_nonneg.2 (Nat.cast_nonneg n)
  have hcoe_div : ∀ N n : ℕ, 1 ≤ n → (((n : ℝ)⁻¹ : ℝ) : EReal) * ((∫ ω, zz x N 0 n ω ∂P : ℝ) : EReal)
      = ((∫ ω, zz x N 0 n ω / (n : ℝ) ∂P : ℝ) : EReal) := by
    intro N n hn
    rw [← EReal.coe_mul, integral_div, div_eq_inv_mul]
  have hlow : ∀ n : ℕ, 1 ≤ n → eMean P ξ ≤
      (((n : ℝ)⁻¹ : ℝ) : EReal) * eMean P (fun ω => x 0 n ω) := by
    intro n hn
    have hne : (((n : ℝ)⁻¹ : ℝ) : EReal) ≠ 0 := by
      have : ((n : ℝ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast (show n ≠ 0 by omega))
      exact_mod_cast this
    have hcont := EReal.continuousAt_mul (p := ((((n : ℝ)⁻¹ : ℝ) : EReal),
      eMean P (fun ω => x 0 n ω))) (Or.inl hne) (Or.inl hne) (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))
    have hc := hcont.tendsto.comp (tendsto_const_nhds.prodMk_nhds (hlimx n hn))
    refine ge_of_tendsto' hc (fun N => ?_)
    show eMean P ξ ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) * ((∫ ω, zz x N 0 n ω ∂P : ℝ) : EReal)
    rw [hcoe_div N n hn]
    exact (hEξle N).trans (by exact_mod_cast hγle N n hn)
  have hup : ∀ N n : ℕ, 1 ≤ n → (((n : ℝ)⁻¹ : ℝ) : EReal) * eMean P (fun ω => x 0 n ω) ≤
      ((∫ ω, zz x N 0 n ω / (n : ℝ) ∂P : ℝ) : EReal) := by
    intro N n hn
    rw [← hcoe_div N n hn, ← hemz N n hn]
    exact mul_le_mul_of_nonneg_left
      (eMean_mono P (Filter.Eventually.of_forall fun ω => le_max_left _ _)) (hinvc n)
  refine ⟨ξ, hξmeas, ?_, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω
    exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) (hξle0 ω), hpt ω hω⟩
  · refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) (hξNint 0).lintegral_lt_top
    rw [← toENNReal_coe_real]
    exact EReal.toENNReal_le_toENNReal (hξle0 ω)
  · rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact lt_of_lt_of_le ha (hlow n hn)
    · intro b hb
      obtain ⟨N, hN⟩ := (hlimξ.eventually (gt_mem_nhds hb)).exists
      have := ((continuous_coe_real_ereal.tendsto _).comp (hL1' N)).eventually (gt_mem_nhds hN)
      filter_upwards [this, eventually_ge_atTop 1] with n h hn
      exact lt_of_le_of_lt (hup N n hn) h
