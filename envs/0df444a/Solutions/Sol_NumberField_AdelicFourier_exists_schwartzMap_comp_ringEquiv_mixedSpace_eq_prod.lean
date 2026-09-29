-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6d805ed6-b16f-530e-925e-94735ea3f287

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod

set_option autoImplicit false

open NumberField NumberField.InfinitePlace MeasureTheory
open scoped SchwartzMap

namespace F1Bump

noncomputable def bump {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E] (c : E) (ε : ℝ) (hε : 0 < ε) :
    ContDiffBump c :=
  ⟨ε / 4, ε / 2, by positivity, by linarith⟩

theorem bump_rOut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E] (c : E) (ε : ℝ) (hε : 0 < ε) :
    (bump c ε hε).rOut = ε / 2 := rfl

theorem zero_of_not_mem_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E] {c : E}
    (f : ContDiffBump c) {x : E} (hx : x ∉ Metric.closedBall c f.rOut) : (f : E → ℝ) x = 0 := by
  have : x ∉ Function.support (f : E → ℝ) := by
    rw [f.support_eq]
    exact fun h => hx (Metric.ball_subset_closedBall h)
  simpa [Function.mem_support] using this

theorem bump_pos_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E] {c : E}
    (f : ContDiffBump c) : 0 < (f : E → ℝ) c := by
  rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)]
  exact one_pos

theorem tsupport_comp_subset_ball {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    {e : X → E} (he : Isometry e) (t : X) (ε : ℝ) (hε : 0 < ε) :
    tsupport (fun y => (((bump (e t) ε hε : E → ℝ) (e y) : ℝ) : ℂ)) ⊆ Metric.ball t ε := by
  intro y hy
  have h1 : tsupport (fun y => (((bump (e t) ε hε : E → ℝ) (e y) : ℝ) : ℂ)) ⊆ e ⁻¹' tsupport (fun s => (((bump (e t) ε hε : E → ℝ) s : ℝ) : ℂ)) :=
    tsupport_comp_subset_preimage (fun s => (((bump (e t) ε hε : E → ℝ) s : ℝ) : ℂ)) he.continuous
  have h2 : tsupport (fun s => (((bump (e t) ε hε : E → ℝ) s : ℝ) : ℂ)) ⊆ tsupport (bump (e t) ε hε : E → ℝ) :=
    tsupport_comp_subset (Complex.ofReal_zero) _
  have hy' := h2 (h1 hy)
  rw [(bump (e t) ε hε).tsupport_eq, bump_rOut, Metric.mem_closedBall] at hy'
  rw [Metric.mem_ball, ← he.dist_eq]
  linarith

end F1Bump

open F1Bump in
open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (t : (w : InfinitePlace F) → w.Completion)
    (U : (w : InfinitePlace F) → Set w.Completion)
    (hU : ∀ w, IsOpen (U w)) (ht : ∀ w, t w ∈ U w) :
    ∃ (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (gw : (w : InfinitePlace F) → w.Completion → ℂ),
      (∀ x : InfiniteAdeleRing F, g (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∏ w, gw w (x w)) ∧
      (∀ w, Continuous (gw w)) ∧ (∀ w, HasCompactSupport (gw w)) ∧ (∀ w, tsupport (gw w) ⊆ U w) ∧
      (∀ w y, (gw w y).im = 0 ∧ 0 ≤ (gw w y).re) ∧ (∀ w, 0 < (gw w (t w)).re) := by
  classical

  have hball : ∀ w, ∃ ε > 0, Metric.ball (t w) ε ⊆ U w := fun w => Metric.isOpen_iff.mp (hU w) (t w) (ht w)
  choose ε hε hεU using hball

  set bR : ∀ r : {w : InfinitePlace F // w.IsReal}, ℝ → ℝ :=
    fun r => (bump (Completion.extensionEmbeddingOfIsReal r.2 (t r.1)) (ε r.1) (hε r.1) : ℝ → ℝ) with hbR
  set bC : ∀ c : {w : InfinitePlace F // w.IsComplex}, ℂ → ℝ :=
    fun c => (bump (Completion.extensionEmbedding c.1 (t c.1)) (ε c.1) (hε c.1) : ℂ → ℝ) with hbC

  set g₀ : mixedEmbedding.mixedSpace F → ℂ :=
    fun u => (((∏ r, bR r (u.1 r)) * ∏ c, bC c (u.2 c) : ℝ) : ℂ) with hg₀
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g₀ := by
    refine (Complex.ofRealCLM.contDiff.of_le le_top).comp ?_
    refine ContDiff.mul (contDiff_prod fun r _ => ?_) (contDiff_prod fun c _ => ?_)
    · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : mixedEmbedding.mixedSpace F => u.1 r) :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) r).comp
          (ContinuousLinearMap.fst ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
            ({w : InfinitePlace F // w.IsComplex} → ℂ))).contDiff
      exact ((bump _ _ _).contDiff).comp h1
    · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : mixedEmbedding.mixedSpace F => u.2 c) :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ) c).comp
          (ContinuousLinearMap.snd ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
            ({w : InfinitePlace F // w.IsComplex} → ℂ))).contDiff
      exact ((bump _ _ _).contDiff).comp h1
  have hcs : HasCompactSupport g₀ := by
    refine HasCompactSupport.intro (K := (Set.pi Set.univ fun r : {w : InfinitePlace F // w.IsReal} =>
        Metric.closedBall (Completion.extensionEmbeddingOfIsReal r.2 (t r.1)) (ε r.1 / 2)) ×ˢ
      (Set.pi Set.univ fun c : {w : InfinitePlace F // w.IsComplex} =>
        Metric.closedBall (Completion.extensionEmbedding c.1 (t c.1)) (ε c.1 / 2)))
      ((isCompact_univ_pi fun r => isCompact_closedBall _ _).prod (isCompact_univ_pi fun c => isCompact_closedBall _ _)) ?_
    intro u hu
    simp only [Set.mem_prod, Set.mem_univ_pi, not_and_or, not_forall] at hu
    simp only [hg₀, Complex.ofReal_eq_zero, mul_eq_zero]
    rcases hu with ⟨r, hr⟩ | ⟨c, hc⟩
    · left
      exact Finset.prod_eq_zero (Finset.mem_univ r) (zero_of_not_mem_closedBall _ (by rwa [bump_rOut]))
    · right
      exact Finset.prod_eq_zero (Finset.mem_univ c) (zero_of_not_mem_closedBall _ (by rwa [bump_rOut]))
  set g : 𝓢(mixedEmbedding.mixedSpace F, ℂ) := hcs.toSchwartzMap hsmooth with hgdef
  have hg : ∀ u, g u = g₀ u := fun u => rfl

  set gw : (w : InfinitePlace F) → w.Completion → ℂ := fun w y =>
    if hw : w.IsReal then ((bR ⟨w, hw⟩ (Completion.extensionEmbeddingOfIsReal hw y) : ℝ) : ℂ)
    else ((bC ⟨w, not_isReal_iff_isComplex.mp hw⟩ (Completion.extensionEmbedding w y) : ℝ) : ℂ) with hgw
  refine ⟨g, gw, fun x => ?_, fun w => ?_, fun w => ?_, fun w => ?_, fun w y => ?_, fun w => ?_⟩
  ·
    rw [hg, hg₀]
    simp only
    rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun w : InfinitePlace F => w.IsReal), Complex.ofReal_mul,
      Complex.ofReal_prod, Complex.ofReal_prod]
    congr 1
    · refine Finset.prod_congr rfl fun r _ => ?_
      rw [hgw]; simp only [dif_pos r.2]
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    · set eqv : {w : InfinitePlace F // ¬ w.IsReal} ≃ {w : InfinitePlace F // w.IsComplex} :=
        Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ w.IsReal) (q := fun w : InfinitePlace F => w.IsComplex)
          (fun w => not_isReal_iff_isComplex) with heqv
      refine (Fintype.prod_equiv eqv (fun r => gw r.1 (x r.1))
        (fun c => (((bC c ((InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 c)) : ℝ) : ℂ)) fun r => ?_).symm
      have e : eqv r = ⟨r.1, not_isReal_iff_isComplex.mp r.2⟩ := rfl
      rw [hgw]; simp only [dif_neg r.2]
      rw [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  ·
    by_cases hw : w.IsReal
    · rw [hgw]; simp only [dif_pos hw]
      exact Complex.continuous_ofReal.comp ((bump _ _ _).continuous.comp
        (Completion.isometry_extensionEmbeddingOfIsReal hw).continuous)
    · rw [hgw]; simp only [dif_neg hw]
      exact Complex.continuous_ofReal.comp ((bump _ _ _).continuous.comp
        (Completion.isometry_extensionEmbedding w).continuous)
  ·
    by_cases hw : w.IsReal
    · rw [hgw]; simp only [dif_pos hw]
      exact (((bump _ _ _).hasCompactSupport.comp_left Complex.ofReal_zero).comp_isClosedEmbedding
        (Completion.isometry_extensionEmbeddingOfIsReal hw).isClosedEmbedding)
    · rw [hgw]; simp only [dif_neg hw]
      exact (((bump _ _ _).hasCompactSupport.comp_left Complex.ofReal_zero).comp_isClosedEmbedding
        (Completion.isometry_extensionEmbedding w).isClosedEmbedding)
  ·
    by_cases hw : w.IsReal
    · rw [hgw]; simp only [dif_pos hw]
      exact (tsupport_comp_subset_ball (Completion.isometry_extensionEmbeddingOfIsReal hw) (t w) (ε w) (hε w)).trans (hεU w)
    · rw [hgw]; simp only [dif_neg hw]
      exact (tsupport_comp_subset_ball (Completion.isometry_extensionEmbedding w) (t w) (ε w) (hε w)).trans (hεU w)
  ·
    by_cases hw : w.IsReal
    · rw [hgw]; simp only [dif_pos hw, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨trivial, (bump _ _ _).nonneg⟩
    · rw [hgw]; simp only [dif_neg hw, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨trivial, (bump _ _ _).nonneg⟩
  ·
    by_cases hw : w.IsReal
    · rw [hgw]; simp only [dif_pos hw, Complex.ofReal_re]
      exact bump_pos_center _
    · rw [hgw]; simp only [dif_neg hw, Complex.ofReal_re]
      exact bump_pos_center _

end S_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod (solution)
