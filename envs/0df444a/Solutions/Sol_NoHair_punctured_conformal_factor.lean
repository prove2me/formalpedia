-- Prove2me | solution 1 for NoHair.punctured_conformal_factor
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:28:47.63299+00:00
-- url     : https://prove2.me/submissions/b119fd6e-bcc9-45a3-bdf4-9462b29c74d5

import Theorems.Thm_HunterPDE_Harmonic_strong_maximum_principle
import Theorems.Thm_YukawaPotential_yukawaPotential_laplacian

open Set Metric Filter Topology InnerProductSpace
open scoped ContDiff

private abbrev X := EuclideanSpace ℝ (Fin 3)
private abbrev puncture : Set X := {0}ᶜ

private lemma harmonic_inverse : HarmonicOnNhd (fun x : X => 1 / ‖x‖) puncture := by
  have h : HarmonicOnNhd (fun x : X => -(1 / ‖x‖)) puncture := by
    intro x hx
    change x ≠ 0 at hx
    refine ⟨(contDiffAt_const.div (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx)).neg, ?_⟩
    filter_upwards [eventually_ne_nhds hx] with y hy
    simpa [YukawaPotential.yukawaPotential, neg_div] using
      YukawaPotential.yukawaPotential_laplacian 1 0 0 y hy
  have e : -(fun x : X => -(1 / ‖x‖)) = (fun x : X => 1 / ‖x‖) := by
    funext x
    simp only [Pi.neg_apply, neg_neg]
  exact e ▸ h.neg

private lemma nonpos_on_puncture (f : X → ℝ) (hf : HarmonicOnNhd f puncture)
    (small : ∃ d : ℝ, 0 < d ∧ ∀ x, 0 < ‖x‖ → ‖x‖ < d → f x ≤ 0)
    (large : ∃ L : ℝ, ∀ x, L < ‖x‖ → f x ≤ 0) :
    ∀ x, x ≠ 0 → f x ≤ 0 := by
  obtain ⟨d, hd, hs⟩ := small
  obtain ⟨L, hl⟩ := large
  intro x hx
  by_contra! hpos
  let K : Set X := closedBall 0 L ∩ {y | d ≤ ‖y‖}
  have memK (y : X) : y ∈ K ↔ ‖y‖ ≤ L ∧ d ≤ ‖y‖ := by simp [K, mem_closedBall]
  have inside (y : X) (hy : y ≠ 0) (hfy : 0 < f y) : y ∈ K := by
    apply (memK y).2
    constructor
    · by_contra! h
      exact hfy.not_ge (hl y h)
    · by_contra! h
      exact hfy.not_ge (hs y (norm_pos_iff.mpr hy) h)
  have hp (y : X) (hy : y ∈ K) : y ∈ puncture := by
    exact norm_pos_iff.mp (hd.trans_le ((memK y).1 hy).2)
  have hK : IsCompact K := (isCompact_closedBall (0 : X) L).inter_right
    (isClosed_le continuous_const continuous_norm)
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, inside x hx hpos⟩
    (hf.contDiffOn.continuousOn.mono (fun _ hy => hp _ hy))
  have hzp := hpos.trans_le (hmax (inside x hx hpos))
  have hsub : HunterPDE.Harmonic.IsSubharmonicOn puncture f :=
    ⟨hf.contDiffOn, fun y hy => le_of_eq ((hf y hy).2.self_of_nhds.symm)⟩
  have hrank : 1 < Module.rank ℝ X :=
    Module.one_lt_rank_of_one_lt_finrank (by rw [finrank_euclideanSpace_fin]; decide)
  have hconn := (isConnected_compl_singleton_of_one_lt_rank hrank (0 : X)).isPreconnected
  obtain ⟨c, hc⟩ := HunterPDE.Harmonic.strong_maximum_principle isOpen_compl_singleton
    hconn hsub ⟨z, hp z hz, fun y hy => by
      by_cases h : 0 < f y
      · exact hmax (inside y hy h)
      · exact (le_of_not_gt h).trans hzp.le⟩
  let p : X := EuclideanSpace.single 0 (d / 2)
  have hpn : ‖p‖ = d / 2 := by simp [p, Real.norm_eq_abs, abs_of_pos hd, hd.le]
  have hpp : 0 < ‖p‖ := by rw [hpn]; exact half_pos hd
  have bound := hs p hpp (by rw [hpn]; exact half_lt_self hd)
  rw [hc p (norm_pos_iff.mp hpp), ← hc z (hp z hz)] at bound
  exact hzp.not_ge bound

private lemma upper_zero (w : X → ℝ) (hw : HarmonicOnNhd w puncture)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧
      ∀ x, 0 < ‖x‖ → ‖x‖ < d → ‖x‖ * w x ≤ ε)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → w x ≤ ε) :
    ∀ x, x ≠ 0 → w x ≤ 0 := by
  intro x hx
  by_contra! hpos
  have hfac : 0 < 1 + 1 / ‖x‖ := by positivity
  let ε := w x / (2 * (1 + 1 / ‖x‖))
  have he : 0 < ε := div_pos hpos (mul_pos (by norm_num) hfac)
  let B := fun y : X => w y - ε * (1 + 1 / ‖y‖)
  have harm : HarmonicOnNhd B puncture := hw.sub
    (((harmonicOnNhd_const 1).add harmonic_inverse).const_smul (c := ε))
  have small : ∃ d : ℝ, 0 < d ∧ ∀ y, 0 < ‖y‖ → ‖y‖ < d → B y ≤ 0 := by
    obtain ⟨d, hd, hy⟩ := hsmall ε he
    refine ⟨d, hd, fun y hr hd' => ?_⟩
    have hdiv : w y ≤ ε / ‖y‖ :=
      (le_div_iff₀ hr).2 (by simpa only [mul_comm] using hy y hr hd')
    dsimp only [B]
    rw [show ε / ‖y‖ = ε * (1 / ‖y‖) by ring] at hdiv
    linarith only [hdiv, he]
  have large : ∃ L : ℝ, ∀ y, L < ‖y‖ → B y ≤ 0 := by
    obtain ⟨L, hL⟩ := hlarge ε he
    refine ⟨L, fun y hy => ?_⟩
    have h := hL y hy
    have ht : 0 ≤ ε * (1 / ‖y‖) := by positivity
    dsimp only [B]
    linarith
  have hbound := nonpos_on_puncture B harm small large x hx
  have heq : ε * (1 + 1 / ‖x‖) = w x / 2 := by
    dsimp only [ε]
    field_simp [hfac.ne']
  dsimp only [B] at hbound
  linarith only [hbound, heq, hpos]

theorem solution (U : X → ℝ) (b : ℝ) (hU : HarmonicOnNhd U ({0}ᶜ))
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε)
    (h₀ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x, 0 < ‖x‖ → ‖x‖ < δ → |‖x‖ * U x - b| ≤ ε) :
    ∀ x, x ≠ 0 → U x = 1 + b / ‖x‖ := by
  let W := fun x : X => U x - (1 + b * (1 / ‖x‖))
  have hw : HarmonicOnNhd W puncture :=
    hU.sub ((harmonicOnNhd_const 1).add (harmonic_inverse.const_smul (c := b)))
  have s (ε : ℝ) (he : 0 < ε) : ∃ d : ℝ, 0 < d ∧
      ∀ x, 0 < ‖x‖ → ‖x‖ < d → |‖x‖ * W x| ≤ ε := by
    obtain ⟨d, hd, h⟩ := h₀ (ε / 2) (half_pos he)
    refine ⟨min d (ε / 2), lt_min hd (half_pos he), fun x hx hx' => ?_⟩
    have hmul : ‖x‖ * W x = (‖x‖ * U x - b) - ‖x‖ := by
      dsimp only [W]
      field_simp [hx.ne'] <;> ring
    rw [hmul]
    have tri := abs_sub (‖x‖ * U x - b) ‖x‖
    rw [abs_of_pos hx] at tri
    linarith only [tri, h x hx (lt_min_iff.mp hx').1, (lt_min_iff.mp hx').2]
  have l (ε : ℝ) (he : 0 < ε) : ∃ L : ℝ, ∀ x, L < ‖x‖ → |W x| ≤ ε := by
    obtain ⟨L, hL⟩ := hfar (ε / 2) (half_pos he)
    refine ⟨max L (|b| / (ε / 2)), fun x hx => ?_⟩
    have hsize := (max_lt_iff.mp hx).2
    have hr : 0 < ‖x‖ := (div_nonneg (abs_nonneg b) (half_pos he).le).trans_lt hsize
    have hfrac : |b| / ‖x‖ ≤ ε / 2 := (div_le_iff₀ hr).2 (by
      linarith only [(div_lt_iff₀ (half_pos he)).1 hsize])
    have tri := abs_sub (U x - 1) (b / ‖x‖)
    rw [abs_div, abs_of_pos hr] at tri
    have heq : W x = (U x - 1) - b / ‖x‖ := by dsimp only [W]; ring
    rw [heq]
    linarith only [tri, hfrac, hL x (max_lt_iff.mp hx).1]
  intro x hx
  have hplus := upper_zero W hw (fun ε he => by
    obtain ⟨d, hd, hs⟩ := s ε he
    exact ⟨d, hd, fun y hy hd' => (le_abs_self _).trans (hs y hy hd')⟩)
    (fun ε he => by
      obtain ⟨L, hl⟩ := l ε he
      exact ⟨L, fun y hy => (le_abs_self _).trans (hl y hy)⟩) x hx
  have hminus := upper_zero (-W) hw.neg (fun ε he => by
    obtain ⟨d, hd, hs⟩ := s ε he
    refine ⟨d, hd, ?_⟩
    intro y hy hd'
    simpa only [Pi.neg_apply, mul_neg] using (neg_le_abs (‖y‖ * W y)).trans (hs y hy hd'))
    (fun ε he => by
      obtain ⟨L, hl⟩ := l ε he
      exact ⟨L, fun y hy => (neg_le_abs _).trans (hl y hy)⟩) x hx
  change -(W x) ≤ 0 at hminus
  dsimp only [W] at hplus hminus
  rw [show b / ‖x‖ = b * (1 / ‖x‖) by ring]
  linarith
