-- Prove2me | solution 1 for MobilePromo.lemma_A1_i
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:56:04.220818+00:00
-- url     : https://prove2.me/submissions/e7038f33-d6d3-466a-b541-510b62d8a00f

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

open Filter Topology MobilePromo

namespace MobilePromo.LemmaA1iProof

theorem deriv_nonneg_of_min_left {g : ℝ → ℝ} {a b x y d : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x < y)
    (hd : HasDerivWithinAt g d (Set.Icc a b) x)
    (hmin : ∀ z ∈ Set.Icc a b, g x ≤ g z) :
    0 ≤ d := by
  have hsub : Set.Ioc x y ⊆ Set.Icc a b :=
    Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hx.1 hy.2)
  have hd_sub : HasDerivWithinAt g d (Set.Ioc x y) x := hd.mono hsub
  have htend : Tendsto (slope g x) (𝓝[Set.Ioc x y \ {x}] x) (𝓝 d) :=
    hasDerivWithinAt_iff_tendsto_slope.mp hd_sub
  have hdiff_eq : Set.Ioc x y \ {x} = Set.Ioc x y := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hz => hz.1.ne'
  rw [hdiff_eq] at htend
  have hmem_cl : x ∈ closure (Set.Ioc x y) := by
    rw [closure_Ioc hxy.ne]
    exact Set.left_mem_Icc.mpr hxy.le
  have : NeBot (𝓝[Set.Ioc x y] x) := mem_closure_iff_nhdsWithin_neBot.mp hmem_cl
  refine ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun z hz => ?_)
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hmin z (hsub hz))) (sub_nonneg.mpr hz.1.le)

theorem deriv_nonpos_of_min_right {g : ℝ → ℝ} {a b x y d : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x < y)
    (hd : HasDerivWithinAt g d (Set.Icc a b) y)
    (hmin : ∀ z ∈ Set.Icc a b, g y ≤ g z) :
    d ≤ 0 := by
  have hsub : Set.Ico x y ⊆ Set.Icc a b :=
    Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc hx.1 hy.2)
  have hd_sub : HasDerivWithinAt g d (Set.Ico x y) y := hd.mono hsub
  have htend : Tendsto (slope g y) (𝓝[Set.Ico x y \ {y}] y) (𝓝 d) :=
    hasDerivWithinAt_iff_tendsto_slope.mp hd_sub
  have hdiff_eq : Set.Ico x y \ {y} = Set.Ico x y := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hz => hz.2.ne
  rw [hdiff_eq] at htend
  have hmem_cl : y ∈ closure (Set.Ico x y) := by
    rw [closure_Ico hxy.ne]
    exact Set.right_mem_Icc.mpr hxy.le
  have : NeBot (𝓝[Set.Ico x y] y) := mem_closure_iff_nhdsWithin_neBot.mp hmem_cl
  refine le_of_tendsto htend (eventually_nhdsWithin_of_forall fun z hz => ?_)
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmin z (hsub hz)))
    (sub_nonpos.mpr hz.2.le)

end MobilePromo.LemmaA1iProof

open MobilePromo.LemmaA1iProof in
theorem solution (M : Model) (h1 : Assumption1 M) (l : Fin M.L) (α : ℝ) (γl : Param (M.n l))
    (hγ : γl ∈ M.Γ₀ l) :
    ∃! b, b ∈ M.B ∧ ∀ b' ∈ M.B, f M l b α γl ≤ f M l b' α γl := by
  let p : ℝ → ℝ := M.p l γl
  let g : ℝ → ℝ := fun b => f M l b α γl
  have huniq_B : UniqueDiffOn ℝ M.B := uniqueDiffOn_Icc M.bmin_lt_bmax
  have hmaps : Set.MapsTo (fun b : ℝ => (γl, b)) M.B (M.Γ l ×ˢ M.B) :=
    fun b hb => ⟨M.Γ₀_subset l hγ, hb⟩
  have hp_cd : ContDiffOn ℝ 2 p M.B :=
    (h1.contDiffOn l).comp (contDiffOn_const.prodMk contDiffOn_id) hmaps
  have hp_diff : DifferentiableOn ℝ p M.B := hp_cd.differentiableOn (by simp)
  have hg_cont : ContinuousOn g M.B :=
    hp_diff.continuousOn.mul ((continuousOn_id.sub continuousOn_const).sub continuousOn_const)
  have hB_ne : M.B.Nonempty := Set.nonempty_Icc.mpr M.bmin_lt_bmax.le
  obtain ⟨b₀, hb₀_mem, hb₀_min⟩ := isCompact_Icc.exists_isMinOn hB_ne hg_cont
  have hlog_deriv : ∀ b ∈ M.B,
      HasDerivWithinAt (fun x => Real.log (p x))
        ((p b)⁻¹ * derivWithin p M.B b) M.B b := by
    intro b hb
    exact HasDerivAt.comp_hasDerivWithinAt b
      (Real.hasDerivAt_log (h1.pos l γl hγ b hb).ne')
      (hp_diff b hb).hasDerivWithinAt
  have hlog_diff : DifferentiableOn ℝ (fun x => Real.log (p x)) M.B :=
    fun b hb => (hlog_deriv b hb).differentiableWithinAt
  have hlog_anti : AntitoneOn (derivWithin (fun x => Real.log (p x)) M.B) M.B :=
    (h1.logConcave l γl hγ).antitoneOn_derivWithin hlog_diff
  have hg_deriv : ∀ b ∈ M.B,
      HasDerivWithinAt g (derivWithin p M.B b * (b - M.e - α) + p b) M.B b := by
    intro b hb
    have hlin : HasDerivWithinAt (fun x : ℝ => x - M.e - α) 1 M.B b :=
      (((hasDerivAt_id b).sub_const M.e).sub_const α).hasDerivWithinAt
    have hmul : HasDerivWithinAt g (derivWithin p M.B b * (b - M.e - α) + p b * 1) M.B b :=
      (hp_diff b hb).hasDerivWithinAt.mul hlin
    simpa only [mul_one] using hmul
  have hmin_unique : ∀ b₁ b₂ : ℝ,
      (b₁ ∈ M.B ∧ ∀ b' ∈ M.B, g b₁ ≤ g b') →
      (b₂ ∈ M.B ∧ ∀ b' ∈ M.B, g b₂ ≤ g b') → b₁ = b₂ := by
    rintro b₁ b₂ ⟨hb₁, hmin₁⟩ ⟨hb₂, hmin₂⟩
    suffices hle : ∀ u v : ℝ, u ∈ M.B → v ∈ M.B →
        (∀ b' ∈ M.B, g u ≤ g b') → (∀ b' ∈ M.B, g v ≤ g b') → ¬ (u < v) by
      rcases lt_trichotomy b₁ b₂ with hlt | heq | hgt
      · exact absurd hlt (hle b₁ b₂ hb₁ hb₂ hmin₁ hmin₂)
      · exact heq
      · exact absurd hgt (hle b₂ b₁ hb₂ hb₁ hmin₂ hmin₁)
    intro u v hu hv hmu hmv huv
    have hd_ge : 0 ≤ derivWithin p M.B u * (u - M.e - α) + p u :=
      deriv_nonneg_of_min_left hu hv huv (hg_deriv u hu) hmu
    have hd_le : derivWithin p M.B v * (v - M.e - α) + p v ≤ 0 :=
      deriv_nonpos_of_min_right hu hv huv (hg_deriv v hv) hmv
    have hpu : 0 < p u := h1.pos l γl hγ u hu
    have hpv : 0 < p v := h1.pos l γl hγ v hv
    have hp'u : 0 < derivWithin p M.B u := h1.deriv_pos l γl hγ u hu
    have hp'v : 0 < derivWithin p M.B v := h1.deriv_pos l γl hγ v hv
    have hlu : derivWithin (fun x => Real.log (p x)) M.B u = (p u)⁻¹ * derivWithin p M.B u :=
      (hlog_deriv u hu).derivWithin (huniq_B u hu)
    have hlv : derivWithin (fun x => Real.log (p x)) M.B v = (p v)⁻¹ * derivWithin p M.B v :=
      (hlog_deriv v hv).derivWithin (huniq_B v hv)
    have hanti := hlog_anti hu hv huv.le
    rw [hlu, hlv, ← div_eq_inv_mul, ← div_eq_inv_mul] at hanti
    have hrec_le : p u / derivWithin p M.B u ≤ p v / derivWithin p M.B v := by
      have hinv := inv_anti₀ (div_pos hp'v hpv) hanti
      simpa [inv_div] using hinv
    have hψ_u : 0 ≤ (u - M.e - α) + p u / derivWithin p M.B u := by
      have hdiv := div_nonneg hd_ge hp'u.le
      have heq : (derivWithin p M.B u * (u - M.e - α) + p u) / derivWithin p M.B u =
          (u - M.e - α) + p u / derivWithin p M.B u := by
        field_simp [hp'u.ne']
      linarith
    have hψ_v : (v - M.e - α) + p v / derivWithin p M.B v ≤ 0 := by
      have hdiv := div_nonpos_of_nonpos_of_nonneg hd_le hp'v.le
      have heq : (derivWithin p M.B v * (v - M.e - α) + p v) / derivWithin p M.B v =
          (v - M.e - α) + p v / derivWithin p M.B v := by
        field_simp [hp'v.ne']
      linarith
    linarith
  refine ⟨b₀, ⟨hb₀_mem, fun b' hb' => hb₀_min hb'⟩, fun b hb => ?_⟩
  exact hmin_unique b b₀ hb ⟨hb₀_mem, fun b' hb' => hb₀_min hb'⟩
