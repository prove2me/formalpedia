-- Prove2me | solution 1 for LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d1ba14fb-036a-59d9-950e-6550e30e5f8c

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib
import Theorems.Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq

set_option autoImplicit false

open scoped ComplexOrder

noncomputable section

namespace RS40E

open Complex Filter Topology Metric Set

theorem dist_ofReal (a b : ℝ) : dist (a : ℂ) (b : ℂ) = dist a b := by
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]

def rterm (d : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else d n / (n : ℝ) ^ σ

theorem term_eq_rterm (d : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n = ((rterm d σ n : ℝ) : ℂ) := by
  rw [LSeries.term_def, rterm]
  split_ifs with h
  · simp
  · push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast

theorem lseries_eq_ofReal_tsum (d : ℕ → ℝ) (σ : ℝ) :
    LSeries (fun n => (d n : ℂ)) (σ : ℂ) = ((∑' n, rterm d σ n : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (term_eq_rterm d σ)

theorem rterm_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (σ : ℝ) (n : ℕ) : 0 ≤ rterm d σ n := by
  unfold rterm; split_ifs
  · exact le_rfl
  · exact div_nonneg (hd n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

theorem lseries_im_eq_zero (d : ℕ → ℝ) (σ : ℝ) : (LSeries (fun n => (d n : ℂ)) (σ : ℂ)).im = 0 := by
  rw [lseries_eq_ofReal_tsum, ofReal_im]

theorem lseries_re_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (σ : ℝ) :
    0 ≤ (LSeries (fun n => (d n : ℂ)) (σ : ℂ)).re := by
  rw [lseries_eq_ofReal_tsum, ofReal_re]
  exact tsum_nonneg (rterm_nonneg hd σ)

theorem ray (Λ L : ℂ → ℂ) (y σ₁ : ℝ)
    (hΛ : ∀ σ : ℝ, y < σ → AnalyticAt ℂ Λ (σ : ℂ)) (hL : ∀ s : ℂ, y < s.re → AnalyticAt ℂ L s)
    (heq : ∀ s : ℂ, σ₁ < s.re → Complex.exp (L s) = Λ s) :
    ∀ σ : ℝ, y < σ → Λ =ᶠ[𝓝 (σ : ℂ)] fun s => Complex.exp (L s) := by
  let P : ℝ → Prop := fun σ => Λ =ᶠ[𝓝 (σ : ℂ)] fun s => Complex.exp (L s)

  have hopen : IsOpen {σ : ℝ | P σ} := by
    rw [Metric.isOpen_iff]
    intro σ hσ
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hσ
    refine ⟨ε / 2, half_pos hε, fun σ' hσ' => ?_⟩
    show Λ =ᶠ[𝓝 (σ' : ℂ)] fun s => Complex.exp (L s)
    refine Metric.eventually_nhds_iff.2 ⟨ε / 2, half_pos hε, fun z hz => hball ?_⟩
    have h1 : dist (σ' : ℂ) (σ : ℂ) < ε / 2 := by rw [dist_ofReal]; exact mem_ball.1 hσ'
    calc dist z (σ : ℂ) ≤ dist z (σ' : ℂ) + dist (σ' : ℂ) (σ : ℂ) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hz h1
      _ = ε := by ring

  have hclosed : IsOpen {σ : ℝ | y < σ ∧ ¬ P σ} := by
    rw [Metric.isOpen_iff]
    rintro σ ⟨hyσ, hnot⟩
    have h1 : AnalyticAt ℂ Λ (σ : ℂ) := hΛ σ hyσ
    have h2 : AnalyticAt ℂ (fun s => Complex.exp (L s)) (σ : ℂ) :=
      (hL σ (by simpa using hyσ)).cexp
    rcases h1.eventually_eq_or_eventually_ne h2 with h | h
    · exact absurd h hnot
    obtain ⟨ε, hε, hne⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
    refine ⟨min ε (σ - y), lt_min hε (by linarith), fun σ' hσ' => ⟨?_, fun hP' => ?_⟩⟩
    · have := lt_of_lt_of_le (mem_ball.1 hσ') (min_le_right _ _)
      rw [Real.dist_eq, abs_lt] at this
      linarith
    · by_cases hσσ : σ' = σ
      · exact hnot (hσσ ▸ hP')
      · have heqpt : Λ (σ' : ℂ) = Complex.exp (L (σ' : ℂ)) := hP'.eq_of_nhds
        have hd : dist (σ' : ℂ) (σ : ℂ) < ε := by
          rw [dist_ofReal]; exact lt_of_lt_of_le (mem_ball.1 hσ') (min_le_left _ _)
        have hmem : (σ' : ℂ) ∈ ({(σ : ℂ)}ᶜ : Set ℂ) := by
          simpa using (fun h => hσσ (by exact_mod_cast h) : (σ' : ℂ) ≠ (σ : ℂ))
        exact hne hd hmem heqpt

  set σ₂ : ℝ := max σ₁ y + 1 with hσ₂
  have hσ₂y : y < σ₂ := by rw [hσ₂]; linarith [le_max_right σ₁ y]
  have hne0 : P σ₂ := by
    show Λ =ᶠ[𝓝 (σ₂ : ℂ)] fun s => Complex.exp (L s)
    have : ∀ᶠ s in 𝓝 (σ₂ : ℂ), σ₁ < s.re := by
      apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      show σ₁ < (σ₂ : ℂ).re
      rw [ofReal_re, hσ₂]; linarith [le_max_left σ₁ y]
    filter_upwards [this] with s hs
    exact (heq s hs).symm

  haveI : PreconnectedSpace (Ioi y) := Subtype.preconnectedSpace isPreconnected_Ioi
  have hcl : IsClosed {p : Ioi y | P p.1} := by
    rw [← isOpen_compl_iff]
    have : {p : Ioi y | P p.1}ᶜ = ((↑) : Ioi y → ℝ) ⁻¹' {σ | y < σ ∧ ¬ P σ} := by
      ext p
      simp only [mem_compl_iff, mem_setOf_eq, mem_preimage]
      exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
    rw [this]
    exact hclosed.preimage continuous_subtype_val
  have hop : IsOpen {p : Ioi y | P p.1} := hopen.preimage continuous_subtype_val
  have hT : IsClopen {p : Ioi y | P p.1} := ⟨hcl, hop⟩
  have huniv := hT.eq_univ ⟨⟨σ₂, hσ₂y⟩, hne0⟩
  intro σ hσ
  have : (⟨σ, hσ⟩ : Ioi y) ∈ {p : Ioi y | P p.1} := by rw [huniv]; trivial
  exact this

end RS40E

open RS40E Complex Filter Topology Metric Set in
theorem solution
    (d : ℕ → ℝ) (hd : ∀ n : ℕ, 0 ≤ d n) (Λ : ℂ → ℂ) (x σ₀ : ℝ)
    (han : ∀ σ : ℝ, x < σ → AnalyticAt ℂ Λ (σ : ℂ))
    (heq : ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable (fun n => (d n : ℂ)) s ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) s) = Λ s) :
    LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ (x : EReal) ∧
      ∀ σ : ℝ, x < σ →
        LSeriesSummable (fun n => (d n : ℂ)) σ ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) σ) = Λ σ := by
  set f : ℕ → ℂ := fun n => (d n : ℂ) with hf
  have hf0 : 0 ≤ f := by
    intro n
    show (0 : ℂ) ≤ (d n : ℂ)
    exact_mod_cast hd n
  set L : ℂ → ℂ := LSeries f with hL
  have hLan : ∀ s : ℂ, LSeries.abscissaOfAbsConv f < s.re → AnalyticAt ℂ L s :=
    fun s hs => LSeries_analyticOnNhd f s hs

  have hxtop : LSeries.abscissaOfAbsConv f ≤ ((σ₀ + 1 : ℝ) : EReal) := by
    have h := (heq ((σ₀ + 1 : ℝ) : ℂ) (by simp)).1.abscissaOfAbsConv_le
    simpa using h

  have hmain : LSeries.abscissaOfAbsConv f ≤ (x : EReal) := by
    by_contra hcon
    push Not at hcon
    have hnetop : LSeries.abscissaOfAbsConv f ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hxtop
    have hnebot : LSeries.abscissaOfAbsConv f ≠ ⊥ := ne_bot_of_gt hcon
    set r : ℝ := (LSeries.abscissaOfAbsConv f).toReal with hr
    have hrx0 : (r : EReal) = LSeries.abscissaOfAbsConv f := EReal.coe_toReal hnetop hnebot
    have hxr : x < r := by rw [← EReal.coe_lt_coe_iff, hrx0]; exact hcon
    have hLan' : ∀ s : ℂ, r < s.re → AnalyticAt ℂ L s := fun s hs =>
      hLan s (by rw [← hrx0]; exact_mod_cast hs)

    have hray := ray Λ L r σ₀ (fun σ hσ => han σ (hxr.trans hσ)) hLan' (fun s hs => (heq s hs).2)
    have hval : ∀ σ : ℝ, r < σ → Λ σ = Complex.exp (L σ) := fun σ hσ => (hray σ hσ).eq_of_nhds
    have hre1 : ∀ σ : ℝ, r < σ → 1 ≤ (Λ σ).re := by
      intro σ hσ
      rw [hval σ hσ, hL, lseries_eq_ofReal_tsum, ← Complex.ofReal_exp, ofReal_re]
      exact Real.one_le_exp (tsum_nonneg (rterm_nonneg hd σ))

    have hΛr : AnalyticAt ℂ Λ (r : ℂ) := han r hxr
    have hcont : ContinuousAt (fun σ : ℝ => Λ (σ : ℂ)) r :=
      hΛr.continuousAt.comp_of_eq continuous_ofReal.continuousAt rfl
    have hre_r : 1 ≤ (Λ (r : ℂ)).re := by
      have h1 : Tendsto (fun σ : ℝ => (Λ (σ : ℂ)).re) (𝓝[>] r) (𝓝 (Λ (r : ℂ)).re) :=
        ((continuous_re.tendsto _).comp hcont.tendsto).mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto h1 (eventually_nhdsWithin_of_forall fun σ hσ => hre1 σ hσ)
    have hslit : Λ (r : ℂ) ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by linarith))

    obtain ⟨ρ₁, hρ₁, hanB⟩ := hΛr.exists_ball_analyticOnNhd
    obtain ⟨ρ₂, hρ₂, hslitB⟩ := Metric.eventually_nhds_iff.1
      (hΛr.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hslit))
    set ρ : ℝ := min ρ₁ ρ₂ with hρdef
    have hρ : 0 < ρ := lt_min hρ₁ hρ₂
    have hFdiff : DifferentiableOn ℂ (fun z => Complex.log (Λ z)) (ball (r : ℂ) ρ) := by
      intro z hz
      have hz1 : z ∈ ball (r : ℂ) ρ₁ := ball_subset_ball (min_le_left _ _) hz
      have hz2 : dist z (r : ℂ) < ρ₂ := lt_of_lt_of_le (mem_ball.1 hz) (min_le_right _ _)
      exact ((hanB z hz1).differentiableAt.clog (hslitB hz2)).differentiableWithinAt

    set V : Set ℂ := ball (r : ℂ) ρ ∩ {s : ℂ | r < s.re} with hV
    have hVpre : IsPreconnected V := ((convex_ball _ _).inter (convex_halfSpace_re_gt r)).isPreconnected
    set σs : ℝ := r + ρ / 2 with hσs
    have hσsr : r < σs := by rw [hσs]; linarith
    have hσsV : (σs : ℂ) ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_ofReal, Real.dist_eq, hσs, show r + ρ / 2 - r = ρ / 2 by ring, abs_of_pos (half_pos hρ)]
        linarith
      · show r < (σs : ℂ).re
        rw [ofReal_re]; exact hσsr
    have hFan : AnalyticOnNhd ℂ (fun z => Complex.log (Λ z)) V :=
      (hFdiff.analyticOnNhd isOpen_ball).mono inter_subset_left
    have hLanV : AnalyticOnNhd ℂ L V := fun s hs => hLan' s hs.2

    have hnear : (fun z => Complex.log (Λ z)) =ᶠ[𝓝 (σs : ℂ)] L := by
      have h1 := hray σs hσsr
      have hLc : ContinuousAt L (σs : ℂ) := (hLan' (σs : ℂ) (by rw [ofReal_re]; exact hσsr)).continuousAt
      have him0 : (L (σs : ℂ)).im = 0 := by rw [hL]; exact lseries_im_eq_zero d σs
      have him : ∀ᶠ z in 𝓝 (σs : ℂ), (L z).im ∈ Ioo (-Real.pi) Real.pi := by
        have hc : ContinuousAt (fun z => (L z).im) (σs : ℂ) := continuous_im.continuousAt.comp hLc
        apply hc.preimage_mem_nhds
        apply isOpen_Ioo.mem_nhds
        rw [him0]; exact ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
      filter_upwards [h1, him] with z hz1 hz2
      show Complex.log (Λ z) = L z
      rw [hz1, Complex.log_exp hz2.1 hz2.2.le]
    have hEq : EqOn (fun z => Complex.log (Λ z)) L V :=
      hFan.eqOn_of_preconnected_of_eventuallyEq hLanV hVpre hσsV hnear

    have hlt := LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball hf0 (x := r) (le_of_eq hrx0.symm) hρ hFdiff
      (fun s hs hsr => hEq ⟨hs, hsr⟩)
    rw [← hrx0] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hmain, fun σ hσ => ?_⟩
  have hσ' : LSeries.abscissaOfAbsConv f < ((σ : ℂ)).re := lt_of_le_of_lt hmain (by simp; exact_mod_cast hσ)
  have hsum : LSeriesSummable f σ := LSeriesSummable_of_abscissaOfAbsConv_lt_re hσ'
  refine ⟨hsum, ?_⟩
  have hray := ray Λ L x σ₀ han
    (fun s hs => hLan s (lt_of_le_of_lt hmain (by exact_mod_cast hs))) (fun s hs => (heq s hs).2)
  exact ((hray σ hσ).eq_of_nhds).symm

end
end S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
end P2MW
export P2MW.S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq (solution)
