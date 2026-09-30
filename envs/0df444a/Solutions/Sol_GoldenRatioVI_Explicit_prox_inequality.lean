-- Prove2me | solution 1 for GoldenRatioVI.Explicit.prox_inequality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:16:22.726174+00:00
-- url     : https://prove2.me/submissions/af2bab90-f597-4d58-aee0-1497333de638

import Definitions.Def_GoldenRatioVI_Explicit_viProblem
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

open scoped RealInnerProductSpace
open GoldenRatioVI.Explicit

private theorem norm_segment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b w : E) (t : ℝ) :
    ‖(1-t) • a + t • b - w‖^2 = ‖a-w‖^2 +
      2*t*⟪a-w,b-a⟫ + t^2*‖b-a‖^2 := by
  have he : (1-t) • a+t • b-w = (a-w)+t • (b-a) := by module
  rw [he, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (hg : IsProperConvexLSC g) (w xbar : E) :
    GoldenRatioVI.Shared.IsProxPoint g w xbar ↔
      ∀ x : E, g xbar ≤ ((inner ℝ (xbar - w) (x - xbar) : ℝ) : EReal) + g x := by
  obtain ⟨y, hy⟩ := hg.exists_ne_top
  have gy : ((g y).toReal : EReal) = g y := EReal.coe_toReal hy (hg.ne_bot y)
  constructor
  · intro hprox
    have hbar : g xbar ≠ ⊤ := by
      intro ht
      have hh := hprox y
      rw [ht, ← gy] at hh
      simpa [← EReal.coe_add] using hh
    have gb : ((g xbar).toReal : EReal) = g xbar := EReal.coe_toReal hbar (hg.ne_bot xbar)
    intro x
    by_cases hx : g x = ⊤
    · simp [hx]
    have gx : ((g x).toReal : EReal) = g x := EReal.coe_toReal hx (hg.ne_bot x)
    rw [← gb, ← gx, ← EReal.coe_add, EReal.coe_le_coe_iff]
    by_contra hn
    let D : ℝ := (g xbar).toReal - (g x).toReal - ⟪xbar-w,x-xbar⟫
    have hD : 0 < D := by dsimp [D]; linarith
    let S : ℝ := ‖x-xbar‖^2
    have hS : 0 ≤ S := sq_nonneg _
    let t : ℝ := min 1 (D/(S+1))
    have ht : 0 < t := lt_min zero_lt_one (div_pos hD (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htd : t*(S+1) ≤ D := (le_div_iff₀ (by positivity : 0 < S+1)).mp (min_le_right _ _)
    have hc := hg.convex_epigraph
      (show (xbar, (g xbar).toReal) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} by
        change g xbar ≤ ((g xbar).toReal : EReal); rw [gb])
      (show (x, (g x).toReal) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} by
        change g x ≤ ((g x).toReal : EReal); rw [gx])
      (show 0 ≤ 1-t by linarith) ht.le (by ring : 1-t+t=1)
    change g ((1-t) • xbar+t • x) ≤ ↑((1-t)*(g xbar).toReal+t*(g x).toReal) at hc
    have hadd : g ((1-t) • xbar+t • x) + ((‖(1-t) • xbar+t • x-w‖^2/2 : ℝ) : EReal) ≤
        ↑((1-t)*(g xbar).toReal+t*(g x).toReal) + ((‖(1-t) • xbar+t • x-w‖^2/2 : ℝ) : EReal) := by
      gcongr
    have hm := (hprox ((1-t) • xbar+t • x)).trans hadd
    rw [← gb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hm
    rw [norm_segment] at hm
    simp only [EReal.toReal_coe] at hm
    have hineq : t*D ≤ t^2*S/2 := by dsimp [D, S]; nlinarith [hm]
    have hdle : D ≤ t*S/2 := by nlinarith
    nlinarith
  · intro h
    have hbar : g xbar ≠ ⊤ := by
      intro ht
      have hh := h y
      rw [ht, ← gy] at hh
      simpa [← EReal.coe_add] using hh
    have gb : ((g xbar).toReal : EReal) = g xbar := EReal.coe_toReal hbar (hg.ne_bot xbar)
    intro x
    by_cases hx : g x = ⊤
    · simp [hx]
    have gx : ((g x).toReal : EReal) = g x := EReal.coe_toReal hx (hg.ne_bot x)
    have hh := h x
    rw [← gb, ← gx, ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
    rw [← gb, ← gx, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have he := norm_segment xbar x w 1
    simp only [sub_self, zero_smul, one_smul, zero_add, one_pow, mul_one] at he
    nlinarith [sq_nonneg ‖x-xbar‖]

