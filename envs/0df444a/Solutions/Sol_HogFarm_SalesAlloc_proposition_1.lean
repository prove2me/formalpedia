-- Prove2me | solution 1 for HogFarm.SalesAlloc.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T17:52:54.630887+00:00
-- url     : https://prove2.me/submissions/314abffe-3e10-4430-9052-acba53cfd9c4

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model
import Theorems.Thm_HogFarm_SalesAlloc_preservation
import Theorems.Thm_HogFarm_SalesAlloc_lemma_2_1
import Theorems.Thm_HogFarm_SalesAlloc_attainment

set_option autoImplicit false

open HogFarm.SalesAlloc in
/-- The Bellman value at `t ≤ T` is the supremum of the action values, and the action value
is the one-period objective with `G = holdGain`; so a one-period optimum is optimal. -/
theorem hogfarm_onePeriodOptimal_isOptimal {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t : ℕ) (htT : t ≤ M.T) (ω : Ω) (s1 s2 y1 y2 z1 z2 : ℝ)
    (h : OnePeriodOptimal (M.price t ω) M.q M.α s1 s2 (holdGain M t ω) y1 y2 z1 z2) :
    IsOptimal M t ω s1 s2 y1 y2 z1 z2 := by
  have hAV : ∀ a b c d : ℝ, actionValue M t ω s1 s2 a b c d =
      onePeriodObjective (M.price t ω) M.q M.α s1 s2 (holdGain M t ω) a b c d := by
    intro a b c d
    simp only [actionValue, onePeriodObjective, holdGain, reward]
    ring
  have hv : ∀ x y : ℝ, ∀ ω' : Ω,
      value M (t + 1) x y ω' = valueAux M (M.T - t) (t + 1) x y ω' := by
    intro x y ω'
    simp only [value]
    rw [show M.T + 1 - (t + 1) = M.T - t by omega]
  have hval : value M t s1 s2 ω = sSup {v : ℝ | ∃ a b c d : ℝ,
      Feasible M.q s1 s2 a b c d ∧ v = actionValue M t ω s1 s2 a b c d} := by
    have hn : M.T + 1 - t = (M.T - t) + 1 := by omega
    rw [value, hn, valueAux]
    congr 1
    ext v
    constructor
    · rintro ⟨a, b, c, d, hf, rfl⟩
      refine ⟨a, b, c, d, hf, ?_⟩
      simp only [actionValue, cont, hv, add_assoc]
    · rintro ⟨a, b, c, d, hf, rfl⟩
      refine ⟨a, b, c, d, hf, ?_⟩
      simp only [actionValue, cont, hv, add_assoc]
  refine ⟨h.1, ?_⟩
  rw [hval]
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨y1, y2, z1, z2, h.1, rfl⟩, ?_⟩
  rintro v ⟨a, b, c, d, hf, rfl⟩
  rw [hAV, hAV]
  exact h.2 a b c d hf

open HogFarm.SalesAlloc in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hS : M.Standing) (hA1 : M.Assumption1) (hA : M.AStar)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T) (ω : Ω)
    (s1 s2 : ℝ) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) :
    let P := M.price t ω
    let f1 := (1 - M.α) * P.pC + P.cP
    let f2 := P.pC + P.cP
    let G := holdGain M t ω
    let zl1 := levelOf G (s1 + s2) f1
    let zb1 := levelOf G (s1 + s2) P.p1
    let Zb2 := levelOf G (s1 + s2) P.p2
    (f2 < P.p2 → f1 < P.p1 →
      IsOptimal M t ω s1 s2 0 0 (min s1 zb1) 0) ∧
    (f2 < P.p2 → P.p1 ≤ f1 →
      let y1 := min (max (s1 - zl1) 0) M.q
      IsOptimal M t ω s1 s2 y1 0 (min (s1 - y1) zb1) 0) ∧
    (P.p2 ≤ f2 → f1 < P.p1 →
      let z1 := min s1 zb1
      IsOptimal M t ω s1 s2 0 (min s2 M.q) z1
        (min (max (s2 - M.q) 0) (max (Zb2 - z1) 0))) ∧
    (P.p2 ≤ f2 → 0 ≤ f1 - P.p1 → f1 - P.p1 ≤ f2 - P.p2 →
      let y1 := min (max (s1 - zl1) 0) (max (M.q - s2) 0)
      let z1 := min (max (s1 - y1) 0) zb1
      IsOptimal M t ω s1 s2 y1 (min s2 M.q) z1
        (min (max (s2 - M.q) 0) (max (Zb2 - z1) 0))) := by
  have hG := (preservation M hS t ht1 htT ω).2
  have hL := lemma_2_1 M hS hA t ht1 htT ω
  dsimp only at hL
  obtain ⟨_hT, hq, hα0, hα1, _hβ0, _hβ1, ⟨B, _hB0, hB⟩, _hmeas⟩ := hS
  have hBt := hB t ω
  dsimp only at hBt
  obtain ⟨hp1, hp12, hpC, _hcH, hcP, _⟩ := hBt
  have hatt := attainment (M.price t ω) M.q M.α s1 s2 (holdGain M t ω) hq hα0 hα1
    hp1 hp12 hpC hcP hs1 hs2 hG hL.1
  dsimp only at hatt
  obtain ⟨h1, h2, h3, h4⟩ := hatt
  intro P f1 f2 G zl1 zb1 Zb2
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a b c => ?_⟩
  · exact hogfarm_onePeriodOptimal_isOptimal M t htT ω _ _ _ _ _ _ (h1 a b)
  · exact hogfarm_onePeriodOptimal_isOptimal M t htT ω _ _ _ _ _ _ (h2 a b)
  · exact hogfarm_onePeriodOptimal_isOptimal M t htT ω _ _ _ _ _ _ (h3 a b)
  · exact hogfarm_onePeriodOptimal_isOptimal M t htT ω _ _ _ _ _ _ (h4 a b c)
