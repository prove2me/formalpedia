-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassage_creepingOnFiniteHit
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:15:15.17233+00:00
-- url     : https://prove2.me/submissions/c6997b09-6181-47ea-883b-73faa5ddfb4f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes

open MeasureTheory AvramDividend.Classical Filter Set Topology Metric
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Pathwise creeping at a finite upward first-passage time for spectrally negative Lévy
processes. Adapted from `creeping_of_goodFin` in the ACCEPTED
`upwardPassage_zeroRootIsSubordinator` solution: right-continuity gives
`x ≤ X_τ`, and left limits + `noPosJumps` give `X_τ ≤ x`.
-/

namespace Kyprianou.Ch03

/-- Pathwise: on `{τ_x^+ ≠ ⊤}`, if `finiteTime` selects `τ_x^+`, then `X_{τ_x^+} = x`. -/
private lemma creeping_at_finiteHit
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 ≤ x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (ω : Omega)
    (hne : firstHittingTime L.X (Set.Ioi x) ω ≠ ⊤) :
    L.X (finiteTime ω) ω = x := by
  have hbne : firstHittingTime L.X (Set.Ioi x) ω != ⊤ := by
    simpa [bne_iff_ne] using hne
  have hft : firstHittingTime L.X (Set.Ioi x) ω =
      (finiteTime ω : WithTop NNReal) := hfin ω hbne
  cases hτ : firstHittingTime L.X (Set.Ioi x) ω with
  | top => exact absurd hτ hne
  | coe t =>
    have ht_eq : finiteTime ω = t := by
      have : (finiteTime ω : WithTop NNReal) = (t : WithTop NNReal) := by
        rw [← hft, hτ]
      exact WithTop.coe_injective this
    rw [ht_eq]
    -- Creeping: `L.X t ω = x`
    by_cases ht0 : t = 0
    · subst ht0
      -- Barrier must be `0`, else right-continuity at `0` forbids `τ = 0`.
      have hx0 : x = 0 := by
        by_contra hxne
        have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxne)
        have hnhds : (fun s => L.X s ω) ⁻¹' Iio x ∈ 𝓝[≥] (0 : NNReal) := by
          have h0 : L.X 0 ω ∈ Iio x := by rw [L.X_zero ω]; exact hx_pos
          exact L.rightCont ω 0 (isOpen_Iio.mem_nhds h0)
        rw [Metric.mem_nhdsWithin_iff] at hnhds
        rcases hnhds with ⟨δ, hδ_pos, hδ⟩
        let d : NNReal := ⟨δ / 2, by positivity⟩
        have hd_pos : (0 : NNReal) < d := by
          rw [← NNReal.coe_lt_coe, NNReal.coe_zero]; change 0 < δ / 2; positivity
        have hd_le : (d : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi x) ω := by
          refine le_sInf ?_
          rintro _ ⟨s, ⟨_, hxs⟩, rfl⟩
          rw [WithTop.coe_le_coe]
          by_contra hslt
          push Not at hslt
          have hs_ball : s ∈ Metric.ball (0 : NNReal) δ := by
            rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
              abs_of_nonneg (NNReal.coe_nonneg s)]
            have : (s : ℝ) < (d : ℝ) := NNReal.coe_lt_coe.mpr hslt
            change (s : ℝ) < δ / 2 at this
            linarith
          have hs_lt : L.X s ω < x := hδ ⟨hs_ball, zero_le (a := s)⟩
          have hxs' : x < L.X s ω := mem_Ioi.mp hxs
          linarith
        rw [hτ, WithTop.coe_le_coe] at hd_le
        exact (lt_of_lt_of_le hd_pos hd_le).false
      rw [L.X_zero ω, hx0]
    · have ht_pos : (0 : NNReal) < t := pos_iff_ne_zero.mpr ht0
      -- `x ≤ X t` by right-continuity at `t`
      have hge : x ≤ L.X t ω := by
        by_contra hlt
        push Not at hlt
        have hnhds : (fun s => L.X s ω) ⁻¹' Iio x ∈ 𝓝[≥] t :=
          L.rightCont ω t (isOpen_Iio.mem_nhds hlt)
        rw [Metric.mem_nhdsWithin_iff] at hnhds
        rcases hnhds with ⟨δ, hδ_pos, hδ⟩
        let u : NNReal := t + ⟨δ / 2, by positivity⟩
        have hτ_lt : firstHittingTime L.X (Set.Ioi x) ω < (u : WithTop NNReal) := by
          rw [hτ, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe]
          change (t : ℝ) < (t : ℝ) + δ / 2
          linarith
        rcases sInf_lt_iff.mp hτ_lt with ⟨_, ⟨s, ⟨hs_pos, hxs⟩, rfl⟩, hsu⟩
        have ht_le_s : t ≤ s := by
          have := sInf_le (show (s : WithTop NNReal) ∈ (fun t : NNReal => (t : WithTop NNReal)) ''
            {t : NNReal | 0 < t ∧ L.X t ω ∈ Set.Ioi x} from ⟨s, ⟨hs_pos, hxs⟩, rfl⟩)
          rwa [← firstHittingTime, hτ, WithTop.coe_le_coe] at this
        have hs_ball : s ∈ Metric.ball t δ := by
          rw [Metric.mem_ball, NNReal.dist_eq,
            abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht_le_s))]
          have : (s : ℝ) < (u : ℝ) := NNReal.coe_lt_coe.mpr (WithTop.coe_lt_coe.mp hsu)
          change (s : ℝ) < (t : ℝ) + δ / 2 at this
          linarith
        have hlt_s : L.X s ω < x := hδ ⟨hs_ball, ht_le_s⟩
        have hxs' : x < L.X s ω := mem_Ioi.mp hxs
        linarith
      -- `X t ≤ x` by left limit + no positive jumps
      have hle : L.X t ω ≤ x := by
        rcases L.leftLim ω t ht_pos with ⟨l, hl⟩
        have hnojump : L.X t ω ≤ l := L.noPosJumps ω t l ht_pos hl
        have hl_le : l ≤ x := by
          have hneBot : (𝓝[<] t).NeBot := by
            rw [nhdsWithin_neBot]
            intro U hU
            rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ_pos, hδ⟩
            let s : NNReal := ⟨max 0 ((t : ℝ) - δ / 2), le_max_left _ _⟩
            have hslt : s < t := by
              rw [← NNReal.coe_lt_coe]
              exact max_lt (NNReal.coe_pos.mpr ht_pos) (by linarith)
            refine ⟨s, hδ ?_, hslt⟩
            rw [Metric.mem_ball, NNReal.dist_eq,
              abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hslt.le))]
            have : (t : ℝ) - δ / 2 ≤ (s : ℝ) := le_max_right _ _
            linarith
          have hev : ∀ᶠ s in 𝓝[<] t, L.X s ω ≤ x := by
            have hmem : Ioo (0 : NNReal) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht_pos
            filter_upwards [hmem] with s hs
            by_contra hgt
            push Not at hgt
            have h1 : firstHittingTime L.X (Set.Ioi x) ω ≤ (s : WithTop NNReal) :=
              sInf_le ⟨s, ⟨hs.1, hgt⟩, rfl⟩
            rw [hτ, WithTop.coe_le_coe] at h1
            exact not_lt_of_ge h1 hs.2
          exact le_of_tendsto hl hev
        exact hnojump.trans hl_le
      exact le_antisymm hle hge

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 ≤ x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal)) :
    ∀ᵐ omega ∂P,
      firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
        L.X (finiteTime omega) omega = x :=
  Filter.Eventually.of_forall fun ω hne =>
    creeping_at_finiteHit L x hx finiteTime hfin ω hne
