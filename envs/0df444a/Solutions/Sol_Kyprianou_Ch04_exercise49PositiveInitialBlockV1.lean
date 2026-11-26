-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PositiveInitialBlockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:49:54.860596+00:00
-- url     : https://prove2.me/submissions/0fc22e95-2262-4323-830d-92d139d44e92

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Positive small-time drift gives a nonnegative initial block with positive terminal gain and positive probability. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (d : ℝ) (hd : 0 < d)
    (hSlope : ∀ᵐ ω ∂P, Tendsto (fun t : NNReal => X t ω / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds d)) :
    ∃ s : NNReal, 0 < s ∧ ∃ a : ℝ, 0 < a ∧
      0 < P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω} := by
  classical
  let t (q : ℚ) : NNReal := Real.toNNReal q
  let A (q : ℚ) : Set Ω := {ω | 0 < q ∧
    (∀ u : NNReal, u ≤ t q → 0 ≤ X u ω) ∧ d / 2 * (t q : ℝ) ≤ X (t q) ω}
  have hA : ∀ᵐ ω ∂P, ω ∈ ⋃ q, A q := by
    filter_upwards [hSlope] with ω hs
    have hh : ∀ᶠ u : NNReal in 𝓝[>] (0 : NNReal),
        d / 2 < X u ω / (u : ℝ) :=
      hs.eventually (eventually_gt_nhds (by linarith : d / 2 < d))
    obtain ⟨ε, hε, hpos⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hh
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (show (0 : ℝ) < ε by exact_mod_cast hε)
    have hqt : 0 < t q := Real.toNNReal_pos.mpr hq0
    have htε : t q < ε := (Real.toNNReal_lt_iff_lt_coe hq0.le).2 hqε
    refine mem_iUnion.mpr ⟨q, by exact_mod_cast hq0, ?_, ?_⟩
    · intro u hu
      by_cases h0 : u = 0
      · simp [h0, congrFun hX.start_zero ω]
      · have hup : 0 < u := pos_iff_ne_zero.mpr h0
        have hh' := hpos ⟨hup, hu.trans_lt htε⟩
        have hu' : 0 < (u : ℝ) := by exact_mod_cast hup
        have hmul := (lt_div_iff₀ hu').mp hh'
        nlinarith
    · exact ((lt_div_iff₀ (show (0 : ℝ) < t q by exact_mod_cast hqt)).mp
        (hpos ⟨hqt, htε⟩)).le
  have hex : ∃ q, 0 < P (A q) := by
    by_contra! h
    have hz : P (⋃ q, A q) = 0 :=
      measure_iUnion_null (fun q => nonpos_iff_eq_zero.mp (h q))
    have hc : P (⋃ q, A q)ᶜ = 0 := ae_iff.mp hA
    have hu : P (Set.univ : Set Ω) = 0 := by
      rw [← Set.union_compl_self (⋃ q, A q)]
      exact le_antisymm ((measure_union_le _ _).trans (by rw [hz, hc, zero_add])) bot_le
    simpa using hu
  obtain ⟨q, hq⟩ := hex
  have hq0 : 0 < q := by
    by_contra! hn
    have he : A q = ∅ := by ext ω; simp [A, not_lt.mpr hn]
    simp [he] at hq
  have ht : 0 < t q := Real.toNNReal_pos.mpr (by exact_mod_cast hq0)
  refine ⟨t q, ht, d / 2 * (t q : ℝ), mul_pos (by linarith)
    (by exact_mod_cast ht), ?_⟩
  simpa [A, hq0] using hq
