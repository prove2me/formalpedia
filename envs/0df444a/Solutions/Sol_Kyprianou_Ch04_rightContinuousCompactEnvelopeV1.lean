-- Prove2me | solution 1 for Kyprianou.Ch04.rightContinuousCompactEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:08:38.629522+00:00
-- url     : https://prove2.me/submissions/e75ba36d-1983-47bc-ad33-1d0a12d3f23f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousDyadicSupV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Countably many measurable time sections represent the compact path supremum. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : NNReal → Ω → ℝ) (T : NNReal)
    (hM : ∀ t, AEMeasurable (Y t) P)
    (hR : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t) :
    ∃ S : Ω → ℝ≥0∞, Measurable S ∧ ∀ᵐ w ∂P,
      (∀ t ≤ T, ENNReal.ofReal |Y t w| ≤ S w) ∧
      (∀ d : ℝ, (∀ t ≤ T, |Y t w| ≤ d) → S w ≤ ENNReal.ofReal d) := by
  classical
  let Z : NNReal → Ω → ℝ := fun t => (hM t).mk (Y t)
  have hm (t : NNReal) : Measurable (Z t) := (hM t).measurable_mk
  have he (t : NNReal) : Y t =ᵐ[P] Z t := (hM t).ae_eq_mk
  by_cases ht : T = 0
  · subst T
    refine ⟨fun w => ENNReal.ofReal |Z 0 w|,ENNReal.measurable_ofReal.comp (hm 0).abs,?_⟩
    filter_upwards [he 0] with w hw
    constructor
    · intro t ht
      have ht0 : t = 0 := le_antisymm ht (by positivity)
      rw [ht0,hw]
    · intro d hd
      rw [← hw]
      exact ENNReal.ofReal_le_ofReal (hd 0 le_rfl)
  have hT : 0 < T := pos_iff_ne_zero.mpr ht
  let g : ℕ → Ω → ℝ := fun n w =>
    (Finset.range (2^n+1)).sup' Finset.nonempty_range_add_one
      (fun i => |Z ((i : NNReal) * T / (2^n : NNReal)) w|)
  let S : Ω → ℝ≥0∞ := fun w => ⨆ n, ENNReal.ofReal (g n w)
  have hg (n : ℕ) : Measurable (g n) := by
    dsimp [g]
    apply Finset.measurable_range_sup''
    intro i hi
    exact (hm _).abs
  have heAll : ∀ᵐ w ∂P, ∀ n i : ℕ,
      Y ((i : NNReal) * T / (2^n : NNReal)) w =
        Z ((i : NNReal) * T / (2^n : NNReal)) w :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun i => he _))
  refine ⟨S,Measurable.iSup (fun n => ENNReal.measurable_ofReal.comp (hg n)),?_⟩
  filter_upwards [hR,heAll] with w hw hEq
  have hgEq (n : ℕ) : g n w = (Finset.range (2^n+1)).sup'
      Finset.nonempty_range_add_one (fun i => |Y ((i : NNReal) * T / (2^n : NNReal)) w|) := by
    dsimp [g]
    simp_rw [← hEq n]
  have hs : (⨆ t : Iic T, ENNReal.ofReal |Y t w|) = S w := by
    rw [Kyprianou.Ch04.rightContinuousDyadicSupV1 (fun t => |Y t w|) T hT
      (fun t => abs_nonneg _) (fun t => (hw t).abs)]
    simp only [S,hgEq]
  rw [← hs]
  constructor
  · intro t ht'
    exact le_iSup (fun r : Iic T => ENNReal.ofReal |Y r w|) ⟨t,ht'⟩
  · intro d hd
    exact iSup_le (fun r => ENNReal.ofReal_le_ofReal (hd r r.2))
