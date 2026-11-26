-- Prove2me | solution 1 for MorreyResolutionAdditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:13.99862+00:00
-- url     : https://prove2.me/submissions/d521109b-2dac-4b5c-8f76-a51f16e369de

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory Set
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (s : ℕ → ℝ)
    (hmono : MonotoneOn s (Set.Icc 0 k)) (h0 : s 0 = 0) (hk : s k = γ.len) :
    curveMeasure γ =
      ∑ i ∈ Finset.range k, Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1)))) := by
-- BODY
  have hmeas : Measurable γ.toFun := (CurveLipschitz γ).continuous.measurable
  have main : ∀ n : ℕ, ∀ t : ℕ → ℝ, MonotoneOn t (Set.Icc 0 n) →
      Measure.map γ.toFun (volume.restrict (Set.Icc (t 0) (t n))) =
        ∑ i ∈ Finset.range n, Measure.map γ.toFun (volume.restrict (Set.Icc (t i) (t (i + 1)))) := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ m ih =>
      intro t hmonot
      have hmono_m : MonotoneOn t (Set.Icc 0 m) :=
        hmonot.mono (fun x hx => ⟨hx.1, hx.2.trans m.le_succ⟩)
      have hab : t 0 ≤ t m :=
        hmonot ⟨le_refl 0, Nat.zero_le (m + 1)⟩ ⟨Nat.zero_le m, m.le_succ⟩ (Nat.zero_le m)
      have hbc : t m ≤ t (m + 1) :=
        hmonot ⟨Nat.zero_le m, m.le_succ⟩ ⟨Nat.zero_le (m + 1), le_refl (m + 1)⟩ m.le_succ
      have hsplit : Set.Icc (t 0) (t (m + 1)) = Set.Icc (t 0) (t m) ∪ Set.Icc (t m) (t (m + 1)) :=
        (Set.Icc_union_Icc_eq_Icc hab hbc).symm
      have hsub : Set.Icc (t 0) (t m) ∩ Set.Icc (t m) (t (m + 1)) ⊆ ({t m} : Set ℝ) := by
        rintro x ⟨⟨_, hx2⟩, ⟨hx3, _⟩⟩
        exact le_antisymm hx2 hx3
      have haed : AEDisjoint volume (Set.Icc (t 0) (t m)) (Set.Icc (t m) (t (m + 1))) :=
        measure_mono_null hsub (by simp)
      rw [hsplit,
        MeasureTheory.Measure.restrict_union₀ haed measurableSet_Icc.nullMeasurableSet,
        Measure.map_add _ _ hmeas, Finset.sum_range_succ, ih t hmono_m]
  have h := main k s hmono
  rw [h0, hk] at h
  unfold curveMeasure
  rw [h]
