-- Prove2me | solution 2 for Kyprianou.Ch03.closedHitApproximationAELimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:39:16.72256+00:00
-- url     : https://prove2.me/submissions/95e96f24-3578-4de9-98d5-5d01362d6a4e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_closedHitDelayedApproxAEEqV1
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitStoppingV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

private theorem weakStrictInfEq (f : NNReal → ℝ)
    (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (a : NNReal) (U : Set ℝ) (hU : IsOpen U) :
    sInf ((fun t : NNReal => (t : WithTop NNReal)) '' {t | a ≤ t ∧ f t ∈ U}) =
      sInf {u : WithTop NNReal | ∃ t : NNReal, a < t ∧ f t ∈ U ∧ u = (t : WithTop NNReal)} := by
  let R := sInf {u : WithTop NNReal | ∃ t : NNReal, a < t ∧ f t ∈ U ∧ u = (t : WithTop NNReal)}
  apply le_antisymm
  · apply sInf_le_sInf
    rintro _ ⟨t, ht, hU', rfl⟩
    exact ⟨t, ⟨ht.le, hU'⟩, rfl⟩
  · by_contra! hn
    obtain ⟨b, ⟨t, ⟨hat, ht⟩, rfl⟩, htR⟩ := sInf_lt_iff.mp hn
    have hev : ∀ᶠ v in 𝓝[≥] t, f v ∈ U :=
      (hrc t).eventually (hU.mem_nhds ht)
    obtain ⟨v, htv, hv⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hmin : (t : WithTop NNReal) < min (v : WithTop NNReal) R :=
      lt_min (WithTop.coe_lt_coe.mpr htv) htR
    obtain ⟨b, htb, hb⟩ := exists_between hmin
    have hfin : b ≠ ⊤ := ne_top_of_lt (hb.trans_le (min_le_left _ _))
    obtain ⟨u, rfl⟩ := WithTop.ne_top_iff_exists.mp hfin
    have htu : t < u := WithTop.coe_lt_coe.mp htb
    have huU := hv ⟨htu.le, WithTop.coe_lt_coe.mp (hb.trans_le (min_le_left _ _))⟩
    have hu : (u : WithTop NNReal) ∈
        {v : WithTop NNReal | ∃ t : NNReal, a < t ∧ f t ∈ U ∧ v = (t : WithTop NNReal)} :=
      ⟨u, hat.trans_lt htu, huU, rfl⟩
    exact not_lt_of_ge (show R ≤ (u : WithTop NNReal) from sInf_le hu)
      (hb.trans_le (min_le_right _ _))

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsClosed B)
    (hStop : ∀ m n : ℕ, IsStoppingTime F (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
      (1 / ((m : NNReal) + 1)) < r ∧
      X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧
      u = (r : WithTop NNReal)})) :
    firstHittingTime X B =ᵐ[P] (fun w : Omega => ⨅ m : ℕ, ⨆ n : ℕ, (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
      (1 / ((m : NNReal) + 1)) < r ∧
      X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧
      u = (r : WithTop NNReal)}) w) := by
  have hRC := completedNaturalLevyFiltrationRightContinuous P X hX F hNatural
  have hW (j n : ℕ) := delayedOpenHitStoppingV1 P F X hX hNatural hRC
    (1 / ((j : NNReal) + 1)) (Metric.thickening (1 / ((n : ℝ) + 1)) B)
    Metric.isOpen_thickening
  have he := closedHitDelayedApproxAEEqV1 P F X hX hNatural B hB hW
  filter_upwards [he, hX.cadlag_ae] with w hw hcad
  rw [hw]
  congr 1
  funext j
  congr 1
  funext n
  exact weakStrictInfEq (fun t => X t w) (fun t => (hcad t).1) _ _ Metric.isOpen_thickening
