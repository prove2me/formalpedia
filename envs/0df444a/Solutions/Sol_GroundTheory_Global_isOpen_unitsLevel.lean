-- Prove2me | solution 1 for GroundTheory.Global.isOpen_unitsLevel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:48.936078+00:00
-- url     : https://prove2.me/submissions/a6fd1efe-4925-4ce4-9536-c0765b16ca72

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter IsDedekindDomain WithZero
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) : IsOpen (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) := by
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective (K := K) (v := v)
    (exp (-(n : ℤ)))
  have ha0 : Valued.v a ≠ 0 := by simp [ha]
  have h1 : {y : v.adicCompletion K | Valued.v y = 1} ∈ 𝓝 (1 : v.adicCompletion K) := by
    simpa using Valued.locally_const (x := (1 : v.adicCompletion K)) (by simp)
  have h2 : {y : v.adicCompletion K | Valued.v (y - 1) ≤ exp (-(n : ℤ))} ∈
      𝓝 (1 : v.adicCompletion K) := by
    have hc : Continuous fun y : v.adicCompletion K ↦ y - 1 + a :=
      (continuous_id.sub continuous_const).add continuous_const
    have h := hc.continuousAt.preimage_mem_nhds (x := (1 : v.adicCompletion K))
      (by simpa using Valued.locally_const (x := a) ha0)
    refine Filter.mem_of_superset h fun y hy ↦ ?_
    have hy' : Valued.v (y - 1 + a) = exp (-(n : ℤ)) := by rw [← ha]; exact hy
    have : y - 1 = (y - 1 + a) - a := by ring
    change Valued.v (y - 1) ≤ exp (-(n : ℤ))
    rw [this]
    exact Valuation.map_sub_le _ hy'.le ha.le
  have h3 := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : (v.adicCompletion K)ˣ))
    (by rw [Units.val_one]; exact Filter.inter_mem h1 h2)
  exact Filter.mem_of_superset h3 fun x hx ↦ hx
end GroundTheory.Global
