-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.funcL_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:15.229894+00:00
-- url     : https://prove2.me/submissions/5c249bde-fa3c-4d89-ada6-28f219d8f77a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_funcL_apply
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_lift_flat_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.HaarSK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {S K : Subgroup G}
variable (hSK : Surjective (mulMap S K))
variable {hSK}
variable [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
variable {mL : Measure (inter S K)} [LocallyCompactSpace S] [CompactSpace (inter S K)]
  [IsFiniteMeasure mL] [mL.IsMulLeftInvariant]
  {hS : IsClosed (S : Set G)} {hK : IsCompact (K : Set G)} {hSK : Surjective (mulMap S K)}
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) :
    funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) (translate s₀ v) =
      funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v := by
  rw [funcL_apply, funcL_apply]
  simp_rw [lift_flat_translate]
  exact integral_mul_left_eq_self (fun g => lift hSK (flat mL v) g) (s₀ : G)
end GroundTheory.Automorphic.HaarSK
