-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.lift_flat_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:28.314009+00:00
-- url     : https://prove2.me/submissions/cbbb659f-95db-4060-bc30-0820ea7cf96a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_translate_apply

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
theorem _root_.solution (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) (g : G) :
    lift hSK (flat mL (translate s₀ v)) g = lift hSK (flat mL v) ((s₀ : G) * g) := by
  obtain ⟨p, rfl⟩ := hSK g
  rw [lift_mulMap (flat_right_inv _) p]
  have : (s₀ : G) * mulMap S K p = mulMap S K (s₀ * p.1, p.2) := by
    simp [mulMap, mul_assoc]
  rw [this, lift_mulMap (flat_right_inv _)]
  simp only [flat, translate_apply, mul_assoc]
end GroundTheory.Automorphic.HaarSK
