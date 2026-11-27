-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_mul_mem_normOneFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:22.795264+00:00
-- url     : https://prove2.me/submissions/6f2106fd-c1f3-4f85-a402-6891fc1a5b14

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (u : normOneSubgroup K) :
    ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ normOneFundamentalDomain K := by
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  have he : ∀ ξ : Kˣ, e ξ • u = u * diagonalToNormOne K ξ := fun _ ↦ rfl
  obtain ⟨γ, hγ, huniq⟩ := (exists_fundamentalDomain_normOne K).choose_spec.2.2 u
  refine ⟨e.symm γ, ?_, fun ξ hξ ↦ ?_⟩
  · show u * diagonalToNormOne K (e.symm γ) ∈ normOneFundamentalDomain K
    rw [← he, e.apply_symm_apply]
    exact hγ
  · change u * diagonalToNormOne K ξ ∈ normOneFundamentalDomain K at hξ
    rw [← he] at hξ
    rw [← huniq _ hξ, e.symm_apply_apply]
end GroundTheory.Global
