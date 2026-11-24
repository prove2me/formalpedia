-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isCompact_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:21.699951+00:00
-- url     : https://prove2.me/submissions/5f309183-263a-46ed-b40a-e5e18e7c64e7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_integralMatrices
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_integralGL_eq_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution : IsCompact (integralGL F n : Set (GL (Fin n) F)) := by
  rw [integralGL_eq_units]
  apply Submonoid.units_isCompact
  have : ((integralMatrices F n).toSubmonoid : Set (Matrix (Fin n) (Fin n) F)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (𝒪[F] : Set F) := by
    ext A
    change A ∈ integralMatrices F n ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, A i j ∈ (𝒪[F] : Set F)
    rw [mem_integralMatrices]
    simp
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))
end GroundTheory.Automorphic.GLnLocal
