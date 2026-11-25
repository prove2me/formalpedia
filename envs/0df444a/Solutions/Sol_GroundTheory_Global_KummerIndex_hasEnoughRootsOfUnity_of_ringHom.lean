-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.hasEnoughRootsOfUnity_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:20.881797+00:00
-- url     : https://prove2.me/submissions/451e1252-ec1d-41fe-8aeb-a3c1753c5cd7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex
namespace GroundTheory.Global.KummerIndex
theorem _root_.solution {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity F n] : HasEnoughRootsOfUnity E n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
  exact ⟨⟨f ζ, hζ.map_of_injective f.injective⟩, rootsOfUnity.isCyclic E n⟩
end GroundTheory.Global.KummerIndex
