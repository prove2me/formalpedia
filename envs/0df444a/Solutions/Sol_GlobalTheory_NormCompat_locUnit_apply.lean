-- Prove2me | solution 1 for GlobalTheory.NormCompat.locUnit_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:49.97231+00:00
-- url     : https://prove2.me/submissions/a3ead797-ebf5-4b21-8976-c0748fcb9c99

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory GlobalTheory.NormCompat
namespace GlobalTheory.NormCompat
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    locUnit F v a = localIdele F v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := rfl
end GlobalTheory.NormCompat
