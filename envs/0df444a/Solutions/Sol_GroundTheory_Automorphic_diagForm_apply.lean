-- Prove2me | solution 1 for GroundTheory.Automorphic.diagForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:47:23.507874+00:00
-- url     : https://prove2.me/submissions/db08919e-ed90-4e80-a249-601d0447ed86

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc

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
open Module Matrix GroundTheory.LocalField
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
namespace GroundTheory.Automorphic
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) (x y : ι → E) :
    (diagForm (E := E) a).toSesq x y = ∑ i, conj F E (x i) * algebraMap F E (a i) * y i := rfl
end GroundTheory.Automorphic
