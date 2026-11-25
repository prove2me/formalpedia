-- Prove2me | solution 1 for GlobalTheory.CountId.lat_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:15.115749+00:00
-- url     : https://prove2.me/submissions/2f12609e-2617-43b3-a7ca-3ebecc239e4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]
variable (O : Type) [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]
variable [IsDomain O] [Module.IsTorsionFree O E]
namespace GlobalTheory.CountId
theorem _root_.solution (e : Basis (Fin n) E V) : (lat O e).FG := Submodule.fg_span (Set.finite_range _)
end GlobalTheory.CountId
