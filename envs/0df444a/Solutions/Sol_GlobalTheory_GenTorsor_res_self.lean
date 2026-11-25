-- Prove2me | solution 1 for GlobalTheory.GenTorsor.res_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:56:44.759827+00:00
-- url     : https://prove2.me/submissions/229f62b6-9a3c-49d6-ba33-2cb3a073595a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
import Theorems.Thm_GlobalTheory_GenTorsor_pb_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.GenTorsor
theorem _root_.solution {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := pb_id h x
end GlobalTheory.GenTorsor
