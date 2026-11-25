-- Prove2me | solution 1 for GlobalTheory.GenTorsor.res_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:49:32.584333+00:00
-- url     : https://prove2.me/submissions/66e0cc98-e023-4541-b7b8-8c212ad5d468

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover

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
theorem _root_.solution (a : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU a U x) = pb a U W h x := rfl
end GlobalTheory.GenTorsor
