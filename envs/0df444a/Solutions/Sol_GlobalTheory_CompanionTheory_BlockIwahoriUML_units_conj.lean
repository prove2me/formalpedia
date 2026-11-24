-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BlockIwahoriUML.units_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:35.924462+00:00
-- url     : https://prove2.me/submissions/4d0ddc84-615e-4420-afcd-fbf2e585e63a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
namespace GlobalTheory.CompanionTheory.BlockIwahoriUML
theorem _root_.solution {M : Type*} [Monoid M] (p q : Mˣ) (x : M) :
    ((p⁻¹ : Mˣ) : M) * ((p : M) * x * (q : M)) * ((q⁻¹ : Mˣ) : M) = x := by
  simp [mul_assoc]
end GlobalTheory.CompanionTheory.BlockIwahoriUML
