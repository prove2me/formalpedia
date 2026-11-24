-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.quad_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:18.384894+00:00
-- url     : https://prove2.me/submissions/bc256e3d-6b3c-480e-98ad-aa2e79a55198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
variable {σ : R →+* R} {β : M → M → ℂ}
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (y z : M) :
    β (w • (y + z)) (y + z) = β (w • y) y * β (w • z) z * β z y := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have key : β (w • y) z * β (w • z) y = β z y := by
    rw [hadj w y z, hsym (w • z) y, ← hr, ← add_smul, add_comm (σ w), hw, one_smul, hsym]
  rw [smul_add, hadd, hr, hr, ← key]
  ring
end GlobalTheory.HermitianGauss
