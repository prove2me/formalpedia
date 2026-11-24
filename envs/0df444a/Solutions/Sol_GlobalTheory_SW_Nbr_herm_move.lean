-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.herm_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:26.79435+00:00
-- url     : https://prove2.me/submissions/4247b06f-88d4-4e05-9519-e1ea76055dec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Base_herm_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (x y : Fin n → E) :
    herm 1 (h *ᵥ x) (h *ᵥ y) = herm 1 x y := by
  have h1 : ∀ x y : Fin n → E, herm 1 x y = (fun a => cc (y a)) ⬝ᵥ x := fun x y => by
    rw [herm_one, dotProduct_comm]; rfl
  have h2 : (fun a => cc ((h *ᵥ y) a)) = (fun a => cc (y a)) ᵥ* ccT h := by
    ext a
    simp [cc, ccT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [h1, h1, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]
end GlobalTheory.SW.Nbr
