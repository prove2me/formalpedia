-- Prove2me | solution 1 for GlobalTheory.FlagData.herm_transvMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:38.759467+00:00
-- url     : https://prove2.me/submissions/459790d3-ce3b-4fa2-9383-b8f6fd16a760

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmulMemOfIsIntegral
import Theorems.Thm_GlobalTheory_FlagData_herm_add_smul_right
import Theorems.Thm_GlobalTheory_FlagData_cc_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FlagData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlagData
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0) {α : E} (hα : FD.cc α = -α) (x y : Fin r → E) :
    FD.herm G (FD.transvMat G ξ α *ᵥ x) (FD.transvMat G ξ α *ᵥ y) = FD.herm G x y := by
  have e : FD.cc (α * FD.herm G y ξ) = -α * FD.herm G ξ y := by
    rw [← hα, ← cc_herm hG y ξ]
    exact map_mul (IsCMField.complexConj E) _ _
  rw [transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, herm_add_smul_right,
    herm_add_smul_right, hξ, e]
  ring
end GlobalTheory.FlagData
