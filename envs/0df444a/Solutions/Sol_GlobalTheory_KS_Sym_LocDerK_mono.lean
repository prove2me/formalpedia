-- Prove2me | solution 1 for GlobalTheory.KS.Sym.LocDerK_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:31:05.792784+00:00
-- url     : https://prove2.me/submissions/fca4a0b1-e77b-4fec-a0b4-678137926ff7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
import Theorems.Thm_GlobalTheory_KS_IsCob_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
variable {K R : Type} [Field K] [CommRing R]
namespace GlobalTheory.KS.Sym
theorem _root_.solution {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W W' : X.Opens}
    {d : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) (h : W' ≤ W) : LocDerK q s m D W' d := ⟨fun V hV => hd.add V (hV.trans h), fun V hV => hd.mul V (hV.trans h),
    fun V V' e hV => hd.res V V' e (hV.trans h), fun V hV => hd.base V (hV.trans h)⟩
end GlobalTheory.KS.Sym
