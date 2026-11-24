-- Prove2me | solution 1 for GlobalTheory.ZM.SFam.sRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:52.888371+00:00
-- url     : https://prove2.me/submissions/fe168be3-086c-434b-bf6a-81543ed89a05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Theorems.Thm_GlobalTheory_ZM_SFam_isSeparated

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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.ZM
namespace SFam
theorem _root_.solution {h p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    SRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := ⟨F.isSeparated, fun S s' c hS hd hc => F.rep S s' c hS hd hc⟩
end SFam
end GlobalTheory.ZM
