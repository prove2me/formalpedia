-- Prove2me | solution 1 for GlobalTheory.NormGlue.valF_eq_of_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:28:57.819486+00:00
-- url     : https://prove2.me/submissions/c34bbe51-c3a5-4d54-893f-247f83fee5c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_toStk_valF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
open GlobalTheory.NormGlue
namespace GlobalTheory.NormGlue
theorem _root_.solution {F : Type} [Field F] {X X' : Scheme.{0}} {x : Sp F ⟶ X} {x' : Sp F ⟶ X'}
    {U : X.Opens} {U' : X'.Opens} (z : Sp F) (h : x z ∈ U) (h' : x' z ∈ U') {u : Γ(X, U)ˣ} {u' : Γ(X', U')ˣ}
    (e : gm x z U u = gm x' z U' u') : valF x U u.val = valF x' U' u'.val :=
  (toStk z).injective (by rw [toStk_valF x U z h, toStk_valF x' U' z h', e])
end GlobalTheory.NormGlue
