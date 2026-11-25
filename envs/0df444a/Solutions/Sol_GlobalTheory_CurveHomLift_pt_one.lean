-- Prove2me | solution 1 for GlobalTheory.CurveHomLift.pt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:21.232895+00:00
-- url     : https://prove2.me/submissions/45e450cf-ee88-4514-800c-422cf770b99c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVector
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CurveHomLift
open UniformLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.CurveHomLift
theorem _root_.solution (C : Curve H) : C.pt 1 = C.pt 0 := by
  have h1 := (C.u.ker _).2 ((C.lat fun _ => C.c * 1).2 ⟨1, 0, by simp⟩)
  have h0 := (C.u.ker _).2 ((C.lat fun _ => C.c * 0).2 ⟨0, 0, by simp⟩)
  rw [Curve.pt, Curve.pt, h1, h0]
end GlobalTheory.CurveHomLift
