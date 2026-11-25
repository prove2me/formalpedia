-- Prove2me | solution 1 for GlobalTheory.CurveHomLift.isHolTo_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:18.173268+00:00
-- url     : https://prove2.me/submissions/1af8c039-3cc4-46d3-827e-81041705b9d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CurveHomLift
open UniformLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.CurveHomLift
theorem _root_.solution (C : Curve H) : IsHolTo Set.univ fun z : Fin 1 → ℂ => C.pt (z 0) := by
  intro U f
  obtain ⟨h1, h2⟩ := C.u.hol U f
  have hd : Differentiable ℂ (fun (z : Fin 1 → ℂ) (_ : Fin C.P.g) => C.c * z 0) := by fun_prop
  refine ⟨?_, h2.comp hd.differentiableOn fun z hz => hz.2⟩
  exact isOpen_univ.inter (h1.preimage hd.continuous)
end GlobalTheory.CurveHomLift
