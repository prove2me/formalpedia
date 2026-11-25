-- Prove2me | solution 1 for GlobalTheory.T.cmCurveHom_exists_pureTypeVector_anyLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:34.693201+00:00
-- url     : https://prove2.me/submissions/9e539351-683c-405c-aa56-18c5d573bcd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmCurveHomExistsPureTypeVectorAnyLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmCurveHomExistsPureTypeVectorAnyLevelStatement
import Theorems.Thm_GlobalTheory_CurveHomLiftAnyLevel_exists_pure_vector
import Theorems.Thm_GlobalTheory_CurveHomLift_exists_pure_vector


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  first | exact @GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector | exact GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector | (intros; apply GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector <;> assumption)
end _root_.GlobalTheory.T
