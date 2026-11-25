-- Prove2me | solution 1 for GlobalTheory.Frames.frPt_eq_of_frMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:29.321833+00:00
-- url     : https://prove2.me/submissions/6a142a44-83f3-4705-8c79-1c6aae33d56c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueFrameChangeByMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeExistsUniqueOfSamePointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeByMatricesReflAndCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeCommBaseChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameEqOfBaseChangeInjective
import Theorems.Thm_GlobalTheory_T_existsUnique_frameChangeByMatrices
import Theorems.Thm_GlobalTheory_T_frameChangeByMatrices_refl_and_comp
import Theorems.Thm_GlobalTheory_T_frameChange_comm_baseChange
import Theorems.Thm_GlobalTheory_T_frameChange_exists_unique_of_same_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Frames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (z z' : FrPt Xo c S) (w : FrPt Xo c T), Function.Injective φ → z'.x = z.x → FrMap φ z w → FrMap φ z' w → z = z' := by
  intro _ E _ _ _ H Dw l Xo c S _ _ T _ _ φ z z' w hφ hx hz hz'
  obtain ⟨g, a, -, hga⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S z z').1 hx
  have h1 := (GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c S T φ z z' w w g (a : S) hga hz).1 hz'
  have h2 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c T w w w).1
  obtain ⟨hg, ha⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c T w w).2 _ _ _ _ h1 h2
  have ha1 : (a : S) = ((1 : Sˣ) : S) := hφ (by rw [ha]; simp)
  have hg1 : g = fun _ => 1 := by
    funext τ
    have h := congrFun hg τ
    ext i j
    apply hφ
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at hij
    rw [hij]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  rw [ha1, hg1] at hga
  have h3 : FrChg (fun _ => 1) ((1 : Sˣ) : S) z z := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S z z z).1
  exact (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S z (fun _ => 1) 1 (fun _ => by simp)).unique h3 hga
end GlobalTheory.Frames
