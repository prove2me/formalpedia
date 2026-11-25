-- Prove2me | solution 1 for GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:15:19.678623+00:00
-- url     : https://prove2.me/submissions/62827b7a-b14a-47eb-a652-f547b79005e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalGeneratorDivBaseUnitEqGeneric
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalGeneratorDivBaseUnitEqGenericStatement
import Theorems.Thm_GlobalTheory_DivConst_exists_genPull_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  first | exact @GlobalTheory.DivConst.exists_genPull_eq | exact GlobalTheory.DivConst.exists_genPull_eq | (intros; apply GlobalTheory.DivConst.exists_genPull_eq <;> assumption)
end _root_.GlobalTheory.T
