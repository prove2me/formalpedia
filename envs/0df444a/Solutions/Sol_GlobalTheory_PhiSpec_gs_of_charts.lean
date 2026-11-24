-- Prove2me | solution 1 for GlobalTheory.PhiSpec.gs_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:15.218215+00:00
-- url     : https://prove2.me/submissions/ac49c405-c95a-4561-aac0-e0e79582a7f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {G : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.PhiSpec
theorem _root_.solution {w : LB.Iso L' (L.pull G)} (hw : PGen w) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ G = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι}
    (hp : ∀ k, G (φ' k (r z)) ∈ L.U (p k)) (hq : ∀ k, φ' k (r z) ∈ L'.U (q k))
    (hp' : ∀ k, G (φ' k (r z)) ∈ L.U (p' k)) (hq' : ∀ k, φ' k (r z) ∈ L'.U (q' k))
    (H : gs (r ≫ h) z (LB.wchart L φ p') (s.f p') =
      (∏ k, gw w (r ≫ φ' k) z (p' k) (q' k) ^ ε k).val * gs r z (LB.wchart L' φ' q') (s'.f q')) :
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L' φ' q) (s'.f q) := by
  have m : ∀ {p : K → L.ι}, (∀ k, G (φ' k (r z)) ∈ L.U (p k)) → (r ≫ h) z ∈ LB.wchart L φ p := fun hp =>
    Set.mem_iInter.2 fun k => by
      show φ k (h (r z)) ∈ L.U _
      rw [pt_eq hψ]; exact hp k
  have a := sec_trans s (r ≫ h) z (m hp) (m hp')
  have b := sec_trans s' r z (Set.mem_iInter.2 hq) (Set.mem_iInter.2 hq')
  have c := pw_trans hw φ' ε r z (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)
    (Set.mem_iInter.2 hq')
  have d : trF (fun k => φ' k ≫ G) ε r z p p' = trF φ ε (r ≫ h) z p p' :=
    Finset.prod_congr rfl fun k _ => by rw [Category.assoc, ← hψ k]
  rw [d] at c
  show _ = (pw w φ' ε r z p q).val * _
  rw [a, b, c, H]
  show _ * ((pw w φ' ε r z p' q').val * _) = _
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_right_comm _ _ (trF φ' ε r z q q'),
    inv_mul_cancel_right]
end GlobalTheory.PhiSpec
