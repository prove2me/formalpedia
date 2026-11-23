-- Prove2me | solution 1 for GlobalTheory.ThetaPtExist.exists_isValueAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:33.105321+00:00
-- url     : https://prove2.me/submissions/396c0370-e4c0-4426-9372-05d592d1865a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Theorems.Thm_GlobalTheory_EvVal_existsUnique_sec_eq_mul_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_linComb_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtExist
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.ThetaPtExist
theorem _root_.solution (hL : L.IsLB) {n : ℤ} (s : LB.Sec (LPow A L n T)) (w : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => n)))
    (hτ : τ.IsGen) : ∃ c, IsValueAt A L n s w τ c :=
  (EvVal.existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover L hL _ _)
    (EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A w).left
      (fun _ => w.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le A L w) s) τ hτ).exists
end GlobalTheory.ThetaPtExist
