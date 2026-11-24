-- Prove2me | solution 1 for GlobalTheory.ThetaPtExist.exists_pullSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:25.977019+00:00
-- url     : https://prove2.me/submissions/d8adbdd7-c37b-4d2d-8aef-56e10245bf8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec


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
open ThetaAct
namespace GlobalTheory.ThetaPtExist
theorem _root_.solution (hL : L.IsLB) {a : ℤ} {T' : Over S} (h : T' ⟶ T) (v : SecM A L a T) :
    ∃ w : SecM A L a T', ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J), Good L z J →
      sv w r z J = sv v (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  obtain ⟨w, hw⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T' A).left) (ε' := fun _ => a)
    (fun U _ f => Finset.prod_congr rfl fun i _ => congrArg (fun q => f q ^ a) e₀)
    (H1.SectionArithmetic.pullSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (SecM.toSec A v) (h ▷ A).left)
  exact ⟨SecM.ofSec A w, fun Z r z J hJ => (hw Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
end GlobalTheory.ThetaPtExist
