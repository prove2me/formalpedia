-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.pullG_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:28.045729+00:00
-- url     : https://prove2.me/submissions/1ceab5b6-9375-4c3a-8ed5-1ce3d09f3b9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_RelModel_sval_cs_one
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
namespace GlobalTheory.UU.RelModel
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) :
    (zeroU R I).PullG F φ k (cs _ _ 1) (cs _ _ 1) := by
  intro Z rA y rG _ _ _ z JA JG _ _
  have a : gw (zeroU R I).wA y z (JG (y ≫ pullback.fst _ (jK R))) (fun _ => JA (y ≫ (zeroU R I).gen.hom.left)) = 1 :=
    map_one _
  rw [a]
  erw [sval_cs_one, sval_cs_one]
  simp
end GlobalTheory.UU.RelModel
