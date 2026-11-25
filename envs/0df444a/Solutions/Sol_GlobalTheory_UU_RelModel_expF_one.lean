-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.expF_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:59.736606+00:00
-- url     : https://prove2.me/submissions/f4dc5e2a-8d7d-4bc9-8980-0e3e554e393b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_RelModel_sval_cs_one
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution : (zeroU R I).ExpF F k (cs _ _ 1) (fun _ => cs _ _ 1) := by
  have g : ∀ {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : Y ⟶ Spec (CommRingCat.of F)), gs r z ⊤ (scal p 1) = 1 :=
    fun r z p => by rw [gs_eq r z ⊤ trivial]; simp only [scal, map_one]
  refine ⟨1, fun _ => 1, fun _ => cs _ _ 1, fun _ _ => cs _ _ 1, fun _ e => ⟨{PUnit.unit}, ?_⟩, ?_, ?_⟩
  · intro Z x rG rB _ _ _ z JG J _ _
    refine ⟨fun α hα => (hα (Finset.mem_singleton_self _)).elim, ?_⟩
    have a : gw ((zeroU R I).w e) x z (J (x ≫ ((zeroU R I).gt e).pG.left)) (fun _ => JG (x ≫ (fstG I e _).left)) = 1 :=
      map_one _
    have b : val (((zeroU R I).gt e).t PUnit.unit) x z J = 1 := (congrArg _ (gv_one _)).trans (map_one _)
    rw [a]
    erw [Finset.sum_singleton, b, sval_cs_one, sval_cs_one]
    simp
  · intro Z rA y rG _ _ z JA JG _ _
    have a : gw (zeroU R I).wA y z (JG (y ≫ pullback.fst _ (jK R))) (fun _ => JA (y ≫ (zeroU R I).gen.hom.left)) = 1 :=
      map_one _
    rw [a, Fin.sum_univ_one, g]
    erw [sval_cs_one, sval_cs_one]
    simp
  · intro α Z rF rB _ z J _
    rw [Fin.sum_univ_one, g]
    erw [sval_cs_one, sval_cs_one]
    simp
end GlobalTheory.UU.RelModel
