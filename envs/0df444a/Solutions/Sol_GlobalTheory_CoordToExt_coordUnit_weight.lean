-- Prove2me | solution 1 for GlobalTheory.CoordToExt.coordUnit_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:24.711509+00:00
-- url     : https://prove2.me/submissions/4a4c6b14-75d0-4033-b74a-1500bdcf25e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_CoordToExt_gm_coordUnit
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)
variable {I D e} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace GlobalTheory.CoordToExt
theorem _root_.solution (χ : D.X) (a : (bundle I D e χ).ι) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (t : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left)
    (h : g.q.left (y.left z) ∈ (bundle I D e χ).U a) :
    gm ((t ≫ g.i) * y).left z _ (coordUnit g χ a) =
      gm t.left z ⊤ (charUnit _ D.X χ) * gm y.left z _ (coordUnit g χ a) := by
  have := g.q_hom
  have e₀ : ((t ≫ g.i) * y) ≫ g.q = y ≫ g.q := by
    rw [MonObj.mul_comp, Category.assoc, g.isKernel.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  have e₁ : ((t ≫ g.i) * y).left ≫ g.q.left = y.left ≫ g.q.left := congrArg (fun f => f.left) e₀
  have h' : g.q.left (((t ≫ g.i) * y).left z) ∈ (bundle I D e χ).U a :=
    (congrArg (fun f => f z ∈ (bundle I D e χ).U a) e₁).mpr h
  have e₂ : ∀ k, ((t ≫ g.i) * y).left ≫ D.Oφ g.pG χ k = y.left ≫ D.Oφ g.pG χ k := fun k => by
    rw [← q_Oφ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans (Category.assoc _ _ _))
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB z
  have v := TorusCoord.val_t_act g t y χ (𝟙 _) z J hJ
  have c : splitTorusPointsEquiv _ D.X Z t (Multiplicative.ofAdd χ) = pullU t.left ⊤ (charUnit _ D.X χ) :=
    Units.ext (splitTorusPointsEquiv_val _ _ _ t χ)
  have c' := gm_pull (𝟙 _) t.left z ⊤ trivial (charUnit _ D.X χ)
  rw [Category.id_comp] at c'
  rw [Category.id_comp, Category.id_comp, c] at v
  have v' := v.trans (congrArg (· * _) c')
  have t₁ := gen_trans (g.t_gen χ) _ z (mem_chart g χ a _ h') (hJ.mem _ ((t ≫ g.i) * y).left)
  have t₂ := gen_trans (g.t_gen χ) _ z (mem_chart g χ a _ h) (hJ.mem _ y.left)
  have t₃ : trF (D.Oφ g.pG χ) Oinvε ((t ≫ g.i) * y).left z a (fun k => J (((t ≫ g.i) * y).left ≫ D.Oφ g.pG χ k)) =
      trF (D.Oφ g.pG χ) Oinvε y.left z a (fun k => J (y.left ≫ D.Oφ g.pG χ k)) :=
    Finset.prod_congr rfl fun k _ => congrArg
      (fun f => gm f z (D.P.L.U (a k) ⊓ D.P.L.U (J f)) (D.P.L.g (a k) (J f)) ^ Oinvε k) (e₂ k)
  refine ((gm_coordUnit g χ a _ z h').trans (t₁.trans (congrArg₂ (· * ·) t₃ v'))).trans (Eq.symm ?_)
  exact (congrArg (_ * ·) ((gm_coordUnit g χ a _ z h).trans t₂)).trans (mul_left_comm _ _ _)
end GlobalTheory.CoordToExt
