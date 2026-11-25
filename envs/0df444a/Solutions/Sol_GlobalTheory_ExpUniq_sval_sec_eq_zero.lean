-- Prove2me | solution 1 for GlobalTheory.ExpUniq.sval_sec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:45.510944+00:00
-- url     : https://prove2.me/submissions/cad0ccd5-6cdf-404b-9150-3e70492e4b18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {σ σ' : U.SecGT T k} {f f' : ∀ α, SecBT D T k α}
namespace GlobalTheory.ExpUniq
theorem _root_.solution (h : U.ExpT T k σ f)
    (hf : ∀ α (Z : Scheme.{0}) (r : Z ⟶ _) z J, Good D.P.L z J → sval (f α) r z J = 0) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ G).left) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (ha : (r ≫ (snd T G).left) ≫ G.hom = a ≫ thick R I e) (z : Z) (JG) (hJG : Good U.P.L.L z JG) :
    sval σ r z JG = 0 := by
  obtain ⟨s, hs⟩ := h e
  let x : Z ⟶ (thickObj R I e G).left := pullback.lift _ a ha
  have hx : x ≫ (fstG I e G).left = r ≫ (snd T G).left := pullback.lift_fst _ _ _
  have hb : (U.gt e).pG.left ≫ D.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have w : (r ≫ (fst T G).left) ≫ T.hom = (x ≫ (U.gt e).pG.left) ≫ D.P.A.hom := by
    rw [Category.assoc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hx, Category.assoc, Category.assoc,
      Over.w, Over.w]
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
  have E := (hs Z x r (pullback.lift _ _ w) hx.symm (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    z JG J hJG hJ).2
  rw [Finset.sum_eq_zero (fun α _ => by rw [hf α _ _ z J hJ, zero_mul]), ← Units.val_pow_eq_pow_val] at E
  exact (Units.mul_right_eq_zero _).1 E
end GlobalTheory.ExpUniq
