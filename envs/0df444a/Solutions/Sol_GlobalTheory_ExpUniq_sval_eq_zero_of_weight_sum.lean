-- Prove2me | solution 1 for GlobalTheory.ExpUniq.sval_eq_zero_of_weight_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:57:15.836278+00:00
-- url     : https://prove2.me/submissions/9238c9ce-ed0c-4044-9706-372da409648c

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
import Theorems.Thm_GlobalTheory_ExpUniq_sval_eq_zero_of_sum
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_left_pG


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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : GtCoord I D e G)
  {Y : Scheme.{0}} (p : Y ⟶ D.P.A.left) {K : Type} [Fintype K] {ε : K → ℤ}
namespace GlobalTheory.ExpUniq
theorem _root_.solution {φ : D.X → K → (Y ⟶ D.P.A.left)} (s : ∀ χ, LB.Sec (LB.LinComb D.P.L (φ χ) ε))
    (F : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y), r ≫ p = x ≫ c.pG.left →
      ∀ z J, Good D.P.L z J → ∑ χ ∈ F, sval (s χ) r z J * (val (c.t χ) x z J).val = 0)
    (α : D.X) (hα : α ∈ F) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y)
    (hr : r ≫ p = x ≫ c.pG.left) (z : Z) (J) (hJ : Good D.P.L z J) : sval (s α) r z J = 0 := by
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (x ≫ (thickObj R I e G).hom)
  let y : Z' ⟶ thickObj R I e G := Over.homMk x rfl
  let m : WeightPf.Te D I e ⊗ Z' ⟶ WeightPf.Te D I e ⊗ thickObj R I e G := WeightPf.Te D I e ◁ y
  let π : (WeightPf.Te D I e ⊗ Z').left ⟶ Z := (snd (WeightPf.Te D I e) Z').left
  have m₁ : m.left ≫ (fst _ _ : _ ⟶ WeightPf.Te D I e).left = (fst (WeightPf.Te D I e) Z').left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have m₂ : m.left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left = π ≫ x := by
    rw [← Over.comp_left, whiskerLeft_snd]; rfl
  have E := sval_eq_zero_of_sum D.X Z' D.P.isLB _ _
    (fun χ => pullMulSec (s χ) r (LB.pullGen D.P.L _ _ (c.t χ) x) (DVR.pullGen_isGen _ _ _ _ (c.t_gen χ) _)) F
    (fun w J hJ => by
      refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_)
        (H _ (m.left ≫ (WeightPf.act c).left) (π ≫ r) (by
          rw [Category.assoc, hr, Category.assoc, WeightPf.act_left_pG, ← Category.assoc, ← m₂, Category.assoc])
          w J hJ)
      have h := val_corr hJ (c.t_weight χ) m.left
      have h' : val (c.t χ) (m.left ≫ (WeightPf.act c).left) w J =
          gm (fst (WeightPf.Te D I e) Z').left w ⊤ (charUnit _ D.X χ) * val (c.t χ) (π ≫ x) w J := by
        rw [← m₁, ← m₂]
        refine (val_pull hJ _ _ _).symm.trans (h.trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) ?_ (val_pull hJ _ _ _))))
        exact (gm_res _ w _ (hJ.mem (PEmpty.elim : PEmpty → (_ ⟶ D.P.A.left)) _) _).trans
          (gm_pull _ _ w ⊤ trivial _)
      have h₀ : gs (𝟙 _) w ⊤ (TorusInj.chiP D.X Z' χ) =
          (gm (fst (WeightPf.Te D I e) Z').left w ⊤ (charUnit _ D.X χ)).val :=
        ((gs_pull (𝟙 _) (fst (WeightPf.Te D I e) Z').left w ⊤ trivial _).trans
          (by rw [Category.id_comp])).trans (gs_unit _ w ⊤ trivial _)
      rw [h', h₀, Units.val_mul, mul_left_comm]
      exact congrArg _ ((sval_pullMulSec _ _ _ _ π w hJ).trans
        (congrArg (fun u => _ * Units.val u) (val_pull hJ _ _ _)))) α hα z J hJ
  have E' := (sval_pullMulSec (s α) r _ _ (𝟙 Z) z hJ).symm.trans E
  rw [Category.id_comp] at E'
  exact (Units.mul_left_eq_zero _).1 E'
end GlobalTheory.ExpUniq
