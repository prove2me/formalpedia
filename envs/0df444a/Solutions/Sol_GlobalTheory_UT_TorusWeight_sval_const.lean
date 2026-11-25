-- Prove2me | solution 1 for GlobalTheory.UT.TorusWeight.sval_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:46:40.319241+00:00
-- url     : https://prove2.me/submissions/068e111b-456c-462f-ba4a-ea7ad19036e8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TxFrameOfOne
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_inv
import Theorems.Thm_P2M_GlobalTheory_UT_CoefBasic_exists_good__0c0484e460d1
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.TorusWeight
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.TorusWeight
theorem _root_.solution {k : ℕ} (α : D.X) (ζ : F) (s s' : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    (∀ j, s'.f j = DegPre.constBF D F ζ _ * s.f j) ↔
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        sval s' ρ.left z J = sval s ρ.left z J *
          gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) j, r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) j →
      gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (DegPre.constBF D F ζ _ * s.f j) =
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (s.f j) *
          gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun Z r z j hm => (gs_mul r z _ hm _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl
      ((gs_res r z le_top hm _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _))))
  constructor
  · intro h T ρ z J hJ
    exact (congrArg (gs ρ.left z _) (h _)).trans (key _ ρ.left z _ (hJ.mem _ _))
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB y
    have e := h _ (𝟙 _) y J hJ
    refine Eq.trans ?_ (key _ (𝟙 _) y j hy).symm
    refine (sec_trans s' (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans ?_
    rw [sec_trans s (𝟙 _) y hy (hJ.mem _ (𝟙 _)), _root_.mul_assoc]
    exact congrArg _ e
end GlobalTheory.UT.TorusWeight
