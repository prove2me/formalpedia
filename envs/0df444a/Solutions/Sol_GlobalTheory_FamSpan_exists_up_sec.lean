-- Prove2me | solution 1 for GlobalTheory.FamSpan.exists_up_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:42:28.074745+00:00
-- url     : https://prove2.me/submissions/ab075ce2-221f-45a4-a9c3-e9362b23461f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_self


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
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamSpan
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.FamSpan
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L' φ' ε)) :
    ∃ a : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (a.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (s.f q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ a : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ a = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (s.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (s.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (inf_le_right : W q ≤ LB.wchart L' φ' q)).op).hom (s.f q),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz)))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => φ' k ≫ F) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2,
          pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2, trF_self hL _ ε (𝟙 Y) y hy.1.1, _root_.one_mul,
          ← _root_.mul_assoc, ← Units.val_mul, mul_right_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨a, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W q)) (ha q)).trans (hv Z r z q hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => ha p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (ha j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y q hy.2 m)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, _root_.mul_one, Units.val_mul,
    _root_.mul_assoc]
  rfl
end GlobalTheory.FamSpan
