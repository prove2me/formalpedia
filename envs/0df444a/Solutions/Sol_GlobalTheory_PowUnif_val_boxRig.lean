-- Prove2me | solution 1 for GlobalTheory.PowUnif.val_boxRig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:32:41.97789+00:00
-- url     : https://prove2.me/submissions/c2507622-eb12-4178-96f9-eeca51bb61f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_val_res
import Theorems.Thm_GlobalTheory_PowUnif_val_res_pull
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__units_prod_4b684ea369c1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
namespace GlobalTheory.PowUnif
theorem _root_.solution {G' G : Over (Sp ℂ)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}
    (p : Out.IsPowGrp G' G j) {L : LB G.left} {L' : LB G'.left} (w : LB.Iso L' (Out.boxLB L p.pr))
    (r : LB.Gen (L.pull (eSec G))) (r' : LB.Gen (L'.pull (eSec G')))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (Out.boxRig p L r))
    (a : L.ι) (b : (L'.pull (eSec G')).ι) (ha : ⊤ ≤ eSec G' ⁻¹ᵁ (Out.boxLB L p.pr).U fun _ => a)
    (hb : ⊤ ≤ (L'.pull (eSec G')).U b) :
    ∏ _i : Fin j, valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec G)).U fun _ => a) (r.s fun _ => a).val =
      valAt' (eSec G') ((Out.boxLB L p.pr).U (fun _ => a) ⊓ L'.U (b PUnit.unit)) (w.s (fun _ => a, b PUnit.unit)).val *
        valAt' (𝟙 (Sp ℂ)) ((L'.pull (eSec G')).U b) (r'.s b).val := by
  have ha' : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ ((Out.boxLB L p.pr).pull (eSec G')).U fun _ _ => a :=
    fun x hx => Set.mem_iInter.2 fun _ => ha hx
  have hV : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ (((Out.boxLB L p.pr).pull (eSec G')).U (fun _ _ => a) ⊓ (L'.pull (eSec G')).U b) :=
    (top_le_preimage_inf _ _ _).2 ⟨ha', hb⟩
  have h1 := (val_res (𝟙 (Sp ℂ)) _ _ hV).symm.trans
    ((congrArg (fun s => valAt' (𝟙 (Sp ℂ)) _ (Units.val s)) (h (fun _ _ => a, b))).trans (valAt'_mul _ _ _ _))
  refine Eq.trans ?_ (h1.trans (congrArg₂ (· * ·) ?_ (val_res _ _ _ hV)))
  · refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) (valAt'_units_prod (κ := Fin j) _ ha' Finset.univ _).symm
    have hi : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ LB.wchart (L.pull (p.pr i).left) (fun _ : PUnit => eSec G') (fun _ _ => a) :=
      top_le_preimage_mono _ (Out.GeneratorPullback.box_le L (fun i => (p.pr i).left) (fun _ : PUnit => eSec G') (fun _ _ => a) i) ha'
    refine Eq.trans ?_ (val_res _ _ _ ha').symm
    exact (val_res_pull (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) _ _ _ hi).symm
  · refine (valAt'_units_prod (κ := PUnit) _ hV Finset.univ _).trans ?_
    rw [Fintype.prod_unique, zpow_one]
    exact val_res_pull (𝟙 (Sp ℂ)) (eSec G') ((Out.boxLB L p.pr).U (fun _ => a) ⊓ L'.U (b PUnit.unit)) _ _ hV
end GlobalTheory.PowUnif
