-- Prove2me | solution 1 for GlobalTheory.ConstFam.exists_sec_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:16:46.630122+00:00
-- url     : https://prove2.me/submissions/02d61c34-c6d5-46d5-816f-f15b33268803

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.ConstFam
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {ε : K → ℤ} (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ t : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  obtain ⟨t, ht⟩ := exists_sec_transfer (A := LB.LinComb L (fun k => φ' k ≫ F) ε) (B := LB.LinComb L' φ' ε)
    (exists_wchart hL' φ') u (fun y p q q' hp hq hq' => by
      refine (congrArg₂ (· * ·) (hu p q _ (𝟙 Y) y ⟨hp, hq⟩) (gm_linComb L' φ' ε (𝟙 Y) y q q' hq hq')).trans
        (Eq.trans ?_ (hu p q' _ (𝟙 Y) y ⟨hp, hq'⟩).symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp hq hq', trF_self hL _ ε (𝟙 Y) y hp, one_mul]
      exact inv_mul_cancel_comm _ _) (fun y p p' q hp hp' hq => by
      refine (hu p q _ (𝟙 Y) y ⟨hp, hq⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
        (gm_linComb L _ ε (𝟙 Y) y p p' hp hp') (hu p' q _ (𝟙 Y) y ⟨hp', hq⟩)).symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp' hq hq, trF_self hL' _ ε (𝟙 Y) y hq, inv_one, mul_one]
      rfl) a
  exact ⟨t, fun Z r z p q hp hq => (ht Z r z p q hp hq).trans
    (congrArg (fun v : (Z.presheaf.stalk z)ˣ => v.val * _) (hu p q Z r z ⟨hp, hq⟩))⟩
end GlobalTheory.ConstFam
