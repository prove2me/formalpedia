-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.exists_gen_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:16.118626+00:00
-- url     : https://prove2.me/submissions/48d73b7c-7c09-4fd7-affa-ed80ac129da6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {Y Y' X X' N N' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB N} {M' : LB N'}
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB) {Φ : X' ⟶ X} {v : LB.Iso L' (L.pull Φ)} (hv : PGen v)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (ω : Y ⟶ Y')
    (hc : ∀ κ, ω ≫ φ' κ ≫ Φ = φ κ) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      val t r z J = (∏ κ, gw v ((r ≫ ω) ≫ φ' κ) z (J (r ≫ φ κ)) (J' ((r ≫ ω) ≫ φ' κ)) ^ ε κ) * val a (r ≫ ω) z J' := by
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_up hv hL hL' a ha
  have hφ : φ = fun κ => ω ≫ φ' κ ≫ Φ := funext fun κ => (hc κ).symm
  subst hφ
  refine ⟨LB.pullGen L (fun k => φ' k ≫ Φ) ε t₀ ω, pullGen_isGen _ _ _ _ ht₀ ω, ?_⟩
  intro Z r z J J' hJ hJ'
  rw [val_pull hJ]
  have h1 := hv₀ Z (r ≫ ω) z _ _ (hJ.mem (fun k => φ' k ≫ Φ) (r ≫ ω)) (hJ'.mem φ' (r ≫ ω))
  unfold val
  rw [h1]
  unfold pw
  simp only [Category.assoc]
end GlobalTheory.ThetaBaseChange
