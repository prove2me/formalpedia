-- Prove2me | solution 1 for GlobalTheory.ConstFam.isExtension_pullThrough
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:20:10.222006+00:00
-- url     : https://prove2.me/submissions/77fb3bff-ea31-446d-b04d-6d9ca0ff2084

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Theorems.Thm_GlobalTheory_ConstFam_exists_sec_up
import Theorems.Thm_GlobalTheory_ConstFam_SecThrough_unique
import Theorems.Thm_GlobalTheory_ConstFam_secThrough_pullThrough
import Theorems.Thm_GlobalTheory_ConstFam_sval_pullThrough
import Theorems.Thm_GlobalTheory_ConstFam_isExtension_comp
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_pullOver
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


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
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
namespace GlobalTheory.ConstFam
theorem _root_.solution {k E : Type} [Field k] [Field E] [Algebra k E] {π : Y ⟶ Spec (CommRingCat.of k)}
    {π' : Y' ⟶ Spec (CommRingCat.of E)} (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    [NoetherianSpace Y] (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) :
    IsExtension (pullThrough hw hL hL' hψ ε H.w) := by
  have hid : 𝟙 Y' ≫ π' = π' ≫ Spec.map (CommRingCat.ofHom (RingHom.id E)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
  have hψ' : ∀ k, φ' k ≫ F = 𝟙 Y' ≫ φ' k ≫ F := fun k => (Category.id_comp _).symm
  let θ := pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' ε hid
  refine isExtension_comp (isExtension_pullOver H hL ε hψ) θ ⟨?_, fun a => ?_⟩ _ fun t => ?_
  · refine (injective_iff_map_eq_zero θ).2 fun t ht => sec_ext' hL fun y J hJ => ?_
    obtain ⟨J', hJ'⟩ := exists_good' hL' y
    have e := sval_pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' hid t (𝟙 _) hJ hJ'
    rw [Category.id_comp] at e
    rw [e, show pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' ε hid t = 0 from ht, sval_zero' hJ',
      sval_zero' hJ, mul_zero]
  · obtain ⟨t, ht⟩ := exists_sec_up ((isGen_iff w).1 hw) hL hL' a
    refine ⟨t, (secThrough_pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' hid t).unique hL hL' hψ'
      fun Z r z p q hp hq => ?_⟩
    rw [Category.comp_id]
    exact ht Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  · refine sec_ext' hL' fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := exists_good' hL y
    refine (Units.mul_right_inj (∏ k, wVal w y J J' (𝟙 Y' ≫ φ' k) ^ ε k)).1 ?_
    rw [← sval_pullThrough hw hL hL' hψ H.w t _ hJ hJ',
      ← sval_pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' hid _ _ hJ hJ', sval_pullOver H.w hψ t _ hJ,
      Category.comp_id]
end GlobalTheory.ConstFam
