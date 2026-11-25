-- Prove2me | solution 1 for GlobalTheory.exists_isLB_of_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:51.889065+00:00
-- url     : https://prove2.me/submissions/cafad5c7-9309-464b-8302-f1bf95b6b7ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMemThetaLevelCharApplyNeZero
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
private lemma valAt'_mul_of_preimage_whole {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f f' : Γ(Y, U)) : valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  simp only [valAt', dif_pos h, valAt, map_mul]
private lemma valAt'_one' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valAt' x U 1 = 1 := by
  simp only [valAt', dif_pos h, valAt, map_one]
private lemma preimage_whole_of_le {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ W :=
  fun _ ha => hVW (h ha)
private lemma preimage_inf_whole_of_whole {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hW : ⊤ ≤ x ⁻¹ᵁ W) : ⊤ ≤ x ⁻¹ᵁ (V ⊓ W) :=
  fun _ ha => ⟨hV ha, hW ha⟩
private lemma valAt'_presheaf_map' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, W)) :
    valAt' x V ((Y.presheaf.map (homOfLE hVW).op).hom f) = valAt' x W f := by
  have hW : ⊤ ≤ x ⁻¹ᵁ W := preimage_whole_of_le x hVW h
  have key : Y.presheaf.map (homOfLE hVW).op ≫ x.appLE V ⊤ h = x.appLE W ⊤ hW := by
    rw [Scheme.Hom.map_appLE]
  simp only [valAt', dif_pos h, dif_pos hW, valAt]
  rw [← key]
  rfl
private lemma valAt'_res_units {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, W)ˣ) :
    valAt' x V ((res hVW f : Γ(Y, V)ˣ) : Γ(Y, V)) = valAt' x W (f : Γ(Y, W)) := by
  unfold res
  rw [Units.coe_map]
  exact valAt'_presheaf_map' x hVW h f
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (X : Over (Sp ℂ)) {Z κ : Type} (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hex : Function.Surjective ex)
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ x.left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f')
    (U : κ → X.left.Opens) (hU : ⨆ i, U i = ⊤) (fr : κ → Z → ℂ)
    (hfr : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ U i → fr i z ≠ 0)
    (hreg : ∀ i j, ∃ φ : Γ(X.left, U i ⊓ U j), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
      valAt' (ex z).left (U i ⊓ U j) φ = fr i z / fr j z) :
    ∃ tr : ∀ i j, Γ(X.left, U i ⊓ U j)ˣ, (LB.mk κ U tr).IsLB ∧ ∀ i j z,
      ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
        fr i z = valAt' (ex z).left (U i ⊓ U j) (tr i j).val * fr j z := by
  choose φ hφ using hreg
  have mem : ∀ (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) {V W : X.left.Opens}, V ≤ W → ⊤ ≤ x.left ⁻¹ᵁ V →
      ⊤ ≤ x.left ⁻¹ᵁ W := fun x _ _ hVW h => preimage_whole_of_le x.left hVW h
  let ψ : ∀ i j, Γ(X.left, U i ⊓ U j) := fun i j =>
    (X.left.presheaf.map (homOfLE (inf_comm (U i) (U j)).le).op).hom (φ j i)
  have hψ : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
      valAt' (ex z).left (U i ⊓ U j) (ψ i j) = fr j z / fr i z := by
    intro i j z hz
    rw [valAt'_presheaf_map' _ _ hz, hφ j i z (mem _ (inf_comm (U i) (U j)).le hz)]
  have hmul : ∀ i j, φ i j * ψ i j = 1 := by
    intro i j
    apply hext
    intro x hx
    obtain ⟨z, rfl⟩ := hex x
    rw [valAt'_mul_of_preimage_whole _ _ hx, valAt'_one' _ _ hx, hφ i j z hx, hψ i j z hx]
    have h1 := hfr i z (mem _ inf_le_left hx)
    have h2 := hfr j z (mem _ inf_le_right hx)
    rw [div_mul_div_comm, mul_comm (fr i z), div_self (mul_ne_zero h2 h1)]
  refine ⟨fun i j => Units.mkOfMulEqOne (φ i j) (ψ i j) (hmul i j), ⟨hU, fun i => ?_, fun i j k => ?_⟩, ?_⟩
  · apply Units.ext
    apply hext
    intro x hx
    obtain ⟨z, rfl⟩ := hex x
    rw [valAt'_res_units _ _ hx, Units.val_one, valAt'_one' _ _ hx]
    simp only [Units.val_mkOfMulEqOne]
    rw [hφ i i z (mem _ ?_ hx), div_self (hfr i z (mem _ ?_ hx))]
    all_goals simp
  · apply Units.ext
    apply hext
    intro x hx
    obtain ⟨z, rfl⟩ := hex x
    have pi := mem _ (inf_le_left.trans inf_le_left) hx
    have pj := mem _ (inf_le_left.trans inf_le_right) hx
    have pk := mem _ inf_le_right hx
    rw [Units.val_mul, valAt'_mul_of_preimage_whole _ _ hx, valAt'_res_units _ _ hx, valAt'_res_units _ _ hx,
      valAt'_res_units _ _ hx]
    simp only [Units.val_mkOfMulEqOne]
    rw [hφ i j z (preimage_inf_whole_of_whole _ pi pj), hφ j k z (preimage_inf_whole_of_whole _ pj pk), hφ i k z (preimage_inf_whole_of_whole _ pi pk)]
    have h1 := hfr i z pi
    have h2 := hfr j z pj
    have h3 := hfr k z pk
    field_simp
  · intro i j z hz
    simp only [Units.val_mkOfMulEqOne]
    rw [hφ i j z hz, div_mul_cancel₀ _ (hfr j z (mem _ inf_le_right hz))]
end GlobalTheory
