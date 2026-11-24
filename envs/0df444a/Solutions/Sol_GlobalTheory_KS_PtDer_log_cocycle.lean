-- Prove2me | solution 1 for GlobalTheory.KS.PtDer.log_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:17.316686+00:00
-- url     : https://prove2.me/submissions/bf457456-00cc-49f5-bf2c-6e4022a1d97c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassIsSymmOfLift
import Theorems.Thm_GlobalTheory_PowUnif_val_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
private theorem valAt'_mul_of_whole_le_preimage {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f f' : Γ(X, W)) : valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt'
  simp only [dif_pos hW]
  unfold valAt
  simp only [map_mul]
private theorem valAt'_one_of_whole_le_preimage {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) :
    valAt' y W 1 = 1 := by
  unfold valAt'
  simp only [dif_pos hW]
  unfold valAt
  simp only [map_one]
private theorem valAt'_unit_ne_zero' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  intro h0
  have h1 := valAt'_mul_of_whole_le_preimage y hW f.val f.inv
  rw [f.val_inv, valAt'_one_of_whole_le_preimage y hW, h0, zero_mul] at h1
  exact one_ne_zero h1
end GlobalTheory.KS
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
namespace GlobalTheory.KS
namespace PtDer
theorem _root_.solution {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) {L : LB X} (hL : L.IsLB)
    (i j k : L.ι) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) (hk : ⊤ ≤ y ⁻¹ᵁ L.U k) :
    δ _ (L.g i j).val / valAt' y _ (L.g i j).val + δ _ (L.g j k).val / valAt' y _ (L.g j k).val =
      δ _ (L.g i k).val / valAt' y _ (L.g i k).val := by
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_inf (le_inf hi hj) hk
  have hc := congrArg Units.val (hL.cocycle i j k)
  rw [Units.val_mul] at hc
  have hv := congrArg (valAt' y _) hc
  have hd := congrArg (δ _) hc
  rw [valAt'_mul_of_whole_le_preimage y hT, PowUnif.val_res y _ _ hT, PowUnif.val_res y _ _ hT,
    PowUnif.val_res y _ _ hT] at hv
  rw [h.mul _ hT, PowUnif.val_res y _ _ hT, PowUnif.val_res y _ _ hT] at hd
  have hd1 : ∀ (a b : L.ι) (hab : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U a ⊓ L.U b),
      δ _ (Semi.res hab (L.g a b)).val = δ (L.U a ⊓ L.U b) (L.g a b).val := fun a b hab =>
    h.res _ _ hab hT _
  rw [hd1, hd1, hd1] at hd
  have na : valAt' y (L.U i ⊓ L.U j) (L.g i j).val ≠ 0 := valAt'_unit_ne_zero' y (W := L.U i ⊓ L.U j) (le_inf hi hj) _
  have nb : valAt' y (L.U j ⊓ L.U k) (L.g j k).val ≠ 0 := valAt'_unit_ne_zero' y (W := L.U j ⊓ L.U k) (le_inf hj hk) _
  rw [← hv, ← hd]
  field_simp
  ring
end PtDer
end GlobalTheory.KS
