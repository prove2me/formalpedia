-- Prove2me | solution 1 for GlobalTheory.KS.Sym.Der.dl_coc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:28:24.602057+00:00
-- url     : https://prove2.me/submissions/7ac6f843-75fc-42fc-9be3-7385ec5f21b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
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
namespace GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
private lemma rsT_eq_resG_of_le_moduli {O₀ O : Z.Opens} (s : Γ(Z, O₀)) (h : O ≤ O₀) : rsT s O = resG Z h s := by
  unfold rsT
  rw [dif_pos h]
private lemma pbT_rsT_of_le_of_le_preimage' (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} (s : Γ(Y, O₀)) (h : O₁ ≤ O₀) {O : Z.Opens}
    (e : O ≤ f ⁻¹ᵁ O₁) : pbT f (rsT s O₁) O = pbT f s O := by
  unfold rsT pbT
  rw [dif_pos h, dif_pos e, dif_pos (e.trans (fun x hx => h hx))]
  dsimp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
private lemma pbT_mul_moduli (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (a * b) O = pbT f a O * pbT f b O := by
  unfold pbT
  split_ifs <;> simp
private lemma pbT_one_of_le_preimage (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (e : O ≤ f ⁻¹ᵁ O₀) :
    pbT f (1 : Γ(Y, O₀)) O = 1 := by
  unfold pbT
  rw [dif_pos e, map_one]
variable {K R : Type} [Field K] [CommRing R]
end GlobalTheory.KS.Sym
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
namespace GlobalTheory.KS.Sym
namespace Der
theorem _root_.solution {h : Z ⟶ X} {T : Z.Opens} {δ : ∀ O : X.Opens, Γ(X, O) → ∀ O' : Z.Opens, Γ(Z, O')}
    (a : Der h T δ) {L : LB X} (hL : L.IsLB) (i j k : L.ι) {O' : Z.Opens} (h₁ : O' ≤ T)
    (hi : O' ≤ h ⁻¹ᵁ L.U i) (hj : O' ≤ h ⁻¹ᵁ L.U j) (hk : O' ≤ h ⁻¹ᵁ L.U k) :
    dl h L δ i j O' + dl h L δ j k O' = dl h L δ i k O' := by
  have hij : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j := inf_le_left
  have hjk : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k := fun x hx => ⟨hx.1.2, hx.2⟩
  have hik : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k := fun x hx => ⟨hx.1.1, hx.2⟩
  have hV : O' ≤ h ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := fun x hx => ⟨⟨hi hx, hj hx⟩, hk hx⟩
  have c := hL.cocycle i j k
  have cv : resG X hij (L.g i j).val * resG X hjk (L.g j k).val = resG X hik (L.g i k).val := by
    have := congrArg Units.val c
    simp only [Units.val_mul] at this
    exact this
  have ci : resG X hij (L.g i j)⁻¹.val * resG X hjk (L.g j k)⁻¹.val = resG X hik (L.g i k)⁻¹.val := by
    have := congrArg (fun u => (u⁻¹).val) c
    simp only [mul_inv_rev, Units.val_mul, ← map_inv] at this
    rw [mul_comm]
    exact this
  have unit : ∀ (u : (Γ(X, L.U i ⊓ L.U j ⊓ L.U k))ˣ), pbT h u.val O' * pbT h u⁻¹.val O' = 1 := fun u => by
    rw [← pbT_mul_moduli, Units.mul_inv, pbT_one_of_le_preimage h hV]
  unfold dl
  simp only [Units.inv_eq_val_inv]
  rw [← a.2.1 _ _ (L.g i j).val O' hij h₁ hV, ← a.2.1 _ _ (L.g j k).val O' hjk h₁ hV,
    ← a.2.1 _ _ (L.g i k).val O' hik h₁ hV,
    ← pbT_rsT_of_le_of_le_preimage' h ((L.g i j)⁻¹.val : Γ(X, L.U i ⊓ L.U j)) hij hV,
    ← pbT_rsT_of_le_of_le_preimage' h ((L.g j k)⁻¹.val : Γ(X, L.U j ⊓ L.U k)) hjk hV,
    ← pbT_rsT_of_le_of_le_preimage' h ((L.g i k)⁻¹.val : Γ(X, L.U i ⊓ L.U k)) hik hV]
  simp only [rsT_eq_resG_of_le_moduli _ hij, rsT_eq_resG_of_le_moduli _ hjk, rsT_eq_resG_of_le_moduli _ hik]
  rw [← cv, ← ci, a.1 _ _ _ O' h₁ hV, pbT_mul_moduli]
  have hA := unit (Units.map (resG X hij).toMonoidHom (L.g i j))
  have hB := unit (Units.map (resG X hjk).toMonoidHom (L.g j k))
  simp only [Units.coe_map, Units.coe_map_inv] at hA hB
  linear_combination (-(δ _ (resG X hjk (L.g j k).val) O' * pbT h (resG X hjk (L.g j k)⁻¹.val) O')) * hA +
    (-(δ _ (resG X hij (L.g i j).val) O' * pbT h (resG X hij (L.g i j)⁻¹.val) O')) * hB
end Der
end GlobalTheory.KS.Sym
