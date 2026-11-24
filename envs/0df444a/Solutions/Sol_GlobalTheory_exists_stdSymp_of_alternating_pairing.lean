-- Prove2me | solution 1 for GlobalTheory.exists_stdSymp_of_alternating_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:03.112031+00:00
-- url     : https://prove2.me/submissions/16a291c8-b32a-440c-a65d-6c1c24ef9981

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
import Theorems.Thm_GlobalTheory_SympMod_exists_stdSymp_zmod
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory
theorem _root_.solution :
    ∀ (M g : ℕ) (G : Type) [CommGroup G] (R : Type) [CommRing R] [IsDomain R] (ζ : Rˣ), 0 < M →
    IsPrimitiveRoot ζ M → (∀ x : G, x ^ M = 1) →
    (∀ d : ℕ, d ∣ M → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) →
    ∀ e : G →* G →* Rˣ, (∀ x, e x x = 1) → (∀ x, (∀ y, e x y = 1) → x = 1) →
    ∃ x : Fin (2 * g) → G, ∀ i j, e (x i) (x j) = ζ ^ stdSymp g i j := by
  intro M g G _ R _ _ ze hM hz hG hc w halt hnd
  have : NeZero M := ⟨hM.ne'⟩
  have wm : ∀ x y, w x y ∈ Subgroup.zpowers ze := fun x y => by
    rw [hz.zpowers_eq, mem_rootsOfUnity, ← map_pow, hG, map_one]
  have hT : ∀ x : Additive G, M • x = 0 := fun x => hG x.toMul
  let _ : Module (ZMod M) (Additive G) := AddCommGroup.zmodModule hT
  let β : Additive G → Additive G → ZMod M := fun x y =>
    hz.zmodEquivZPowers.symm (Additive.ofMul ⟨w x.toMul y.toMul, wm _ _⟩)
  have βl : ∀ x x' y, β (x + x') y = β x y + β x' y := fun x x' y => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (by
      show w (x.toMul * x'.toMul) y.toMul = w x.toMul y.toMul * w x'.toMul y.toMul
      rw [map_mul, MonoidHom.mul_apply]))
  have βr : ∀ x y y', β x (y + y') = β x y + β x y' := fun x y y' => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (map_mul (w x.toMul) y.toMul y'.toMul))
  have βw : ∀ x y (n : ℤ), β x y = n ↔ w x.toMul y.toMul = ze ^ n := fun x y n => by
    simp only [β]
    rw [AddEquiv.symm_apply_eq, hz.zmodEquivZPowers_apply_coe_int]
    exact Subtype.ext_iff
  let B : LinearMap.BilinForm (ZMod M) (Additive G) := LinearMap.mk₂ _ β βl
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β · y) fun x x' => βl x x' y) c x) βr
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β x) (βr x)) c y)
  obtain ⟨v, hv⟩ := SympMod.exists_stdSymp_zmod (V := Additive G) (g := g) (B := B)
    (fun x => ((βw x x 0).2 (by simpa using halt _)).trans Int.cast_zero)
    (fun x hx => hnd x.toMul fun y => by
      have h := (βw x (Additive.ofMul y) 0).1 ((hx _).trans Int.cast_zero.symm)
      rwa [zpow_zero] at h) (fun d hd => hc d hd)
  exact ⟨fun i => (v i).toMul, fun i k => (βw _ _ _).1 (hv i k)⟩
end GlobalTheory
