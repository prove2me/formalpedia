-- Prove2me | solution 1 for GlobalTheory.LevelExist.exists_stdSymp_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:24.116278+00:00
-- url     : https://prove2.me/submissions/07d93414-fd5a-4226-a443-5563786b08bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsIsSymplecticFamilySpan
import Theorems.Thm_GlobalTheory_LevelExist_exists_stdSymp_zmod
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
open GlobalTheory GlobalTheory.LevelExist
open ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.LevelExist
theorem _root_.solution {p J g : ℕ} (hp : p.Prime) {G R : Type*} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ m, Nat.card {x : G // x ^ p ^ m = 1} = (p ^ m) ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze (p ^ J))
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ p ^ J = 1 → y ^ p ^ J = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ p ^ J = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ p ^ J = 1 → (∀ y, y ^ p ^ J = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ p ^ J = 1) ∧ (∀ i k, W (v i) (v k) (ze ^ stdSymp g i k)) ∧
      Function.Injective fun c : Fin (2 * g) → Fin (p ^ J) => ∏ i, v i ^ (c i : ℕ) := by
  rcases J with _ | j
  · obtain rfl : ze = 1 := by simpa using hz.pow_eq_one
    refine ⟨fun _ => 1, fun _ => one_pow _, fun _ _ => by simpa using halt 1 (one_pow _), fun c c' _ => ?_⟩
    exact funext fun i => Fin.ext (by have := (c i).2; have := (c' i).2; simp at *; omega)
  have hp0 := hp.pos
  have : NeZero (p ^ (j + 1)) := ⟨by positivity⟩
  let T : Subgroup G := (powMonoidHom (p ^ (j + 1))).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  have wm : ∀ x y, w x y ∈ Subgroup.zpowers ze := fun x y => by
    rw [hz.zpowers_eq, mem_rootsOfUnity]
    have := map_pow (MonoidHom.mk' (w x) (wr x)) y (p ^ (j + 1))
    rw [show y ^ p ^ (j + 1) = 1 from Subtype.ext y.2, map_one] at this
    exact this.symm
  have hT : ∀ x : Additive T, p ^ (j + 1) • x = 0 := fun x => Subtype.ext x.toMul.2
  let _ : Module (ZMod (p ^ (j + 1))) (Additive T) := AddCommGroup.zmodModule hT
  let β : Additive T → Additive T → ZMod (p ^ (j + 1)) := fun x y =>
    hz.zmodEquivZPowers.symm (Additive.ofMul ⟨w x.toMul y.toMul, wm _ _⟩)
  have βl : ∀ x x' y, β (x + x') y = β x y + β x' y := fun x x' y => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (wl _ _ _))
  have βr : ∀ x y y', β x (y + y') = β x y + β x y' := fun x y y' => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (wr _ _ _))
  have βw : ∀ x y (n : ℤ), β x y = n ↔ w x.toMul y.toMul = ze ^ n := fun x y n => by
    simp only [β]
    rw [AddEquiv.symm_apply_eq, hz.zmodEquivZPowers_apply_coe_int]
    exact Subtype.ext_iff
  let B : LinearMap.BilinForm (ZMod (p ^ (j + 1))) (Additive T) := LinearMap.mk₂ _ β βl
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β · y) fun x x' => βl x x' y) c x) βr
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β x) (βr x)) c y)
  have hcount : ∀ m, m ≤ j + 1 → Nat.card {x : Additive T // p ^ m • x = 0} = (p ^ m) ^ (2 * g) := fun m hm => by
    rw [← hc m]
    refine Nat.card_congr ⟨fun x => ⟨x.1.toMul.1, congrArg Subtype.val x.2⟩,
      fun x => ⟨Additive.ofMul ⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩
    obtain ⟨d, hd⟩ := pow_dvd_pow p hm
    show x.1 ^ _ = 1
    rw [hd, pow_mul, x.2, one_pow]
  obtain ⟨v, hv, hli⟩ := exists_stdSymp_zmod (V := Additive T) (g := g) hp (hc (j + 1)) (hcount j j.le_succ)
    (by simpa using hcount 1 (by omega)) (B := B)
    (fun x => ((βw x x 0).2 (by simpa using (hw' _ _ _ (halt _ x.toMul.2)).symm)).trans Int.cast_zero)
    (fun x hx => Subtype.ext (hnd _ x.toMul.2 fun y hy => by
      have h := (βw x (Additive.ofMul ⟨y, hy⟩) 0).1 ((hx _).trans Int.cast_zero.symm)
      rw [zpow_zero] at h
      exact h ▸ hw x.toMul ⟨y, hy⟩))
  refine ⟨fun i => (v i).toMul.1, fun i => (v i).toMul.2, fun i k => (βw _ _ _).1 (hv i k) ▸ hw _ _,
    fun c c' h => funext fun i => ?_⟩
  have h' : ∑ i, ((c i : ℕ) : ZMod (p ^ (j + 1))) • v i = ∑ i, ((c' i : ℕ) : ZMod (p ^ (j + 1))) • v i := by
    simp only [Nat.cast_smul_eq_nsmul]
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa using h
  have := Fintype.linearIndependent_iffₛ.1 hli _ _ h' i
  rw [ZMod.natCast_eq_natCast_iff'] at this
  exact Fin.ext (by rwa [Nat.mod_eq_of_lt (c i).2, Nat.mod_eq_of_lt (c' i).2] at this)
end GlobalTheory.LevelExist
