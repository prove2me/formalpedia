-- Prove2me | solution 1 for GlobalTheory.exists_alternating_bilinForm_eq_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:37.379423+00:00
-- url     : https://prove2.me/submissions/dab53e98-8fbb-4f28-bdba-cda4039c0182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegrality
import Theorems.Thm_GlobalTheory_alternating_pairing_expand
import Theorems.Thm_GlobalTheory_exists_int_of_isInteger_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by
  intro F V _ _ _ _ hfin L hadd hsm P halt hPadd hPsmul x x' hx hx' hne
  have hP0 : ∀ y ∈ L, P 0 y = 0 := by
    intro y hy
    simpa using hPsmul 0 x hx y hy
  have hP0' : ∀ y ∈ L, P y 0 = 0 := by
    intro y hy
    have h0 : (0 : V) ∈ L := by simpa using hsm 0 x hx
    rw [halt y hy 0 h0, hP0 y hy, neg_zero]
  have hdne : ∀ d : (𝓞 F)⁰, ((d : 𝓞 F) : F) ≠ 0 := by
    intro d
    exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰ ![s, t]
    obtain ⟨n₀, hn₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) s (hd 0)
    obtain ⟨n₁, hn₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) t (hd 1)
    have hrel : (n₀ : F) • x + (n₁ : F) • x' = 0 := by
      rw [hn₀, hn₁, ← smul_smul, ← smul_smul, ← smul_add, hst, smul_zero]
    have e₀ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' n₀ n₁ 0 1
    have e₁ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' 1 0 n₀ n₁
    rw [hrel, hP0 _ (hadd _ (hsm 0 x hx) _ (hsm 1 x' hx'))] at e₀
    rw [hrel, hP0' _ (hadd _ (hsm 1 x hx) _ (hsm 0 x' hx'))] at e₁
    push_cast at e₀ e₁
    simp only [mul_one, mul_zero, sub_zero, one_mul, zero_mul] at e₀ e₁
    have h0 : (n₀ : F) = 0 := by
      rcases mul_eq_zero.mp e₀.symm with h | h
      · exact h
      · exact absurd h hne
    have h1 : (n₁ : F) = 0 := by
      rcases mul_eq_zero.mp e₁.symm with h | h
      · exact h
      · exact absurd h hne
    rw [hn₀] at h0
    rw [hn₁] at h1
    exact ⟨(mul_eq_zero.mp h0).resolve_left (hdne d), (mul_eq_zero.mp h1).resolve_left (hdne d)⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F V := by simp [hfin]
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2) F V, ⇑b = ![x, x'] :=
    ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩
  have hb0 : b 0 = x := by rw [hb]; rfl
  have hb1 : b 1 = x' := by rw [hb]; rfl
  let B : LinearMap.BilinForm F V := LinearMap.mk₂ F
    (fun z w => P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0))
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
  have hB : ∀ z w, B z w = P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0) :=
    fun _ _ => rfl
  have hBxx' : B x x' = P x x' := by
    rw [hB, ← hb0, ← hb1, b.repr_self, b.repr_self]
    simp
  refine ⟨B, fun z => by rw [hB]; ring, ?_⟩
  intro z hz w hw
  have hsum : ∀ v : V, v = b.repr v 0 • x + b.repr v 1 • x' := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two, hb0, hb1]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰
    ![b.repr z 0, b.repr z 1, b.repr w 0, b.repr w 1]
  obtain ⟨r₀, hr₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 0) (hd 0)
  obtain ⟨r₁, hr₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 1) (hd 1)
  obtain ⟨s₀, hs₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 0) (hd 2)
  obtain ⟨s₁, hs₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 1) (hd 3)
  set e : 𝓞 F := (d : 𝓞 F) with he
  have hez : (e : F) • z = (r₀ : F) • x + (r₁ : F) • x' := by
    calc (e : F) • z = (e : F) • (b.repr z 0 • x + b.repr z 1 • x') := congrArg _ (hsum z)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hr₀, hr₁]
  have hew : (e : F) • w = (s₀ : F) • x + (s₁ : F) • x' := by
    calc (e : F) • w = (e : F) • (b.repr w 0 • x + b.repr w 1 • x') := congrArg _ (hsum w)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hs₀, hs₁]
  have hPe : P ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * P z w) := by
    have a1 := hPsmul e z hz _ (hsm e w hw)
    have a2 := halt z hz _ (hsm e w hw)
    have a3 := hPsmul e w hw z hz
    have a4 := halt w hw z hz
    linear_combination a1 + (e : F) * a2 - (e : F) * a3 - (e : F) * (e : F) * a4
  have hBe : B ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * B z w) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have eP := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' r₀ r₁ s₀ s₁
  have eB := alternating_pairing_expand L hadd hsm (fun u v => B u v)
    (fun u _ v _ => by simp only [hB]; ring) (fun u₁ _ u₂ _ v _ => by rw [map_add, LinearMap.add_apply])
    (fun a u _ v _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]) hx hx' r₀ r₁ s₀ s₁
  rw [← hez, ← hew, hPe] at eP
  rw [← hez, ← hew, hBe, hBxx'] at eB
  have hee : (e : F) * (e : F) ≠ 0 := mul_ne_zero (hdne d) (hdne d)
  apply mul_left_cancel₀ hee
  linear_combination eP - eB
end GlobalTheory
