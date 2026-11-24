-- Prove2me | solution 1 for GlobalTheory.symm_pairing_eq_one_of_odd_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:55.423689+00:00
-- url     : https://prove2.me/submissions/20acad61-14e5-4fd8-8820-f3f62b514ff6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
open Matrix
namespace GlobalTheory
private lemma eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one {U : Type} [CommGroup U] (k : ℕ) (b : ℤ) (hb : (k : ℤ) ∣ 2 * b - 1)
    (u : U) (hu : u ^ k = 1) (h : u ^ b * u ^ b = 1) : u = 1 := by
  obtain ⟨m, hm⟩ := hb
  have h2 : u ^ (2 * b) = 1 := by rw [two_mul, _root_.zpow_add]; exact h
  have hk : u ^ (k : ℤ) = 1 := by rw [zpow_natCast]; exact hu
  have hsplit : 2 * b = k * m + 1 := by linarith
  rw [hsplit, _root_.zpow_add, _root_.zpow_mul, hk, _root_.one_zpow, one_mul, _root_.zpow_one] at h2
  exact h2
private lemma eq_one_of_hom_eq_one_on_basis {X U : Type} [AddCommGroup X] [CommGroup U] {d : ℕ}
    (e : Module.Basis (Fin d) ℤ X) (f : X → U) (hf : ∀ x x', f (x + x') = f x * f x')
    (he : ∀ i, f (e i) = 1) (x : X) : f x = 1 := by
  have h0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    simpa using h
  let g : X →+ Additive U :=
    { toFun := fun x => Additive.ofMul (f x)
      map_zero' := by simp [h0]
      map_add' := fun x x' => by simp [hf] }
  have hg : g.toIntLinearMap = 0 := e.ext fun i => by simp [g, he]
  have hx := LinearMap.congr_fun hg x
  simpa [g] using hx
end GlobalTheory
end

set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X U : Type) [AddCommGroup X] [CommGroup U] (d k : ℕ) (e : Module.Basis (Fin d) ℤ X) (b : ℤ), Odd k → (k : ℤ) ∣ 2 * b - 1 → ∀ δ : X → X → U, (∀ x x' y, δ (x + x') y = δ x y * δ x' y) → (∀ x y, δ x y = δ y x) → (∀ x y, δ x y ^ k = 1) → (∀ i, δ (e i) (e i) ^ b = 1) → (∀ i j, δ (e i + e j) (e i + e j) ^ b = 1) → ∀ x y, δ x y = 1 := by
  intro X U _ _ d k e b _ hb δ hadd hsymm hk1 hdiag hdiag2
  have hadd2 : ∀ x y y', δ x (y + y') = δ x y * δ x y' := by
    intro x y y'
    rw [hsymm x, hadd, hsymm y, hsymm y']
  have hoff : ∀ i j, δ (e i) (e j) = 1 := by
    intro i j
    have h := hdiag2 i j
    rw [hadd, hadd2, hadd2, hsymm (e j) (e i), _root_.mul_zpow, _root_.mul_zpow, _root_.mul_zpow, hdiag i, hdiag j] at h
    apply eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one k b hb _ (hk1 _ _)
    simpa using h
  have hrow : ∀ i y, δ (e i) y = 1 := fun i =>
    eq_one_of_hom_eq_one_on_basis e (δ (e i)) (hadd2 (e i)) (hoff i)
  intro x y
  exact eq_one_of_hom_eq_one_on_basis e (fun x => δ x y) (fun x x' => hadd x x' y) (fun i => hrow i y) x
end GlobalTheory
