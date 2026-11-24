-- Prove2me | solution 1 for GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:04:32.31007+00:00
-- url     : https://prove2.me/submissions/8cb353c0-b550-4c2e-be47-b41199a635c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvenCubicUnitMultipleFractionRing
import Theorems.Thm_GlobalTheory_EvenCubicNorm_eq_zero_of_even_cubic
import Theorems.Thm_GlobalTheory_EvenCubicNorm_prodPow_add
import Theorems.Thm_GlobalTheory_EvenCubicNorm_prodPow_single
import Theorems.Thm_GlobalTheory_EvenCubicNorm_indicator_sum_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.EvenCubicNorm
open Finset
namespace GlobalTheory.EvenCubicNorm
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ)
    (hev : ∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (hcub : ∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) :
    ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧
      (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧
      ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  classical
  set K := FractionRing R
  let φ : Rˣ →* Kˣ := Units.map (algebraMap R K).toMonoidHom
  have hφ : ∀ u : Rˣ, ((φ u : Kˣ) : K) = algebraMap R K (u : R) := fun u => rfl
  let H : Subgroup Kˣ := φ.range
  let ψ : Kˣ → Additive (Kˣ ⧸ H) := fun x => Additive.ofMul (QuotientGroup.mk x)
  have ψmul : ∀ x y, ψ (x * y) = ψ x + ψ y := fun x y => rfl
  have ψφ : ∀ x u, ψ (x * φ u) = ψ x := by
    intro x u
    rw [ψmul]
    have : ψ (φ u) = 0 := by
      show Additive.ofMul (QuotientGroup.mk (φ u) : Kˣ ⧸ H) = 0
      rw [(QuotientGroup.eq_one_iff (φ u)).mpr (MonoidHom.mem_range.mpr ⟨u, rfl⟩)]; rfl
    rw [this, add_zero]
  have ψeq : ∀ x y, ψ x = ψ y → ∃ u : Rˣ, y = x * φ u := by
    intro x y h
    have h' : (QuotientGroup.mk x : Kˣ ⧸ H) = QuotientGroup.mk y := h
    obtain ⟨u, hu⟩ := QuotientGroup.eq.mp h'
    exact ⟨u, by rw [hu]; group⟩
  let b := (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let n : Fin r → X → ℤ := fun i a => b.repr a i
  let z : Fin r → Fin r → Kˣ := fun i j =>
    if i = j then κ₀ (b i) else if i < j then κ₀ (b i + b j) * (κ₀ (b i))⁻¹ * (κ₀ (b j))⁻¹ else 1
  let E : X → Fin r → Fin r → ℤ := fun a i j => n i a * n j a
  let κ : X → Kˣ := fun a => prodPow z (E a)
  have hκ : ∀ a, κ a = prodPow z (E a) := fun _ => rfl
  have κev : ∀ a, κ (-a) = κ a := by
    intro a; simp only [hκ]; congr 1; funext i j; simp [E, n]
  have κcub : ∀ a a' c, κ (a + a' + c) * κ a * κ a' * κ c = κ (a + a') * κ (a + c) * κ (a' + c) := by
    intro a a' c
    simp only [hκ, prodPow_add]
    congr 1; funext i j; simp only [E, n, map_add, Finsupp.add_apply]; ring
  have nb : ∀ i k, n i (b k) = if i = k then 1 else 0 := by
    intro i k; simp [n, Finsupp.single_apply, eq_comm]
  have κb : ∀ k, κ (b k) = κ₀ (b k) := by
    intro k
    have : E (b k) = fun i j => if i = k ∧ j = k then 1 else 0 := by
      funext i j; simp only [E, nb]; split_ifs <;> simp_all
    rw [hκ, this, prodPow_single]; simp [z]
  have κbb : ∀ k l, k < l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    have hne : k ≠ l := ne_of_lt hkl
    have hsplit : prodPow z (E (b k + b l)) =
        prodPow z (fun i j => if i = k ∧ j = k then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = l then 1 else 0) *
        prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = k then 1 else 0) := by
      simp only [prodPow_add]
      congr 1; funext i j; simp only [E, n, map_add, Finsupp.add_apply]
      have h1 := nb i k; have h2 := nb i l; have h3 := nb j k; have h4 := nb j l
      simp only [n] at h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      exact indicator_sum_mul i j k l hne
    rw [hκ, hsplit, prodPow_single, prodPow_single, prodPow_single, prodPow_single]
    have hzk : z k k = κ₀ (b k) := by simp only [z]; exact if_pos trivial
    have hzl : z l l = κ₀ (b l) := by simp only [z]; exact if_pos trivial
    have hzkl : z k l = κ₀ (b k + b l) * (κ₀ (b k))⁻¹ * (κ₀ (b l))⁻¹ := by
      simp only [z]; rw [if_neg hne, if_pos hkl]
    have hzlk : z l k = 1 := by simp only [z]; rw [if_neg hne.symm, if_neg (not_lt_of_gt hkl)]
    rw [hzk, hzl, hzkl, hzlk, mul_one, mul_comm (κ₀ (b k) * κ₀ (b l)), mul_assoc, mul_assoc,
      ← mul_assoc (κ₀ (b k))⁻¹, ← mul_inv, inv_mul_cancel, mul_one]
  have κbb' : ∀ k l, k ≠ l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact κbb k l h
    · rw [add_comm]; exact κbb l k h

  have κ₀ev : ∀ a, ψ (κ₀ (-a)) = ψ (κ₀ a) := by
    intro a
    obtain ⟨u, hu⟩ := hev a
    have : κ₀ (-a) = κ₀ a * φ u := Units.ext (by rw [Units.val_mul, hφ]; exact hu)
    rw [this, ψφ]
  have κ₀cub : ∀ a a' c, ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) =
      ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)) := by
    intro a a' c
    obtain ⟨u, hu⟩ := hcub a a' c
    have : κ₀ (a + a' + c) * κ₀ a * κ₀ a' * κ₀ c = κ₀ (a + a') * κ₀ (a + c) * κ₀ (a' + c) * φ u :=
      Units.ext (by rw [Units.val_mul _ (φ u), hφ]; exact hu)
    have h := congrArg ψ this
    rw [ψφ] at h
    simpa only [ψmul] using h
  let f : X → Additive (Kˣ ⧸ H) := fun a => ψ (κ (a)) - ψ (κ₀ a)
  have hf : ∀ a, f a = 0 := by
    refine EvenCubicNorm.eq_zero_of_even_cubic b f ?_ ?_ ?_ ?_
    · intro a; simp only [f]; rw [κev, κ₀ev]
    · intro a a' c
      have h1 := κ₀cub a a' c
      have h2 := congrArg ψ (κcub a a' c)
      simp only [ψmul] at h2
      simp only [f]
      have e : ψ (κ (a + a' + c)) - ψ (κ₀ (a + a' + c)) + (ψ (κ a) - ψ (κ₀ a)) + (ψ (κ a') - ψ (κ₀ a')) +
            (ψ (κ c) - ψ (κ₀ c)) - (ψ (κ (a + a')) - ψ (κ₀ (a + a')) + (ψ (κ (a + c)) - ψ (κ₀ (a + c))) +
            (ψ (κ (a' + c)) - ψ (κ₀ (a' + c)))) =
          (ψ (κ (a + a' + c)) + ψ (κ a) + ψ (κ a') + ψ (κ c) - (ψ (κ (a + a')) + ψ (κ (a + c)) + ψ (κ (a' + c)))) -
          (ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) -
            (ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)))) := by abel
      rw [← sub_eq_zero, e, h1, h2, sub_self, sub_self, sub_self]
    · intro i; simp only [f]; rw [κb, sub_self]
    · intro i j hij; simp only [f]; rw [κbb' i j hij, sub_self]
  refine ⟨κ, κev, κcub, fun a => ?_⟩
  have h := hf a
  simp only [f, sub_eq_zero] at h
  obtain ⟨u, hu⟩ := ψeq _ _ h.symm
  exact ⟨u, by rw [hu, Units.val_mul, hφ]⟩
end GlobalTheory.EvenCubicNorm
