-- Prove2me | solution 1 for HILL.PRG.inverter_check_advantage_bound
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T04:54:40.291125+00:00
-- url     : https://prove2.me/submissions/d1a4fb85-b5d8-4e22-840a-92c9c89fd793

import Definitions.Def_HILL_PRG_Model

open HILL.PRG
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace WentaoHILLInversion

private lemma cube_card (n : ℕ) : (cube n).card = 2 ^ n := by
  change (Finset.univ.image (fun v : Fin n → Bool => List.ofFn v)).card = _
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp

private lemma mem_cube {n : ℕ} {x : Bits} : x ∈ cube n ↔ x.length = n := by
  constructor
  · intro hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    simp
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨fun i : Fin n => x[i.val]'(by omega), Finset.mem_univ _, ?_⟩
    apply List.ext_getElem
    · simpa using hx.symm
    · intro i hi hj
      simp

private lemma uniform_on_cube (n : ℕ) (x : Bits) (hx : x ∈ cube n) :
    uniformBits n x = 1 / ((cube n).card : ℝ) := by
  have hf : (cube n).filter (fun z => id z = x) = {x} := by
    ext y
    simp only [Finset.mem_filter, id_eq, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h; subst y; exact ⟨hx, rfl⟩
  simp only [uniformBits, lawOn, hf, Finset.card_singleton, Nat.cast_one]

private lemma finite_check_bound {α β : Type} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (f : α → β) (q : β → ℝ)
    (hX : 0 < X.card) (hsize : 2 * X.card ≤ Y.card)
    (hmap : ∀ x ∈ X, f x ∈ Y)
    (hq : ∀ y ∈ Y, 0 ≤ q y)
    (hzero : ∀ y ∈ Y, (∀ x ∈ X, f x ≠ y) → q y = 0) :
    (∑ x ∈ X, q (f x)) / (X.card : ℝ) ≤
      2 * |∑ y ∈ Y, (lawOn X f y - 1 / (Y.card : ℝ)) * q y| := by
  classical
  have hXr : (0 : ℝ) < X.card := by exact_mod_cast hX
  have hYr : (0 : ℝ) < Y.card := by exact_mod_cast (show 0 < Y.card by omega)
  have hsizeR : (2 : ℝ) * X.card ≤ Y.card := by exact_mod_cast hsize
  have hfiber : (∑ y ∈ Y, lawOn X f y * q y) =
      (∑ x ∈ X, q (f x)) / (X.card : ℝ) := by
    unfold lawOn
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    calc
      _ = ∑ y ∈ Y, ∑ x ∈ X, if f x = y then q y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul]
      _ = ∑ x ∈ X, q (f x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        simp [hmap x hx, eq_comm]
  have hpoint : ∀ y ∈ Y, lawOn X f y * q y ≤
      2 * ((lawOn X f y - 1 / (Y.card : ℝ)) * q y) := by
    intro y hy
    by_cases him : ∃ x ∈ X, f x = y
    · obtain ⟨x, hx, hxy⟩ := him
      have hc : 1 ≤ (X.filter (fun x => f x = y)).card :=
        Finset.one_le_card.mpr ⟨x, by simp [hx, hxy]⟩
      have hcR : (1 : ℝ) ≤ (X.filter (fun x => f x = y)).card := by exact_mod_cast hc
      have hD : 2 / (Y.card : ℝ) ≤ lawOn X f y := by
        unfold lawOn
        apply (div_le_div_iff₀ hYr hXr).mpr
        have : (Y.card : ℝ) ≤ (X.filter (fun x => f x = y)).card * Y.card :=
          le_mul_of_one_le_left hYr.le hcR
        nlinarith
      simp only [div_eq_mul_inv, one_mul] at hD ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr hD) (hq y hy)]
    · have hz : q y = 0 := hzero y hy (by simpa using him)
      simp [hz]
  calc
    _ = ∑ y ∈ Y, lawOn X f y * q y := hfiber.symm
    _ ≤ ∑ y ∈ Y, 2 * ((lawOn X f y - 1 / (Y.card : ℝ)) * q y) :=
      Finset.sum_le_sum hpoint
    _ = 2 * (∑ y ∈ Y, (lawOn X f y - 1 / (Y.card : ℝ)) * q y) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)

private lemma uniformProb_sum {α : Type} [DecidableEq α] (X : Finset α)
    (P : α → Prop) [DecidablePred P] :
    uniformProb X P = (∑ x ∈ X, if P x then (1 : ℝ) else 0) / (X.card : ℝ) := by
  simp [uniformProb]

private lemma uniformProb_product {α β : Type} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (R : Finset β) (P : α × β → Prop) [DecidablePred P] :
    uniformProb (X ×ˢ R) P =
      (∑ x ∈ X, uniformProb R (fun r => P (x, r))) / (X.card : ℝ) := by
  classical
  simp_rw [uniformProb_sum]
  rw [Finset.sum_product, Finset.card_product, Nat.cast_mul, ← Finset.sum_div]
  ring

end WentaoHILLInversion

open WentaoHILLInversion

theorem solution (G : FunEns) (A B : Adv)
    (hlen : ∀ n x, x ∈ cube (G.t n) → (G.f 0 n x).length = G.ℓ n)
    (hcoins : B.coins = A.coins)
    (hcheck : ∀ n y r, y ∈ cube (G.ℓ n) → r ∈ cube (A.coins n) →
      (B.run (encAdvice n 0 (y ++ r)) = [true] ↔
        let out := A.run (enc n (y ++ r));
        out ∈ cube (G.t n) ∧ G.f 0 n out = y))
    (n : ℕ) (hstr : G.t n < G.ℓ n) :
    invSucc G A n ≤ 2 * advantage B n (fun _ => 0) (G.ℓ n)
      (G.law (fun _ => 0) n) (uniformBits (G.ℓ n)) := by
  classical
  let q : Bits → ℝ := acceptProb B n (fun _ => 0)
  have hmap : ∀ x ∈ cube (G.t n), G.f 0 n x ∈ cube (G.ℓ n) := by
    intro x hx
    exact mem_cube.mpr (hlen n x hx)
  have hq : ∀ y ∈ cube (G.ℓ n), 0 ≤ q y := by
    intro y hy
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hzero : ∀ y ∈ cube (G.ℓ n),
      (∀ x ∈ cube (G.t n), G.f 0 n x ≠ y) → q y = 0 := by
    intro y hy hout
    have hf : (cube (B.coins n)).filter
        (fun r => B.run (encAdvice n 0 (y ++ r)) = [true]) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r hr hacc
      have hrA : r ∈ cube (A.coins n) := by simpa [hcoins] using hr
      obtain ⟨hx, heq⟩ := (hcheck n y r hy hrA).mp hacc
      exact hout _ hx heq
    change ((Finset.filter _ _).card : ℝ) / _ = 0
    rw [hf]
    simp
  have hsuccess : invSucc G A n =
      (∑ x ∈ cube (G.t n), q (G.f 0 n x)) / ((cube (G.t n)).card : ℝ) := by
    unfold invSucc
    rw [uniformProb_product]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hevents : (cube (A.coins n)).filter
        (fun r => let out := A.run (enc n (G.f 0 n x ++ r));
          out ∈ cube (G.t n) ∧ G.f 0 n out = G.f 0 n x) =
        (cube (A.coins n)).filter
          (fun r => B.run (encAdvice n 0 (G.f 0 n x ++ r)) = [true]) := by
      apply Finset.filter_congr
      intro r hr
      exact (hcheck n (G.f 0 n x) r (hmap x hx) hr).symm
    change ((Finset.filter _ _).card : ℝ) / _ =
      ((Finset.filter _ _).card : ℝ) / _
    rw [hcoins, hevents]
  rw [hsuccess]
  have hsize : 2 * (cube (G.t n)).card ≤ (cube (G.ℓ n)).card := by
    simp only [cube_card]
    calc
      2 * 2 ^ G.t n = 2 ^ (G.t n + 1) := by ring
      _ ≤ 2 ^ G.ℓ n := Nat.pow_le_pow_right (by omega) hstr
  have hh := finite_check_bound (cube (G.t n)) (cube (G.ℓ n)) (G.f 0 n) q
    (by simp [cube_card]) hsize hmap hq hzero
  have hadv : advantage B n (fun _ => 0) (G.ℓ n)
      (G.law (fun _ => 0) n) (uniformBits (G.ℓ n)) =
      |∑ y ∈ cube (G.ℓ n), (lawOn (cube (G.t n)) (G.f 0 n) y -
        1 / ((cube (G.ℓ n)).card : ℝ)) * q y| := by
    unfold advantage FunEns.law
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [uniform_on_cube _ y hy]
  rw [hadv]
  exact hh
