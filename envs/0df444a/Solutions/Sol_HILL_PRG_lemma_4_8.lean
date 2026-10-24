-- Prove2me | solution 1 for HILL.PRG.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T02:17:48.837988+00:00
-- url     : https://prove2.me/submissions/9d8cb873-c8f8-4297-9341-cd5f6fc23fd0

import Mathlib
import Definitions.Def_HILL_PRG_Constructions

open HILL.PRG
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace WentaoLeftoverHash

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

private lemma hash_length (h : HashFamily) (hh : h.IsUniversal) (n : ℕ)
    (key x : Bits) (hk : key ∈ cube (h.keyLen n)) (hx : x ∈ cube (h.inLen n)) :
    h.eval n key x ∈ cube (h.outLen n) := by
  obtain ⟨_, _, _, _, M, hM, heval⟩ := hh.1
  exact mem_cube.mpr (heval n key x hk hx).2

private lemma finite_hash_bound {α β κ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq κ]
    (X : Finset α) (Y : Finset β) (K : Finset κ) (D : α → ℝ) (h : κ → α → β)
    (hD : ∀ x ∈ X, 0 ≤ D x) (hsum : ∑ x ∈ X, D x = 1)
    (hY : 0 < Y.card) (hK : 0 < K.card)
    (hmap : ∀ k ∈ K, ∀ x ∈ X, h k x ∈ Y)
    (hcoll : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' →
      (∑ k ∈ K, if h k x = h k x' then (1 : ℝ) else 0) ≤
        (K.card : ℝ) / Y.card) :
    let P := fun k a => ∑ x ∈ X, if h k x = a then D x else 0
    (∑ k ∈ K, ∑ a ∈ Y, |P k a - 1 / (Y.card : ℝ)|) ^ 2 ≤
      (Y.card : ℝ) * (K.card : ℝ) ^ 2 * (∑ x ∈ X, (D x) ^ 2) := by
  classical
  intro P
  let M : ℝ := Y.card
  let N : ℝ := K.card
  let C : ℝ := ∑ x ∈ X, (D x) ^ 2
  have hM : 0 < M := by dsimp [M]; exact_mod_cast hY
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hK
  have hp (k : κ) (hk : k ∈ K) : ∑ a ∈ Y, P k a = 1 := by
    dsimp [P]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x ∈ X, D x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hmap k hk x hx, eq_comm]
      _ = 1 := hsum
  have hmoment (k : κ) (hk : k ∈ K) :
      ∑ a ∈ Y, (P k a) ^ 2 =
        ∑ x ∈ X, ∑ x' ∈ X, if h k x = h k x' then D x * D x' else 0 := by
    simp_rw [P, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' hx'
    have hprod (a : β) :
        (if h k x = a then D x else 0) * (if h k x' = a then D x' else 0) =
          if h k x = a then (if h k x' = a then D x * D x' else 0) else 0 := by
      split_ifs <;> simp_all
    simp_rw [hprod]
    simp [hmap k hk x hx, eq_comm]
  have htotal : (∑ k ∈ K, ∑ a ∈ Y, (P k a) ^ 2) ≤ N * C + N / M := by
    calc
      _ = ∑ x ∈ X, ∑ x' ∈ X,
          (D x * D x') * (∑ k ∈ K, if h k x = h k x' then (1 : ℝ) else 0) := by
        simp_rw [Finset.sum_congr rfl (fun k hk => hmoment k hk)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x' hx'
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ ≤ ∑ x ∈ X, ∑ x' ∈ X,
          (N * (if x = x' then (D x) ^ 2 else 0) + (N / M) * (D x * D x')) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro x' hx'
        by_cases hxx : x = x'
        · subst x'
          simp only [ite_true, Finset.sum_const, nsmul_eq_mul, mul_one]
          dsimp only [N]
          nlinarith [mul_nonneg (div_nonneg hN.le hM.le) (sq_nonneg (D x))]
        · rw [if_neg hxx]
          have hh := mul_le_mul_of_nonneg_left (hcoll x hx x' hx' hxx)
            (mul_nonneg (hD x hx) (hD x' hx'))
          simpa only [mul_zero, zero_add, mul_comm] using hh
      _ = N * C + N / M := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hdiag : (∑ x ∈ X, ∑ x' ∈ X, if x = x' then (D x) ^ 2 else 0) = C := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [hx]
        have hall : (∑ x ∈ X, ∑ x' ∈ X, D x * D x') = 1 := by
          rw [← Finset.sum_mul_sum, hsum, one_mul]
        rw [hdiag]; simp only [hsum, mul_one]
  have hvariance (k : κ) (hk : k ∈ K) :
      ∑ a ∈ Y, (P k a - 1 / M) ^ 2 = (∑ a ∈ Y, (P k a) ^ 2) - 1 / M := by
    have heq (a : β) : (P k a - 1 / M) ^ 2 =
        (P k a) ^ 2 - (2 / M) * P k a + (1 / M) ^ 2 := by ring
    simp_rw [heq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hp k hk, Finset.sum_const, nsmul_eq_mul]
    dsimp only [M]
    field_simp
    <;> ring
  have hv : (∑ k ∈ K, ∑ a ∈ Y, (P k a - 1 / M) ^ 2) ≤ N * C := by
    simp_rw [Finset.sum_congr rfl (fun k hk => hvariance k hk)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have heq : N * (1 / M) = N / M := by ring
    rw [heq]
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (K ×ˢ Y)
    (fun z => |P z.1 z.2 - 1 / M|) (fun _ => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, nsmul_eq_mul,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hcs
  calc
    _ ≤ (∑ k ∈ K, ∑ a ∈ Y, (P k a - 1 / M) ^ 2) * (N * M) := hcs
    _ ≤ (N * C) * (N * M) := mul_le_mul_of_nonneg_right hv (by positivity)
    _ = _ := by ring

end WentaoLeftoverHash

open WentaoLeftoverHash in
theorem solution (n m e kl : ℕ) (he : 0 < e) (hme : 2 * e ≤ m)
    (D : Bits → ℝ) (hD : IsProbOn (cube n) D)
    (hH : (m : ℝ) ≤ renyiOn (cube n) D)
    (h : HashFamily) (hh : h.IsUniversal)
    (hin : h.inLen n = n) (hout : h.outLen n = m - 2 * e)
    (hkey : h.keyLen n = kl) :
    statDistOn (cube (m - 2 * e) ×ˢ cube kl)
      (hashJoint D h n) (hashUniform h n) ≤
      (2 : ℝ) ^ (-((e : ℝ) + 1)) := by
  classical
  let X := cube n
  let Y := cube (m - 2 * e)
  let K := cube kl
  let M : ℝ := Y.card
  let N : ℝ := K.card
  let C : ℝ := ∑ x ∈ X, (D x) ^ 2
  let P := fun key a => ∑ x ∈ X, if h.eval n key x = a then D x else 0
  let Z : ℝ := ∑ key ∈ K, ∑ a ∈ Y, |P key a - 1 / M|
  have hMc : Y.card = 2 ^ (m - 2 * e) := cube_card _
  have hNc : K.card = 2 ^ kl := cube_card _
  have hM : 0 < M := by dsimp [M]; rw [hMc]; positivity
  have hN : 0 < N := by dsimp [N]; rw [hNc]; positivity
  have hMpow : M = (2 : ℝ) ^ (m - 2 * e) := by dsimp [M]; rw [hMc]; norm_cast
  have hNpow : N = (2 : ℝ) ^ kl := by dsimp [N]; rw [hNc]; norm_cast
  have hmap (key : Bits) (hk : key ∈ K) (x : Bits) (hx : x ∈ X) : h.eval n key x ∈ Y := by
    change h.eval n key x ∈ cube (m - 2 * e)
    rw [← hout]
    apply hash_length h hh n key x
    · simpa only [hkey] using hk
    · simpa only [hin] using hx
  have hcollision (x : Bits) (hx : x ∈ X) (x' : Bits) (hx' : x' ∈ X) (hne : x ≠ x') :
      (∑ key ∈ K, if h.eval n key x = h.eval n key x' then (1 : ℝ) else 0) ≤ N / M := by
    have hpair (a : Bits) (ha : a ∈ Y) :
        (∑ key ∈ K, if h.eval n key x = a ∧ h.eval n key x' = a then (1 : ℝ) else 0) = N / M ^ 2 := by
      have ht := hh.2 n x x' a a (by simpa only [hin] using hx)
        (by simpa only [hin] using hx') hne
        (by simpa only [hout] using ha) (by simpa only [hout] using ha)
      rw [hout, hkey] at ht
      have htr :
          (((K.filter fun key => h.eval n key x = a ∧ h.eval n key x' = a).card : ℝ)) * M ^ 2 = N := by
        rw [hMpow, hNpow, ← pow_mul]
        have hr := congrArg (fun z : ℕ => (z : ℝ)) ht
        push_cast at hr
        simpa only [Nat.mul_comm] using hr
      have hc : (∑ key ∈ K, if h.eval n key x = a ∧ h.eval n key x' = a then (1 : ℝ) else 0) =
          ((K.filter fun key => h.eval n key x = a ∧ h.eval n key x' = a).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl
      rw [hc]
      exact (eq_div_iff (by positivity : M ^ 2 ≠ 0)).mpr htr
    have hsplit : (∑ key ∈ K, if h.eval n key x = h.eval n key x' then (1 : ℝ) else 0) =
        ∑ a ∈ Y, ∑ key ∈ K,
          if h.eval n key x = a ∧ h.eval n key x' = a then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro key hk
      have hprod (a : Bits) :
          (if h.eval n key x = a ∧ h.eval n key x' = a then (1 : ℝ) else 0) =
            if h.eval n key x = a then (if h.eval n key x' = a then (1 : ℝ) else 0) else 0 := by
        split_ifs <;> simp_all
      simp_rw [hprod]
      simp [hmap key hk x hx, eq_comm]
    rw [hsplit]
    simp_rw [Finset.sum_congr rfl hpair]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change M * (N / M ^ 2) ≤ N / M
    field_simp
    <;> norm_num
  have hbound := finite_hash_bound X Y K D (fun key x => h.eval n key x)
    hD.1 hD.2 (by dsimp [M] at hM; exact_mod_cast hM) (by dsimp [N] at hN; exact_mod_cast hN) hmap hcollision
  change Z ^ 2 ≤ M * N ^ 2 * C at hbound
  have hC : 0 < C := by
    obtain ⟨x, hx, hDx⟩ : ∃ x ∈ X, 0 < D x := by
      apply (Finset.sum_pos_iff_of_nonneg hD.1).mp
      rw [hD.2]
      norm_num
    apply Finset.sum_pos'
    · intro y hy; positivity
    · exact ⟨x, hx, sq_pos_of_pos hDx⟩
  have hCsmall : C ≤ (2 : ℝ) ^ (-(m : ℝ)) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hC).mp
    change (m : ℝ) ≤ -Real.logb 2 C at hH
    linarith
  let u : ℝ := 1 / (2 : ℝ) ^ e
  have hu : 0 < u := by dsimp [u]; positivity
  have hmneg : (2 : ℝ) ^ (-(m : ℝ)) = 1 / (2 : ℝ) ^ m := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
  have hpow : (2 : ℝ) ^ m = M * ((2 : ℝ) ^ e) ^ 2 := by
    rw [hMpow, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hMC : M * C ≤ u ^ 2 := by
    calc
      _ ≤ M * (2 : ℝ) ^ (-(m : ℝ)) := mul_le_mul_of_nonneg_left hCsmall hM.le
      _ = u ^ 2 := by rw [hmneg, hpow]; dsimp [u]; field_simp <;> ring
  have hZsquare : Z ^ 2 ≤ (N * u) ^ 2 := by
    calc
      _ ≤ M * N ^ 2 * C := hbound
      _ = N ^ 2 * (M * C) := by ring
      _ ≤ N ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_left hMC (sq_nonneg N)
      _ = _ := by ring
  have hZ : Z ≤ N * u :=
    (sq_le_sq₀ (by dsimp [Z]; positivity) (mul_pos hN hu).le).mp hZsquare
  have hjoint (a key : Bits) (hk : key ∈ K) : hashJoint D h n (a, key) = P key a / N := by
    unfold hashJoint weightedLaw
    rw [hkey, Finset.sum_product]
    have ht (x key' : Bits) :
        (if (h.eval n key' x, key') = (a, key) then D x / ((cube kl).card : ℝ) else 0) =
          if key' = key then
            (if h.eval n key x = a then D x / ((cube kl).card : ℝ) else 0) else 0 := by
      by_cases hk' : key' = key
      · subst key'; simp
      · simp [hk']
    simp_rw [ht]
    simp only [show key ∈ cube kl from hk, Finset.sum_ite_eq', if_true]
    rw [Finset.sum_div]
    congr 1
    funext x
    split_ifs
    · rfl
    · rw [zero_div]
  have huniform (a key : Bits) (ha : a ∈ Y) (hk : key ∈ K) :
      hashUniform h n (a, key) = 1 / (M * N) := by
    rw [hashUniform, hout, hkey, uniform_on_cube _ _ ha, uniform_on_cube _ _ hk]
    dsimp only [M, N, Y, K]
    ring
  have hsd : statDistOn (Y ×ˢ K) (hashJoint D h n) (hashUniform h n) = Z / (2 * N) := by
    unfold statDistOn
    rw [Finset.sum_product, Finset.sum_comm]
    have hs : (∑ key ∈ K, ∑ a ∈ Y, |hashJoint D h n (a, key) - hashUniform h n (a, key)|) = Z / N := by
      dsimp only [Z]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro key hk
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hjoint a key hk, huniform a key ha hk]
      have heq : P key a / N - 1 / (M * N) = (P key a - 1 / M) / N := by ring
      rw [heq, abs_div, abs_of_pos hN]
    rw [hs]
    ring
  calc
    _ = Z / (2 * N) := hsd
    _ ≤ (N * u) / (2 * N) := div_le_div_of_nonneg_right hZ (by positivity)
    _ = u / 2 := by field_simp <;> ring
    _ = (2 : ℝ) ^ (-((e : ℝ) + 1)) := by
      dsimp [u]
      rw [Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num),
        Real.rpow_natCast, Real.rpow_one, one_div]
      ring
