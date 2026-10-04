-- Prove2me | solution 1 for NaculichRegge.regge_Bll_all_loops
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T17:06:36.349805+00:00
-- url     : https://prove2.me/submissions/b35fb3dd-7d14-4e35-83f0-e89ce59145f4

import Mathlib
import Definitions.Def_NaculichRegge_TraceBasis

set_option autoImplicit false

namespace NaculichReggeBllAux

open Polynomial NaculichRegge

lemma P_Tt2 : crossing * Tt2 * crossing = Tt2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tt2, crossing, Matrix.mul_apply, Fin.sum_univ_succ]

lemma P_Tsu2 : crossing * Tsu2 * crossing = -Tsu2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tsu2, crossing, Matrix.mul_apply, Fin.sum_univ_succ]

lemma P_C00 : crossing.mulVec C00 = -C00 := by
  ext i
  fin_cases i <;> simp [crossing, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma PP : crossing * crossing = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossing, Matrix.mul_apply, Fin.sum_univ_succ]

def IsOddOp (M : ColorOp) : Prop := crossing * M * crossing = -M
def IsEvenOp (M : ColorOp) : Prop := crossing * M * crossing = M

lemma conj_mul (A B : ColorOp) :
    crossing * (A * B) * crossing = (crossing * A * crossing) * (crossing * B * crossing) := by
  calc crossing * (A * B) * crossing
      = crossing * A * (crossing * crossing) * B * crossing := by
        rw [PP]; simp only [mul_one, mul_assoc]
    _ = _ := by simp only [mul_assoc]

lemma conj_comm (A B : ColorOp) :
    crossing * NaculichRegge.comm A B * crossing = NaculichRegge.comm (crossing * A * crossing) (crossing * B * crossing) := by
  unfold NaculichRegge.comm
  rw [mul_sub, sub_mul, conj_mul, conj_mul]

lemma comm_even_odd {A B : ColorOp} (hA : IsEvenOp A) (hB : IsOddOp B) : IsOddOp (NaculichRegge.comm A B) := by
  unfold IsOddOp IsEvenOp at *
  rw [conj_comm, hA, hB]
  simp only [NaculichRegge.comm, mul_neg, neg_mul]
  abel

lemma comm_odd_odd {A B : ColorOp} (hA : IsOddOp A) (hB : IsOddOp B) : IsEvenOp (NaculichRegge.comm A B) := by
  unfold IsOddOp IsEvenOp at *
  rw [conj_comm, hA, hB]
  simp only [NaculichRegge.comm, mul_neg, neg_mul, neg_neg]

lemma comm_odd_even {A B : ColorOp} (hA : IsOddOp A) (hB : IsEvenOp B) : IsOddOp (NaculichRegge.comm A B) := by
  unfold IsOddOp IsEvenOp at *
  rw [conj_comm, hA, hB]
  simp only [NaculichRegge.comm, mul_neg, neg_mul]
  abel

lemma iter_T (n : ℕ) : IsOddOp ((NaculichRegge.comm Tt2)^[n] Tsu2) := by
  induction n with
  | zero => simpa [IsOddOp] using P_Tsu2
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact comm_even_odd P_Tt2 ih

lemma iter_S (n : ℕ) : ∀ Y : ColorOp, IsOddOp Y → IsOddOp ((NaculichRegge.comm Tsu2)^[2 * n] Y) := by
  induction n with
  | zero => intro Y hY; simpa using hY
  | succ n ih =>
    intro Y hY
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, Function.iterate_add_apply]
    apply ih
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    exact comm_odd_even P_Tsu2 (comm_odd_odd P_Tsu2 hY)

lemma odd_vec {M : ColorOp} (hM : IsOddOp M) : (M.mulVec C00) 0 = (M.mulVec C00) 2 := by
  have h1 : crossing.mulVec (M.mulVec C00) = M.mulVec C00 := by
    calc crossing.mulVec (M.mulVec C00)
        = (crossing * M * crossing).mulVec (crossing.mulVec C00) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (crossing * M), PP, mul_one]
      _ = M.mulVec C00 := by
          rw [hM, P_C00, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
  have h2 : ∀ w : ColorVec, (crossing.mulVec w) 0 = w 2 := by
    intro w; simp [crossing, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  conv_lhs => rw [← h1]
  rw [h2]

lemma odd_off (m k : ℕ) (h : IsReggeIndex (2 * m) k) (hk : k ≠ 2 * m) :
    IsOddOp (reggeOp (2 * m) k) := by
  unfold IsReggeIndex at h
  have hm : 2 * m ≠ 0 := by omega
  unfold reggeOp
  rw [if_neg hm, if_neg hk]
  by_cases k1 : k = 1
  · rw [if_pos k1]; exact iter_T _
  · rw [if_neg k1]
    have hk2 : k = 2 * m - 1 := by omega
    rw [if_pos hk2, show 2 * m - 2 = 2 * (m - 1) by omega]
    exact iter_S _ _ (comm_even_odd P_Tt2 P_Tsu2)

noncomputable def c0 : Fin 6 → ℂ := ![1, 0, -1, 0, 0, 0]

lemma hc0 : (⇑(evalRingHom (0 : ℂ))) ∘ C00 = c0 := by
  funext i; fin_cases i <;> simp [C00, c0]

lemma S2c : ((Tsu2.map (evalRingHom (0 : ℂ))) * (Tsu2.map (evalRingHom (0 : ℂ)))).mulVec c0
    = (3 : ℂ) • c0 := by
  ext i
  fin_cases i <;> simp [Tsu2, c0, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    norm_num

lemma Spow (m : ℕ) : ((Tsu2.map (evalRingHom (0 : ℂ))) ^ (2 * m)).mulVec c0 = (3 : ℂ) ^ m • c0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, pow_two, ← Matrix.mulVec_mulVec, S2c,
      Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

lemma key_ll (m : ℕ) :
    ((reggeColor (2 * m) (2 * m)) 0).coeff 0 - ((reggeColor (2 * m) (2 * m)) 2).coeff 0
      = 2 * 3 ^ m := by
  have hop : reggeOp (2 * m) (2 * m) = Tsu2 ^ (2 * m) := by
    unfold reggeOp
    by_cases h : 2 * m = 0
    · rw [if_pos h, h, pow_zero]
    · rw [if_neg h, if_pos rfl]
  have hmap : ∀ j, ((reggeColor (2 * m) (2 * m)) j).coeff 0
      = (((Tsu2.map (evalRingHom (0 : ℂ))) ^ (2 * m)).mulVec c0) j := by
    intro j
    rw [coeff_zero_eq_eval_zero, reggeColor, hop, ← coe_evalRingHom, RingHom.map_mulVec,
      ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, hc0]
  rw [hmap, hmap, Spow]
  simp [c0]
  ring

lemma amp_coeff0 (ℓ : ℕ) (B : ℕ × ℕ → ℂ) (j : Fin 6) :
    (reggeAmplitude ℓ B j).coeff 0
      = ∑ p ∈ reggeIndex ℓ, if p.1 = ℓ then B p * (reggeColor p.1 p.2 j).coeff 0 else 0 := by
  unfold reggeAmplitude
  rw [Finset.sum_apply, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro p hp
  have hle : p.1 ≤ ℓ := by
    simp only [reggeIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    omega
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with h1 h2 h2
  · simp
  · omega
  · omega
  · simp

end NaculichReggeBllAux

open Polynomial NaculichReggeBllAux in
open NaculichRegge in
theorem solution (ℓ : ℕ) (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    (Even ℓ → κ * B (ℓ, ℓ) =
        (colorOrderedAmp ℓ κ B (3 * ℓ + 1) - colorOrderedAmp ℓ κ B (3 * ℓ + 3)) /
          (2 * 3 ^ (ℓ / 2))) ∧
    (ℓ = 1 → κ * B (1, 1) = -(colorOrderedAmp 1 κ B 1 + colorOrderedAmp 1 κ B 3)) := by
  refine ⟨fun hℓ => ?_, fun h1 => ?_⟩
  · obtain ⟨m, hm⟩ := hℓ
    subst hm
    rw [show m + m = 2 * m by ring]
    have hs1 : extSlot (3 * (2 * m) + 1) = 0 := Fin.ext (by simp [extSlot]; omega)
    have hs3 : extSlot (3 * (2 * m) + 3) = 2 := Fin.ext (by simp [extSlot]; omega)
    have hd1 : extDegree (2 * m) (3 * (2 * m) + 1) = 0 := by
      unfold extDegree; split_ifs <;> omega
    have hd3 : extDegree (2 * m) (3 * (2 * m) + 3) = 0 := by
      unfold extDegree; split_ifs <;> omega
    have hsum : (reggeAmplitude (2 * m) B 0).coeff 0 - (reggeAmplitude (2 * m) B 2).coeff 0
        = B (2 * m, 2 * m) * (2 * 3 ^ m) := by
      rw [amp_coeff0, amp_coeff0, ← Finset.sum_sub_distrib,
        Finset.sum_eq_single (2 * m, 2 * m)]
      · rw [if_pos rfl, if_pos rfl, ← mul_sub, key_ll]
      · intro b hb hne
        by_cases hb1 : b.1 = 2 * m
        · rw [if_pos hb1, if_pos hb1, ← mul_sub]
          have hreg : IsReggeIndex b.1 b.2 := by
            simp only [reggeIndex, Finset.mem_filter] at hb
            exact hb.2
          have hk : b.2 ≠ 2 * m := by
            intro h; apply hne; exact Prod.ext hb1 h
          rw [hb1] at hreg ⊢
          have := odd_vec (odd_off m b.2 hreg hk)
          simp only [reggeColor]
          rw [this, sub_self, mul_zero]
        · rw [if_neg hb1, if_neg hb1, sub_self]
      · intro hnot
        exfalso; apply hnot
        rw [reggeIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        show IsReggeIndex (2 * m) (2 * m)
        unfold IsReggeIndex
        omega
    unfold colorOrderedAmp extCoord
    rw [if_pos (by omega), if_pos (by omega), hs1, hd1, hs3, hd3,
      Nat.mul_div_cancel_left m (by norm_num : 0 < 2), ← mul_sub, hsum]
    field_simp
  · subst h1
    have hidx : reggeIndex 1 = {(0, 0), (1, 1)} := by decide
    have hv : reggeAmplitude 1 B 0 + reggeAmplitude 1 B 2 = -(C (B (1, 1)) * X) := by
      rw [reggeAmplitude, hidx, Finset.sum_pair (by decide)]
      have h2 : (C (2⁻¹ : ℂ)) * (2 : ℂ[X]) = 1 := by
        rw [show (2 : ℂ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
      simp [reggeColor, reggeOp, C00, Tsu2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      linear_combination (-(X * C (B (1, 1)))) * h2
    have e1 : extCoord 1 (reggeAmplitude 1 B) 1 = (reggeAmplitude 1 B 0).coeff 1 := by
      unfold extCoord; rw [if_pos (by norm_num)]; rfl
    have e3 : extCoord 1 (reggeAmplitude 1 B) 3 = (reggeAmplitude 1 B 2).coeff 1 := by
      unfold extCoord; rw [if_pos (by norm_num)]; rfl
    unfold colorOrderedAmp
    rw [e1, e3, ← mul_add, ← coeff_add, hv]
    simp
