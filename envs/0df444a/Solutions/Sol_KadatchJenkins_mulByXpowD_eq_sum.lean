-- Prove2me | solution 1 for KadatchJenkins.mulByXpowD_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T09:09:44.551961+00:00
-- url     : https://prove2.me/submissions/d6122350-f259-4512-a09c-442890b29ddb

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial
namespace KadatchJenkins

theorem AuxKJ_dd (v : (ZMod 2)[X]) (a b : ℕ) : (v /ₘ X ^ a) /ₘ X ^ b = v /ₘ X ^ (a + b) := by
  set w := v /ₘ X ^ a
  have h1 := modByMonic_add_div v ((X : (ZMod 2)[X]) ^ a)
  have h2 := modByMonic_add_div w ((X : (ZMod 2)[X]) ^ b)
  have hr1 := degree_modByMonic_lt v (monic_X_pow (R := ZMod 2) a)
  have hr2 := degree_modByMonic_lt w (monic_X_pow (R := ZMod 2) b)
  rw [degree_X_pow] at hr1 hr2
  have key := div_modByMonic_unique (f := v) (g := X ^ (a + b)) (w /ₘ X ^ b)
    (v %ₘ X ^ a + X ^ a * (w %ₘ X ^ b)) (monic_X_pow _) ⟨?_, ?_⟩
  · exact key.1.symm
  · rw [pow_add]
    calc v %ₘ X ^ a + X ^ a * (w %ₘ X ^ b) + X ^ a * X ^ b * (w /ₘ X ^ b)
        = v %ₘ X ^ a + X ^ a * (w %ₘ X ^ b + X ^ b * (w /ₘ X ^ b)) := by ring
      _ = v := by rw [h2]; exact h1
  · rw [degree_X_pow, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_add, coeff_X_pow_mul', if_pos (by omega)]
    rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr1 (by exact_mod_cast (by omega : a ≤ m))),
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr2 (by exact_mod_cast (by omega : b ≤ m - a))),
      add_zero]

theorem AuxKJ_dig (v : (ZMod 2)[X]) (B : ℕ) (K : ℕ) :
    v = ∑ j ∈ Finset.range K, ((v /ₘ X ^ (j * B)) %ₘ X ^ B) * X ^ (j * B) +
      X ^ (K * B) * (v /ₘ X ^ (K * B)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h2 := modByMonic_add_div (v /ₘ X ^ (K * B)) ((X : (ZMod 2)[X]) ^ B)
    rw [AuxKJ_dd, ← Nat.succ_mul] at h2
    rw [Finset.sum_range_succ]
    conv_lhs => rw [ih]
    rw [add_assoc]
    refine congrArg (_ + ·) ?_
    conv_lhs => rw [← h2]
    rw [Nat.succ_mul, pow_add]
    ring

theorem AuxKJ_summod (P : (ZMod 2)[X]) (f : ℕ → (ZMod 2)[X]) (K : ℕ) :
    (∑ k ∈ Finset.range K, f k) % P = ∑ k ∈ Finset.range K, f k % P := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, Polynomial.add_mod, ih]

theorem mulByXpowD_eq_sum (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W B : ℕ) (hB : 0 < B)
    (v : (ZMod 2)[X]) (hv : v.degree < (W : WithBot ℕ)) :
    let K := (W + B - 1) / B
    let vk : ℕ → (ZMod 2)[X] := fun k => (v /ₘ X ^ ((K - 1 - k) * B)) %ₘ X ^ B
    v = ∑ k ∈ Finset.range K, vk k * X ^ ((K - 1 - k) * B) ∧
      mulByXpowD P v = ∑ k ∈ Finset.range K, (vk k * X ^ ((K - 1 - k) * B + P.natDegree)) % P := by
  intro K vk
  have hKB : W ≤ K * B := by
    have h1 := Nat.div_add_mod (W + B - 1) B
    have h2 := Nat.mod_lt (W + B - 1) hB
    simp only [K]
    rw [Nat.mul_comm]
    omega
  have hz : v /ₘ X ^ (K * B) = 0 := by
    rw [divByMonic_eq_zero_iff (monic_X_pow _), degree_X_pow]
    exact lt_of_lt_of_le hv (by exact_mod_cast hKB)
  have e1 : v = ∑ k ∈ Finset.range K, vk k * X ^ ((K - 1 - k) * B) := by
    have := AuxKJ_dig v B K
    rw [hz, mul_zero, add_zero] at this
    refine this.trans ?_
    simp only [vk]
    exact (Finset.sum_range_reflect (fun j => ((v /ₘ X ^ (j * B)) %ₘ X ^ B) * X ^ (j * B)) K).symm
  refine ⟨e1, ?_⟩
  have e2 : mulByXpowD P v = ((∑ k ∈ Finset.range K, vk k * X ^ ((K - 1 - k) * B)) * X ^ P.natDegree) % P := by
    unfold mulByXpowD
    exact congrArg (fun t => (t * X ^ P.natDegree) % P) e1
  rw [e2, Finset.sum_mul, AuxKJ_summod]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_assoc, ← pow_add]

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W B : ℕ) (hB : 0 < B)
    (v : (ZMod 2)[X]) (hv : v.degree < (W : WithBot ℕ)) :
    let K := (W + B - 1) / B
    let vk : ℕ → (ZMod 2)[X] := fun k => (v /ₘ X ^ ((K - 1 - k) * B)) %ₘ X ^ B
    v = ∑ k ∈ Finset.range K, vk k * X ^ ((K - 1 - k) * B) ∧
      KadatchJenkins.mulByXpowD P v = ∑ k ∈ Finset.range K, (vk k * X ^ ((K - 1 - k) * B + P.natDegree)) % P :=
  KadatchJenkins.mulByXpowD_eq_sum P hP W B hB v hv
