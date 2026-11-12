-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.conditional_squaring
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:14:51.206367+00:00
-- url     : https://prove2.me/submissions/d9feb3b9-7ba9-40f9-b061-3254b14888b5

import Mathlib
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_KernelPotential

section
set_option autoImplicit false

namespace LinearHashingPoissonesque.Dev.CondSq
open LinearHashingPoissonesque.ExpectedLoads

lemma card_next {U i : ℕ} {v : Fin i → BinaryVector U} (hv : LinearIndependent (ZMod 2) v) :
    ((nextVectors v).card : ℝ) = 2 ^ U - 2 ^ i := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BinaryVector U)))
    (fun w => w ∈ tupleSpan v)
  have h2 : (Finset.univ.filter (fun w : BinaryVector U => w ∈ tupleSpan v)).card = 2 ^ i := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2)]
    rw [tupleSpan, finrank_span_eq_card hv]
    simp
  have h3 : (Finset.univ : Finset (BinaryVector U)).card = 2 ^ U := by
    simp
  have h4 : (nextVectors v).card = (Finset.univ.filter (fun w : BinaryVector U => ¬ w ∈ tupleSpan v)).card := by
    unfold nextVectors; congr
  rw [h2, h3] at h1
  have : (nextVectors v).card + 2 ^ i = 2 ^ U := by omega
  have h5 : ((nextVectors v).card : ℝ) + 2 ^ i = 2 ^ U := by exact_mod_cast this
  linarith

open Classical in
lemma card_span {U i : ℕ} {v : Fin i → BinaryVector U} (hv : LinearIndependent (ZMod 2) v) :
    (Finset.univ.filter (fun w : BinaryVector U => w ∈ tupleSpan v)).card = 2 ^ i := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2)]
  rw [tupleSpan, finrank_span_eq_card hv]
  simp

lemma mem_snoc {U i : ℕ} (v : Fin i → BinaryVector U) (w t : BinaryVector U) :
    t ∈ tupleSpan (Fin.snoc v w : Fin (i+1) → BinaryVector U) ↔
      t ∈ tupleSpan v ∨ t - w ∈ tupleSpan v := by
  unfold tupleSpan
  rw [Fin.range_snoc, Submodule.mem_span_insert]
  constructor
  · rintro ⟨a, z, hz, h⟩
    have : a = 0 ∨ a = 1 := (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a
    rcases this with rfl | rfl
    · left; simpa [h] using hz
    · right; rw [h]; simpa using hz
  · rintro (h | h)
    · exact ⟨0, t, h, by simp⟩
    · exact ⟨1, t - w, h, by simp⟩

lemma ccl_snoc {U i : ℕ} (hi : i < U) (S : Finset (BinaryVector U)) (v : Fin i → BinaryVector U)
    (w : BinaryVector U) (hw : w ∉ tupleSpan v) (x : BinaryVector U) :
    centeredCosetLoad S (Fin.snoc v w : Fin (i+1) → BinaryVector U) x =
      centeredCosetLoad S v x + centeredCosetLoad S v (x + w) := by
  classical
  unfold centeredCosetLoad
  have hset : S.filter (fun s => s - x ∈ tupleSpan (Fin.snoc v w : Fin (i+1) → BinaryVector U)) =
      S.filter (fun s => s - x ∈ tupleSpan v) ∪ S.filter (fun s => s - (x + w) ∈ tupleSpan v) := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr (fun s _ => ?_)
    rw [mem_snoc, sub_add_eq_sub_sub, sub_right_comm]
  have hdisj : Disjoint (S.filter (fun s => s - x ∈ tupleSpan v))
      (S.filter (fun s => s - (x + w) ∈ tupleSpan v)) := by
    rw [Finset.disjoint_filter]
    intro s _ h1 h2
    apply hw
    have := Submodule.sub_mem _ h1 h2
    have e : s - x - (s - (x + w)) = w := by abel
    rwa [e] at this
  have hc : (U - (i+1)) + 1 = U - i := by omega
  have hp : (2:ℝ) ^ (U - i) = 2 ^ (U - (i+1)) * 2 := by rw [← hc, pow_succ]
  rw [hset, Finset.card_union_of_disjoint hdisj, Nat.cast_add, hp]
  have : (0:ℝ) < 2 ^ (U - (i+1)) := by positivity
  field_simp
  ring

lemma ccl_add_mem {U i : ℕ} (S : Finset (BinaryVector U)) (v : Fin i → BinaryVector U)
    (y : BinaryVector U) (hy : y ∈ tupleSpan v) (x : BinaryVector U) :
    centeredCosetLoad S v (x + y) = centeredCosetLoad S v x := by
  classical
  unfold centeredCosetLoad
  congr 3
  refine Finset.filter_congr (fun s _ => ?_)
  rw [sub_add_eq_sub_sub]
  exact Submodule.sub_mem_iff_left _ hy

noncomputable def E {U i : ℕ} (S : Finset (BinaryVector U)) (lam : ℝ) (v : Fin i → BinaryVector U)
    (x : BinaryVector U) : ℝ := Real.exp (lam * centeredCosetLoad S v x)

noncomputable def Psi {U i : ℕ} (S : Finset (BinaryVector U)) (lam : ℝ) (v : Fin i → BinaryVector U)
    (w : BinaryVector U) : ℝ := ∑ x, E S lam v x * E S lam v (x + w)

lemma pot_snoc {U i : ℕ} (hi : i < U) (S : Finset (BinaryVector U)) (lam : ℝ)
    (v : Fin i → BinaryVector U) (w : BinaryVector U) (hw : w ∉ tupleSpan v) :
    kernelPotential S lam (Fin.snoc v w : Fin (i+1) → BinaryVector U) = Psi S lam v w / 2 ^ U := by
  unfold kernelPotential Psi E
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [ccl_snoc hi S v w hw, mul_add, Real.exp_add]

lemma psi_mem {U i : ℕ} (S : Finset (BinaryVector U)) (lam : ℝ) (v : Fin i → BinaryVector U)
    (w : BinaryVector U) (hw : w ∈ tupleSpan v) :
    Psi S lam v w = ∑ x, E S lam v x ^ 2 := by
  unfold Psi
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have : E S lam v (x + w) = E S lam v x := by unfold E; rw [ccl_add_mem S v w hw]
  rw [this, sq]

lemma psi_total {U i : ℕ} (S : Finset (BinaryVector U)) (lam : ℝ) (v : Fin i → BinaryVector U) :
    ∑ w, Psi S lam v w = (∑ x, E S lam v x) ^ 2 := by
  unfold Psi
  calc ∑ w, ∑ x, E S lam v x * E S lam v (x + w)
      = ∑ x, ∑ w, E S lam v x * E S lam v (x + w) := Finset.sum_comm
    _ = ∑ x, E S lam v x * ∑ y, E S lam v y := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.mul_sum]
        congr 1
        exact Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun w => rfl)
    _ = (∑ x, E S lam v x) ^ 2 := by rw [← Finset.sum_mul, sq]

end LinearHashingPoissonesque.Dev.CondSq

namespace LinearHashingPoissonesque.ExpectedLoads
open LinearHashingPoissonesque.Dev.CondSq in
theorem chk_conditional_squaring {u i : ℕ} (hi : i < u)
    (S : Finset (BinaryVector u)) (lam : ℝ) (v : Fin i → BinaryVector u)
    (hv : LinearIndependent (ZMod 2) v) :
    (∑ w ∈ nextVectors v, kernelPotential S lam (Fin.snoc v w)) /
      ((nextVectors v).card : ℝ) ≤ (kernelPotential S lam v) ^ 2 := by
  classical
  have hsum : ∑ w ∈ nextVectors v, kernelPotential S lam (Fin.snoc v w) =
      (∑ w ∈ nextVectors v, Psi S lam v w) / 2 ^ u := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have : w ∉ tupleSpan v := by simpa [nextVectors] using hw
    exact pot_snoc hi S lam v w this
  set T : ℝ := ∑ x, E S lam v x with hT
  set Q : ℝ := ∑ x, E S lam v x ^ 2 with hQ
  set N : ℝ := 2 ^ u with hN
  set c : ℝ := 2 ^ i with hc
  have hNpos : 0 < N := by positivity
  have hcnn : 0 ≤ c := by positivity
  have hcN : c < N := by
    rw [hN, hc]; exact pow_lt_pow_right₀ (by norm_num) hi
  have hpot : kernelPotential S lam v = T / N := rfl
  have hCS : T ^ 2 ≤ N * Q := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (BinaryVector u)))
      (f := fun x => E S lam v x)
    simpa [hT, hQ, hN] using this
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (BinaryVector u))
    (fun w => w ∈ tupleSpan v) (Psi S lam v)
  rw [psi_total] at hsplit
  have hin : ∑ w ∈ Finset.univ.filter (fun w => w ∈ tupleSpan v), Psi S lam v w = c * Q := by
    rw [Finset.sum_congr rfl (fun w hw => psi_mem S lam v w (Finset.mem_filter.1 hw).2)]
    rw [Finset.sum_const, card_span hv, nsmul_eq_mul]
    push_cast; rfl
  have hout : ∑ w ∈ nextVectors v, Psi S lam v w = T ^ 2 - c * Q := by
    have : nextVectors v = Finset.univ.filter (fun w => ¬ w ∈ tupleSpan v) := rfl
    rw [this]; linarith
  rw [hsum, hout, card_next hv, hpot]
  have hD : 0 < N - c := by linarith
  rw [div_div, div_le_iff₀ (by positivity)]
  have e : (T / N) ^ 2 * (N * (N - c)) = T ^ 2 * (N - c) / N := by
    field_simp
  rw [e, le_div_iff₀ hNpos]
  nlinarith [mul_nonneg hcnn (sub_nonneg.2 hCS)]
end LinearHashingPoissonesque.ExpectedLoads
end

theorem solution : type_of% @LinearHashingPoissonesque.ExpectedLoads.chk_conditional_squaring := @LinearHashingPoissonesque.ExpectedLoads.chk_conditional_squaring
