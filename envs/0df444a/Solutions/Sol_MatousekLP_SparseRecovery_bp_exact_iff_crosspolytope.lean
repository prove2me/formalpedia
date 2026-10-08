-- Prove2me | solution 1 for MatousekLP.SparseRecovery.bp_exact_iff_crosspolytope
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:04:32.874481+00:00
-- url     : https://prove2.me/submissions/c97fbc44-1fe9-4068-8b3c-fb77293d9bb1

import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit
import Mathlib

open Matrix MatousekLP.SparseRecovery

namespace BPExactAux

lemma l1Norm_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : l1Norm (a • x) = |a| * l1Norm x := by
  simp [l1Norm, abs_mul, Finset.mul_sum]

lemma l1Norm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ l1Norm x :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

lemma l1Norm_eq_zero {n : ℕ} (x : Fin n → ℝ) (h : l1Norm x = 0) : x = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => abs_nonneg (x j)).mp h i
    (Finset.mem_univ i)
  simpa using this

lemma supp_smul {n : ℕ} (a : ℝ) (ha : a ≠ 0) (x : Fin n → ℝ) : supp (a • x) = supp x := by
  ext i; simp [supp, ha]

end BPExactAux

open BPExactAux in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (hmn : m < n) (hrm : r ≤ m) :
    IsBPExact A r ↔
      ∀ z : Fin n → ℝ, l1Norm z = 1 → (supp z).card ≤ r →
        translate (kernel A) z ∩ crosspolytope n = {z} := by
  constructor
  · intro hex z hz hsupp
    obtain ⟨⟨-, hopt⟩, huniq⟩ := hex (A *ᵥ z) z rfl hsupp
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨l, hl, rfl⟩, hw⟩
      have hAw : A *ᵥ (l + z) = A *ᵥ z := by
        rw [mulVec_add]; simp [show A *ᵥ l = 0 from hl]
      apply huniq
      refine ⟨hAw, fun x' hx' => ?_⟩
      have : l1Norm (l + z) ≤ 1 := hw
      have := hopt x' hx'
      linarith
    · rintro rfl
      exact ⟨⟨0, by simp [kernel], by simp⟩, by simp [crosspolytope, hz]⟩
  · intro hcross b xt hxt hsupp
    by_cases h0 : xt = 0
    · subst h0
      have hopt : IsBPOptimal A b 0 := ⟨hxt, fun x' _ => by simpa [l1Norm] using l1Norm_nonneg x'⟩
      refine ⟨hopt, fun x' hx' => l1Norm_eq_zero x' (le_antisymm ?_ (l1Norm_nonneg x'))⟩
      simpa [l1Norm] using hx'.2 0 hopt.1
    · set s := l1Norm xt
      have hs : 0 < s := lt_of_le_of_ne (l1Norm_nonneg xt) (fun h => h0 (l1Norm_eq_zero xt h.symm))
      set z := s⁻¹ • xt
      have hz : l1Norm z = 1 := by
        rw [l1Norm_smul, abs_of_pos (inv_pos.mpr hs), inv_mul_cancel₀ hs.ne']
      have hzs : (supp z).card ≤ r := by rwa [supp_smul _ (inv_ne_zero hs.ne')]
      have hgood := hcross z hz hzs
      -- any solution of norm at most `s` equals `xt`
      have key : ∀ x', A *ᵥ x' = b → l1Norm x' ≤ s → x' = xt := by
        intro x' hx' hle
        have hmem : s⁻¹ • x' ∈ translate (kernel A) z ∩ crosspolytope n := by
          refine ⟨⟨s⁻¹ • x' - z, ?_, by abel⟩, ?_⟩
          · show A *ᵥ (s⁻¹ • x' - z) = 0
            rw [mulVec_sub, mulVec_smul, mulVec_smul, hx', hxt, sub_self]
          · show l1Norm (s⁻¹ • x') ≤ 1
            rw [l1Norm_smul, abs_of_pos (inv_pos.mpr hs)]
            calc s⁻¹ * l1Norm x' ≤ s⁻¹ * s := by gcongr
              _ = 1 := inv_mul_cancel₀ hs.ne'
        rw [hgood, Set.mem_singleton_iff] at hmem
        have := congrArg (fun v => s • v) hmem
        simpa [z, smul_smul, mul_inv_cancel₀ hs.ne'] using this
      have hopt : IsBPOptimal A b xt := by
        refine ⟨hxt, fun x' hx' => ?_⟩
        by_contra hlt; push_neg at hlt
        have := key x' hx' hlt.le
        rw [this] at hlt; exact lt_irrefl _ hlt
      exact ⟨hopt, fun x' hx' => key x' hx'.1 (hx'.2 xt hxt)⟩
