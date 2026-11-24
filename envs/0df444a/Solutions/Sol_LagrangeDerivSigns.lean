-- Prove2me | solution 1 for LagrangeDerivSigns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:27:38.65599+00:00
-- url     : https://prove2.me/submissions/c2f22bbb-e24d-4e4f-97f5-ae4d989a3e27

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_LagrangeDerivSigns

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution (m i : ℕ) (hi : i ≤ m) (k : ℕ) :
    0 ≤ (-1 : ℝ) ^ i *
      ((∏ j ∈ (Finset.range (m + 1)).erase i,
            (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j))⁻¹ *
        ∑ t ∈ Finset.powersetCard k ((Finset.range (m + 1)).erase i),
          ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a)) := by
  have h1 : 0 < (-1 : ℝ) ^ i *
      ∏ j ∈ (Finset.range (m + 1)).erase i,
        (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j) :=
    Polynomial.Chebyshev.zero_lt_prod_node_sub_node hi
  have hsum : 0 ≤ ∑ t ∈ Finset.powersetCard k ((Finset.range (m + 1)).erase i),
      ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a) := by
    refine Finset.sum_nonneg fun t _ => Finset.prod_nonneg fun a _ => ?_
    have : Polynomial.Chebyshev.node m a ≤ 1 := by
      simpa [Polynomial.Chebyshev.node] using Real.cos_le_one ((a : ℝ) * Real.pi / m)
    linarith
  have hinv : 0 ≤ (-1 : ℝ) ^ i *
      (∏ j ∈ (Finset.range (m + 1)).erase i,
        (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j))⁻¹ := by
    rcases Nat.even_or_odd i with he | ho
    · rw [he.neg_one_pow] at h1 ⊢; simp at h1 ⊢; positivity
    · rw [ho.neg_one_pow] at h1 ⊢
      have hneg : (∏ j ∈ (Finset.range (m + 1)).erase i,
          (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j)) < 0 := by linarith
      simp only [neg_mul, one_mul, neg_nonneg]
      exact inv_nonpos.mpr hneg.le
  calc (0 : ℝ)
      ≤ ((-1 : ℝ) ^ i *
          (∏ j ∈ (Finset.range (m + 1)).erase i,
            (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j))⁻¹) *
        (∑ t ∈ Finset.powersetCard k ((Finset.range (m + 1)).erase i),
          ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a)) := mul_nonneg hinv hsum
    _ = _ := by ring
