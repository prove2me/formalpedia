-- Prove2me | solution 1 for LagrangeDerivCoeffOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:28:03.524613+00:00
-- url     : https://prove2.me/submissions/96deff86-66c8-408b-af3e-7efe19892f77

module
public import Definitions.Def_PHarmonicPoly_ChebNodeTelescope
public import Definitions.Def_PHarmonicPoly_LagrangeDerivCoeffOne
public import Theorems.Thm_ChebNodeTelescope


set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    (∏ j ∈ (Finset.range (m + 1)).erase 1,
        (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m j))⁻¹ *
      (∑ t ∈ Finset.powersetCard (m - 1) ((Finset.range (m + 1)).erase 1),
        ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a))
      = -2 / (1 - Polynomial.Chebyshev.node m 1) := by
  have hE : (Finset.range (m + 1)).erase 1 = insert 0 (Finset.Icc 2 m) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hcardIcc : (Finset.Icc 2 m).card = m - 1 := by
    rw [Nat.card_Icc]
    omega
  have h0notIcc : (0 : ℕ) ∉ Finset.Icc 2 m := by simp
  have hnodezero : Polynomial.Chebyshev.node m 0 = 1 := Polynomial.Chebyshev.node_eq_one
  have hpos : ∀ a ∈ Finset.Icc 2 m,
      0 < Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    have h := Polynomial.Chebyshev.node_lt (n := m) (i := 1) (j := a) ha.2 (by omega)
    linarith
  have hPpos : (0 : ℝ) < ∏ a ∈ Finset.Icc 2 m,
      (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a) :=
    Finset.prod_pos hpos
  have hPne : (∏ a ∈ Finset.Icc 2 m,
      (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a)) ≠ 0 := ne_of_gt hPpos
  have hx1lt : Polynomial.Chebyshev.node m 1 < 1 := by
    have h := Polynomial.Chebyshev.node_lt (n := m) (i := 0) (j := 1) (by omega) (by omega)
    rw [hnodezero] at h
    exact h
  have h1x : (1 : ℝ) - Polynomial.Chebyshev.node m 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    linarith
  have hsum : ∑ t ∈ Finset.powersetCard (m - 1) ((Finset.range (m + 1)).erase 1),
      ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a)
      = ∏ a ∈ Finset.Icc 2 m, (1 - Polynomial.Chebyshev.node m a) := by
    refine Finset.sum_eq_single_of_mem (Finset.Icc 2 m) ?_ ?_
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, hcardIcc⟩
      rw [hE]
      exact Finset.subset_insert _ _
    · intro t ht hne
      rw [Finset.mem_powersetCard] at ht
      have h0t : (0 : ℕ) ∈ t := by
        by_contra h0
        refine hne (Finset.eq_of_subset_of_card_le ?_ (hcardIcc.trans_le ht.2.ge))
        intro j hj
        have hjE := ht.1 hj
        rw [hE] at hjE
        rcases Finset.mem_insert.mp hjE with h | h
        · subst h
          exact absurd hj h0
        · exact h
      refine Finset.prod_eq_zero h0t ?_
      rw [hnodezero]
      ring
  have hprod : ∏ j ∈ (Finset.range (m + 1)).erase 1,
      (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m j)
      = (Polynomial.Chebyshev.node m 1 - 1) *
        ∏ a ∈ Finset.Icc 2 m,
          (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a) := by
    rw [hE, Finset.prod_insert h0notIcc, hnodezero]
  have hx1 : Polynomial.Chebyshev.node m 1 - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    linarith
  have htel := ChebNodeTelescope hm
  rw [Finset.prod_div_distrib] at htel
  have hnum := (div_eq_iff hPne).mp htel
  rw [hsum, hprod, hnum]
  field_simp
  ring
