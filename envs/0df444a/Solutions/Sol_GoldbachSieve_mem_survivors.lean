-- Prove2me | solution 1 for GoldbachSieve.mem_survivors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:03:27.761626+00:00
-- url     : https://prove2.me/submissions/a5120d82-603d-45ac-863b-64e9d2896903

import Definitions.Def_GoldbachSieve

open GoldbachSieve

theorem solution {lo hi c q : ℕ} :
    q ∈ survivors lo hi c ↔
      max 2 lo ≤ q ∧ q ≤ hi ∧ ∀ r : ℕ, r.Prime → r ≤ c → r ∣ q → r = q := by
  unfold survivors
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hcard⟩
    refine ⟨h1, h2, ?_⟩
    intro r hrp hrc hrd
    by_contra hne
    have hmem : r ∈ (Finset.Icc 2 c).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrp.two_le, hrc⟩, hrp⟩
    have hf : r ∈ ((Finset.Icc 2 c).filter Nat.Prime).filter (fun r => r ∣ q ∧ r ≠ q) :=
      Finset.mem_filter.mpr ⟨hmem, hrd, hne⟩
    have hempty : ((Finset.Icc 2 c).filter Nat.Prime).filter (fun r => r ∣ q ∧ r ≠ q) = ∅ :=
      Finset.card_eq_zero.mp hcard
    rw [hempty] at hf
    exact absurd hf (Finset.notMem_empty r)
  · rintro ⟨h1, h2, hraw⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra hne
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    exact hr.2.2 (hraw r hr.1.2 hr.1.1.2 hr.2.1)

theorem survivor_of_prime {lo hi c q : ℕ} (hq : q.Prime)
    (h1 : max 2 lo ≤ q) (h2 : q ≤ hi) : q ∈ survivors lo hi c :=
  solution.mpr ⟨h1, h2, fun r hrp _ hrd => (Nat.prime_dvd_prime_iff_eq hrp hq).mp hrd⟩

