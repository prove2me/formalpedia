-- Prove2me | solution 1 for MasulloRH.every_integer_shell_has_odd_primitive_quarter_turn_character
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:53:16.679344+00:00
-- url     : https://prove2.me/submissions/e353954d-02e7-4916-b1e7-697401d0326f

import Mathlib

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ q ∣ n^2 + 1 ∧
      (n : ZMod q)^2 = -1 ∧ ∃ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive ∧ χ.Odd ∧
      (χ (n : ZMod q) = Complex.I ∨ χ (n : ZMod q) = -Complex.I) := by
  have hm : ∃ m : ℕ, 1 < m ∧ ¬ 2 ∣ m ∧ m ∣ n^2+1 := by
    let k := n/2
    have hsplit : n = 2*k ∨ n = 2*k+1 := by dsimp [k]; omega
    rcases hsplit with hk|hk
    · refine ⟨n^2+1, by nlinarith, ?_, dvd_refl _⟩
      have h : n^2+1 = 2*(2*k^2)+1 := by rw [hk]; ring
      rw [h]; omega
    · have hkpos : 1 ≤ k := by omega
      refine ⟨2*(k^2+k)+1, by nlinarith, by omega, 2, ?_⟩
      rw [hk]; ring
  obtain ⟨m,hgt,hodd,hd⟩ := hm
  let q := m.minFac
  have hp : q.Prime := Nat.minFac_prime (by omega)
  have hqm : q ∣ m := Nat.minFac_dvd _
  have hq2 : 2 < q := by
    have hh := hp.two_le
    by_contra! h
    exact hodd ((show q = 2 by omega) ▸ hqm)
  have hd' := hqm.trans hd
  have h0 := (ZMod.natCast_eq_zero_iff _ _).2 hd'
  push_cast at h0
  have hsq : (n : ZMod q)^2 = -1 := eq_neg_of_add_eq_zero_left h0
  letI : Fact (2 < q) := ⟨hq2⟩
  letI : NeZero q := ⟨by omega⟩
  obtain ⟨χ,hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
      (ZMod.neg_one_ne_one (n := q))
  have ho : χ.Odd := χ.even_or_odd.resolve_left hχ
  have hne : χ ≠ 1 := by
    intro he
    subst χ
    apply hχ
    exact MulChar.one_apply (by simp)
  have hpr : χ.IsPrimitive := by
    rcases (Nat.dvd_prime hp).1 χ.conductor_dvd_level with ha|ha
    · exact (hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr ha)).elim
    · exact ha
  have he : χ (n : ZMod q)^2 = Complex.I^2 := by
    rw [← map_pow, hsq, Complex.I_sq]
    exact ho
  exact ⟨q,hp,hq2,hd',hsq,χ,hpr,ho,sq_eq_sq_iff_eq_or_eq_neg.mp he⟩
