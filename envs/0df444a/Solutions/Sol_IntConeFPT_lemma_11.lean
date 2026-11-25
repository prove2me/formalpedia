-- Prove2me | solution 1 for IntConeFPT.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T09:38:21.722683+00:00
-- url     : https://prove2.me/submissions/fa3d87b8-420a-4187-8cbb-2ac6c9469c52

import Definitions.Def_IntConeFPT_Formulation

open IntConeFPT Set

theorem solution (I : Instance) (_hI : I.Valid) (M : ℕ) (hM : 1 ≤ M)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (Nmax : ℕ) (R : Cand I) (_hR : IsCandidate I R)
    (γ : ℚ) :
    (∀ ξ ∈ K I R Nmax γ, ∀ t i,
      (∀ j, |(ξ t i).1 j| ≤ ((max 1 (Nmax * M) : ℕ) : ℝ)) ∧
      (∀ j, |(ξ t i).2.1 j| ≤ ((max 1 (Nmax * M) : ℕ) : ℝ)) ∧
      (ξ t i).2.2 ≤ ((max 1 (Nmax * M) : ℕ) : ℝ)) ∧
    Nat.size (max 1 (Nmax * M)) ≤ Nat.size Nmax + Nat.size M := by
  constructor
  · intro ξ hξ t i
    have hnn (s j) : 0 ≤ (ξ s j).2.2 := by
      rcases hξ.2.1 s j with he | h
      · change ξ s j = 0 at he
        simp [he]
      · exact h.1.le
    have hcnt : (ξ t i).2.2 ≤ (Nmax : ℝ) := calc
      _ ≤ blockCount ξ t := Finset.single_le_sum (fun j _ => hnn t j) (Finset.mem_univ i)
      _ ≤ ∑ s, blockCount ξ s := Finset.single_le_sum (f := blockCount ξ)
        (fun s _ => Finset.sum_nonneg fun j _ => hnn s j) (Finset.mem_univ t)
      _ ≤ _ := hξ.2.2.2.1
    have hscale : (ξ t i).2.2 * M ≤ (max 1 (Nmax*M) : ℕ) := by
      exact (mul_le_mul_of_nonneg_right hcnt (Nat.cast_nonneg _)).trans (by exact_mod_cast le_max_right 1 (Nmax*M))
    have hlast := (le_mul_of_one_le_right (hnn t i) (by exact_mod_cast hM : (1:ℝ) ≤ M)).trans hscale
    refine ⟨?_,?_,hlast⟩ <;> intro j
    all_goals
      rcases hξ.2.1 t i with he | hh
      · change ξ t i = 0 at he
        simp [he]
      obtain ⟨hpos, hnorm⟩ := hh
      let lo : (Fin I.d → ℝ) × (Fin I.k → ℝ) := (fun _ => -(M:ℝ),fun _ => -(M:ℝ))
      let hi : (Fin I.d → ℝ) × (Fin I.k → ℝ) := (fun _ => (M:ℝ),fun _ => (M:ℝ))
      have hb : I.Pr t ((R t).get i) ⊆ Icc lo hi := by
        apply convexHull_min _ (convex_Icc ..)
        rintro _ ⟨g,hg,rfl⟩
        have hh := hbox t g.toReal hg.1
        exact ⟨⟨fun l => (abs_le.mp (hh.1 l)).1,fun l => (abs_le.mp (hh.2 l)).1⟩,
          ⟨fun l => (abs_le.mp (hh.1 l)).2,fun l => (abs_le.mp (hh.2 l)).2⟩⟩
      have hb' := hb hnorm
      apply le_trans _ hscale
    · have h := abs_le.mpr ⟨hb'.1.1 j,hb'.2.1 j⟩
      change |(ξ t i).2.2⁻¹ * (ξ t i).1 j| ≤ (M:ℝ) at h
      rwa [abs_mul,abs_inv,abs_of_pos hpos,← div_eq_inv_mul,div_le_iff₀ hpos,mul_comm] at h
    · have h := abs_le.mpr ⟨hb'.1.2 j,hb'.2.2 j⟩
      change |(ξ t i).2.2⁻¹ * (ξ t i).2.1 j| ≤ (M:ℝ) at h
      rwa [abs_mul,abs_inv,abs_of_pos hpos,← div_eq_inv_mul,div_le_iff₀ hpos,mul_comm] at h
  · apply Nat.size_le.mpr
    rw [max_lt_iff]
    refine ⟨?_,?_⟩
    · exact lt_of_le_of_lt (by omega : 1 ≤ M) ((Nat.lt_size_self M).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)))
    · rw [pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self Nmax) (Nat.lt_size_self M)
