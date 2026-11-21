-- Prove2me | solution 1 for LinExchangeSP.ZPlus.claim_7_3_iii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:39:18.117573+00:00
-- url     : https://prove2.me/submissions/340e64dd-3f65-478f-a208-3ba10211f6a7

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace Aux_LinExchangeSP_ZPlus_claim_7_3_iii

open LinExchangeSP.ZPlus

/-- Maximum propagation: if a left null vector `e` of a Z₊ matrix attains its maximum at `b`
and `a → b` is an arc, then `e` attains its maximum at `a`. -/
theorem prop_arc {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (e : Fin t → ℚ)
    (hcol : ∀ j, ∑ h, e h * M h j = 0) (Mx : ℚ) (hMx : 0 ≤ Mx) (hle : ∀ h, e h ≤ Mx)
    (a b : Fin t) (hab : arcH M a b) (hb : e b = Mx) : e a = Mx := by
  have hT : ∀ h ∈ (Finset.univ : Finset (Fin t)), 0 ≤ (e h - Mx) * M h b := by
    intro h _
    by_cases hhb : h = b
    · rw [hhb, hb, sub_self, zero_mul]
    · have hne : (h : ℕ) ≠ (b : ℕ) := fun heq => hhb (Fin.ext heq)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hle h]) (hM.1 h b hne)
  have hsumT : ∑ h, (e h - Mx) * M h b = -(Mx * ∑ h, M h b) := by
    have : ∀ h, (e h - Mx) * M h b = e h * M h b - Mx * M h b := fun h => by ring
    rw [Finset.sum_congr rfl (fun h _ => this h), Finset.sum_sub_distrib, hcol b,
      ← Finset.mul_sum]
    ring
  have hcs : 0 ≤ ∑ h, M h b := hM.2 b
  have hle0 : ∑ h, (e h - Mx) * M h b ≤ 0 := by
    rw [hsumT]
    have := mul_nonneg hMx hcs
    linarith
  have hzero : ∑ h, (e h - Mx) * M h b = 0 :=
    le_antisymm hle0 (Finset.sum_nonneg hT)
  have hTa := (Finset.sum_eq_zero_iff_of_nonneg hT).mp hzero a (Finset.mem_univ _)
  rcases mul_eq_zero.mp hTa with h | h
  · linarith
  · exact absurd h (ne_of_lt hab.2)

theorem key {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t)
    (e : Fin t → ℚ) (hcol : ∀ j, ∑ h, e h * M h j = 0)
    (hsupp : ∀ h, e h ≠ 0 → Relation.ReflTransGen (arcH M) i h)
    (hpos : ∃ h, 0 < e h) : 0 < e i := by
  obtain ⟨h0, hh0⟩ := hpos
  have hne : (Finset.univ : Finset (Fin t)).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨Mx, hMxdef⟩ : ∃ Mx, Mx = Finset.univ.sup' hne e := ⟨_, rfl⟩
  have hle : ∀ h, e h ≤ Mx := fun h => by
    rw [hMxdef]; exact Finset.le_sup' e (Finset.mem_univ h)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne e
  rw [← hMxdef] at hj
  have hMxpos : 0 < Mx := lt_of_lt_of_le hh0 (hle h0)
  have hjreach : Relation.ReflTransGen (arcH M) i j := hsupp j (by rw [← hj]; exact ne_of_gt hMxpos)
  have hpath : ∀ x, Relation.ReflTransGen (arcH M) i x → e x = Mx → e i = Mx := by
    intro x hx
    induction hx with
    | refl => exact id
    | tail _ hbc ih =>
      intro hc
      exact ih (prop_arc M hM e hcol Mx hMxpos.le hle _ _ hbc hc)
  rw [hpath j hjreach hj.symm]
  exact hMxpos

end Aux_LinExchangeSP_ZPlus_claim_7_3_iii

open LinExchangeSP.ZPlus Aux_LinExchangeSP_ZPlus_claim_7_3_iii in
theorem solution {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (i : Fin t) (hi : InT3 M i) :
    M i ∈ Submodule.span ℚ ((fun h => M h) '' ((D M i : Set (Fin t)) \ {i})) := by
  classical
  obtain ⟨_, hrk⟩ := hi
  have hdep : ¬ LinearIndependent ℚ
      (M.submatrix (fun r : {j // j ∈ D M i} => (r : Fin t)) id).row := by
    intro hli
    have h1 := hli.rank_matrix
    unfold rowRank at hrk
    rw [h1] at hrk
    simp at hrk
  obtain ⟨g, hg, r0, hr0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨c, hc⟩ : ∃ c : Fin t → ℚ,
      c = fun h => if hh : h ∈ D M i then g ⟨h, hh⟩ else 0 := ⟨_, rfl⟩
  have hc_in : ∀ h (hh : h ∈ D M i), c h = g ⟨h, hh⟩ := fun h hh => by
    rw [hc]; exact dif_pos hh
  have hc_out : ∀ h, h ∉ D M i → c h = 0 := fun h hh => by
    rw [hc]; exact dif_neg hh
  have hgcol : ∀ j, ∑ r : {j // j ∈ D M i}, g r * M r j = 0 := by
    intro j
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply,
      Matrix.submatrix_apply, id, Pi.zero_apply] at this
    exact this
  have hcol : ∀ j, ∑ h, c h * M h j = 0 := by
    intro j
    calc ∑ h, c h * M h j = ∑ h ∈ D M i, c h * M h j :=
          (Finset.sum_subset (Finset.subset_univ _)
            (fun h _ hh => by rw [hc_out h hh, zero_mul])).symm
      _ = ∑ r : {j // j ∈ D M i}, c r * M r j := (Finset.sum_coe_sort _ _).symm
      _ = ∑ r : {j // j ∈ D M i}, g r * M r j :=
          Finset.sum_congr rfl (fun r _ => by rw [hc_in r.1 r.2])
      _ = 0 := hgcol j
  have hreach : ∀ h, h ∈ D M i → Relation.ReflTransGen (arcH M) i h := by
    intro h hh
    unfold D at hh
    rw [Finset.mem_filter] at hh
    exact hh.2
  have hsupp : ∀ h, c h ≠ 0 → Relation.ReflTransGen (arcH M) i h := by
    intro h hh
    by_cases hD : h ∈ D M i
    · exact hreach h hD
    · exact absurd (hc_out h hD) hh
  have hcr0 : c r0 ≠ 0 := by rw [hc_in r0.1 r0.2]; exact hr0
  have hci : c i ≠ 0 := by
    by_cases hpos : ∃ h, 0 < c h
    · exact ne_of_gt (key M hM i c hcol hsupp hpos)
    · push_neg at hpos
      have hneg : c r0 < 0 := lt_of_le_of_ne (hpos r0) hcr0
      have hcol' : ∀ j, ∑ h, (-c h) * M h j = 0 := by
        intro j
        have := hcol j
        simp only [neg_mul, Finset.sum_neg_distrib, this, neg_zero]
      have hsupp' : ∀ h, -c h ≠ 0 → Relation.ReflTransGen (arcH M) i h :=
        fun h hh => hsupp h (fun h0 => hh (by rw [h0, neg_zero]))
      have := key M hM i (fun h => -c h) hcol' hsupp' ⟨r0, show 0 < -c r0 by linarith⟩
      intro h0
      have h3 : 0 < -c i := this
      rw [h0, neg_zero] at h3
      exact lt_irrefl _ h3
  -- vector form of the dependency
  have hsum0 : ∑ h, c h • M h = 0 := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hcol j
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)] at hsum0
  have heq : c i • M i = -∑ h ∈ Finset.univ.erase i, c h • M h :=
    eq_neg_of_add_eq_zero_left hsum0
  have hmem : ∑ h ∈ Finset.univ.erase i, c h • M h ∈
      Submodule.span ℚ ((fun h => M h) '' ((D M i : Set (Fin t)) \ {i})) := by
    apply Submodule.sum_mem
    intro h hh
    by_cases hD : h ∈ D M i
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨h, Set.mem_diff_of_mem (Finset.mem_coe.mpr hD) ?_, rfl⟩
      rw [Set.mem_singleton_iff]
      exact Finset.ne_of_mem_erase hh
    · rw [hc_out h hD, zero_smul]
      exact Submodule.zero_mem _
  have hMi : M i = (c i)⁻¹ • (c i • M i) := by
    rw [smul_smul, inv_mul_cancel₀ hci, one_smul]
  rw [hMi, heq]
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)
