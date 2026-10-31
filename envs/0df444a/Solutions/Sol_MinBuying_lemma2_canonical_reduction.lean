-- Prove2me | solution 1 for MinBuying.lemma2_canonical_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:52:00.070654+00:00
-- url     : https://prove2.me/submissions/15b57c50-b634-4c96-8de8-77a450a8898d

import Theorems.Thm_MinBuying_canonical_revenue_bridge
import Theorems.Thm_MinBuying_canonical_list_completion
import Theorems.Thm_MinBuying_triangular_list_pruning
import Theorems.Thm_MinBuying_triangular_cap_list_extraction

open MinBuying
open scoped BigOperators

noncomputable section

private lemma terminal_uniform_bound (P t : ℝ) (ht : 0 ≤ t) :
    t * (1 - triangularReject 1 P t) ≤ 1 := by
  by_cases ht0 : t = 0
  · subst t; norm_num
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hcap : t ≤ P
  · simp only [triangularReject, if_neg htpos.not_ge, if_pos hcap]
    have hd : 0 < t + 1 := by positivity
    have heq : t * (1 - t / (t + 1)) = t / (t + 1) := by field_simp; ring
    rw [heq]
    exact (div_le_one hd).mpr (by linarith)
  · simp [triangularReject, htpos.not_ge, hcap]

private lemma terminal_only (ε : ℝ) (hε : 0 < ε) :
    ∃ J : CanonicalInstance, J.count = 0 ∧
      1 - ε ≤ canonicalCapRevenue J ∧ UPRevenue (canonicalLaw J) ≤ 1 := by
  let P := 2 + 1 / ε
  have hinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hP1 : 1 < P := by dsimp [P]; linarith
  have hPden : 0 < P + 1 := by linarith
  have hεP : 1 ≤ ε * (P + 1) := by
    have hinveq : ε * (1 / ε) = 1 := mul_one_div_cancel hε.ne'
    have hsmall : 1 / ε ≤ P + 1 := by dsimp [P]; linarith
    nlinarith only [hinveq, mul_le_mul_of_nonneg_left hsmall hε.le]
  have hz : 1 - ε ≤ P / (P + 1) := by
    apply (le_div_iff₀ hPden).mpr
    nlinarith only [hεP]
  let J : CanonicalInstance := {
    count := 0
    terminalCap := P
    a := Fin.elim0
    cap := Fin.elim0
    terminal_one_lt := hP1
    a_pos := fun i => Fin.elim0 i
    cap_one_lt := fun i => Fin.elim0 i
    cap_lt_terminal := fun i => Fin.elim0 i
    caps_decreasing := fun i => Fin.elim0 i }
  refine ⟨J,rfl,?_,?_⟩
  · simpa [canonicalCapRevenue,canonicalContinuation,J] using hz
  · apply csSup_le
    · exact ⟨uniformRevenue (canonicalLaw J) 0,0,le_refl _,rfl⟩
    · rintro r ⟨t,ht,rfl⟩
      rw [(canonical_revenue_bridge J).2.2.2 t ht]
      simpa [canonicalUniformRevenueAt,J] using terminal_uniform_bound P t ht

theorem solution (n : ℕ) (hn : 0 < n) (I : TriangularInstance n)
    (hNorm : UPRevenue (triangularJoint I) = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : CanonicalInstance, J.count ≤ n ∧
      DPRevenue (triangularJoint I) - ε ≤ Revenue (canonicalLaw J) (canonicalPrices J) ∧
      UPRevenue (canonicalLaw J) ≤ 1 := by
  by_cases hD : DPRevenue (triangularJoint I) ≤ 1
  · obtain ⟨J,hcount,hcap,hU⟩ := terminal_only ε hε
    refine ⟨J,by simp [hcount],?_,hU⟩
    rw [(canonical_revenue_bridge J).2.2.1]
    exact (sub_le_sub_right hD ε).trans hcap
  · obtain ⟨L,hLlen,hLpar,hLdec,hLcap,hLU⟩ :=
      triangular_cap_list_extraction n hn I hNorm
    have hLfinal : 1 < L.foldl (fun S x => continuationStep x.1 x.2 S) 0 :=
      (lt_of_not_ge hD).trans_le hLcap
    obtain ⟨M,hMlen,hMpar,hMdec,hMcap,hMprod⟩ :=
      triangular_list_pruning L hLpar hLdec hLfinal
    have hMfinal : 1 < M.foldl (fun S x => continuationStep x.1 x.2 S) 0 :=
      hLfinal.trans_le hMcap
    have hMU : ∀ t : ℝ, 0 < t → t * (1 - (t / (t + 0)) *
        (M.map (fun x => triangularReject x.1 x.2 t)).prod) ≤ 1 := by
      intro t ht
      have h := (mul_le_mul_of_nonneg_left (sub_le_sub_left (hMprod t ht) 1) ht.le).trans (hLU t ht)
      simpa only [add_zero,div_self ht.ne',one_mul] using h
    obtain ⟨J,hJlen,hJcap,hJU⟩ :=
      canonical_list_completion M hMpar hMdec 0 (le_refl _) (by norm_num) hMU hMfinal ε hε
    refine ⟨J,hJlen.trans (hMlen.trans hLlen),?_,hJU⟩
    rw [(canonical_revenue_bridge J).2.2.1]
    exact (sub_le_sub_right (hLcap.trans hMcap) ε).trans hJcap
