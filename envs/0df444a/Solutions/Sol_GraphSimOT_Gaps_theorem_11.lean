-- Prove2me | solution 1 for GraphSimOT.Gaps.theorem_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:24.966921+00:00
-- url     : https://prove2.me/submissions/56edb461-5977-40f0-812b-e07309bfff8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Definitions.Def_GraphSimOT_Gaps_CutRounding
import Theorems.Thm_GraphSimOT_Gaps_theorem_35
import Theorems.Thm_GraphSimOT_Gaps_theorem_38
import Theorems.Thm_GraphSimOT_Gaps_theorem_39

open Matrix GraphSimOT.Gaps

namespace Theorem11Aux

lemma cutNorm_nonneg {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (M : Matrix R C ℝ) : 0 ≤ FriezeKannan.CutDecomp.cutNorm M :=
  (abs_nonneg _).trans
    (Finset.le_sup' (fun p : Finset R × Finset C => |FriezeKannan.CutDecomp.blockSum M p.1 p.2|)
      (Finset.mem_univ (∅, ∅)))

lemma deltaOTCut_nonneg {n : ℕ} (G H : SimpleGraph (Fin n)) : 0 ≤ deltaOTCut G H := by
  apply Real.sInf_nonneg
  rintro _ ⟨_, _, rfl⟩
  exact cutNorm_nonneg _

lemma cutNorm_smul_le {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    {c : ℝ} (hc : 0 ≤ c) (M : Matrix R C ℝ) :
    FriezeKannan.CutDecomp.cutNorm (c • M) ≤ c * FriezeKannan.CutDecomp.cutNorm M := by
  unfold FriezeKannan.CutDecomp.cutNorm
  apply Finset.sup'_le
  intro p _
  have h1 : FriezeKannan.CutDecomp.blockSum (c • M) p.1 p.2 =
      c * FriezeKannan.CutDecomp.blockSum M p.1 p.2 := by
    unfold FriezeKannan.CutDecomp.blockSum
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [h1, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun q : Finset R × Finset C => |FriezeKannan.CutDecomp.blockSum M q.1 q.2|)
      (Finset.mem_univ p)) hc

lemma cutNorm_smul_nonneg {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    {c : ℝ} (hc : 0 ≤ c) (M : Matrix R C ℝ) :
    FriezeKannan.CutDecomp.cutNorm (c • M) = c * FriezeKannan.CutDecomp.cutNorm M := by
  apply le_antisymm (cutNorm_smul_le hc M)
  rcases hc.eq_or_lt with rfl | hpos
  · rw [zero_mul]; exact cutNorm_nonneg _
  · have hinv := cutNorm_smul_le (inv_nonneg.mpr hpos.le) (c • M)
    rw [inv_smul_smul₀ hpos.ne'] at hinv
    have hmul := mul_le_mul_of_nonneg_left hinv hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hmul

lemma costCutPerm_eq_cutNorm_Bmat {n : ℕ} (G H : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    costCutPerm G H π = FriezeKannan.CutDecomp.cutNorm (Bmat G H (π.permMatrix ℝ)) := by
  classical
  set P := π.permMatrix ℝ
  have hP_val : ∀ u v : Fin n, P u v = if π u = v then 1 else 0 := by
    intro u v
    simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  unfold costCutPerm FriezeKannan.CutDecomp.cutNorm
  apply le_antisymm
  · apply Finset.sup'_le
    intro p _
    let S : Finset (Fin n × Fin n) := Finset.univ ×ˢ p.1
    let T : Finset (Fin n × Fin n) := Finset.univ ×ˢ p.2
    have hsum : FriezeKannan.CutDecomp.blockSum (permAdj G π - adj H) p.1 p.2 =
        FriezeKannan.CutDecomp.blockSum (Bmat G H P) S T := by
      change (∑ w ∈ p.1, ∑ w' ∈ p.2, (permAdj G π - adj H) w w') =
        ∑ a ∈ S, ∑ b ∈ T, P a.1 a.2 * (adj G a.1 b.1 - adj H a.2 b.2) * P b.1 b.2
      have hrhs : (∑ a ∈ S, ∑ b ∈ T, P a.1 a.2 * (adj G a.1 b.1 - adj H a.2 b.2) * P b.1 b.2) =
          ∑ v : Fin n, ∑ w ∈ p.1, ∑ v' : Fin n, ∑ w' ∈ p.2,
            (if π v = w then (1 : ℝ) else 0) * (adj G v v' - adj H w w') *
              (if π v' = w' then 1 else 0) := by
        simp_rw [S, T, Finset.sum_product, hP_val]
      rw [hrhs, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w _
      calc
        ∑ w' ∈ p.2, (permAdj G π - adj H) w w'
            = ∑ w' ∈ p.2, ∑ v : Fin n, ∑ v' : Fin n,
                (if π v = w then (1 : ℝ) else 0) * (adj G v v' - adj H w w') *
                  (if π v' = w' then 1 else 0) := by
              apply Finset.sum_congr rfl; intro w' _
              symm
              rw [Finset.sum_eq_single (π.symm w)]
              · simp only [Equiv.apply_symm_apply, ↓reduceIte, one_mul]
                rw [Finset.sum_eq_single (π.symm w')]
                · simp [permAdj]
                · intro v' _ hv'
                  have : π v' ≠ w' := fun h => hv' (π.eq_symm_apply.mpr h)
                  simp [this]
                · intro h; exact absurd (Finset.mem_univ _) h
              · intro v _ hv
                have : π v ≠ w := fun h => hv (π.eq_symm_apply.mpr h)
                simp [this]
              · intro h; exact absurd (Finset.mem_univ _) h
        _ = ∑ v : Fin n, ∑ v' : Fin n, ∑ w' ∈ p.2,
              (if π v = w then (1 : ℝ) else 0) * (adj G v v' - adj H w w') *
                (if π v' = w' then 1 else 0) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro v _
              exact Finset.sum_comm
    rw [hsum]
    exact Finset.le_sup'
      (fun q : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) =>
        |FriezeKannan.CutDecomp.blockSum (Bmat G H P) q.1 q.2|)
      (Finset.mem_univ (S, T))
  · apply Finset.sup'_le
    intro p _
    let W1 : Finset (Fin n) := Finset.univ.filter (fun w => (π.symm w, w) ∈ p.1)
    let W2 : Finset (Fin n) := Finset.univ.filter (fun w' => (π.symm w', w') ∈ p.2)
    have hsum : FriezeKannan.CutDecomp.blockSum (Bmat G H P) p.1 p.2 =
        FriezeKannan.CutDecomp.blockSum (permAdj G π - adj H) W1 W2 := by
      unfold FriezeKannan.CutDecomp.blockSum Bmat disc
      have h1 : (∑ a ∈ p.1, ∑ b ∈ p.2,
          P a.1 a.2 * (adj G a.1 b.1 - adj H a.2 b.2) * P b.1 b.2) =
          ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
            (if a ∈ p.1 then P a.1 a.2 else 0) * (adj G a.1 b.1 - adj H a.2 b.2) *
              (if b ∈ p.2 then P b.1 b.2 else 0) := by
        rw [← Finset.sum_subset (Finset.subset_univ p.1)]
        · apply Finset.sum_congr rfl; intro a ha
          simp only [ha, ite_true]
          rw [← Finset.sum_subset (Finset.subset_univ p.2)]
          · apply Finset.sum_congr rfl; intro b hb; simp [hb]
          · intro b _ hb; simp [hb]
        · intro a _ ha; simp [ha]
      rw [h1, Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, hP_val]
      rw [Finset.sum_comm]
      have houter : ∑ w : Fin n, ∑ v : Fin n, ∑ v' : Fin n, ∑ w' : Fin n,
          (if (v, w) ∈ p.1 then if π v = w then (1 : ℝ) else 0 else 0) *
            (adj G v v' - adj H w w') *
            (if (v', w') ∈ p.2 then if π v' = w' then (1 : ℝ) else 0 else 0) =
          ∑ w : Fin n, (if w ∈ W1 then (1 : ℝ) else 0) *
            (∑ w' : Fin n, (if w' ∈ W2 then (1 : ℝ) else 0) *
              (adj G (π.symm w) (π.symm w') - adj H w w')) := by
        apply Finset.sum_congr rfl; intro w _
        rw [Finset.sum_eq_single (π.symm w)]
        · have hw1 : ((π.symm w, w) ∈ p.1) ↔ w ∈ W1 := by simp [W1]
          simp only [Equiv.apply_symm_apply, ↓reduceIte, hw1, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro w' _
          rw [Finset.sum_eq_single (π.symm w')]
          · have hw2 : ((π.symm w', w') ∈ p.2) ↔ w' ∈ W2 := by simp [W2]
            simp only [Equiv.apply_symm_apply, ↓reduceIte, hw2]; ring
          · intro v' _ hv'
            have : π v' ≠ w' := fun h => hv' (π.eq_symm_apply.mpr h)
            simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro v _ hv
          have : π v ≠ w := fun h => hv (π.eq_symm_apply.mpr h)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [houter, ← Finset.sum_subset (Finset.subset_univ W1)]
      · apply Finset.sum_congr rfl; intro w hw
        simp only [hw, ite_true, one_mul]
        rw [← Finset.sum_subset (Finset.subset_univ W2)]
        · apply Finset.sum_congr rfl; intro w' hw'
          simp [hw', permAdj]
        · intro w' _ hw'; simp [hw']
      · intro w _ hw; simp [hw]
    rw [hsum]
    exact Finset.le_sup'
      (fun q : Finset (Fin n) × Finset (Fin n) =>
        |FriezeKannan.CutDecomp.blockSum (permAdj G π - adj H) q.1 q.2|)
      (Finset.mem_univ (W1, W2))

lemma deltaCut_le_zeta_perm {n : ℕ} (hn : n ≠ 0) (G H : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) :
    deltaCut G H ≤ zeta G H (π.permMatrix ℝ) := by
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  unfold deltaCut zeta
  apply div_le_div_of_nonneg_right _ hn2.le
  exact (Finset.inf'_le _ (Finset.mem_univ π)).trans_eq (costCutPerm_eq_cutNorm_Bmat G H π)

lemma deltaOTCut_le_deltaCut {n : ℕ} (G H : SimpleGraph (Fin n)) :
    deltaOTCut G H ≤ deltaCut G H := by
  by_cases hn : n = 0
  · subst hn
    have h0 : deltaCut G H = 0 := by simp [deltaCut]
    rw [h0]
    have h0mem : (0 : Matrix (Fin 0) (Fin 0) ℝ) ∈ DSstar 0 := by simp [DSstar]
    have hbdd : BddBelow (costCut G H '' DSstar 0) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨_, _, rfl⟩
      exact cutNorm_nonneg _
    refine (csInf_le hbdd ⟨0, h0mem, rfl⟩).trans ?_
    unfold costCut FriezeKannan.CutDecomp.cutNorm
    apply Finset.sup'_le; intro p _
    unfold FriezeKannan.CutDecomp.blockSum Bmat
    simp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  unfold deltaCut
  rw [le_div_iff₀ hn2]
  unfold dCut
  apply Finset.le_inf'
  intro π _
  rw [← le_div_iff₀ hn2]
  let Qstar : Matrix (Fin n) (Fin n) ℝ := (1 / (n : ℝ)) • π.permMatrix ℝ
  have hQstar : Qstar ∈ DSstar n := by
    have hPds : π.permMatrix ℝ ∈ doublyStochastic ℝ (Fin n) := by
      change π.permMatrix ℝ ∈ (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ))
      rw [doublyStochastic_eq_convexHull_permMatrix]
      exact subset_convexHull ℝ _ ⟨π, rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hPds
    rcases hPds with ⟨hnn, hrow, hcol⟩
    refine ⟨fun i j => mul_nonneg (by positivity) (hnn i j), ?_, ?_⟩
    · intro i; simp only [Qstar, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hrow i, mul_one]
    · intro j; simp only [Qstar, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hcol j, mul_one]
  have hBmat : Bmat G H Qstar = (1 / (n : ℝ) ^ 2) • Bmat G H (π.permMatrix ℝ) := by
    ext a b
    change Qstar a.1 a.2 * disc G H a b * Qstar b.1 b.2 =
      (1 / (n : ℝ) ^ 2) * (π.permMatrix ℝ a.1 a.2 * disc G H a b * π.permMatrix ℝ b.1 b.2)
    simp only [Qstar, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcost : costCut G H Qstar = costCutPerm G H π / (n : ℝ) ^ 2 := by
    unfold costCut
    rw [hBmat, cutNorm_smul_nonneg (by positivity), ← costCutPerm_eq_cutNorm_Bmat G H π,
        one_div_mul_eq_div]
  have hbdd : BddBelow (costCut G H '' DSstar n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨_, _, rfl⟩
    exact cutNorm_nonneg _
  exact (csInf_le hbdd ⟨Qstar, hQstar, rfl⟩).trans_eq hcost

lemma deltaCut_le_one {n : ℕ} (G H : SimpleGraph (Fin n)) : deltaCut G H ≤ 1 := by
  by_cases hn : n = 0
  · subst hn; simp [deltaCut]
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [deltaCut, div_le_one hn2]
  refine (Finset.inf'_le _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).trans ?_
  unfold costCutPerm FriezeKannan.CutDecomp.cutNorm
  apply Finset.sup'_le
  intro p _
  unfold FriezeKannan.CutDecomp.blockSum
  calc
    |∑ i ∈ p.1, ∑ j ∈ p.2, (permAdj G 1 - adj H) i j|
        ≤ ∑ i ∈ p.1, ∑ j ∈ p.2, |(permAdj G 1 - adj H) i j| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
          refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ p.1)
            (fun _ _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans ?_
          apply Finset.sum_le_sum; intro i _
          refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ p.2)
            (fun _ _ _ => abs_nonneg _)).trans ?_
          apply Finset.sum_le_sum; intro j _
          simp only [Matrix.sub_apply, permAdj, adj]
          split_ifs <;> norm_num
    _ = (n : ℝ) ^ 2 := by simp [sq]

lemma deltaCut_zero_of_le_one {n : ℕ} (hn : n ≤ 1) (G H : SimpleGraph (Fin n)) :
    deltaCut G H = 0 := by
  have hnn : 0 ≤ deltaCut G H :=
    (deltaOTCut_nonneg G H).trans (deltaOTCut_le_deltaCut G H)
  apply le_antisymm _ hnn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · simp [deltaCut]
  · rw [deltaCut]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    refine (Finset.inf'_le _ (Finset.mem_univ (1 : Equiv.Perm (Fin 1)))).trans ?_
    unfold costCutPerm FriezeKannan.CutDecomp.cutNorm
    apply Finset.sup'_le; intro p _
    unfold FriezeKannan.CutDecomp.blockSum
    have h0 : ∀ i j : Fin 1, (permAdj G 1 - adj H) i j = 0 := by
      intro i j
      have hij : i = j := Subsingleton.elim i j
      subst hij
      simp [permAdj, adj]
    simp [h0]

lemma log_le_rpow_div {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    Real.log u ≤ u ^ t / t := by
  rw [le_div_iff₀ ht, mul_comm, ← Real.log_rpow hu]
  have hpos : 0 < u ^ t := Real.rpow_pos_of_pos hu t
  linarith [Real.log_le_sub_one_of_pos hpos]

lemma log8_gt_one : 1 < Real.log 8 := by
  have he : Real.exp 1 < 8 := by linarith [Real.exp_one_lt_d9]
  have := Real.log_lt_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

lemma polylog_pos_of_ge2 {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log 4 * Real.log (Real.log 8) ∧
    Real.log 4 * Real.log (Real.log 8) ≤
      Real.log (2 * n) * Real.log (Real.log (4 * n)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hll8_pos : 0 < Real.log (Real.log 8) := Real.log_pos log8_gt_one
  refine ⟨mul_pos hl4_pos hll8_pos, ?_⟩
  have h1 : Real.log 4 ≤ Real.log (2 * n) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h2 : Real.log 8 ≤ Real.log (4 * n) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h3 : Real.log (Real.log 8) ≤ Real.log (Real.log (4 * n)) :=
    Real.log_le_log (by linarith [log8_gt_one]) h2
  exact mul_le_mul h1 h3 hll8_pos.le (hl4_pos.le.trans h1)

lemma ds_bound_of_small {Cthin : ℝ} (hCthin : 0 < Cthin) (hthin : IsThinConstant Cthin)
    {n : ℕ} (hn : 2 ≤ n) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (hf_pos : 0 < zeta G H Q) (hf_lt : zeta G H Q < 1 / 2) :
    deltaCut G H ≤
      max (42 * (1 / (Real.log 4 * Real.log (Real.log 8)) + 4 * Cthin)) 600 *
        zeta G H Q * Real.log (Real.exp 1 / zeta G H Q) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / zeta G H Q)) := by
  set f : ℝ := zeta G H Q
  set c0 : ℝ := Real.log 4 * Real.log (Real.log 8)
  have hc0 := polylog_pos_of_ge2 hn
  set C1 : ℝ := 1 / c0 + 4 * Cthin
  have hC1_pos : 0 < C1 := add_pos (one_div_pos.mpr hc0.1) (by positivity)
  set Cbig : ℝ := max (42 * C1) 600
  have hn_ne : n ≠ 0 := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  set Lf : ℝ := Real.log (Real.exp 1 / f)
  have hLf_eq : Lf = 1 + Real.log (1 / f) := by
    dsimp only [Lf]
    rw [div_eq_mul_one_div, Real.log_mul (Real.exp_pos 1).ne' (one_div_pos.mpr hf_pos).ne',
        Real.log_exp]
  have hlog_inv_pos : 0 < Real.log (1 / f) := by
    apply Real.log_pos
    rw [one_lt_div hf_pos]; linarith
  have hLf_gt1 : 1 < Lf := by linarith
  have hll_gt1 : 1 < Real.log (Real.exp 1 * Lf) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
    have : 0 < Real.log Lf := Real.log_pos hLf_gt1
    linarith
  by_cases hn_case : (n : ℝ) ≤ f ^ (-(12 : ℝ))
  · -- Multiplicative regime: Theorem 38
    rcases theorem_38 Cthin hCthin hthin hn G H Q hQ with ⟨π, hπ⟩
    have hd_le := (deltaCut_le_zeta_perm hn_ne G H π).trans hπ
    set Plog : ℝ := Real.log (2 * n) * Real.log (Real.log (4 * n))
    have h1_le_P : 1 ≤ (1 / c0) * Plog := by
      rw [one_div_mul_eq_div, one_le_div hc0.1]
      exact hc0.2
    have hd_C1 : deltaCut G H ≤ C1 * Plog * f := by
      have hassoc : Cthin * Real.log (2 * n) * Real.log (Real.log (4 * n)) = Cthin * Plog :=
        mul_assoc _ _ _
      have hfac : 1 + 4 * (Cthin * Real.log (2 * n) * Real.log (Real.log (4 * n))) ≤ C1 * Plog := by
        rw [hassoc]; dsimp only [C1]; nlinarith
      exact hd_le.trans (mul_le_mul_of_nonneg_right hfac hf_pos.le)
    have hlog_n_le : Real.log n ≤ 12 * Real.log (1 / f) := by
      have hlog1 := Real.log_le_log hn_pos hn_case
      rw [Real.log_rpow hf_pos] at hlog1
      have : -(12 : ℝ) * Real.log f = 12 * Real.log (1 / f) := by
        rw [one_div, Real.log_inv]; ring
      linarith
    have hlog2n : Real.log (2 * n) ≤ 13 * Lf := by
      rw [Real.log_mul (by norm_num) hn_pos.ne']
      have hl2 : Real.log 2 ≤ 1 := by
        have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have := Real.log_le_log (by norm_num) this
        rwa [Real.log_exp] at this
      linarith
    have hlog4n : Real.log (4 * n) ≤ 14 * Lf := by
      have h42 : (4 : ℝ) * n = 2 * (2 * n) := by ring
      rw [h42, Real.log_mul (by norm_num) (by positivity)]
      have hl2 : Real.log 2 ≤ 1 := by
        have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have := Real.log_le_log (by norm_num) this
        rwa [Real.log_exp] at this
      linarith
    have hll4n : Real.log (Real.log (4 * n)) ≤ 3 * Real.log (Real.exp 1 * Lf) := by
      have h4n_pos : 0 < Real.log (4 * n) := Real.log_pos (by linarith)
      have hle14 : Real.log (Real.log (4 * n)) ≤ Real.log 14 + Real.log Lf :=
        (Real.log_le_log h4n_pos hlog4n).trans_eq
          (Real.log_mul (by norm_num) (by linarith))
      rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
      have hl14 : Real.log 14 ≤ 3 := by
        have he3 : (14 : ℝ) ≤ Real.exp 3 := by
          have he_gt : (2.71 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have hpow : (2.71 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
            pow_lt_pow_left₀ he_gt (by norm_num) (by norm_num)
          rw [← Real.exp_nat_mul] at hpow
          norm_num at hpow
          linarith
        have := Real.log_le_log (by norm_num) he3
        rwa [Real.log_exp] at this
      have hlogLf_nn : 0 ≤ Real.log Lf := Real.log_nonneg hLf_gt1.le
      linarith
    have hPlog_le : Plog ≤ 39 * Lf * Real.log (Real.exp 1 * Lf) := by
      dsimp only [Plog]
      have h8_le : Real.log 8 ≤ Real.log (4 * n) :=
        Real.log_le_log (by norm_num) (by linarith)
      have hll_nn : 0 ≤ Real.log (Real.log (4 * n)) :=
        Real.log_nonneg (by linarith [log8_gt_one])
      calc
        Real.log (2 * n) * Real.log (Real.log (4 * n))
            ≤ (13 * Lf) * (3 * Real.log (Real.exp 1 * Lf)) :=
              mul_le_mul hlog2n hll4n hll_nn (by linarith)
        _ = 39 * Lf * Real.log (Real.exp 1 * Lf) := by ring
    have h39_le : 39 * C1 ≤ Cbig := by
      have : 42 * C1 ≤ Cbig := le_max_left _ _
      linarith
    calc
      deltaCut G H ≤ C1 * Plog * f := hd_C1
      _ ≤ C1 * (39 * Lf * Real.log (Real.exp 1 * Lf)) * f := by
            apply mul_le_mul_of_nonneg_right _ hf_pos.le
            exact mul_le_mul_of_nonneg_left hPlog_le hC1_pos.le
      _ = (39 * C1) * f * Lf * Real.log (Real.exp 1 * Lf) := by ring
      _ ≤ Cbig * f * Lf * Real.log (Real.exp 1 * Lf) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul_of_nonneg_right h39_le hf_pos.le
  · -- Additive regime: Theorem 39
    have hn_gt : f ^ (-(12 : ℝ)) < n := lt_of_not_ge hn_case
    rcases theorem_39 hn G H Q hQ with ⟨π, hπ⟩
    have hd_le := (deltaCut_le_zeta_perm hn_ne G H π).trans hπ
    -- Bound ⌈2 log₂ n⌉₊ ≤ 4 * ln n + 1 ≤ 5 * ln n (since n ≥ 2, ln n ≥ ln 2 > 1/2)
    have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 := by
      have hexp : Real.exp (1 / 2) < 2 := by
        have he_lt : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
        have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; norm_num
        by_contra hge
        have hge' : 2 ≤ Real.exp (1 / 2) := le_of_not_gt hge
        have : (2 : ℝ) ^ 2 ≤ Real.exp (1 / 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hge' 2
        linarith
      have := Real.log_lt_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at this
    have hlogn_gt : (1 : ℝ) / 2 < Real.log n :=
      hlog2_gt.trans_le (Real.log_le_log (by norm_num) hnR)
    have hdn_le : (⌈2 * Real.logb 2 n⌉₊ : ℝ) ≤ 6 * Real.log n := by
      have hlb_nn : 0 ≤ 2 * Real.logb 2 n := by
        rw [Real.logb]; exact mul_nonneg (by norm_num)
          (div_nonneg (by linarith) (by linarith))
      have hceil : (⌈2 * Real.logb 2 n⌉₊ : ℝ) ≤ 2 * Real.logb 2 n + 1 :=
        (Nat.ceil_lt_add_one hlb_nn).le
      have hlb_le : 2 * Real.logb 2 n ≤ 4 * Real.log n := by
        rw [Real.logb, mul_div_assoc', div_le_iff₀ (by linarith : 0 < Real.log 2)]
        nlinarith
      linarith
    have hlog_pow : Real.log n ≤ 12 * (n : ℝ) ^ (1 / (12 : ℝ)) := by
      have := log_le_rpow_div hn_pos (by norm_num : (0 : ℝ) < 1 / 12)
      linarith
    have hdn_rpow : (⌈2 * Real.logb 2 n⌉₊ : ℝ) ≤ 72 * (n : ℝ) ^ (1 / (12 : ℝ)) := by
      linarith
    have hsqrt_dn : Real.sqrt (⌈2 * Real.logb 2 n⌉₊ : ℝ) ≤
        9 * (n : ℝ) ^ (1 / (24 : ℝ)) := by
      have h72 : (72 : ℝ) ≤ 9 ^ 2 := by norm_num
      have hrpow_sq : ((n : ℝ) ^ (1 / (24 : ℝ))) ^ 2 = (n : ℝ) ^ (1 / (12 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
        congr 1; norm_num
      have hsq_le : (⌈2 * Real.logb 2 n⌉₊ : ℝ) ≤ (9 * (n : ℝ) ^ (1 / (24 : ℝ))) ^ 2 := by
        rw [mul_pow, hrpow_sq]
        have : 0 ≤ (n : ℝ) ^ (1 / (12 : ℝ)) := Real.rpow_nonneg hn_pos.le _
        nlinarith
      exact (Real.sqrt_le_sqrt hsq_le).trans_eq
        (Real.sqrt_sq (mul_nonneg (by norm_num) (Real.rpow_nonneg hn_pos.le _)))
    have herr_n : 36 * Real.sqrt (⌈2 * Real.logb 2 n⌉₊ : ℝ) * (n : ℝ) ^ (-(1 / 6 : ℝ)) ≤
        324 * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt_dn (by norm_num : (0 : ℝ) ≤ 36))
        (Real.rpow_nonneg hn_pos.le (-(1 / 6 : ℝ)))
      have hpow_comb : (n : ℝ) ^ (1 / (24 : ℝ)) * (n : ℝ) ^ (-(1 / 6 : ℝ)) =
          (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
        rw [← Real.rpow_add hn_pos]
        congr 1; norm_num
      linarith
    have hn_neg8 : (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ f := by
      have h1 : (n : ℝ) ^ (1 / 8 : ℝ) > (f ^ (-(12 : ℝ))) ^ (1 / 8 : ℝ) :=
        Real.rpow_lt_rpow (Real.rpow_nonneg hf_pos.le _) hn_gt (by norm_num)
      rw [← Real.rpow_mul hf_pos.le] at h1
      have hexp1 : -(12 : ℝ) * (1 / 8 : ℝ) = -(3 / 2 : ℝ) := by norm_num
      rw [hexp1] at h1
      have hinv1 : (n : ℝ) ^ (-(1 / 8 : ℝ)) = 1 / (n : ℝ) ^ (1 / 8 : ℝ) := by
        rw [Real.rpow_neg hn_pos.le, ← one_div]
      have hinv2 : f ^ (3 / 2 : ℝ) = 1 / f ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_neg hf_pos.le, ← one_div (f ^ (3 / 2 : ℝ)), one_div_one_div]
      have hle_f32 : (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ f ^ (3 / 2 : ℝ) := by
        rw [hinv1, hinv2]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hf_pos _) h1.le
      have hf32_le_f : f ^ (3 / 2 : ℝ) ≤ f := by
        conv_rhs => rw [← Real.rpow_one f]
        exact Real.rpow_le_rpow_of_exponent_ge hf_pos (by linarith) (by norm_num)
      exact hle_f32.trans hf32_le_f
    have htot_325 : deltaCut G H ≤ 325 * f := by
      change deltaCut G H ≤ f + _ at hd_le
      nlinarith
    have h600 : (600 : ℝ) ≤ Cbig := le_max_right _ _
    have h1_le_logs : 1 ≤ Lf * Real.log (Real.exp 1 * Lf) :=
      one_le_mul_of_one_le_of_one_le hLf_gt1.le hll_gt1.le
    calc
      deltaCut G H ≤ 325 * f := htot_325
      _ ≤ Cbig * f * 1 := by nlinarith
      _ ≤ Cbig * f * (Lf * Real.log (Real.exp 1 * Lf)) :=
            mul_le_mul_of_nonneg_left h1_le_logs (mul_nonneg (by linarith) hf_pos.le)
      _ = Cbig * f * Lf * Real.log (Real.exp 1 * Lf) := by ring

end Theorem11Aux

theorem solution :
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      deltaOTCut G H ≤ deltaCut G H ∧
      deltaCut G H ≤ C * deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      deltaCut G H ≤ C * deltaOTCut G H ^ (1 - ε)) := by
  rcases theorem_35 with ⟨Cthin, hCthin, hthin⟩
  set c0 : ℝ := Real.log 4 * Real.log (Real.log 8)
  have hc0_pos : 0 < c0 := (Theorem11Aux.polylog_pos_of_ge2 (le_refl 2)).1
  set C0 : ℝ := max (42 * (1 / c0 + 4 * Cthin)) 600
  have hC0_pos : 0 < C0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 600) (le_max_right _ _)
  set Cmain : ℝ := max 4 (2 * C0)
  have hCmain_pos : 0 < Cmain := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _)
  have hpart1 : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      deltaOTCut G H ≤ deltaCut G H ∧
      deltaCut G H ≤ Cmain * deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H)) := by
    intro n G H
    refine ⟨Theorem11Aux.deltaOTCut_le_deltaCut G H, ?_⟩
    set f : ℝ := deltaOTCut G H
    have hf_nn : 0 ≤ f := Theorem11Aux.deltaOTCut_nonneg G H
    have hf_le_d : f ≤ deltaCut G H := Theorem11Aux.deltaOTCut_le_deltaCut G H
    have hd_le1 : deltaCut G H ≤ 1 := Theorem11Aux.deltaCut_le_one G H
    have hf_le1 : f ≤ 1 := hf_le_d.trans hd_le1
    by_cases hn : n ≤ 1
    · have hd0 : deltaCut G H = 0 := Theorem11Aux.deltaCut_zero_of_le_one hn G H
      have hf0 : f = 0 := le_antisymm (hf_le_d.trans_eq hd0) hf_nn
      rw [hd0, hf0]; simp
    have hn2 : 2 ≤ n := by omega
    have hn_ne : n ≠ 0 := by omega
    have hnR : (0 : ℝ) < n := by positivity
    have hDS_ne : (DSstar n).Nonempty := by
      refine ⟨(1 / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
      · intro i j; simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        split_ifs <;> positivity
      · intro i; simp [Matrix.one_apply]
      · intro j; simp [Matrix.one_apply]
    have hQ_from_Qstar : ∀ Qstar ∈ DSstar n,
        (n : ℝ) • Qstar ∈ doublyStochastic ℝ (Fin n) ∧
        zeta G H ((n : ℝ) • Qstar) = costCut G H Qstar := by
      intro Qstar hQstar
      refine ⟨?_, ?_⟩
      · rw [mem_doublyStochastic_iff_sum]
        refine ⟨fun i j => mul_nonneg hnR.le (hQstar.1 i j), ?_, ?_⟩
        · intro i; simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.1 i]
          exact mul_one_div_cancel hnR.ne'
        · intro j; simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.2 j]
          exact mul_one_div_cancel hnR.ne'
      · unfold zeta costCut
        have hB : Bmat G H ((n : ℝ) • Qstar) = ((n : ℝ) ^ 2) • Bmat G H Qstar := by
          ext a b
          change ((n : ℝ) • Qstar) a.1 a.2 * disc G H a b * ((n : ℝ) • Qstar) b.1 b.2 =
            (n : ℝ) ^ 2 * (Qstar a.1 a.2 * disc G H a b * Qstar b.1 b.2)
          simp only [Matrix.smul_apply, smul_eq_mul]
          ring
        rw [hB, Theorem11Aux.cutNorm_smul_nonneg (by positivity),
            mul_div_cancel_left₀ _ (by positivity)]
    rcases hf_nn.eq_or_lt with hf0 | hf_pos
    · -- f = 0: Theorem 38 forces deltaCut G H = 0
      rw [← hf0]; simp only [mul_zero, zero_mul]
      by_contra hgt
      have hd_pos : 0 < deltaCut G H := lt_of_not_ge hgt
      set Mfac : ℝ := 1 + 4 * (Cthin * Real.log (2 * n) * Real.log (Real.log (4 * n)))
      have hM_pos : 0 < Mfac := by
        have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hl2n : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
        have hll4n : 0 < Real.log (Real.log (4 * n)) := by
          apply Real.log_pos
          exact Theorem11Aux.log8_gt_one.trans_le
            (Real.log_le_log (by norm_num) (by linarith))
        positivity
      let δ : ℝ := deltaCut G H / (2 * Mfac)
      have hδ_pos : 0 < δ := by positivity
      rcases exists_lt_of_csInf_lt (hDS_ne.image (costCut G H))
          (by rw [show sInf (costCut G H '' DSstar n) = f from rfl, ← hf0]; linarith :
            sInf (costCut G H '' DSstar n) < δ) with ⟨_, ⟨Qstar, hQstar, rfl⟩, hc_lt⟩
      rcases hQ_from_Qstar Qstar hQstar with ⟨hQ, hzeta_eq⟩
      rcases theorem_38 Cthin hCthin hthin hn2 G H ((n : ℝ) • Qstar) hQ with ⟨π, hπ⟩
      have hd_le := (Theorem11Aux.deltaCut_le_zeta_perm hn_ne G H π).trans hπ
      rw [hzeta_eq] at hd_le
      have hmul_lt : Mfac * costCut G H Qstar < deltaCut G H / 2 := by
        have := mul_lt_mul_of_pos_left hc_lt hM_pos
        have hcancel : Mfac * δ = deltaCut G H / 2 := by
          dsimp only [δ]; field_simp
        linarith
      linarith
    · by_cases hf_big : (1 : ℝ) / 4 ≤ f
      · -- f ≥ 1/4: trivial bound since deltaCut ≤ 1 and logs ≥ 1
        have hLf_ge1 : 1 ≤ Real.log (Real.exp 1 / f) := by
          have : Real.exp 1 ≤ Real.exp 1 / f := by
            rw [le_div_iff₀ hf_pos]
            nlinarith [Real.exp_pos 1]
          have h1 := Real.log_le_log (Real.exp_pos 1) this
          rwa [Real.log_exp] at h1
        have hll_ge1 : 1 ≤ Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by
          have : Real.exp 1 ≤ Real.exp 1 * Real.log (Real.exp 1 / f) :=
            le_mul_of_one_le_right (Real.exp_pos 1).le hLf_ge1
          have h1 := Real.log_le_log (Real.exp_pos 1) this
          rwa [Real.log_exp] at h1
        have h4_le : 4 ≤ Cmain := le_max_left _ _
        have h1_le_Cf : 1 ≤ Cmain * f := by nlinarith
        have h1_le_logs : 1 ≤ Real.log (Real.exp 1 / f) *
            Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) :=
          one_le_mul_of_one_le_of_one_le hLf_ge1 hll_ge1
        calc
          deltaCut G H ≤ 1 := hd_le1
          _ ≤ (Cmain * f) * 1 := by linarith
          _ ≤ (Cmain * f) * (Real.log (Real.exp 1 / f) *
                Real.log (Real.exp 1 * Real.log (Real.exp 1 / f))) :=
                mul_le_mul_of_nonneg_left h1_le_logs (by positivity)
          _ = Cmain * f * Real.log (Real.exp 1 / f) *
                Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by ring
      · -- 0 < f < 1/4: pick Qstar with costCut < 2 f < 1/2
        have hf_lt4 : f < 1 / 4 := lt_of_not_ge hf_big
        rcases exists_lt_of_csInf_lt (hDS_ne.image (costCut G H))
            (by show f < 2 * f; linarith) with ⟨_, ⟨Qstar, hQstar, rfl⟩, hc_lt⟩
        rcases hQ_from_Qstar Qstar hQstar with ⟨hQ, hzeta_eq⟩
        have hbdd : BddBelow (costCut G H '' DSstar n) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨_, _, rfl⟩
          exact Theorem11Aux.cutNorm_nonneg _
        have hf_le_q : f ≤ zeta G H ((n : ℝ) • Qstar) := by
          rw [hzeta_eq]; exact csInf_le hbdd ⟨Qstar, hQstar, rfl⟩
        set f' : ℝ := zeta G H ((n : ℝ) • Qstar)
        have hf'_pos : 0 < f' := lt_of_lt_of_le hf_pos hf_le_q
        have hf'_lt : f' < 1 / 2 := by rw [hzeta_eq]; linarith
        have hsmall := Theorem11Aux.ds_bound_of_small hCthin hthin hn2 G H
          ((n : ℝ) • Qstar) hQ hf'_pos hf'_lt
        have hlog1_le : Real.log (Real.exp 1 / f') ≤ Real.log (Real.exp 1 / f) := by
          apply Real.log_le_log (by positivity)
          exact div_le_div_of_nonneg_left (Real.exp_pos 1).le hf_pos hf_le_q
        have hLf'_gt1 : 1 < Real.log (Real.exp 1 / f') := by
          have : Real.exp 1 < Real.exp 1 / f' := by
            rw [lt_div_iff₀ hf'_pos]; nlinarith [Real.exp_pos 1]
          have h1 := Real.log_lt_log (Real.exp_pos 1) this
          rwa [Real.log_exp] at h1
        have hlog2_le : Real.log (Real.exp 1 * Real.log (Real.exp 1 / f')) ≤
            Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by
          apply Real.log_le_log (by positivity)
          exact mul_le_mul_of_nonneg_left hlog1_le (Real.exp_pos 1).le
        have hll'_nn : 0 ≤ Real.log (Real.exp 1 * Real.log (Real.exp 1 / f')) := by
          apply Real.log_nonneg
          have := Real.exp_one_gt_d9
          nlinarith
        have h2C0_le : 2 * C0 ≤ Cmain := le_max_right _ _
        have hf'_le : f' ≤ 2 * f := by rw [hzeta_eq]; exact hc_lt.le
        calc
          deltaCut G H ≤ C0 * f' * Real.log (Real.exp 1 / f') *
              Real.log (Real.exp 1 * Real.log (Real.exp 1 / f')) := hsmall
          _ ≤ C0 * (2 * f) * Real.log (Real.exp 1 / f) *
                Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by
                have hm1 : C0 * f' ≤ C0 * (2 * f) :=
                  mul_le_mul_of_nonneg_left hf'_le hC0_pos.le
                have hm2 : C0 * f' * Real.log (Real.exp 1 / f') ≤
                    C0 * (2 * f) * Real.log (Real.exp 1 / f) :=
                  mul_le_mul hm1 hlog1_le (by linarith) (by positivity)
                have hlog1_nn : 0 ≤ Real.log (Real.exp 1 / f) := by linarith
                exact mul_le_mul hm2 hlog2_le hll'_nn (by positivity)
          _ = (2 * C0) * f * Real.log (Real.exp 1 / f) *
                Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by ring
          _ ≤ Cmain * f * Real.log (Real.exp 1 / f) *
                Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by
                have hpos_logs : 0 ≤ f * Real.log (Real.exp 1 / f) *
                    Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by
                  have : 0 ≤ Real.log (Real.exp 1 / f) := by linarith
                  have : 0 ≤ Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) :=
                    hll'_nn.trans hlog2_le
                  positivity
                nlinarith
  refine ⟨⟨Cmain, hCmain_pos, hpart1⟩, ?_⟩
  intro ε hε
  by_cases hε1 : 1 ≤ ε
  · refine ⟨1, zero_lt_one, fun n G H => ?_⟩
    rw [one_mul]
    set f : ℝ := deltaOTCut G H
    have hf_nn : 0 ≤ f := Theorem11Aux.deltaOTCut_nonneg G H
    have hd_le1 : deltaCut G H ≤ 1 := Theorem11Aux.deltaCut_le_one G H
    have hf_le1 : f ≤ 1 := (Theorem11Aux.deltaOTCut_le_deltaCut G H).trans hd_le1
    rcases hf_nn.eq_or_lt with hf0 | hf_pos
    · have hd_le_zero : deltaCut G H ≤ 0 := by
        have hp : deltaCut G H ≤ Cmain * f * Real.log (Real.exp 1 / f) *
            Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := (hpart1 n G H).2
        rw [← hf0] at hp
        simpa using hp
      have hrpow_nn : 0 ≤ f ^ (1 - ε) := Real.rpow_nonneg hf_nn _
      linarith
    · have h1_le : 1 ≤ f ^ (1 - ε) := by
        have := Real.rpow_le_rpow_of_exponent_ge hf_pos hf_le1 (by linarith : 1 - ε ≤ 0)
        simpa using this
      exact hd_le1.trans h1_le
  · have hε_lt1 : ε < 1 := lt_of_not_ge hε1
    set t : ℝ := ε / 2
    have ht_pos : 0 < t := by positivity
    let Cε : ℝ := Cmain * (Real.exp (1 + ε) / t ^ 2)
    have hCε_pos : 0 < Cε := by positivity
    refine ⟨Cε, hCε_pos, fun n G H => ?_⟩
    set f : ℝ := deltaOTCut G H
    have hf_nn : 0 ≤ f := Theorem11Aux.deltaOTCut_nonneg G H
    rcases hf_nn.eq_or_lt with hf0 | hf_pos
    · have hd_le_zero : deltaCut G H ≤ 0 := by
        have hp : deltaCut G H ≤ Cmain * f * Real.log (Real.exp 1 / f) *
            Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := (hpart1 n G H).2
        rw [← hf0] at hp
        simpa using hp
      have hrpow_nn : 0 ≤ Cε * f ^ (1 - ε) :=
        mul_nonneg hCε_pos.le (Real.rpow_nonneg hf_nn _)
      linarith
    · have hp : deltaCut G H ≤ Cmain * f * Real.log (Real.exp 1 / f) *
          Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := (hpart1 n G H).2
      have hf_le1 : f ≤ 1 :=
        (Theorem11Aux.deltaOTCut_le_deltaCut G H).trans (Theorem11Aux.deltaCut_le_one G H)
      have hef_pos : 0 < Real.exp 1 / f := by positivity
      have hlog1_le : Real.log (Real.exp 1 / f) ≤ (Real.exp 1 / f) ^ t / t :=
        Theorem11Aux.log_le_rpow_div hef_pos ht_pos
      have hLf_ge1 : 1 ≤ Real.log (Real.exp 1 / f) := by
        have : Real.exp 1 ≤ Real.exp 1 / f := by
          rw [le_div_iff₀ hf_pos]; nlinarith [Real.exp_pos 1]
        have h1 := Real.log_le_log (Real.exp_pos 1) this
        rwa [Real.log_exp] at h1
      have hlog2_le : Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) ≤
          Real.exp 1 * ((Real.exp 1 / f) ^ t / t) := by
        have hpos_arg : 0 < Real.exp 1 * Real.log (Real.exp 1 / f) := by positivity
        have hle_id : Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) ≤
            Real.exp 1 * Real.log (Real.exp 1 / f) := by
          have := Real.log_le_sub_one_of_pos hpos_arg
          linarith
        exact hle_id.trans (mul_le_mul_of_nonneg_left hlog1_le (Real.exp_pos 1).le)
      have hll_nn : 0 ≤ Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) := by
        apply Real.log_nonneg
        have := Real.exp_one_gt_d9
        nlinarith
      have hprod_logs : Real.log (Real.exp 1 / f) *
          Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) ≤
          (Real.exp (1 + ε) / t ^ 2) * f ^ (-ε) := by
        calc
          Real.log (Real.exp 1 / f) * Real.log (Real.exp 1 * Real.log (Real.exp 1 / f))
              ≤ ((Real.exp 1 / f) ^ t / t) * (Real.exp 1 * ((Real.exp 1 / f) ^ t / t)) :=
                mul_le_mul hlog1_le hlog2_le hll_nn (by positivity)
          _ = (Real.exp 1 * ((Real.exp 1 / f) ^ t) ^ 2) / t ^ 2 := by ring
          _ = (Real.exp (1 + ε) / t ^ 2) * f ^ (-ε) := by
                have hpow2 : ((Real.exp 1 / f) ^ t) ^ 2 = (Real.exp 1 / f) ^ ε := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul hef_pos.le]
                  congr 1; dsimp only [t]; norm_num
                rw [hpow2, Real.div_rpow (Real.exp_pos 1).le hf_pos.le,
                    ← Real.exp_mul, one_mul, mul_div_assoc', ← Real.exp_add,
                    div_eq_mul_inv (Real.exp (1 + ε)) (f ^ ε), ← Real.rpow_neg hf_pos.le]
                ring
      have hf_pow : f * f ^ (-ε) = f ^ (1 - ε) := by
        conv_lhs => lhs; rw [← Real.rpow_one f]
        rw [← Real.rpow_add hf_pos, sub_eq_add_neg]
      calc
        deltaCut G H ≤ Cmain * f *
            (Real.log (Real.exp 1 / f) *
              Real.log (Real.exp 1 * Real.log (Real.exp 1 / f))) := by linarith
        _ ≤ Cmain * f * ((Real.exp (1 + ε) / t ^ 2) * f ^ (-ε)) :=
              mul_le_mul_of_nonneg_left hprod_logs (mul_nonneg hCmain_pos.le hf_pos.le)
        _ = Cε * (f * f ^ (-ε)) := by dsimp only [Cε]; ring
        _ = Cε * f ^ (1 - ε) := by rw [hf_pow]
