-- Prove2me | solution 1 for Micromobility.Transient.proposition_H_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:54:04.331806+00:00
-- url     : https://prove2.me/submissions/40e5b91f-0ca7-4f94-a9df-ea935ec20b86

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting
import Theorems.Thm_FanGlicksberg_kakutani_fan_glicksberg

namespace Micromobility.Transient.PropH3

open Finset Filter Topology

/-! ## Section 1: Finite-dimensional action space and compact convex action set -/

abbrev ActVec {ê : ℕ} (M : Model ê) :=
  (∀ e : Fin ê, Fin (M.U e + 1) → ℝ) × (Fin ê → ℝ)

private def toAction {ê : ℕ} (M : Model ê) (v : ActVec M) : Action ê where
  d := fun e d => if h : d ≤ M.U e then v.1 e ⟨d, Nat.lt_succ_of_le h⟩ else 0
  r := v.2

private def ofAction {ê : ℕ} (M : Model ê) (a : Action ê) : ActVec M :=
  (fun e b => a.d e b.val, a.r)

private lemma toAction_ofAction {ê : ℕ} (M : Model ê) {a : Action ê} (ha : M.InA a) :
    toAction M (ofAction M a) = a := by
  cases a with
  | mk ad ar =>
    simp only [toAction, ofAction, Action.mk.injEq, and_true]
    ext e d
    split_ifs with h
    · rfl
    · exact (ha.support e d (Or.inr (by omega))).symm

private lemma toAction_d_add {ê : ℕ} (M : Model ê) (u v : ActVec M) (e : Fin ê) (d : ℕ) :
    (toAction M (u + v)).d e d = (toAction M u).d e d + (toAction M v).d e d := by
  simp only [toAction]
  split_ifs <;> simp

private lemma toAction_d_smul {ê : ℕ} (M : Model ê) (c : ℝ) (v : ActVec M) (e : Fin ê) (d : ℕ) :
    (toAction M (c • v)).d e d = c * (toAction M v).d e d := by
  simp only [toAction]
  split_ifs <;> simp

private lemma toAction_r_add {ê : ℕ} (M : Model ê) (u v : ActVec M) (e : Fin ê) :
    (toAction M (u + v)).r e = (toAction M u).r e + (toAction M v).r e := rfl

private lemma toAction_r_smul {ê : ℕ} (M : Model ê) (c : ℝ) (v : ActVec M) (e : Fin ê) :
    (toAction M (c • v)).r e = c * (toAction M v).r e := rfl

private lemma continuous_toAction_d {ê : ℕ} (M : Model ê) (e : Fin ê) (d : ℕ) :
    Continuous (fun v : ActVec M => (toAction M v).d e d) := by
  simp only [toAction]
  by_cases h : d ≤ M.U e
  · simp only [dif_pos h]
    exact (continuous_apply (⟨d, Nat.lt_succ_of_le h⟩ : Fin (M.U e + 1))).comp
      ((continuous_apply e).comp continuous_fst)
  · simp only [dif_neg h]
    exact continuous_const

private lemma continuous_toAction_r {ê : ℕ} (M : Model ê) (e : Fin ê) :
    Continuous (fun v : ActVec M => (toAction M v).r e) :=
  (continuous_apply e).comp continuous_snd

private def actSet {ê : ℕ} (M : Model ê) : Set (ActVec M) :=
  { v | M.InA (toAction M v) }

private lemma ofAction_mem_actSet {ê : ℕ} (M : Model ê) {a : Action ê} (ha : M.InA a) :
    ofAction M a ∈ actSet M := by
  show M.InA (toAction M (ofAction M a))
  rw [toAction_ofAction M ha]
  exact ha

private lemma n_nonneg {ê : ℕ} (M : Model ê) : 0 ≤ M.n :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

private lemma n_pos_of_elem {ê : ℕ} (M : Model ê) (hM : M.Standing) (e : Fin ê) : 0 < M.n := by
  have h1 : (1 : ℝ) ≤ (M.nst e : ℝ) := by exact_mod_cast hM.nst_pos e
  have h2 : (M.nst e : ℝ) ≤ M.n :=
    Finset.single_le_sum (fun i _ => Nat.cast_nonneg (M.nst i)) (Finset.mem_univ e)
  linarith

private lemma nst_div_n_le_one {ê : ℕ} (M : Model ê) (hM : M.Standing) (e : Fin ê) :
    (M.nst e : ℝ) / M.n ≤ 1 := by
  have hn : 0 < M.n := n_pos_of_elem M hM e
  rw [div_le_one hn]
  exact Finset.single_le_sum (fun i _ => Nat.cast_nonneg (M.nst i)) (Finset.mem_univ e)

private lemma actSet_nonempty {ê : ℕ} (M : Model ê) (hM : M.Standing) : (actSet M).Nonempty := by
  refine ⟨(fun e b => if b.val = M.L e then (M.nst e : ℝ) / M.n else 0, fun e => M.Lr e), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e d
    simp only [toAction]
    split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) (n_nonneg M)
    · exact le_rfl
    · exact le_rfl
  · intro e d hd
    have hLU := hM.L_le_U e
    simp only [toAction]
    split_ifs with h1 h2
    · omega
    · rfl
    · rfl
  · intro e
    have hLU := hM.L_le_U e
    rw [Finset.sum_eq_single (M.L e)]
    · simp [toAction, hLU]
    · intro b _ hb
      simp only [toAction]
      split_ifs with h1
      · simp
      · rfl
    · intro hmem
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hLU⟩) hmem
  · intro e; exact le_rfl
  · intro e; exact hM.Lr_le_Ur e

private lemma actSet_convex {ê : ℕ} (M : Model ê) : Convex ℝ (actSet M) := by
  intro u hu v hv a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e d
    rw [toAction_d_add, toAction_d_smul, toAction_d_smul]
    exact add_nonneg (mul_nonneg ha (hu.nonneg e d)) (mul_nonneg hb (hv.nonneg e d))
  · intro e d hd
    rw [toAction_d_add, toAction_d_smul, toAction_d_smul, hu.support e d hd, hv.support e d hd]
    ring
  · intro e
    calc ∑ d ∈ Icc (M.L e) (M.U e), (toAction M (a • u + b • v)).d e d
        = ∑ d ∈ Icc (M.L e) (M.U e), (a * (toAction M u).d e d + b * (toAction M v).d e d) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [toAction_d_add, toAction_d_smul, toAction_d_smul]
      _ = a * ∑ d ∈ Icc (M.L e) (M.U e), (toAction M u).d e d +
          b * ∑ d ∈ Icc (M.L e) (M.U e), (toAction M v).d e d := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = a * ((M.nst e : ℝ) / M.n) + b * ((M.nst e : ℝ) / M.n) := by rw [hu.mass e, hv.mass e]
      _ = (M.nst e : ℝ) / M.n := by rw [← add_mul, hab, one_mul]
  · intro e
    rw [toAction_r_add, toAction_r_smul, toAction_r_smul]
    calc M.Lr e = (a + b) * M.Lr e := by rw [hab, one_mul]
      _ = a * M.Lr e + b * M.Lr e := add_mul _ _ _
      _ ≤ a * (toAction M u).r e + b * (toAction M v).r e :=
          add_le_add (mul_le_mul_of_nonneg_left (hu.r_ge e) ha)
            (mul_le_mul_of_nonneg_left (hv.r_ge e) hb)
  · intro e
    rw [toAction_r_add, toAction_r_smul, toAction_r_smul]
    calc a * (toAction M u).r e + b * (toAction M v).r e
        ≤ a * M.Ur e + b * M.Ur e :=
          add_le_add (mul_le_mul_of_nonneg_left (hu.r_le e) ha)
            (mul_le_mul_of_nonneg_left (hv.r_le e) hb)
      _ = M.Ur e := by rw [← add_mul, hab, one_mul]

private lemma mem_actSet_iff {ê : ℕ} (M : Model ê) (v : ActVec M) :
    v ∈ actSet M ↔
      (∀ e (b : Fin (M.U e + 1)), 0 ≤ v.1 e b) ∧
      (∀ e (b : Fin (M.U e + 1)), b.val < M.L e → v.1 e b = 0) ∧
      (∀ e, ∑ d ∈ Icc (M.L e) (M.U e), (toAction M v).d e d = (M.nst e : ℝ) / M.n) ∧
      (∀ e, M.Lr e ≤ v.2 e) ∧
      (∀ e, v.2 e ≤ M.Ur e) := by
  constructor
  · intro hv
    refine ⟨fun e b => ?_, fun e b hb => ?_, hv.mass, hv.r_ge, hv.r_le⟩
    · have := hv.nonneg e b.val
      simpa [toAction, Nat.le_of_lt_succ b.isLt] using this
    · have := hv.support e b.val (Or.inl hb)
      simpa [toAction, Nat.le_of_lt_succ b.isLt] using this
  · rintro ⟨hnn, hsupp, hmass, hrge, hrle⟩
    refine ⟨fun e d => ?_, fun e d hd => ?_, hmass, hrge, hrle⟩
    · simp only [toAction]
      split_ifs with h
      · exact hnn e ⟨d, Nat.lt_succ_of_le h⟩
      · exact le_rfl
    · simp only [toAction]
      split_ifs with h
      · rcases hd with hlt | hgt
        · exact hsupp e ⟨d, Nat.lt_succ_of_le h⟩ hlt
        · omega
      · rfl

private lemma actSet_isClosed {ê : ℕ} (M : Model ê) : IsClosed (actSet M) := by
  have heq : actSet M =
      (⋂ e, ⋂ b : Fin (M.U e + 1), {v : ActVec M | 0 ≤ v.1 e b}) ∩
      (⋂ e, ⋂ b : Fin (M.U e + 1), ⋂ (_ : b.val < M.L e), {v : ActVec M | v.1 e b = 0}) ∩
      (⋂ e, {v : ActVec M | ∑ d ∈ Icc (M.L e) (M.U e), (toAction M v).d e d = (M.nst e : ℝ) / M.n}) ∩
      (⋂ e, {v : ActVec M | M.Lr e ≤ v.2 e}) ∩
      (⋂ e, {v : ActVec M | v.2 e ≤ M.Ur e}) := by
    ext v; simp [mem_actSet_iff, and_assoc]
  rw [heq]
  refine ((((IsClosed.inter ?_ ?_).inter ?_).inter ?_).inter ?_)
  · exact isClosed_iInter fun e => isClosed_iInter fun b =>
      isClosed_le continuous_const ((continuous_apply b).comp ((continuous_apply e).comp continuous_fst))
  · exact isClosed_iInter fun e => isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply b).comp ((continuous_apply e).comp continuous_fst)) continuous_const
  · exact isClosed_iInter fun e =>
      isClosed_eq (continuous_finsetSum _ fun d _ => continuous_toAction_d M e d) continuous_const
  · exact isClosed_iInter fun e =>
      isClosed_le continuous_const ((continuous_apply e).comp continuous_snd)
  · exact isClosed_iInter fun e =>
      isClosed_le ((continuous_apply e).comp continuous_snd) continuous_const

private lemma actSet_isCompact {ê : ℕ} (M : Model ê) (hM : M.Standing) : IsCompact (actSet M) := by
  let box : Set (ActVec M) :=
    (Set.univ.pi fun e : Fin ê => Set.univ.pi fun _ : Fin (M.U e + 1) => Set.Icc (0 : ℝ) 1) ×ˢ
    (Set.univ.pi fun e : Fin ê => Set.Icc (M.Lr e) (M.Ur e))
  have hbox : IsCompact box :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)
  refine hbox.of_isClosed_subset (actSet_isClosed M) ?_
  intro v hv
  refine ⟨fun e _ b _ => ?_, fun e _ => ⟨hv.r_ge e, hv.r_le e⟩⟩
  have hbU : b.val ≤ M.U e := Nat.le_of_lt_succ b.isLt
  have h0 : 0 ≤ v.1 e b := by
    have := hv.nonneg e b.val
    simpa [toAction, hbU] using this
  refine ⟨h0, ?_⟩
  by_cases hL : b.val < M.L e
  · have hzero := hv.support e b.val (Or.inl hL)
    have : v.1 e b = 0 := by simpa [toAction, hbU] using hzero
    linarith
  · push Not at hL
    have hmem : b.val ∈ Icc (M.L e) (M.U e) := Finset.mem_Icc.mpr ⟨hL, hbU⟩
    have hle : (toAction M v).d e b.val ≤ ∑ d ∈ Icc (M.L e) (M.U e), (toAction M v).d e d :=
      Finset.single_le_sum (fun d _ => hv.nonneg e d) hmem
    have hval : (toAction M v).d e b.val = v.1 e b := by simp [toAction, hbU]
    rw [hval, hv.mass e] at hle
    exact hle.trans (nst_div_n_le_one M hM e)

/-! ## Section 2: Simplifications for `q = 0` and linearity of `next` -/

private lemma lam_eq_zero {ê : ℕ} (M : Model ê) (hq : M.q = 0) (a : Action ê) (e : Fin ê) :
    M.lam a e = 0 := by
  simp [Model.lam, hq]

private lemma poisPMF_zero (j : ℕ) : Model.poisPMF 0 j = if j = 0 then 1 else 0 := by
  cases j <;> simp [Model.poisPMF]

private lemma transProb_zero {ê : ℕ} (M : Model ê) (e : Fin ê) (b d : ℕ) :
    M.transProb e 0 b d = ∑' k : ℕ, if b - k = d then (M.D e k).toReal else 0 := by
  unfold Model.transProb
  congr 1
  ext k
  rw [poisPMF_zero]
  split_ifs <;> (simp_all; try omega)

private lemma transProb_zero_nonneg {ê : ℕ} (M : Model ê) (e : Fin ê) (b d : ℕ) :
    0 ≤ M.transProb e 0 b d := by
  rw [transProb_zero]
  exact tsum_nonneg fun k => by split_ifs <;> [exact ENNReal.toReal_nonneg; exact le_rfl]

private lemma transProb_zero_of_lt {ê : ℕ} (M : Model ê) (e : Fin ê) {b d : ℕ} (h : b < d) :
    M.transProb e 0 b d = 0 := by
  rw [transProb_zero]
  have hzero : ∀ k : ℕ, (if b - k = d then (M.D e k).toReal else 0) = 0 := fun k => by
    rw [if_neg (by omega)]
  simp_rw [hzero]
  exact tsum_zero

private lemma pmf_toReal_summable (p : PMF ℕ) : Summable (fun k => (p k).toReal) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

private lemma pmf_toReal_tsum (p : PMF ℕ) : ∑' k, (p k).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun k => p.apply_ne_top k), p.tsum_coe]
  simp

private lemma transProb_zero_sum_le_one {ê : ℕ} (M : Model ê) (e : Fin ê) {b : ℕ}
    (hb : b ≤ M.U e) : ∑ d ∈ range (M.U e), M.transProb e 0 b d ≤ 1 := by
  have hsub : ∑ d ∈ range (M.U e), M.transProb e 0 b d ≤
      ∑ d ∈ range (M.U e + 1), M.transProb e 0 b d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _))
      (fun d _ _ => transProb_zero_nonneg M e b d)
  refine hsub.trans ?_
  have hsum : ∀ d ∈ range (M.U e + 1),
      Summable (fun k : ℕ => if b - k = d then (M.D e k).toReal else 0) := by
    intro d _
    refine (pmf_toReal_summable (M.D e)).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · split_ifs <;> [exact ENNReal.toReal_nonneg; exact le_rfl]
    · split_ifs <;> [exact le_rfl; exact ENNReal.toReal_nonneg]
  have heq : ∑ d ∈ range (M.U e + 1), M.transProb e 0 b d =
      ∑' k : ℕ, ∑ d ∈ range (M.U e + 1), (if b - k = d then (M.D e k).toReal else 0) := by
    simp_rw [transProb_zero]
    exact (Summable.tsum_finsetSum hsum).symm
  rw [heq]
  have hinner : ∀ k : ℕ,
      ∑ d ∈ range (M.U e + 1), (if b - k = d then (M.D e k).toReal else 0) = (M.D e k).toReal := by
    intro k
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  simp_rw [hinner]
  rw [pmf_toReal_tsum]

private lemma mixProb_eq_zero_of_gt {ê : ℕ} (M : Model ê) (hq : M.q = 0)
    (a : Action ê) (e : Fin ê) {d : ℕ} (hd : M.U e < d) : M.mixProb a e d = 0 := by
  unfold Model.mixProb
  apply Finset.sum_eq_zero
  intro b hb
  rw [lam_eq_zero M hq, transProb_zero_of_lt M e (lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hd),
    mul_zero]

private lemma next_s_eq_zero {ê : ℕ} (M : Model ê) (hq : M.q = 0) (a : Action ê) (e : Fin ê) :
    (M.next a).s e = 0 := by
  unfold Model.next
  dsimp only
  have hzero : ∀ d : ℕ, (if M.U e < d then (d : ℝ) * M.mixProb a e d else 0) = 0 := fun d => by
    split_ifs with h
    · rw [mixProb_eq_zero_of_gt M hq a e h, mul_zero]
    · rfl
  simp_rw [hzero]
  exact tsum_zero

private lemma next_u_eq_zero {ê : ℕ} (M : Model ê) (hq : M.q = 0) (a : Action ê) (e : Fin ê) :
    (M.next a).u e = 0 := by
  unfold Model.next
  dsimp only
  have hzero : ∀ d : ℕ,
      (if M.U e < d then ((d : ℝ) - (M.U e : ℝ)) * M.mixProb a e d else 0) = 0 := fun d => by
    split_ifs with h
    · rw [mixProb_eq_zero_of_gt M hq a e h, mul_zero]
    · rfl
  simp_rw [hzero]
  exact tsum_zero

private lemma p_nonneg {ê : ℕ} (M : Model ê) (hM : M.Standing) (e' e : Fin ê) : 0 ≤ M.p e' e :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hM.w_nonneg e' e)) (le_of_lt (hM.w_sum_pos e'))

private lemma EminD_summable {ê : ℕ} (M : Model ê) (e : Fin ê) (b : ℕ) :
    Summable (fun k : ℕ => (M.D e k).toReal * ((min b k : ℕ) : ℝ)) := by
  refine ((pmf_toReal_summable (M.D e)).mul_right (b : ℝ)).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  · exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.min_le_left b k)) ENNReal.toReal_nonneg

private lemma EminD_nonneg {ê : ℕ} (M : Model ê) (e : Fin ê) (b : ℕ) : 0 ≤ M.EminD e b :=
  tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

private lemma EminD_mono {ê : ℕ} (M : Model ê) (e : Fin ê) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) :
    M.EminD e b₁ ≤ M.EminD e b₂ :=
  (EminD_summable M e b₁).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (min_le_min_right k h)) ENNReal.toReal_nonneg)
    (EminD_summable M e b₂)

private lemma next_inX {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0)
    {a : Action ê} (ha : M.InA a) : M.InX (M.next a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e d hd
    simp only [Model.next]
    rw [if_neg (by omega)]
  · intro e
    have h1 : ∑ d ∈ range (M.U e), (M.next a).d e d =
        ∑ d ∈ range (M.U e), M.mixProb a e d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [Model.next]
      rw [if_pos (le_of_lt (Finset.mem_range.mp hd))]
    rw [h1]
    simp only [Model.mixProb, lam_eq_zero M hq]
    rw [Finset.sum_comm]
    calc ∑ b ∈ Icc (M.L e) (M.U e), ∑ d ∈ range (M.U e), a.d e b * M.transProb e 0 b d
        = ∑ b ∈ Icc (M.L e) (M.U e), a.d e b * ∑ d ∈ range (M.U e), M.transProb e 0 b d := by
            refine Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ b ∈ Icc (M.L e) (M.U e), a.d e b * 1 := by
            refine Finset.sum_le_sum fun b hb => ?_
            exact mul_le_mul_of_nonneg_left
              (transProb_zero_sum_le_one M e (Finset.mem_Icc.mp hb).2) (ha.nonneg e b)
      _ = (M.nst e : ℝ) / M.n := by simp [ha.mass e]
  · intro e
    simp only [Model.next, hq, sub_zero, one_mul]
    refine add_nonneg ((hM.Lr_nonneg e).trans (ha.r_ge e)) ?_
    refine Finset.sum_nonneg fun e' _ => mul_nonneg (p_nonneg M hM e' e) ?_
    exact Finset.sum_nonneg fun b _ => mul_nonneg (ha.nonneg e' b) (EminD_nonneg M e' b)
  · intro e
    simp only [Model.next]
    refine add_le_add (ha.r_le e) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hM.q_le_one])
    refine Finset.sum_le_sum fun e' _ => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (p_nonneg M hM e' e)
    calc ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' b
        ≤ ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' (M.U e') :=
          Finset.sum_le_sum fun b hb =>
            mul_le_mul_of_nonneg_left (EminD_mono M e' (Finset.mem_Icc.mp hb).2) (ha.nonneg e' b)
      _ = (∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b) * M.EminD e' (M.U e') :=
          (Finset.sum_mul _ _ _).symm
      _ = ((M.nst e' : ℝ) / M.n) * M.EminD e' (M.U e') := by rw [ha.mass e']
  · intro e; rw [next_s_eq_zero M hq]
  · intro e
    rw [next_s_eq_zero M hq]
    have hlamU : M.lamU e = 0 := by simp [Model.lamU, hq]
    rw [hlamU]
    exact tsum_nonneg fun d => by
      split_ifs
      · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (n_nonneg M)))
          (transProb_zero_nonneg M e (M.U e) d)
      · exact le_rfl
  · intro e; rw [next_u_eq_zero M hq]
  · intro e
    rw [next_u_eq_zero M hq]
    have hlamU : M.lamU e = 0 := by simp [Model.lamU, hq]
    rw [hlamU]
    exact tsum_nonneg fun d => by
      split_ifs with h
      · have hsub : (0 : ℝ) ≤ (d : ℝ) - (M.U e : ℝ) := by
          have : (M.U e : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr (le_of_lt h)
          linarith
        exact mul_nonneg (mul_nonneg hsub (div_nonneg (Nat.cast_nonneg _) (n_nonneg M)))
          (transProb_zero_nonneg M e (M.U e) d)
      · exact le_rfl

private lemma mixProb_linear {ê : ℕ} (M : Model ê) (hq : M.q = 0)
    (a b : ℝ) (u v : ActVec M) (e : Fin ê) (d : ℕ) :
    M.mixProb (toAction M (a • u + b • v)) e d =
      a * M.mixProb (toAction M u) e d + b * M.mixProb (toAction M v) e d := by
  simp only [Model.mixProb, lam_eq_zero M hq]
  calc ∑ k ∈ Icc (M.L e) (M.U e), (toAction M (a • u + b • v)).d e k * M.transProb e 0 k d
      = ∑ k ∈ Icc (M.L e) (M.U e),
          (a * ((toAction M u).d e k * M.transProb e 0 k d) +
           b * ((toAction M v).d e k * M.transProb e 0 k d)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [toAction_d_add, toAction_d_smul, toAction_d_smul]; ring
    _ = a * ∑ k ∈ Icc (M.L e) (M.U e), (toAction M u).d e k * M.transProb e 0 k d +
        b * ∑ k ∈ Icc (M.L e) (M.U e), (toAction M v).d e k * M.transProb e 0 k d := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private lemma next_d_linear {ê : ℕ} (M : Model ê) (hq : M.q = 0)
    (a b : ℝ) (u v : ActVec M) (e : Fin ê) (d : ℕ) :
    (M.next (toAction M (a • u + b • v))).d e d =
      a * (M.next (toAction M u)).d e d + b * (M.next (toAction M v)).d e d := by
  simp only [Model.next]
  split_ifs
  · exact mixProb_linear M hq a b u v e d
  · ring

private lemma next_r_linear {ê : ℕ} (M : Model ê) (a b : ℝ) (u v : ActVec M) (e : Fin ê) :
    (M.next (toAction M (a • u + b • v))).r e =
      a * (M.next (toAction M u)).r e + b * (M.next (toAction M v)).r e := by
  simp only [Model.next]
  have hsum : ∀ e', ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M (a • u + b • v)).d e' k * M.EminD e' k =
      a * ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M u).d e' k * M.EminD e' k +
      b * ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M v).d e' k * M.EminD e' k := by
    intro e'
    calc ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M (a • u + b • v)).d e' k * M.EminD e' k
        = ∑ k ∈ Icc (M.L e') (M.U e'),
            (a * ((toAction M u).d e' k * M.EminD e' k) +
             b * ((toAction M v).d e' k * M.EminD e' k)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [toAction_d_add, toAction_d_smul, toAction_d_smul]; ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have houter : ∑ e', M.p e' e * ∑ k ∈ Icc (M.L e') (M.U e'),
        (toAction M (a • u + b • v)).d e' k * M.EminD e' k =
      a * ∑ e', M.p e' e * ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M u).d e' k * M.EminD e' k +
      b * ∑ e', M.p e' e * ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M v).d e' k * M.EminD e' k := by
    calc _ = ∑ e',
          (a * (M.p e' e * ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M u).d e' k * M.EminD e' k) +
           b * (M.p e' e * ∑ k ∈ Icc (M.L e') (M.U e'), (toAction M v).d e' k * M.EminD e' k)) := by
          refine Finset.sum_congr rfl fun e' _ => ?_
          rw [hsum e']; ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [houter, toAction_r_add, toAction_r_smul, toAction_r_smul]
  ring

private lemma continuous_next_d {ê : ℕ} (M : Model ê) (hq : M.q = 0) (e : Fin ê) (d : ℕ) :
    Continuous (fun v : ActVec M => (M.next (toAction M v)).d e d) := by
  simp only [Model.next, Model.mixProb, lam_eq_zero M hq]
  by_cases h : d ≤ M.U e
  · simp only [if_pos h]
    exact continuous_finsetSum _ fun b _ => (continuous_toAction_d M e b).mul continuous_const
  · simp only [if_neg h]
    exact continuous_const

private lemma continuous_next_r {ê : ℕ} (M : Model ê) (e : Fin ê) :
    Continuous (fun v : ActVec M => (M.next (toAction M v)).r e) := by
  simp only [Model.next]
  refine (continuous_toAction_r M e).add (continuous_const.mul ?_)
  refine continuous_finsetSum _ fun e' _ => continuous_const.mul ?_
  exact continuous_finsetSum _ fun b _ => (continuous_toAction_d M e' b).mul continuous_const

/-! ## Section 3: Transshipment LP convexity and Lipschitz continuity -/

section Transship

variable {ι κ : Type*} [Fintype ι]

private lemma transshipCost_nonneg [DecidableEq ι] (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (y : ι → ι → ℝ) (hy : ∀ i j, 0 ≤ y i j) : 0 ≤ transshipCost cost y :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hc i j) (hy i j)

private lemma transshipValue_nonneg [DecidableEq ι] (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (b : κ → ℝ) : 0 ≤ transshipValue cost node b := by
  apply Real.sInf_nonneg
  rintro v ⟨y, hy, rfl⟩
  exact transshipCost_nonneg cost hc y hy.1

private lemma transshipValue_le [DecidableEq ι] (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (b : κ → ℝ) (y : ι → ι → ℝ) (hy : TransshipFeasible node b y) :
    transshipValue cost node b ≤ transshipCost cost y :=
  csInf_le ⟨0, by rintro v ⟨y, hy, rfl⟩; exact transshipCost_nonneg cost hc y hy.1⟩ ⟨y, hy, rfl⟩

private lemma transshipCost_add [DecidableEq ι] (cost : ι → ι → ℝ) (y z : ι → ι → ℝ) :
    transshipCost cost (y + z) = transshipCost cost y + transshipCost cost z := by
  unfold transshipCost
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma transshipCost_smul [DecidableEq ι] (cost : ι → ι → ℝ) (t : ℝ) (y : ι → ι → ℝ) :
    transshipCost cost (t • y) = t * transshipCost cost y := by
  unfold transshipCost
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma feasible_add {node : κ → ι} {b b' : κ → ℝ} {y z : ι → ι → ℝ}
    (hy : TransshipFeasible node b y) (hz : TransshipFeasible node b' z) :
    TransshipFeasible node (b + b') (y + z) := by
  refine ⟨fun i j => add_nonneg (hy.1 i j) (hz.1 i j), fun k => ?_⟩
  simp only [Pi.add_apply]
  rw [← hy.2 k, ← hz.2 k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma feasible_smul {node : κ → ι} {b : κ → ℝ} {t : ℝ} (ht : 0 ≤ t) {y : ι → ι → ℝ}
    (hy : TransshipFeasible node b y) : TransshipFeasible node (t • b) (t • y) := by
  refine ⟨fun i j => mul_nonneg ht (hy.1 i j), fun k => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← hy.2 k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma feasible_zero (node : κ → ι) : TransshipFeasible node (0 : κ → ℝ) (0 : ι → ι → ℝ) :=
  ⟨fun _ _ => le_rfl, fun _ => by simp⟩

private noncomputable def hubFlow [DecidableEq ι] [Fintype κ] (node : κ → ι) (o : ι) (b : κ → ℝ) :
    ι → ι → ℝ :=
  fun i j =>
    (if j = o then ∑ k, (if i = node k then max (b k) 0 else 0) else 0) +
    (if i = o then ∑ k, (if j = node k then max (-b k) 0 else 0) else 0)

private lemma hubFlow_feasible [DecidableEq ι] [Fintype κ] (node : κ → ι)
    (hinj : Function.Injective node) (o : ι) (ho : ∀ k, node k ≠ o) (b : κ → ℝ) :
    TransshipFeasible node b (hubFlow node o b) := by
  refine ⟨fun i j => ?_, fun k => ?_⟩
  · unfold hubFlow
    refine add_nonneg ?_ ?_
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
  · have hs : ∀ (f : κ → ℝ), ∑ k', (if node k = node k' then f k' else 0) = f k := by
      intro f
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hk'; rw [if_neg]; intro h; exact hk' (hinj h).symm
      · simp
    have hA : ∀ j, hubFlow node o b (node k) j = if j = o then max (b k) 0 else 0 := by
      intro j; unfold hubFlow; rw [if_neg (ho k), add_zero]
      split_ifs
      · exact hs _
      · rfl
    have hB : ∀ j, hubFlow node o b j (node k) = if j = o then max (-b k) 0 else 0 := by
      intro j; unfold hubFlow; rw [if_neg (ho k), zero_add]
      split_ifs
      · exact hs _
      · rfl
    simp only [hA, hB, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases le_total 0 (b k) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring

private lemma hubFlow_cost_le [DecidableEq ι] [Fintype κ] (cost : ι → ι → ℝ)
    (hc : ∀ i j, 0 ≤ cost i j) (node : κ → ι) (o : ι) (b : κ → ℝ) :
    transshipCost cost (hubFlow node o b) ≤
      ∑ k, (cost (node k) o * max (b k) 0 + cost o (node k) * max (-b k) 0) := by
  have hnn : ∀ i j, 0 ≤ hubFlow node o b i j := by
    intro i j; unfold hubFlow
    refine add_nonneg ?_ ?_
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
  calc transshipCost cost (hubFlow node o b)
      ≤ ∑ i, ∑ j, cost i j * hubFlow node o b i j := by
        unfold transshipCost
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun j _ _ => mul_nonneg (hc i j) (hnn i j)
    _ = (∑ i, ∑ j, cost i j * (if j = o then ∑ k, (if i = node k then max (b k) 0 else 0) else 0)) +
        (∑ i, ∑ j, cost i j * (if i = o then ∑ k, (if j = node k then max (-b k) 0 else 0) else 0)) := by
        unfold hubFlow
        simp only [mul_add, Finset.sum_add_distrib]
    _ = (∑ k, cost (node k) o * max (b k) 0) + (∑ k, cost o (node k) * max (-b k) 0) := by
        congr 1
        · calc ∑ i, ∑ j, cost i j * (if j = o then ∑ k, (if i = node k then max (b k) 0 else 0) else 0)
              = ∑ i, cost i o * ∑ k, (if i = node k then max (b k) 0 else 0) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
            _ = ∑ i, ∑ k, (if i = node k then cost i o * max (b k) 0 else 0) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
            _ = ∑ k, ∑ i, (if i = node k then cost i o * max (b k) 0 else 0) := Finset.sum_comm
            _ = ∑ k, cost (node k) o * max (b k) 0 := by
                  refine Finset.sum_congr rfl fun k _ => by simp
        · calc ∑ i, ∑ j, cost i j * (if i = o then ∑ k, (if j = node k then max (-b k) 0 else 0) else 0)
              = ∑ j, ∑ i, (if i = o then cost i j * ∑ k, (if j = node k then max (-b k) 0 else 0) else 0) := by
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
                    split_ifs <;> ring
            _ = ∑ j, cost o j * ∑ k, (if j = node k then max (-b k) 0 else 0) := by
                  refine Finset.sum_congr rfl fun j _ => by simp
            _ = ∑ j, ∑ k, (if j = node k then cost o j * max (-b k) 0 else 0) := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
            _ = ∑ k, ∑ j, (if j = node k then cost o j * max (-b k) 0 else 0) := Finset.sum_comm
            _ = ∑ k, cost o (node k) * max (-b k) 0 := by
                  refine Finset.sum_congr rfl fun k _ => by simp
    _ = ∑ k, (cost (node k) o * max (b k) 0 + cost o (node k) * max (-b k) 0) :=
        (Finset.sum_add_distrib).symm

private lemma transshipValue_le_const_mul_norm [DecidableEq ι] [Fintype κ]
    (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (hinj : Function.Injective node) (o : ι) (ho : ∀ k, node k ≠ o) (b : κ → ℝ) :
    transshipValue cost node b ≤ (∑ k, (cost (node k) o + cost o (node k))) * ‖b‖ := by
  calc transshipValue cost node b
      ≤ transshipCost cost (hubFlow node o b) :=
        transshipValue_le cost hc node b _ (hubFlow_feasible node hinj o ho b)
    _ ≤ ∑ k, (cost (node k) o * max (b k) 0 + cost o (node k) * max (-b k) 0) :=
        hubFlow_cost_le cost hc node o b
    _ ≤ ∑ k, (cost (node k) o + cost o (node k)) * ‖b‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hbk : |b k| ≤ ‖b‖ := norm_le_pi_norm b k
        have h1 : max (b k) 0 ≤ ‖b‖ := max_le ((le_abs_self _).trans hbk) (norm_nonneg b)
        have h2 : max (-b k) 0 ≤ ‖b‖ := max_le ((neg_le_abs _).trans hbk) (norm_nonneg b)
        have hc1 := hc (node k) o
        have hc2 := hc o (node k)
        nlinarith
    _ = (∑ k, (cost (node k) o + cost o (node k))) * ‖b‖ := (Finset.sum_mul _ _ _).symm

private lemma transshipValue_subadd [DecidableEq ι] [Fintype κ]
    (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (hinj : Function.Injective node) (o : ι) (ho : ∀ k, node k ≠ o)
    (b₁ b₂ : κ → ℝ) :
    transshipValue cost node (b₁ + b₂) ≤
      transshipValue cost node b₁ + transshipValue cost node b₂ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hne₁ : {v : ℝ | ∃ y, TransshipFeasible node b₁ y ∧ v = transshipCost cost y}.Nonempty :=
    ⟨_, hubFlow node o b₁, hubFlow_feasible node hinj o ho b₁, rfl⟩
  have hne₂ : {v : ℝ | ∃ y, TransshipFeasible node b₂ y ∧ v = transshipCost cost y}.Nonempty :=
    ⟨_, hubFlow node o b₂, hubFlow_feasible node hinj o ho b₂, rfl⟩
  obtain ⟨v₁, ⟨y₁, hy₁, rfl⟩, hv₁⟩ :=
    exists_lt_of_csInf_lt hne₁ (lt_add_of_pos_right (transshipValue cost node b₁) (half_pos hε))
  obtain ⟨v₂, ⟨y₂, hy₂, rfl⟩, hv₂⟩ :=
    exists_lt_of_csInf_lt hne₂ (lt_add_of_pos_right (transshipValue cost node b₂) (half_pos hε))
  have hle := transshipValue_le cost hc node (b₁ + b₂) (y₁ + y₂) (feasible_add hy₁ hy₂)
  rw [transshipCost_add] at hle
  linarith

private lemma transshipValue_smul_le [DecidableEq ι] [Fintype κ]
    (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (hinj : Function.Injective node) (o : ι) (ho : ∀ k, node k ≠ o)
    {t : ℝ} (ht : 0 ≤ t) (b : κ → ℝ) :
    transshipValue cost node (t • b) ≤ t * transshipValue cost node b := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp only [zero_smul, zero_mul]
    have hle := transshipValue_le cost hc node 0 0 (feasible_zero node)
    have h0 : transshipCost cost (0 : ι → ι → ℝ) = 0 := by simp [transshipCost]
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hne : {v : ℝ | ∃ y, TransshipFeasible node b y ∧ v = transshipCost cost y}.Nonempty :=
      ⟨_, hubFlow node o b, hubFlow_feasible node hinj o ho b, rfl⟩
    obtain ⟨v, ⟨y, hy, rfl⟩, hv⟩ :=
      exists_lt_of_csInf_lt hne (lt_add_of_pos_right (transshipValue cost node b) (div_pos hε htpos))
    have hle := transshipValue_le cost hc node (t • b) (t • y) (feasible_smul ht hy)
    rw [transshipCost_smul] at hle
    have hmul : t * transshipCost cost y < t * (transshipValue cost node b + ε / t) :=
      mul_lt_mul_of_pos_left hv htpos
    have hsimp : t * (transshipValue cost node b + ε / t) = t * transshipValue cost node b + ε := by
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt htpos)]
    linarith

private lemma transshipValue_convex [DecidableEq ι] [Fintype κ]
    (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (hinj : Function.Injective node) (o : ι) (ho : ∀ k, node k ≠ o) :
    ConvexOn ℝ Set.univ (transshipValue cost node) := by
  refine ⟨convex_univ, fun b₁ _ b₂ _ a b ha hb _ => ?_⟩
  calc transshipValue cost node (a • b₁ + b • b₂)
      ≤ transshipValue cost node (a • b₁) + transshipValue cost node (b • b₂) :=
        transshipValue_subadd cost hc node hinj o ho (a • b₁) (b • b₂)
    _ ≤ a * transshipValue cost node b₁ + b * transshipValue cost node b₂ :=
        add_le_add (transshipValue_smul_le cost hc node hinj o ho ha b₁)
          (transshipValue_smul_le cost hc node hinj o ho hb b₂)

private lemma transshipValue_continuous [DecidableEq ι] [Fintype κ]
    (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (hinj : Function.Injective node) (o : ι) (ho : ∀ k, node k ≠ o) :
    Continuous (transshipValue cost node) := by
  set K : ℝ := ∑ k, (cost (node k) o + cost o (node k))
  have hK : 0 ≤ K := Finset.sum_nonneg fun k _ => add_nonneg (hc (node k) o) (hc o (node k))
  let Knn : NNReal := ⟨K, hK⟩
  refine (LipschitzWith.of_dist_le_mul (K := Knn) fun b₁ b₂ => ?_).continuous
  change dist (transshipValue cost node b₁) (transshipValue cost node b₂) ≤ K * dist b₁ b₂
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  constructor
  · have h := transshipValue_subadd cost hc node hinj o ho b₁ (b₂ - b₁)
    rw [add_sub_cancel] at h
    have hb := transshipValue_le_const_mul_norm cost hc node hinj o ho (b₂ - b₁)
    rw [norm_sub_rev] at hb
    linarith
  · have h := transshipValue_subadd cost hc node hinj o ho b₂ (b₁ - b₂)
    rw [add_sub_cancel] at h
    have hb := transshipValue_le_const_mul_norm cost hc node hinj o ho (b₁ - b₂)
    linarith

end Transship

private lemma flowCoeff_nonneg {ê : ℕ} (M : Model ê) (hM : M.Standing)
    (e1 e2 : Fin (2 * ê + 1)) : 0 ≤ M.flowCoeff e1 e2 := by
  unfold Model.flowCoeff
  linarith [hM.c_triangle e1 e2]

private lemma extNode_injective {ê : ℕ} : Function.Injective (Model.extNode (ê := ê)) := by
  intro x y h
  cases x with
  | inl e1 =>
    cases y with
    | inl e2 =>
      simp only [Model.extNode, Sum.elim_inl, chg, Fin.mk.injEq] at h
      exact congrArg Sum.inl (Fin.ext (by omega))
    | inr e2 =>
      simp only [Model.extNode, Sum.elim_inl, Sum.elim_inr, chg, dep, Fin.mk.injEq] at h
      omega
  | inr e1 =>
    cases y with
    | inl e2 =>
      simp only [Model.extNode, Sum.elim_inl, Sum.elim_inr, chg, dep, Fin.mk.injEq] at h
      omega
    | inr e2 =>
      simp only [Model.extNode, Sum.elim_inr, dep, Fin.mk.injEq] at h
      exact congrArg Sum.inr (Fin.ext (by omega))

private lemma extNode_ne_zero {ê : ℕ} (k : Fin ê ⊕ Fin ê) :
    Model.extNode k ≠ (0 : Fin (2 * ê + 1)) := by
  cases k with
  | inl e => simp [Model.extNode, chg, Fin.ext_iff]
  | inr e => simp [Model.extNode, dep, Fin.ext_iff]

/-! ## Section 4: Joint convexity and continuity of `stageG` and `Fmap` -/

private noncomputable def stageG {ê : ℕ} (M : Model ê) (p : ActVec M × ActVec M) : ℝ :=
  M.c2 (M.next (toAction M p.1)) (toAction M p.2) + M.Nhat (toAction M p.2)

private noncomputable def Fmap {ê : ℕ} (M : Model ê) (u v : ActVec M) : ℝ :=
  stageG M ((1 - M.γ) • u + M.γ • v, v)

private lemma flowSupply_next_linear {ê : ℕ} (M : Model ê) (hq : M.q = 0)
    (a b : ℝ) (p₁ p₂ : ActVec M × ActVec M) :
    M.flowSupply (M.next (toAction M (a • p₁.1 + b • p₂.1))) (toAction M (a • p₁.2 + b • p₂.2)) =
      a • M.flowSupply (M.next (toAction M p₁.1)) (toAction M p₁.2) +
      b • M.flowSupply (M.next (toAction M p₂.1)) (toAction M p₂.2) := by
  ext k
  cases k with
  | inl e =>
    simp only [Model.flowSupply, Sum.elim_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      next_s_eq_zero M hq, zero_add]
    calc ∑ d ∈ Icc 1 (M.U e), (d : ℝ) *
            ((M.next (toAction M (a • p₁.1 + b • p₂.1))).d e d -
             (toAction M (a • p₁.2 + b • p₂.2)).d e d)
        = ∑ d ∈ Icc 1 (M.U e),
            (a * ((d : ℝ) * ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d)) +
             b * ((d : ℝ) * ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d))) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [next_d_linear M hq, toAction_d_add, toAction_d_smul, toAction_d_smul]; ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  | inr e =>
    simp only [Model.flowSupply, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [next_r_linear M, toAction_r_add, toAction_r_smul, toAction_r_smul]
    ring

private lemma continuous_flowSupply_next {ê : ℕ} (M : Model ê) (hq : M.q = 0) :
    Continuous (fun p : ActVec M × ActVec M =>
      M.flowSupply (M.next (toAction M p.1)) (toAction M p.2)) := by
  refine continuous_pi fun k => ?_
  cases k with
  | inl e =>
    simp only [Model.flowSupply, Sum.elim_inl, next_s_eq_zero M hq, zero_add]
    exact continuous_finsetSum _ fun b _ =>
      continuous_const.mul
        (((continuous_next_d M hq e b).comp continuous_fst).sub
          ((continuous_toAction_d M e b).comp continuous_snd))
  | inr e =>
    simp only [Model.flowSupply, Sum.elim_inr]
    exact ((continuous_next_r M e).comp continuous_fst).sub
      ((continuous_toAction_r M e).comp continuous_snd)

private lemma Nhat_linear {ê : ℕ} (M : Model ê) (a b : ℝ) (u v : ActVec M) :
    M.Nhat (toAction M (a • u + b • v)) =
      a * M.Nhat (toAction M u) + b * M.Nhat (toAction M v) := by
  unfold Model.Nhat
  have h1 : ∑ e, ∑ d ∈ Icc (M.L e) (M.U e), (d : ℝ) * (toAction M (a • u + b • v)).d e d =
      a * (∑ e, ∑ d ∈ Icc (M.L e) (M.U e), (d : ℝ) * (toAction M u).d e d) +
      b * (∑ e, ∑ d ∈ Icc (M.L e) (M.U e), (d : ℝ) * (toAction M v).d e d) := by
    have : ∀ e, ∑ d ∈ Icc (M.L e) (M.U e), (d : ℝ) * (toAction M (a • u + b • v)).d e d =
        a * ∑ d ∈ Icc (M.L e) (M.U e), (d : ℝ) * (toAction M u).d e d +
        b * ∑ d ∈ Icc (M.L e) (M.U e), (d : ℝ) * (toAction M v).d e d := fun e => by
      calc _ = ∑ d ∈ Icc (M.L e) (M.U e),
              (a * ((d : ℝ) * (toAction M u).d e d) + b * ((d : ℝ) * (toAction M v).d e d)) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [toAction_d_add, toAction_d_smul, toAction_d_smul]; ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ e, (toAction M (a • u + b • v)).r e =
      a * (∑ e, (toAction M u).r e) + b * (∑ e, (toAction M v).r e) := by
    simp_rw [toAction_r_add, toAction_r_smul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h3 : ∑ e, ∑ d ∈ Icc (M.L e) (M.U e), (toAction M (a • u + b • v)).d e d * M.EposD e d =
      a * (∑ e, ∑ d ∈ Icc (M.L e) (M.U e), (toAction M u).d e d * M.EposD e d) +
      b * (∑ e, ∑ d ∈ Icc (M.L e) (M.U e), (toAction M v).d e d * M.EposD e d) := by
    have : ∀ e, ∑ d ∈ Icc (M.L e) (M.U e), (toAction M (a • u + b • v)).d e d * M.EposD e d =
        a * ∑ d ∈ Icc (M.L e) (M.U e), (toAction M u).d e d * M.EposD e d +
        b * ∑ d ∈ Icc (M.L e) (M.U e), (toAction M v).d e d * M.EposD e d := fun e => by
      calc _ = ∑ d ∈ Icc (M.L e) (M.U e),
              (a * ((toAction M u).d e d * M.EposD e d) +
               b * ((toAction M v).d e d * M.EposD e d)) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [toAction_d_add, toAction_d_smul, toAction_d_smul]; ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3]; ring

private lemma continuous_Nhat {ê : ℕ} (M : Model ê) :
    Continuous (fun v : ActVec M => M.Nhat (toAction M v)) := by
  unfold Model.Nhat
  refine ((continuous_const.mul (continuous_finsetSum _ fun e _ =>
      continuous_finsetSum _ fun b _ => continuous_const.mul (continuous_toAction_d M e b))).add
    (continuous_const.mul (continuous_finsetSum _ fun e _ => continuous_toAction_r M e))).add
    (continuous_const.mul (continuous_finsetSum _ fun e _ =>
      continuous_finsetSum _ fun b _ => (continuous_toAction_d M e b).mul continuous_const))

private lemma stageG_continuous {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) :
    Continuous (stageG M) := by
  unfold stageG Model.c2 Model.flowValue
  simp_rw [next_u_eq_zero M hq, mul_zero, Finset.sum_const_zero, mul_zero, zero_add]
  refine Continuous.add ?_ ((continuous_Nhat M).comp continuous_snd)
  refine Continuous.add ?_ ?_
  · refine continuous_const.mul (continuous_finsetSum _ fun e _ => continuous_const.mul ?_)
    refine continuous_finsetSum _ fun b _ => Continuous.abs ?_
    exact continuous_finsetSum _ fun d _ =>
      ((continuous_next_d M hq e d).comp continuous_fst).sub
        ((continuous_toAction_d M e d).comp continuous_snd)
  · exact continuous_const.mul
      ((transshipValue_continuous M.flowCoeff (flowCoeff_nonneg M hM)
        Model.extNode extNode_injective 0 extNode_ne_zero).comp (continuous_flowSupply_next M hq))

private lemma stageG_convex {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) :
    ConvexOn ℝ Set.univ (stageG M) := by
  refine ⟨convex_univ, fun p₁ _ p₂ _ a b ha hb hab => ?_⟩
  unfold stageG Model.c2 Model.flowValue
  simp_rw [next_u_eq_zero M hq, mul_zero, Finset.sum_const_zero, mul_zero, zero_add]
  have h1 : M.n * ∑ e, M.c (chg e) (chg e) / 2 *
        ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
          ((M.next (toAction M (a • p₁.1 + b • p₂.1))).d e d -
           (toAction M (a • p₁.2 + b • p₂.2)).d e d)| ≤
      a * (M.n * ∑ e, M.c (chg e) (chg e) / 2 *
        ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
          ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d)|) +
      b * (M.n * ∑ e, M.c (chg e) (chg e) / 2 *
        ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
          ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d)|) := by
    have hinner : ∀ e k,
        |∑ d ∈ range (k + 1),
          ((M.next (toAction M (a • p₁.1 + b • p₂.1))).d e d -
           (toAction M (a • p₁.2 + b • p₂.2)).d e d)| ≤
        a * |∑ d ∈ range (k + 1), ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d)| +
        b * |∑ d ∈ range (k + 1), ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d)| := by
      intro e k
      have hlin : ∑ d ∈ range (k + 1),
            ((M.next (toAction M (a • p₁.1 + b • p₂.1))).d e d -
             (toAction M (a • p₁.2 + b • p₂.2)).d e d) =
          a * ∑ d ∈ range (k + 1), ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d) +
          b * ∑ d ∈ range (k + 1), ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d) := by
        calc _ = ∑ d ∈ range (k + 1),
              (a * ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d) +
               b * ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d)) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [next_d_linear M hq, toAction_d_add, toAction_d_smul, toAction_d_smul]; ring
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hlin]
      calc |a * _ + b * _|
          ≤ |a * _| + |b * _| := abs_add_le _ _
        _ = a * |_| + b * |_| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have hsum : ∑ e, M.c (chg e) (chg e) / 2 *
          ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
            ((M.next (toAction M (a • p₁.1 + b • p₂.1))).d e d -
             (toAction M (a • p₁.2 + b • p₂.2)).d e d)| ≤
        a * ∑ e, M.c (chg e) (chg e) / 2 *
          ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
            ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d)| +
        b * ∑ e, M.c (chg e) (chg e) / 2 *
          ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
            ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d)| := by
      calc _ ≤ ∑ e, M.c (chg e) (chg e) / 2 *
            ∑ k ∈ range (M.U e),
              (a * |∑ d ∈ range (k + 1), ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d)| +
               b * |∑ d ∈ range (k + 1), ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d)|) :=
            Finset.sum_le_sum fun e _ =>
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hinner e k)
                (div_nonneg (hM.c_nonneg _ _) (by norm_num))
        _ = ∑ e, (a * (M.c (chg e) (chg e) / 2 *
              ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
                ((M.next (toAction M p₁.1)).d e d - (toAction M p₁.2).d e d)|) +
            b * (M.c (chg e) (chg e) / 2 *
              ∑ k ∈ range (M.U e), |∑ d ∈ range (k + 1),
                ((M.next (toAction M p₂.1)).d e d - (toAction M p₂.2).d e d)|)) := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hsum (n_nonneg M)
    linarith
  have h2 : M.n * transshipValue M.flowCoeff Model.extNode
        (M.flowSupply (M.next (toAction M (a • p₁.1 + b • p₂.1)))
          (toAction M (a • p₁.2 + b • p₂.2))) ≤
      a * (M.n * transshipValue M.flowCoeff Model.extNode
        (M.flowSupply (M.next (toAction M p₁.1)) (toAction M p₁.2))) +
      b * (M.n * transshipValue M.flowCoeff Model.extNode
        (M.flowSupply (M.next (toAction M p₂.1)) (toAction M p₂.2))) := by
    rw [flowSupply_next_linear M hq]
    have hcvx := (transshipValue_convex M.flowCoeff (flowCoeff_nonneg M hM)
      Model.extNode extNode_injective 0 extNode_ne_zero).2
      (Set.mem_univ (M.flowSupply (M.next (toAction M p₁.1)) (toAction M p₁.2)))
      (Set.mem_univ (M.flowSupply (M.next (toAction M p₂.1)) (toAction M p₂.2)))
      ha hb hab
    simp only [smul_eq_mul] at hcvx
    have := mul_le_mul_of_nonneg_left hcvx (n_nonneg M)
    linarith
  have h3 : M.Nhat (toAction M (a • p₁.2 + b • p₂.2)) =
      a * M.Nhat (toAction M p₁.2) + b * M.Nhat (toAction M p₂.2) :=
    Nhat_linear M a b p₁.2 p₂.2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linarith

private lemma Fmap_continuous {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) :
    Continuous (fun p : ActVec M × ActVec M => Fmap M p.1 p.2) := by
  have h1 : Continuous (fun p : ActVec M × ActVec M => (1 - M.γ) • p.1 + M.γ • p.2) :=
    (continuous_fst.const_smul (1 - M.γ)).add (continuous_snd.const_smul M.γ)
  exact (stageG_continuous M hM hq).comp (h1.prodMk continuous_snd)

private lemma Fmap_continuous_right {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0)
    (u : ActVec M) : Continuous (fun v : ActVec M => Fmap M u v) := by
  have h1 : Continuous (fun v : ActVec M => (1 - M.γ) • u + M.γ • v) :=
    continuous_const.add (continuous_id.const_smul M.γ)
  exact (stageG_continuous M hM hq).comp (h1.prodMk continuous_id)

private lemma Fmap_convex_right {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0)
    (u : ActVec M) : ConvexOn ℝ Set.univ (fun v => Fmap M u v) := by
  refine ⟨convex_univ, fun v₁ _ v₂ _ a b ha hb hab => ?_⟩
  have hpair : ((1 - M.γ) • u + M.γ • (a • v₁ + b • v₂), a • v₁ + b • v₂) =
      a • ((1 - M.γ) • u + M.γ • v₁, v₁) + b • ((1 - M.γ) • u + M.γ • v₂, v₂) := by
    refine Prod.ext ?_ rfl
    simp only [Prod.fst_add, Prod.smul_fst, smul_add, smul_smul]
    have hu : (1 - M.γ) • u = (a * (1 - M.γ)) • u + (b * (1 - M.γ)) • u := by
      rw [← add_smul, ← add_mul, hab, one_mul]
    rw [hu, mul_comm M.γ a, mul_comm M.γ b]
    abel
  unfold Fmap
  dsimp only
  rw [hpair]
  exact (stageG_convex M hM hq).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

private lemma Fmap_diag {ê : ℕ} (M : Model ê) (u : ActVec M) :
    Fmap M u u = stageG M (u, u) := by
  unfold Fmap
  have : (1 - M.γ) • u + M.γ • u = u := by
    rw [← add_smul]; simp
  rw [this]

/-! ## Section 5: Fixed point via Kakutani–Fan–Glicksberg -/

private lemma exists_argmin_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKne : K.Nonempty) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (F : E → E → ℝ) (hFcont : Continuous (fun p : E × E => F p.1 p.2))
    (hFconv : ∀ u ∈ K, ConvexOn ℝ Set.univ (fun v => F u v)) :
    ∃ u ∈ K, ∀ w ∈ K, F u u ≤ F u w := by
  let Φ : E → Set E := fun u => { v ∈ K | ∀ w ∈ K, F u v ≤ F u w }
  have hFright : ∀ u : E, Continuous (fun v : E => F u v) := fun u =>
    hFcont.comp ((continuous_const (y := u)).prodMk continuous_id)
  have hΦsub : ∀ u ∈ K, Φ u ⊆ K := fun _ _ _ hv => hv.1
  have hΦne : ∀ u ∈ K, (Φ u).Nonempty := by
    intro u _
    obtain ⟨v, hvK, hmin⟩ := hKc.exists_isMinOn hKne (hFright u).continuousOn
    exact ⟨v, hvK, fun w hw => hmin hw⟩
  have hΦconv : ∀ u ∈ K, Convex ℝ (Φ u) := by
    intro u hu v₁ hv₁ v₂ hv₂ a b ha hb hab
    refine ⟨hKconv hv₁.1 hv₂.1 ha hb hab, fun w hw => ?_⟩
    have hcvx := (hFconv u hu).2 (Set.mem_univ v₁) (Set.mem_univ v₂) ha hb hab
    simp only [smul_eq_mul] at hcvx
    calc F u (a • v₁ + b • v₂)
        ≤ a * F u v₁ + b * F u v₂ := hcvx
      _ ≤ a * F u w + b * F u w :=
          add_le_add (mul_le_mul_of_nonneg_left (hv₁.2 w hw) ha)
            (mul_le_mul_of_nonneg_left (hv₂.2 w hw) hb)
      _ = F u w := by rw [← add_mul, hab, one_mul]
  have hΦclosed : ∀ u ∈ K, IsClosed (Φ u) := by
    intro u _
    have heq : Φ u = K ∩ ⋂ w ∈ K, {v : E | F u v ≤ F u w} := by
      ext v; simp [Φ]
    rw [heq]
    refine hKc.isClosed.inter (isClosed_biInter fun w _ => ?_)
    exact isClosed_le (hFright u) continuous_const
  have hΦuhc : UpperHemicontinuousOn Φ K := by
    refine UpperHemicontinuousOn.of_forall_isOpen fun u hu U hU hsub => ?_
    by_contra hnot
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ p : E × E,
        p.1 ∈ K ∧ dist p.1 u < 1 / ((n : ℝ) + 1) ∧ p.2 ∈ Φ p.1 ∧ p.2 ∉ U := by
      intro n
      have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hnsub := hnot (1 / ((n : ℝ) + 1)) hε
      rw [Set.not_subset] at hnsub
      obtain ⟨u', ⟨hu'ball, hu'K⟩, hnotSub⟩ := hnsub
      simp only [Set.mem_ofPred_eq] at hnotSub
      rw [Set.not_subset] at hnotSub
      obtain ⟨v', hv'best, hv'notU⟩ := hnotSub
      exact ⟨(u', v'), hu'K, Metric.mem_ball.mp hu'ball, hv'best, hv'notU⟩
    choose ps hps using hex
    let us : ℕ → E := fun n => (ps n).1
    let vs : ℕ → E := fun n => (ps n).2
    have hus_lim : Tendsto us atTop (𝓝 u) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      have h1 : dist (us n) u < 1 / ((n : ℝ) + 1) := (hps n).2.1
      have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
      linarith
    have hKdiff : IsCompact (K \ U) := hKc.diff hU
    have hvs_mem : ∀ n, vs n ∈ K \ U := fun n => ⟨(hps n).2.2.1.1, (hps n).2.2.2⟩
    obtain ⟨v, hv_mem, φ, hφ, hvs_lim⟩ := hKdiff.tendsto_subseq hvs_mem
    have hus_sub : Tendsto (us ∘ φ) atTop (𝓝 u) := hus_lim.comp hφ.tendsto_atTop
    have hv_best : v ∈ Φ u := by
      refine ⟨hv_mem.1, fun w hw => ?_⟩
      have hL : Tendsto (fun n => F (us (φ n)) (vs (φ n))) atTop (𝓝 (F u v)) :=
        (hFcont.tendsto (u, v)).comp (hus_sub.prodMk_nhds hvs_lim)
      have hR : Tendsto (fun n => F (us (φ n)) w) atTop (𝓝 (F u w)) :=
        (hFcont.tendsto (u, w)).comp (hus_sub.prodMk_nhds (tendsto_const_nhds (x := w)))
      exact le_of_tendsto_of_tendsto hL hR
        (Eventually.of_forall fun n => (hps (φ n)).2.2.1.2 w hw)
    exact hv_mem.2 (hsub hv_best)
  obtain ⟨u, huK, huFixed⟩ :=
    FanGlicksberg.kakutani_fan_glicksberg K hKne hKc hKconv
      Φ hΦuhc hΦsub hΦne hΦconv hΦclosed
  exact ⟨u, huK, huFixed.2⟩

private lemma exists_Fmap_fixed {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) :
    ∃ u ∈ actSet M, ∀ w ∈ actSet M, Fmap M u u ≤ Fmap M u w :=
  exists_argmin_fixed (actSet_nonempty M hM) (actSet_isCompact M hM) (actSet_convex M)
    (Fmap M) (Fmap_continuous M hM hq) (fun u _ => Fmap_convex_right M hM hq u)

/-! ## Section 6: Discounted Jensen inequality and optimality at the fixed point -/

private lemma stageG_bounded {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ actSet M, ∀ q ∈ actSet M, |stageG M (p, q)| ≤ B := by
  have hKc := (actSet_isCompact M hM).prod (actSet_isCompact M hM)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (stageG_continuous M hM hq).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p hp q hq' => ?_⟩
  have := hC (p, q) ⟨hp, hq'⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

private lemma traj_eq_next_seq {ê : ℕ} (M : Model ê) (p₀ : ActVec M) (a : ℕ → Action ê)
    (ha : ∀ k, M.InA (a k)) (k : ℕ) :
    M.traj (M.next (toAction M p₀)) a k =
      M.next (toAction M (match k with | 0 => p₀ | j + 1 => ofAction M (a j))) := by
  cases k with
  | zero => rfl
  | succ j =>
    simp only [Model.traj, DetDP.traj, Model.dp]
    rw [toAction_ofAction M (ha j)]

private lemma J_summable_of_next {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0)
    {p₀ : ActVec M} (hp₀ : p₀ ∈ actSet M) (a : ℕ → Action ê) (ha : ∀ k, M.InA (a k)) :
    Summable (fun k : ℕ => M.γ ^ k * (M.c2 (M.traj (M.next (toAction M p₀)) a k) (a k) + M.Nhat (a k))) := by
  obtain ⟨B, _, hbound⟩ := stageG_bounded M hM hq
  refine Summable.of_norm_bounded (g := fun k : ℕ => B * M.γ ^ k)
    ((summable_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one).mul_left B) fun k => ?_
  let pk : ActVec M := match k with | 0 => p₀ | j + 1 => ofAction M (a j)
  have hmem : pk ∈ actSet M := by
    cases k with
    | zero => exact hp₀
    | succ j => exact ofAction_mem_actSet M (ha j)
  have htraj : M.traj (M.next (toAction M p₀)) a k = M.next (toAction M pk) :=
    traj_eq_next_seq M p₀ a ha k
  rw [htraj]
  have hstage : M.c2 (M.next (toAction M pk)) (a k) + M.Nhat (a k) =
      stageG M (pk, ofAction M (a k)) := by
    unfold stageG
    rw [toAction_ofAction M (ha k)]
  rw [hstage, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hM.gamma_nonneg k)]
  have hle := hbound pk hmem (ofAction M (a k)) (ofAction_mem_actSet M (ha k))
  rw [mul_comm B (M.γ ^ k)]
  exact mul_le_mul_of_nonneg_left hle (pow_nonneg hM.gamma_nonneg k)

private lemma J_ge_fixed {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0)
    {u : ActVec M} (hu : u ∈ actSet M)
    (hfix : ∀ w ∈ actSet M, Fmap M u u ≤ Fmap M u w)
    (a : ℕ → Action ê) (ha : ∀ k, M.InA (a k)) :
    stageG M (u, u) ≤ (1 - M.γ) * M.J (M.next (toAction M u)) a := by
  let v : ℕ → ActVec M := fun k => ofAction M (a k)
  let u_seq : ℕ → ActVec M := fun k => match k with | 0 => u | j + 1 => v j
  have hv_mem : ∀ k, v k ∈ actSet M := fun k => ofAction_mem_actSet M (ha k)
  have hu_mem : ∀ k, u_seq k ∈ actSet M := fun k => by
    cases k with
    | zero => exact hu
    | succ j => exact hv_mem j
  -- Summability of `γ^k • v k`
  obtain ⟨R, hR⟩ := (actSet_isCompact M hM).isBounded.subset_closedBall (0 : ActVec M)
  have hRnn : 0 ≤ R := by
    have h0 := hR hu
    rw [Metric.mem_closedBall, dist_zero_right] at h0
    exact (norm_nonneg u).trans h0
  have hv_summable : Summable (fun k : ℕ => M.γ ^ k • v k) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => M.γ ^ k * R)
      ((summable_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one).mul_right R) fun k => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hM.gamma_nonneg k)]
    have hk := hR (hv_mem k)
    rw [Metric.mem_closedBall, dist_zero_right] at hk
    exact mul_le_mul_of_nonneg_left hk (pow_nonneg hM.gamma_nonneg k)
  let S_v : ActVec M := ∑' k : ℕ, M.γ ^ k • v k
  let vbar : ActVec M := (1 - M.γ) • S_v
  -- Weight normalization factor `c N = (1 - γ) / (1 - γ^(N+1))`
  let c : ℕ → ℝ := fun N => (1 - M.γ) / (1 - M.γ ^ (N + 1))
  have hc_lim : Tendsto c atTop (𝓝 (1 - M.γ)) := by
    have hpow : Tendsto (fun N : ℕ => M.γ ^ (N + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hM.gamma_nonneg hM.gamma_lt_one).comp
        (tendsto_add_atTop_nat 1)
    have hden : Tendsto (fun N : ℕ => 1 - M.γ ^ (N + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hpow
    have hdiv : Tendsto (fun N : ℕ => (1 - M.γ) / (1 - M.γ ^ (N + 1))) atTop (𝓝 ((1 - M.γ) / (1 - 0))) :=
      tendsto_const_nhds.div hden (by norm_num)
    simpa [c] using hdiv
  have hV_lim : Tendsto (fun N : ℕ => c N • ∑ k ∈ range (N + 1), M.γ ^ k • v k) atTop (𝓝 vbar) := by
    have hpart : Tendsto (fun N : ℕ => ∑ k ∈ range (N + 1), M.γ ^ k • v k) atTop (𝓝 S_v) :=
      hv_summable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact hc_lim.smul hpart
  have hU_lim : Tendsto (fun N : ℕ => c N • ∑ k ∈ range (N + 1), M.γ ^ k • u_seq k)
      atTop (𝓝 ((1 - M.γ) • u + M.γ • vbar)) := by
    have hsplit : ∀ N : ℕ, ∑ k ∈ range (N + 1), M.γ ^ k • u_seq k =
        M.γ • (∑ k ∈ range N, M.γ ^ k • v k) + u := by
      intro N
      rw [Finset.sum_range_succ']
      simp only [u_seq, pow_zero, one_smul]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ', smul_smul]
    simp_rw [hsplit]
    have hpart : Tendsto (fun N : ℕ => ∑ k ∈ range N, M.γ ^ k • v k) atTop (𝓝 S_v) :=
      hv_summable.hasSum.tendsto_sum_nat
    have h1 : Tendsto (fun N : ℕ => c N • (M.γ • (∑ k ∈ range N, M.γ ^ k • v k) + u))
        atTop (𝓝 ((1 - M.γ) • (M.γ • S_v + u))) :=
      hc_lim.smul ((tendsto_const_nhds.smul hpart).add tendsto_const_nhds)
    have heq : (1 - M.γ) • (M.γ • S_v + u) = (1 - M.γ) • u + M.γ • vbar := by
      simp only [vbar, smul_add, smul_smul]
      rw [mul_comm (1 - M.γ) M.γ, add_comm]
    rwa [heq] at h1
  -- Show weights are convex weights and deduce `vbar ∈ actSet M` and finite Jensen inequality
  have hw_nonneg : ∀ N k, 0 ≤ c N * M.γ ^ k := by
    intro N k
    have hden : 0 < 1 - M.γ ^ (N + 1) := by
      have : M.γ ^ (N + 1) < 1 :=
        pow_lt_one₀ hM.gamma_nonneg hM.gamma_lt_one (Nat.succ_ne_zero N)
      linarith
    have hc_pos : 0 < c N := div_pos (by linarith [hM.gamma_lt_one]) hden
    exact mul_nonneg (le_of_lt hc_pos) (pow_nonneg hM.gamma_nonneg k)
  have hw_sum : ∀ N, ∑ k ∈ range (N + 1), c N * M.γ ^ k = 1 := by
    intro N
    rw [← Finset.mul_sum, geom_sum_eq (ne_of_lt hM.gamma_lt_one)]
    have h1 : 1 - M.γ ≠ 0 := by linarith [hM.gamma_lt_one]
    have h2 : 1 - M.γ ^ (N + 1) ≠ 0 := by
      have : M.γ ^ (N + 1) < 1 :=
        pow_lt_one₀ hM.gamma_nonneg hM.gamma_lt_one (Nat.succ_ne_zero N)
      linarith
    dsimp only [c]
    have hnum : M.γ ^ (N + 1) - 1 = -(1 - M.γ ^ (N + 1)) := by ring
    have hden : M.γ - 1 = -(1 - M.γ) := by ring
    rw [hnum, hden, neg_div_neg_eq]
    field_simp
  have hvbar_mem : vbar ∈ actSet M := by
    refine (actSet_isClosed M).mem_of_tendsto hV_lim (Eventually.of_forall fun N => ?_)
    have hsum_eq : c N • ∑ k ∈ range (N + 1), M.γ ^ k • v k =
        ∑ k ∈ range (N + 1), (c N * M.γ ^ k) • v k := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => by rw [smul_smul]
    rw [hsum_eq]
    exact (actSet_convex M).sum_mem (fun k _ => hw_nonneg N k) (hw_sum N) (fun k _ => hv_mem k)
  -- Finite Jensen inequality for `stageG`
  have hjensen : ∀ N : ℕ,
      stageG M (c N • ∑ k ∈ range (N + 1), M.γ ^ k • u_seq k,
                c N • ∑ k ∈ range (N + 1), M.γ ^ k • v k) ≤
      c N * ∑ k ∈ range (N + 1), M.γ ^ k * stageG M (u_seq k, v k) := by
    intro N
    have hmap := (stageG_convex M hM hq).map_sum_le (t := range (N + 1))
      (w := fun k => c N * M.γ ^ k) (p := fun k => (u_seq k, v k))
      (fun k _ => hw_nonneg N k) (hw_sum N) (fun k _ => Set.mem_univ _)
    have hpair : ∑ k ∈ range (N + 1), (c N * M.γ ^ k) • (u_seq k, v k) =
        (c N • ∑ k ∈ range (N + 1), M.γ ^ k • u_seq k,
         c N • ∑ k ∈ range (N + 1), M.γ ^ k • v k) := by
      refine Prod.ext ?_ ?_
      · dsimp only
        rw [Prod.fst_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => by simp [smul_smul]
      · dsimp only
        rw [Prod.snd_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => by simp [smul_smul]
    have hrhs : ∑ k ∈ range (N + 1), (c N * M.γ ^ k) • stageG M (u_seq k, v k) =
        c N * ∑ k ∈ range (N + 1), M.γ ^ k * stageG M (u_seq k, v k) := by
      simp only [smul_eq_mul, mul_assoc]
      rw [← Finset.mul_sum]
    rw [hpair, hrhs] at hmap
    exact hmap
  -- Pass to the limit as `N → ∞`
  have hLHS_lim : Tendsto
      (fun N : ℕ => stageG M (c N • ∑ k ∈ range (N + 1), M.γ ^ k • u_seq k,
                              c N • ∑ k ∈ range (N + 1), M.γ ^ k • v k))
      atTop (𝓝 (Fmap M u vbar)) :=
    ((stageG_continuous M hM hq).tendsto ((1 - M.γ) • u + M.γ • vbar, vbar)).comp
      (hU_lim.prodMk_nhds hV_lim)
  have hterm_eq : ∀ k : ℕ,
      M.γ ^ k * stageG M (u_seq k, v k) =
      M.γ ^ k * (M.c2 (M.traj (M.next (toAction M u)) a k) (a k) + M.Nhat (a k)) := by
    intro k
    rw [traj_eq_next_seq M u a ha k]
    unfold stageG
    rw [toAction_ofAction M (ha k)]
  have hJ_sum : Summable (fun k : ℕ => M.γ ^ k * stageG M (u_seq k, v k)) := by
    simp_rw [hterm_eq]
    exact J_summable_of_next M hM hq hu a ha
  have hJ_eq : ∑' k : ℕ, M.γ ^ k * stageG M (u_seq k, v k) = M.J (M.next (toAction M u)) a := by
    simp_rw [hterm_eq]
    rfl
  have hRHS_lim : Tendsto
      (fun N : ℕ => c N * ∑ k ∈ range (N + 1), M.γ ^ k * stageG M (u_seq k, v k))
      atTop (𝓝 ((1 - M.γ) * M.J (M.next (toAction M u)) a)) := by
    rw [← hJ_eq]
    exact hc_lim.mul (hJ_sum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have hlim : Fmap M u vbar ≤ (1 - M.γ) * M.J (M.next (toAction M u)) a :=
    le_of_tendsto_of_tendsto hLHS_lim hRHS_lim (Eventually.of_forall hjensen)
  have hdiag : stageG M (u, u) ≤ Fmap M u vbar := by
    rw [← Fmap_diag M u]
    exact hfix vbar hvbar_mem
  exact hdiag.trans hlim

private lemma J_const_at_next {ê : ℕ} (M : Model ê) (hM : M.Standing) (u : ActVec M) :
    M.J (M.next (toAction M u)) (fun _ => toAction M u) =
      (1 - M.γ)⁻¹ * stageG M (u, u) := by
  have htraj : ∀ k, M.traj (M.next (toAction M u)) (fun _ => toAction M u) k =
      M.next (toAction M u) := by
    intro k; cases k <;> rfl
  unfold Model.J DetDP.J Model.dp
  dsimp only
  have : ∀ k, M.traj (M.next (toAction M u)) (fun _ => toAction M u) k =
      M.next (toAction M u) := htraj
  change ∑' k : ℕ, M.γ ^ k *
      (M.c2 (M.traj (M.next (toAction M u)) (fun _ => toAction M u) k) (toAction M u) +
       M.Nhat (toAction M u)) = _
  simp_rw [htraj]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one]
  rfl

private lemma Vhat_eq_iInf {ê : ℕ} (M : Model ê) (x : State ê) :
    M.Vhat x = ⨅ a : {a : ℕ → Action ê // ∀ k, M.InA (a k)}, M.J x a.1 := rfl

private lemma Vhat_le_bellman {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0)
    {u : ActVec M} (hu : u ∈ actSet M) {a' : Action ê} (ha' : M.InA a') :
    M.Vhat (M.next (toAction M u)) ≤
      M.c2 (M.next (toAction M u)) a' + M.Nhat a' + M.γ * M.Vhat (M.next a') := by
  set xf := M.next (toAction M u)
  have : Nonempty {b : ℕ → Action ê // ∀ k, M.InA (b k)} := ⟨⟨fun _ => a', fun _ => ha'⟩⟩
  have hstep : ∀ b : {b : ℕ → Action ê // ∀ k, M.InA (b k)},
      M.Vhat xf ≤ M.c2 xf a' + M.Nhat a' + M.γ * M.J (M.next a') b.1 := by
    intro b
    let cseq : ℕ → Action ê := fun k => match k with | 0 => a' | j + 1 => b.1 j
    have hc_adm : ∀ k, M.InA (cseq k) := fun k => by
      cases k with
      | zero => exact ha'
      | succ j => exact b.2 j
    have hbdd : BddBelow (Set.range fun s : {s : ℕ → Action ê // ∀ k, M.InA (s k)} => M.J xf s.1) := by
      obtain ⟨B, _, hbound⟩ := stageG_bounded M hM hq
      refine ⟨-((1 - M.γ)⁻¹ * B), ?_⟩
      rintro _ ⟨s, rfl⟩
      have hsum := J_summable_of_next M hM hq hu s.1 s.2
      have hterm_ge : ∀ k, -(M.γ ^ k * B) ≤
          M.γ ^ k * (M.c2 (M.traj xf s.1 k) (s.1 k) + M.Nhat (s.1 k)) := by
        intro k
        let pk : ActVec M := match k with | 0 => u | j + 1 => ofAction M (s.1 j)
        have hmem : pk ∈ actSet M := by
          cases k with
          | zero => exact hu
          | succ j => exact ofAction_mem_actSet M (s.2 j)
        have htraj : M.traj xf s.1 k = M.next (toAction M pk) :=
          traj_eq_next_seq M u s.1 s.2 k
        rw [htraj]
        have hstage : M.c2 (M.next (toAction M pk)) (s.1 k) + M.Nhat (s.1 k) =
            stageG M (pk, ofAction M (s.1 k)) := by
          unfold stageG; rw [toAction_ofAction M (s.2 k)]
        rw [hstage]
        have habs := hbound pk hmem (ofAction M (s.1 k)) (ofAction_mem_actSet M (s.2 k))
        have hneg : -B ≤ stageG M (pk, ofAction M (s.1 k)) := neg_le_of_abs_le habs
        have hmul := mul_le_mul_of_nonneg_left hneg (pow_nonneg hM.gamma_nonneg k)
        linarith
      have hneg_sum : Summable (fun k : ℕ => -(M.γ ^ k * B)) :=
        ((summable_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one).mul_right B).neg
      have hle := hneg_sum.tsum_le_tsum hterm_ge hsum
      rw [tsum_neg, tsum_mul_right, tsum_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one] at hle
      exact hle
    have hVle : M.Vhat xf ≤ M.J xf cseq := by
      rw [Vhat_eq_iInf M xf]
      exact ciInf_le hbdd ⟨cseq, hc_adm⟩
    have hJsplit : M.J xf cseq = M.c2 xf a' + M.Nhat a' + M.γ * M.J (M.next a') b.1 := by
      have hsum := J_summable_of_next M hM hq hu cseq hc_adm
      change ∑' k : ℕ, M.γ ^ k * (M.c2 (M.traj xf cseq k) (cseq k) + M.Nhat (cseq k)) = _
      rw [hsum.tsum_eq_zero_add]
      have h0 : M.γ ^ 0 * (M.c2 (M.traj xf cseq 0) (cseq 0) + M.Nhat (cseq 0)) =
          M.c2 xf a' + M.Nhat a' := by
        simp [Model.traj, DetDP.traj, cseq]
      have htraj_shift : ∀ k, M.traj xf cseq (k + 1) = M.traj (M.next a') b.1 k := by
        intro k; cases k <;> rfl
      have htail :
          ∑' k : ℕ, M.γ ^ (k + 1) * (M.c2 (M.traj xf cseq (k + 1)) (cseq (k + 1)) + M.Nhat (cseq (k + 1))) =
          M.γ * M.J (M.next a') b.1 := by
        change ∑' k : ℕ, M.γ ^ (k + 1) * (M.c2 (M.traj xf cseq (k + 1)) (cseq (k + 1)) + M.Nhat (cseq (k + 1))) =
            M.γ * ∑' k : ℕ, M.γ ^ k * (M.c2 (M.traj (M.next a') b.1 k) (b.1 k) + M.Nhat (b.1 k))
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        rw [htraj_shift k, pow_succ', mul_assoc]
      exact congrArg₂ (· + ·) h0 htail
    linarith
  rcases eq_or_lt_of_le hM.gamma_nonneg with hγ0 | hγpos
  · have := hstep ⟨fun _ => a', fun _ => ha'⟩
    rw [← hγ0, zero_mul] at this ⊢
    exact this
  · have hdiv : ∀ b : {b : ℕ → Action ê // ∀ k, M.InA (b k)},
        (M.Vhat xf - (M.c2 xf a' + M.Nhat a')) / M.γ ≤ M.J (M.next a') b.1 := by
      intro b
      rw [div_le_iff₀ hγpos]
      linarith [hstep b]
    have hle : (M.Vhat xf - (M.c2 xf a' + M.Nhat a')) / M.γ ≤ M.Vhat (M.next a') := by
      rw [Vhat_eq_iInf M (M.next a')]
      exact le_ciInf hdiv
    rw [div_le_iff₀ hγpos] at hle
    linarith

private theorem proposition_H_3_proof {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) :
    ∃ xf af, M.IsFixedPoint xf af := by
  obtain ⟨u, hu, hfix⟩ := exists_Fmap_fixed M hM hq
  let af : Action ê := toAction M u
  let xf : State ê := M.next af
  have haf : M.InA af := hu
  have hxf : M.InX xf := next_inX M hM hq haf
  refine ⟨xf, af, hxf, ⟨haf, ?_⟩, rfl⟩
  have h1mγ : 0 < 1 - M.γ := by linarith [hM.gamma_lt_one]
  have : Nonempty {a : ℕ → Action ê // ∀ k, M.InA (a k)} := ⟨⟨fun _ => af, fun _ => haf⟩⟩
  have hJ_ge : ∀ a : {a : ℕ → Action ê // ∀ k, M.InA (a k)},
      (1 - M.γ)⁻¹ * stageG M (u, u) ≤ M.J xf a.1 := by
    intro a
    have h := J_ge_fixed M hM hq hu hfix a.1 a.2
    rw [inv_mul_eq_div, div_le_iff₀ h1mγ]
    linarith
  have hbdd : BddBelow (Set.range fun a : {a : ℕ → Action ê // ∀ k, M.InA (a k)} => M.J xf a.1) := by
    refine ⟨(1 - M.γ)⁻¹ * stageG M (u, u), ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hJ_ge a
  have hV_ge : (1 - M.γ)⁻¹ * stageG M (u, u) ≤ M.Vhat xf := by
    rw [Vhat_eq_iInf M xf]
    exact le_ciInf hJ_ge
  have hV_le : M.Vhat xf ≤ (1 - M.γ)⁻¹ * stageG M (u, u) := by
    calc M.Vhat xf
        = ⨅ a : {a : ℕ → Action ê // ∀ k, M.InA (a k)}, M.J xf a.1 := Vhat_eq_iInf M xf
      _ ≤ M.J xf (fun _ => af) := ciInf_le hbdd ⟨fun _ => af, fun _ => haf⟩
      _ = (1 - M.γ)⁻¹ * stageG M (u, u) := J_const_at_next M hM u
  have hV_eq : M.Vhat xf = (1 - M.γ)⁻¹ * stageG M (u, u) := le_antisymm hV_le hV_ge
  have hself : M.c2 xf af + M.Nhat af + M.γ * M.Vhat (M.next af) = M.Vhat xf := by
    have hstage : M.c2 xf af + M.Nhat af = stageG M (u, u) := rfl
    change M.c2 xf af + M.Nhat af + M.γ * M.Vhat xf = M.Vhat xf
    rw [hstage, hV_eq]
    have hne0 : 1 - M.γ ≠ 0 := ne_of_gt h1mγ
    field_simp
    ring
  intro a' ha'
  rw [hself]
  exact Vhat_le_bellman M hM hq hu ha'

end Micromobility.Transient.PropH3

open Micromobility.Transient in
theorem solution {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) :
    ∃ xf af, M.IsFixedPoint xf af :=
  Micromobility.Transient.PropH3.proposition_H_3_proof M hM hq
