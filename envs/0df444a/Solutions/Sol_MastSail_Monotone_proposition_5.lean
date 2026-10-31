-- Prove2me | solution 1 for MastSail.Monotone.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:45:45.325628+00:00
-- url     : https://prove2.me/submissions/8c2d5b6a-9501-42b2-98e9-689e6ec8c95b

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone

open MeasureTheory

/-- Survival ratio below the density ratio at any earlier point. -/
lemma surv_le_ratio (M : Model) (hM : M.Standing) (s i : ℝ) (hs : 0 ≤ s) (hsi : s ≤ i)
    (hi : i ≤ M.Ibar) :
    (1 - cdf M.gL i) / (1 - cdf M.gH i) ≤ M.gL s / M.gH s := by
  obtain ⟨hI0, hIQ, -, -, ⟨hgLc, hgLp, hgL1⟩, ⟨hgHc, hgHp, hgH1⟩, -, hg⟩ := hM
  have hQ : 0 ≤ M.Qbar := by linarith
  have hiQ : i < M.Qbar := by linarith
  have hi0 : 0 ≤ i := le_trans hs hsi
  have intL : IntervalIntegrable M.gL volume 0 M.Qbar :=
    hgLc.intervalIntegrable_of_Icc hQ
  have intH : IntervalIntegrable M.gH volume 0 M.Qbar :=
    hgHc.intervalIntegrable_of_Icc hQ
  have sub : Set.uIcc i M.Qbar ⊆ Set.uIcc 0 M.Qbar := by
    rw [Set.uIcc_of_le hiQ.le, Set.uIcc_of_le hQ]
    exact Set.Icc_subset_Icc hi0 le_rfl
  have sub' : Set.uIcc 0 i ⊆ Set.uIcc 0 M.Qbar := by
    rw [Set.uIcc_of_le hi0, Set.uIcc_of_le hQ]
    exact Set.Icc_subset_Icc le_rfl hiQ.le
  have eL : 1 - cdf M.gL i = ∫ x in i..M.Qbar, M.gL x := by
    unfold cdf; rw [← hgL1]
    exact intervalIntegral.integral_interval_sub_left intL (intL.mono_set sub')
  have eH : 1 - cdf M.gH i = ∫ x in i..M.Qbar, M.gH x := by
    unfold cdf; rw [← hgH1]
    exact intervalIntegral.integral_interval_sub_left intH (intH.mono_set sub')
  have posH : 0 < ∫ x in i..M.Qbar, M.gH x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (intH.mono_set sub) _ hiQ
    intro x hx
    exact hgHp x ⟨by linarith [hx.1], hx.2.le⟩
  set r := M.gL s / M.gH s
  have hle : ∫ x in i..M.Qbar, M.gL x ≤ ∫ x in i..M.Qbar, r * M.gH x := by
    apply intervalIntegral.integral_mono_on hiQ.le (intL.mono_set sub)
      ((intH.mono_set sub).const_mul r)
    intro x hx
    have hx0 : x ∈ Set.Icc 0 M.Qbar := ⟨by linarith [hx.1], hx.2⟩
    have hpos := hgHp x hx0
    have : M.gL x / M.gH x ≤ r :=
      hg ⟨hs, by linarith⟩ hx0 (by linarith [hx.1])
    rw [div_le_iff₀ hpos] at this
    linarith
  rw [intervalIntegral.integral_const_mul] at hle
  rw [eL, eH, div_le_iff₀ posH]
  linarith

lemma ratio_nonneg_g (M : Model) (hM : M.Standing) (s : ℝ) (hs : s ∈ Set.Icc 0 M.Qbar) :
    0 ≤ M.gL s / M.gH s := by
  obtain ⟨-, -, -, -, ⟨-, hgLp, -⟩, ⟨-, hgHp, -⟩, -, -⟩ := hM
  exact (div_pos (hgLp s hs) (hgHp s hs)).le

lemma ratio_nonneg_f (M : Model) (hM : M.Standing) (s : ℝ) (hs : s ∈ Set.Icc 0 M.Ibar) :
    0 ≤ M.fL s / M.fH s := by
  obtain ⟨-, -, ⟨-, hp1, -⟩, ⟨-, hp2, -⟩, -, -, -, -⟩ := hM
  exact (div_pos (hp1 s hs) (hp2 s hs)).le

/-- `φ^NSO` is monotone in both coordinates. -/
lemma phiNSO_mono (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid)
    (i i' s s' : ℝ) (hi : i ∈ Set.Icc 0 M.Ibar) (hi' : i' ∈ Set.Icc 0 M.Ibar)
    (hs : s ∈ Set.Icc 0 M.Qbar) (hs' : s' ∈ Set.Icc 0 M.Qbar) (hii : i ≤ i') (hss : s ≤ s') :
    phiNSO M ω i s ≤ phiNSO M ω i' s' := by
  have hf := hM.2.2.2.2.2.2.1
  have hg := hM.2.2.2.2.2.2.2
  obtain ⟨h1, h2, h3, -⟩ := hω
  have a1 : M.gL s' / M.gH s' ≤ M.gL s / M.gH s := hg hs hs' hss
  have a2 : M.fL i' / M.fH i' ≤ M.fL i / M.fH i := hf hi hi' hii
  have n1 := ratio_nonneg_g M hM s' hs'
  have n2 := ratio_nonneg_f M hM i' hi'
  have n3 := ratio_nonneg_f M hM i hi
  have a3 : M.fL i' * M.gL s' / (M.fH i' * M.gH s') ≤ M.fL i * M.gL s / (M.fH i * M.gH s) := by
    rw [mul_div_mul_comm, mul_div_mul_comm]
    exact mul_le_mul a2 a1 n1 n3
  unfold phiNSO RNSO_HL RNSO_LH RNSO_LL
  nlinarith [mul_le_mul_of_nonneg_left a1 h1, mul_le_mul_of_nonneg_left a2 h2,
    mul_le_mul_of_nonneg_left a3 h3]

/-- On the mast line, `φ^SO(i) ≥ φ^NSO(i, s)` for `s ≤ i`. -/
lemma phiNSO_le_phiSO (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid)
    (i s : ℝ) (hs : 0 ≤ s) (hsi : s ≤ i) (hi : i ≤ M.Ibar) :
    phiNSO M ω i s ≤ phiSO M ω i := by
  have key := surv_le_ratio M hM s i hs hsi hi
  have hIQ := hM.2.1
  obtain ⟨h1, h2, h3, -⟩ := hω
  have n3 := ratio_nonneg_f M hM i ⟨le_trans hs hsi, hi⟩
  have a3 : M.fL i * (1 - cdf M.gL i) / (M.fH i * (1 - cdf M.gH i)) ≤
      M.fL i * M.gL s / (M.fH i * M.gH s) := by
    rw [mul_div_mul_comm, mul_div_mul_comm]
    exact mul_le_mul_of_nonneg_left key n3
  unfold phiNSO phiSO RNSO_HL RNSO_LH RNSO_LL RSO_HL RSO_LL
  nlinarith [mul_le_mul_of_nonneg_left key h1, mul_le_mul_of_nonneg_left a3 h3]

/-- Continuity of `φ^NSO` on the rectangle. -/
lemma phiNSO_contOn (M : Model) (hM : M.Standing) (ω : Weights) :
    ContinuousOn (fun p : ℝ × ℝ => phiNSO M ω p.1 p.2)
      (Set.Icc 0 M.Ibar ×ˢ Set.Icc 0 M.Qbar) := by
  obtain ⟨-, -, ⟨hfLc, hfLp, -⟩, ⟨hfHc, hfHp, -⟩, ⟨hgLc, hgLp, -⟩, ⟨hgHc, hgHp, -⟩, -, -⟩ := hM
  have m1 : Set.MapsTo (fun p : ℝ × ℝ => p.1) (Set.Icc 0 M.Ibar ×ˢ Set.Icc 0 M.Qbar)
      (Set.Icc 0 M.Ibar) := fun p hp => hp.1
  have m2 : Set.MapsTo (fun p : ℝ × ℝ => p.2) (Set.Icc 0 M.Ibar ×ˢ Set.Icc 0 M.Qbar)
      (Set.Icc 0 M.Qbar) := fun p hp => hp.2
  have cfL : ContinuousOn (fun p : ℝ × ℝ => M.fL p.1) _ := hfLc.comp continuous_fst.continuousOn m1
  have cfH : ContinuousOn (fun p : ℝ × ℝ => M.fH p.1) _ := hfHc.comp continuous_fst.continuousOn m1
  have cgL : ContinuousOn (fun p : ℝ × ℝ => M.gL p.2) _ := hgLc.comp continuous_snd.continuousOn m2
  have cgH : ContinuousOn (fun p : ℝ × ℝ => M.gH p.2) _ := hgHc.comp continuous_snd.continuousOn m2
  have nfH : ∀ p ∈ Set.Icc 0 M.Ibar ×ˢ Set.Icc 0 M.Qbar, M.fH p.1 ≠ 0 :=
    fun p hp => (hfHp _ hp.1).ne'
  have ngH : ∀ p ∈ Set.Icc 0 M.Ibar ×ˢ Set.Icc 0 M.Qbar, M.gH p.2 ≠ 0 :=
    fun p hp => (hgHp _ hp.2).ne'
  unfold phiNSO RNSO_HL RNSO_LH RNSO_LL
  apply ContinuousOn.add
  apply ContinuousOn.add
  · exact continuousOn_const.mul (continuousOn_const.sub (cgL.div cgH ngH))
  · exact continuousOn_const.mul (continuousOn_const.sub (cfL.div cfH nfH))
  · refine continuousOn_const.mul (continuousOn_const.sub ((cfL.mul cgL).div (cfH.mul cgH) ?_))
    intro p hp; exact mul_ne_zero (nfH p hp) (ngH p hp)

lemma iS_le (M : Model) (ω : Weights) (t : ℝ) : iS M ω t ≤ M.Ibar := by
  unfold iS
  split_ifs with h
  · obtain ⟨i, hi, hti⟩ := h
    exact le_trans (csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨hi, hti⟩) hi.2
  · exact le_rfl

/-- Above the sail's critical inventory, the diagonal is in the sail's closure. -/
lemma diag_of_ge_iS (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid) (t : ℝ)
    (i : ℝ) (hi : i ∈ Set.Icc 0 M.Ibar) (hge : iS M ω t ≤ i)
    (hne : ∃ j ∈ Set.Icc 0 M.Ibar, t ≤ phiNSO M ω j j) : t ≤ phiNSO M ω i i := by
  have hIQ := hM.2.1
  set S := {j | j ∈ Set.Icc 0 M.Ibar ∧ t ≤ phiNSO M ω j j}
  have hS : iS M ω t = sInf S := by unfold iS; rw [if_pos hne]
  have dcont : ContinuousOn (fun j : ℝ => phiNSO M ω j j) (Set.Icc 0 M.Ibar) := by
    have := phiNSO_contOn M hM ω
    refine this.comp (continuous_id.prodMk continuous_id).continuousOn ?_
    intro j hj; exact ⟨hj, hj.1, le_trans hj.2 hIQ.le⟩
  have hclosed : IsClosed S := by
    have := dcont.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_Ici (a := t))
    exact this
  have hSne : S.Nonempty := by obtain ⟨j, hj, h⟩ := hne; exact ⟨j, hj, h⟩
  have hmem : sInf S ∈ S := hclosed.csInf_mem hSne ⟨0, fun x hx => hx.1.1⟩
  obtain ⟨hj, htj⟩ := hmem
  refine le_trans htj ?_
  apply phiNSO_mono M hM ω hω _ _ _ _ hj hi ⟨hj.1, by linarith [hj.2]⟩
    ⟨hi.1, by linarith [hi.2]⟩ <;> linarith

theorem proposition_5' (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid) (t wbar : ℝ)
    (hw : 0 < wbar) :
    MonotoneInS M (plan M ω t wbar) ∧
    (iS M ω t = iM M ω t →
      MonotoneInI M (plan M ω t wbar) ∧ JointlyMonotone M (plan M ω t wbar)) ∧
    (iM M ω t < iS M ω t →
      ¬ MonotoneInI M (plan M ω t wbar) ∧ ¬ JointlyMonotone M (plan M ω t wbar)) := by
  have hIQ := hM.2.1
  -- plan values
  have planNSO : ∀ i s, inD M i s → s < i →
      plan M ω t wbar i s = if t ≤ phiNSO M ω i s then wbar else 0 := by
    intro i s hD hsi
    unfold plan
    by_cases h : t ≤ phiNSO M ω i s
    · rw [if_pos (Set.mem_union_left _ (show (i, s) ∈ bonusNSO M ω t from ⟨hD, hsi, h⟩)), if_pos h]
    · rw [if_neg, if_neg h]
      rintro (⟨-, -, h'⟩ | ⟨-, h', -⟩)
      · exact h h'
      · exact absurd h' hsi.ne
  have planSO : ∀ i, inD M i i →
      plan M ω t wbar i i = if t ≤ phiSO M ω i then wbar else 0 := by
    intro i hD
    unfold plan
    by_cases h : t ≤ phiSO M ω i
    · rw [if_pos (Set.mem_union_right _ (show (i, i) ∈ bonusSO M ω t from ⟨hD, rfl, h⟩)), if_pos h]
    · rw [if_neg, if_neg h]
      rintro (⟨-, h', -⟩ | ⟨-, -, h'⟩)
      · exact lt_irrefl _ h'
      · exact h h'
  have plan_cases : ∀ i s, plan M ω t wbar i s = wbar ∨ plan M ω t wbar i s = 0 := by
    intro i s; unfold plan; split_ifs <;> simp
  have plan_nonneg : ∀ i s, 0 ≤ plan M ω t wbar i s := by
    intro i s; rcases plan_cases i s with h | h <;> rw [h]; exact hw.le
  -- reduce to: bonus at first point implies bonus at second
  have reduce : ∀ i' s' i'' s'', (plan M ω t wbar i' s' = wbar → plan M ω t wbar i'' s'' = wbar) →
      plan M ω t wbar i' s' ≤ plan M ω t wbar i'' s'' := by
    intro i' s' i'' s'' himp
    rcases plan_cases i' s' with h | h
    · rw [himp h, h]
    · rw [h]; exact plan_nonneg _ _
  -- membership of rectangle
  have rI : ∀ i s, inD M i s → i ∈ Set.Icc 0 M.Ibar := fun i s h => ⟨by linarith [h.1, h.2.1], h.2.2⟩
  have rQ : ∀ i s, inD M i s → s ∈ Set.Icc 0 M.Qbar :=
    fun i s h => ⟨h.1, by linarith [h.2.1, h.2.2]⟩
  have rQi : ∀ i s, inD M i s → i ∈ Set.Icc 0 M.Qbar :=
    fun i s h => ⟨by linarith [h.1, h.2.1], by linarith [h.2.2]⟩
  have hwne : (0:ℝ) ≠ wbar := hw.ne
  have getNSO : ∀ i s, inD M i s → s < i → plan M ω t wbar i s = wbar → t ≤ phiNSO M ω i s := by
    intro i s hD hsi hb
    rw [planNSO i s hD hsi] at hb
    split_ifs at hb with h
    · exact h
    · exact absurd hb hwne
  have getSO : ∀ i, inD M i i → plan M ω t wbar i i = wbar → t ≤ phiSO M ω i := by
    intro i hD hb
    rw [planSO i hD] at hb
    split_ifs at hb with h
    · exact h
    · exact absurd hb hwne
  have putNSO : ∀ i s, inD M i s → s < i → t ≤ phiNSO M ω i s → plan M ω t wbar i s = wbar := by
    intro i s hD hsi h; rw [planNSO i s hD hsi, if_pos h]
  have putSO : ∀ i, inD M i i → t ≤ phiSO M ω i → plan M ω t wbar i i = wbar := by
    intro i hD h; rw [planSO i hD, if_pos h]
  -- bonus on SO line with iS = iM gives diagonal NSO bonus
  have soDiag : iS M ω t = iM M ω t → ∀ i, inD M i i → i < M.Ibar → t ≤ phiSO M ω i →
      t ≤ phiNSO M ω i i := by
    intro heq i hD hlt ht
    have hneSO : ∃ j ∈ Set.Icc 0 M.Ibar, t ≤ phiSO M ω j := ⟨i, rI i i hD, ht⟩
    have hiM : iM M ω t ≤ i := by
      unfold iM; rw [if_pos hneSO]
      exact csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨rI i i hD, ht⟩
    by_cases hne : ∃ j ∈ Set.Icc 0 M.Ibar, t ≤ phiNSO M ω j j
    · exact diag_of_ge_iS M hM ω hω t i (rI i i hD) (heq ▸ hiM) hne
    · have : iS M ω t = M.Ibar := by unfold iS; rw [if_neg hne]
      linarith
  refine ⟨?_, ?_, ?_⟩
  · -- monotone in s
    intro i s' s'' hD' hD'' hle
    apply reduce; intro hb
    rcases hD''.2.1.eq_or_lt with h'' | h''
    · subst h''
      rcases hD'.2.1.eq_or_lt with h' | h'
      · subst h'; exact hb
      · apply putSO _ hD''
        exact le_trans (getNSO _ _ hD' h' hb)
          (phiNSO_le_phiSO M hM ω hω _ _ hD'.1 hD'.2.1 hD'.2.2)
    · have h' : s' < i := lt_of_le_of_lt hle h''
      apply putNSO _ _ hD'' h''
      exact le_trans (getNSO _ _ hD' h' hb)
        (phiNSO_mono M hM ω hω _ _ _ _ (rI _ _ hD') (rI _ _ hD'') (rQ _ _ hD') (rQ _ _ hD'')
          le_rfl hle)
  · intro heq
    constructor
    · intro i' i'' s hD' hD'' hle
      apply reduce; intro hb
      rcases hle.eq_or_lt with h | h
      · subst h; exact hb
      · have hsi : s < i'' := lt_of_le_of_lt hD'.2.1 h
        apply putNSO _ _ hD'' hsi
        have base : t ≤ phiNSO M ω i' s := by
          rcases hD'.2.1.eq_or_lt with h' | h'
          · subst h'
            exact soDiag heq _ hD' (lt_of_lt_of_le h hD''.2.2) (getSO _ hD' hb)
          · exact getNSO _ _ hD' h' hb
        exact le_trans base
          (phiNSO_mono M hM ω hω _ _ _ _ (rI _ _ hD') (rI _ _ hD'') (rQ _ _ hD') (rQ _ _ hD'')
            h.le le_rfl)
    · intro i' s' i'' s'' hD' hD'' hi hs
      apply reduce; intro hb
      have base : t ≤ phiNSO M ω i' s' := by
        rcases hD'.2.1.eq_or_lt with h' | h'
        · subst h'
          exact soDiag heq _ hD' (lt_of_lt_of_le hi hD''.2.2) (getSO _ hD' hb)
        · exact getNSO _ _ hD' h' hb
      have hs'i'' : s' < i'' := lt_of_lt_of_le hs hD''.2.1
      have hD3 : inD M i'' s' := ⟨hD'.1, hs'i''.le, hD''.2.2⟩
      have step : t ≤ phiNSO M ω i'' s' :=
        le_trans base (phiNSO_mono M hM ω hω _ _ _ _ (rI _ _ hD') (rI _ _ hD3) (rQ _ _ hD')
          (rQ _ _ hD3) hi.le le_rfl)
      rcases hD''.2.1.eq_or_lt with h'' | h''
      · subst h''
        exact putSO _ hD'' (le_trans step
          (phiNSO_le_phiSO M hM ω hω _ _ hD'.1 hs'i''.le hD''.2.2))
      · apply putNSO _ _ hD'' h''
        exact le_trans step (phiNSO_mono M hM ω hω _ _ _ _ (rI _ _ hD3) (rI _ _ hD'')
          (rQ _ _ hD3) (rQ _ _ hD'') le_rfl hs.le)
  · intro hlt
    have hneSO : ∃ j ∈ Set.Icc 0 M.Ibar, t ≤ phiSO M ω j := by
      by_contra hne
      have : iM M ω t = M.Ibar := by unfold iM; rw [if_neg hne]
      linarith [iS_le M ω t]
    have hiM : iM M ω t = sInf {i | i ∈ Set.Icc 0 M.Ibar ∧ t ≤ phiSO M ω i} := by
      unfold iM; rw [if_pos hneSO]
    rw [hiM] at hlt
    obtain ⟨x, ⟨hxI, hxt⟩, hxlt⟩ := exists_lt_of_csInf_lt
      (by obtain ⟨j, hj, h⟩ := hneSO; exact ⟨j, hj, h⟩) hlt
    have hxIbar : x < M.Ibar := lt_of_lt_of_le hxlt (iS_le M ω t)
    have hxnot : phiNSO M ω x x < t := by
      by_contra h
      rw [not_lt] at h
      have hne : ∃ j ∈ Set.Icc 0 M.Ibar, t ≤ phiNSO M ω j j := ⟨x, hxI, h⟩
      have : iS M ω t ≤ x := by
        unfold iS; rw [if_pos hne]
        exact csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨hxI, h⟩
      linarith
    have hxD : inD M x x := ⟨hxI.1, le_rfl, hxI.2⟩
    have hxmem : ((x, x) : ℝ × ℝ) ∈ Set.Icc 0 M.Ibar ×ˢ Set.Icc 0 M.Qbar :=
      ⟨hxI, hxI.1, by linarith [hxI.2]⟩
    have hc := (phiNSO_contOn M hM ω) (x, x) hxmem
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨δ, hδ, hδc⟩ := hc (t - phiNSO M ω x x) (by linarith)
    set d := min (δ / 4) ((M.Ibar - x) / 2) with hd
    have hd0 : 0 < d := lt_min (by linarith) (by linarith)
    have hd1 : d ≤ δ / 4 := min_le_left _ _
    have hd2 : d ≤ (M.Ibar - x) / 2 := min_le_right _ _
    have near : ∀ a b : ℝ, x ≤ a → a ≤ x + 2 * d → x ≤ b → b ≤ x + d →
        phiNSO M ω a b < t := by
      intro a b ha1 ha2 hb1 hb2
      have hmem : ((a, b) : ℝ × ℝ) ∈ Set.Icc 0 M.Ibar ×ˢ Set.Icc 0 M.Qbar :=
        ⟨⟨by linarith [hxI.1], by linarith⟩, by linarith [hxI.1], by linarith⟩
      have hdist : dist ((a, b) : ℝ × ℝ) (x, x) < δ := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        exact max_lt (by linarith) (by linarith)
      have := hδc hmem hdist
      rw [Real.dist_eq] at this
      have := (abs_lt.mp this).2
      simp only at this
      linarith
    have hD1 : inD M (x + 2 * d) x := ⟨hxI.1, by linarith, by linarith⟩
    have hD2 : inD M (x + 2 * d) (x + d) := ⟨by linarith [hxI.1], by linarith, by linarith⟩
    have p0 : plan M ω t wbar x x = wbar := putSO x hxD hxt
    have p1 : plan M ω t wbar (x + 2 * d) x = 0 := by
      rw [planNSO _ _ hD1 (by linarith), if_neg (not_le.mpr (near _ _ (by linarith) le_rfl le_rfl
        (by linarith)))]
    have p2 : plan M ω t wbar (x + 2 * d) (x + d) = 0 := by
      rw [planNSO _ _ hD2 (by linarith), if_neg (not_le.mpr (near _ _ (by linarith) le_rfl
        (by linarith) le_rfl))]
    constructor
    · intro h
      have := h x (x + 2 * d) x hxD hD1 (by linarith)
      rw [p0, p1] at this; linarith
    · intro h
      have := h x x (x + 2 * d) (x + d) hxD hD2 (by linarith) (by linarith)
      rw [p0, p2] at this; linarith

end MastSail.Monotone

open MastSail.Monotone in
theorem solution (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid) (t wbar : ℝ)
    (hw : 0 < wbar) :
    MonotoneInS M (plan M ω t wbar) ∧
    (iS M ω t = iM M ω t →
      MonotoneInI M (plan M ω t wbar) ∧ JointlyMonotone M (plan M ω t wbar)) ∧
    (iM M ω t < iS M ω t →
      ¬ MonotoneInI M (plan M ω t wbar) ∧ ¬ JointlyMonotone M (plan M ω t wbar)) :=
  proposition_5' M hM ω hω t wbar hw
