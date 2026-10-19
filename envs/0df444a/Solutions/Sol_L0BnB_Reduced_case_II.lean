-- Prove2me | solution 1 for L0BnB.Reduced.case_II
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-19T04:41:03.245925+00:00
-- url     : https://prove2.me/submissions/fa6cf910-396d-40b8-bec9-985045e5df1b

import Definitions.Def_L0BnB_Reduced_Setup

section

open Set L0BnB.Reduced

namespace SparseProof

lemma feas_abs {M b z s : ℝ} (h : CoordFeas M b z s) : |b| ≤ M * z := by
  exact abs_le.mpr ⟨by linarith [h.2.1], h.2.2.1⟩

lemma feas_square {M b z s : ℝ} (h : CoordFeas M b z s) : b ^ 2 ≤ s := by
  nlinarith [h.1, mul_nonneg h.2.2.2.2.2 (sub_nonneg.mpr h.2.2.2.2.1)]

lemma feas_box {M b z s : ℝ} (hM : 0 < M) (h : CoordFeas M b z s) : |b| ≤ M := by
  exact (feas_abs h).trans (by nlinarith [h.2.2.2.2.1])

lemma zhat_le {M b z s : ℝ} (hM : 0 < M) (h : CoordFeas M b z s) : zhat M b s ≤ z := by
  apply max_le
  · by_cases hs : s = 0
    · simpa [hs] using h.2.2.2.1
    · apply (div_le_iff₀ (lt_of_le_of_ne h.2.2.2.2.2 (Ne.symm hs))).mpr
      nlinarith [h.1]
  · exact (div_le_iff₀ hM).mpr (by nlinarith [feas_abs h])

lemma zhat_feas {M b s : ℝ} (hM : 0 < M) (hb : |b| ≤ M) (hs : b ^ 2 ≤ s) :
    CoordFeas M b (zhat M b s) s := by
  have hs0 : 0 ≤ s := (sq_nonneg b).trans hs
  have hz0 : 0 ≤ zhat M b s := (div_nonneg (abs_nonneg b) hM.le).trans (le_max_right _ _)
  have hz1 : zhat M b s ≤ 1 := by
    apply max_le
    · by_cases hs' : s = 0
      · simp [hs']
      · exact (div_le_one (lt_of_le_of_ne hs0 (Ne.symm hs'))).mpr hs
    · exact (div_le_one hM).mpr hb
  have hab : |b| ≤ M * zhat M b s := by
    unfold zhat
    have h := (div_le_iff₀ hM).mp (le_max_right (b ^ 2 / s) (|b| / M))
    nlinarith
  refine ⟨?_, ?_, ?_, hz0, hz1, hs0⟩
  · by_cases hs' : s = 0
    · simpa [hs'] using hs
    · have h := (div_le_iff₀ (lt_of_le_of_ne hs0 (Ne.symm hs'))).mp
        (le_max_left (b ^ 2 / s) (|b| / M))
      unfold zhat
      nlinarith
  · linarith [neg_abs_le b]
  · exact (le_abs_self b).trans hab

lemma obj_eq {lam0 lam2 M b s : ℝ} (h0 : 0 < lam0) :
    obj36 lam0 lam2 M b s = lam0 * zhat M b s + lam2 * s := by
  unfold obj36 zhat
  rw [mul_max_of_nonneg _ _ h0.le, max_add_add_right]

lemma reduction (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hb : |b| ≤ M) :
    (∀ z s : ℝ, CoordFeas M b z s → b ^ 2 ≤ s ∧ zhat M b s ≤ z) ∧
    (∀ s : ℝ, b ^ 2 ≤ s → CoordFeas M b (zhat M b s) s) ∧
    (∀ v : ℝ, IsLeast (omegaValues lam0 lam2 M b) v ↔ IsLeast (values36 lam0 lam2 M b) v) := by
  refine ⟨fun z s h => ⟨feas_square h, zhat_le hM h⟩, fun s hs => zhat_feas hM hb hs, ?_⟩
  intro v
  constructor
  · rintro ⟨⟨z, s, hf, hv⟩, hlo⟩
    have hm : obj36 lam0 lam2 M b s ≤ v := by
      rw [obj_eq h0, hv]
      linarith [mul_le_mul_of_nonneg_left (zhat_le hM hf) h0.le]
    have hmem : obj36 lam0 lam2 M b s ∈ omegaValues lam0 lam2 M b :=
      ⟨zhat M b s, s, zhat_feas hM hb (feas_square hf), obj_eq h0⟩
    refine ⟨⟨s, feas_square hf, le_antisymm (hlo hmem) hm⟩, ?_⟩
    rintro w ⟨t, ht, rfl⟩
    exact hlo ⟨zhat M b t, t, zhat_feas hM hb ht, obj_eq h0⟩
  · rintro ⟨⟨s, hs, hv⟩, hlo⟩
    refine ⟨⟨zhat M b s, s, zhat_feas hM hb hs, hv.trans (obj_eq h0)⟩, ?_⟩
    rintro w ⟨z, t, hf, rfl⟩
    have h := hlo (show obj36 lam0 lam2 M b t ∈ values36 lam0 lam2 M b from ⟨t, feas_square hf, rfl⟩)
    rw [obj_eq h0] at h
    linarith [mul_le_mul_of_nonneg_left (zhat_le hM hf) h0.le]

lemma simple_feas {M b : ℝ} (hb : |b| ≤ M) : CoordFeas M b 1 (b ^ 2) := by
  rcases abs_le.mp hb with ⟨hl, hu⟩
  dsimp [CoordFeas]
  simp only [mul_one]
  exact ⟨le_rfl, hl, hu, zero_le_one, le_rfl, sq_nonneg b⟩

lemma perspective_bound {k t z s : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) (hz : 0 ≤ z)
    (hs : 0 ≤ s) (hcone : t ^ 2 ≤ s * z) : 2 * k * t ≤ k ^ 2 * z + s := by
  by_cases hz' : z = 0
  · have ht0 : t = 0 := by nlinarith
    simp [hz', ht0, hs]
  · have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hz')
    by_contra h
    have hn := mul_neg_of_pos_of_neg hzp (sub_neg.mpr (not_le.mp h))
    nlinarith [sq_nonneg (k * z - t)]

end SparseProof

end

section

open Set L0BnB.Reduced

namespace SparseProof

lemma scaled_feas {M b k : ℝ} (hk : 0 < k) (hkM : k ≤ M) (hb : |b| ≤ k) :
    CoordFeas M b (|b| / k) (k * |b|) := by
  have hz := div_nonneg (abs_nonneg b) hk.le
  have he := div_mul_cancel₀ |b| hk.ne'
  have hab : |b| ≤ M * (|b| / k) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkM) hz]
  refine ⟨?_, ?_, (le_abs_self b).trans hab, hz, (div_le_one hk).mpr hb, mul_nonneg hk.le (abs_nonneg b)⟩
  · have hh : (k * |b|) * (|b| / k) = b ^ 2 := by
      field_simp
      nlinarith [sq_abs b]
    exact hh.ge
  · linarith [neg_abs_le b]

lemma low_least {lam2 M b k : ℝ} (h2 : 0 < lam2) (hk : 0 < k) (hkM : k ≤ M)
    (hb : |b| ≤ k) : IsLeast (omegaValues (lam2 * k ^ 2) lam2 M b) (2 * lam2 * k * |b|) := by
  refine ⟨⟨|b| / k, k * |b|, scaled_feas hk hkM hb, ?_⟩, ?_⟩
  · field_simp
    <;> ring
  · rintro w ⟨z, s, hf, rfl⟩
    have hp := perspective_bound hk.le (abs_nonneg b) hf.2.2.2.1 hf.2.2.2.2.2
      (show |b| ^ 2 ≤ s * z by simpa only [sq_abs] using hf.1)
    nlinarith [mul_le_mul_of_nonneg_left hp h2.le]

lemma high_least {lam2 M b k : ℝ} (h2 : 0 < lam2) (hk : 0 < k) (hkb : k ≤ |b|)
    (hb : |b| ≤ M) : IsLeast (omegaValues (lam2 * k ^ 2) lam2 M b) (lam2 * k ^ 2 + lam2 * b ^ 2) := by
  refine ⟨⟨1, b ^ 2, simple_feas hb, by ring⟩, ?_⟩
  rintro w ⟨z, s, hf, rfl⟩
  have hsq : k ^ 2 ≤ b ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
  have hsk : k ^ 2 ≤ s := hsq.trans (feas_square hf)
  have h : k ^ 2 + b ^ 2 ≤ k ^ 2 * z + s := by
    nlinarith [hf.1, mul_nonneg (sub_nonneg.mpr hsk) (sub_nonneg.mpr hf.2.2.2.2.1)]
  have hm := mul_le_mul_of_nonneg_left h h2.le
  convert! hm using 1 <;> ring

lemma narrow_least {lam2 M b k : ℝ} (h2 : 0 < lam2) (hM : 0 < M) (hMk : M ≤ k)
    (hb : |b| ≤ M) : IsLeast (omegaValues (lam2 * k ^ 2) lam2 M b)
      ((lam2 * k ^ 2 / M + lam2 * M) * |b|) := by
  refine ⟨⟨|b| / M, M * |b|, scaled_feas hM le_rfl hb, by ring⟩, ?_⟩
  rintro w ⟨z, s, hf, rfl⟩
  have hp := perspective_bound hM.le (abs_nonneg b) hf.2.2.2.1 hf.2.2.2.2.2
    (show |b| ^ 2 ≤ s * z by simpa only [sq_abs] using hf.1)
  have ha : |b| / M ≤ z := (div_le_iff₀ hM).mpr (by nlinarith [feas_abs hf])
  have hk2 : 0 ≤ k ^ 2 - M ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left ha hk2
  have he : (k ^ 2 / M + M) * |b| = 2 * M * |b| + (k ^ 2 - M ^ 2) * (|b| / M) := by
    field_simp
    <;> ring
  have h : (k ^ 2 / M + M) * |b| ≤ k ^ 2 * z + s := by rw [he]; nlinarith
  have hm := mul_le_mul_of_nonneg_left h h2.le
  convert! hm using 1 <;> ring

lemma psi1_formula {lam0 lam2 b : ℝ} (h0 : 0 < lam0) (h2 : 0 < lam2) :
    psi1 lam0 lam2 b =
      if |b| ≤ Real.sqrt (lam0 / lam2) then 2 * lam2 * Real.sqrt (lam0 / lam2) * |b|
      else lam0 + lam2 * b ^ 2 := by
  let k := Real.sqrt (lam0 / lam2)
  have hk : 0 < k := Real.sqrt_pos.mpr (div_pos h0 h2)
  have hs : lam2 * k ^ 2 = lam0 := by
    dsimp [k]
    rw [Real.sq_sqrt (div_pos h0 h2).le]
    exact mul_div_cancel₀ lam0 h2.ne'
  have hq : Real.sqrt (lam2 / lam0) = k⁻¹ := by
    dsimp [k]
    rw [← Real.sqrt_inv, inv_div]
  have hab : |b * Real.sqrt (lam2 / lam0)| = |b| / k := by
    rw [hq, abs_mul, abs_inv, abs_of_pos hk, div_eq_mul_inv]
  unfold psi1 reverseHuber
  simp only [hab]
  simp only [div_le_one hk]
  rw [hq]
  change (2 * lam0 * if |b| ≤ k then |b| / k else ((b * k⁻¹) ^ 2 + 1) / 2) =
    if |b| ≤ k then 2 * lam2 * k * |b| else lam0 + lam2 * b ^ 2
  by_cases hb : |b| ≤ k
  · simp only [if_pos hb]
    rw [← hs]
    field_simp
    <;> ring
  · simp only [if_neg hb]
    rw [← hs]
    field_simp
    <;> ring

lemma case_one (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M) (hb : |b| ≤ M) :
    IsLeast (omegaValues lam0 lam2 M b) (psi1 lam0 lam2 b) := by
  have hk : 0 < Real.sqrt (lam0 / lam2) := Real.sqrt_pos.mpr (div_pos h0 h2)
  have hs : lam2 * Real.sqrt (lam0 / lam2) ^ 2 = lam0 := by
    rw [Real.sq_sqrt (div_pos h0 h2).le]
    exact mul_div_cancel₀ lam0 h2.ne'
  rw [psi1_formula h0 h2]
  split_ifs with h
  · simpa only [hs] using low_least h2 hk hreg h
  · simpa only [hs] using high_least h2 hk (not_le.mp h).le hb

lemma case_two (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2)) (hb : |b| ≤ M) :
    IsLeast (omegaValues lam0 lam2 M b) (psi2 lam0 lam2 M b) := by
  have hs : lam2 * Real.sqrt (lam0 / lam2) ^ 2 = lam0 := by
    rw [Real.sq_sqrt (div_pos h0 h2).le]
    exact mul_div_cancel₀ lam0 h2.ne'
  simpa only [hs, psi2] using narrow_least h2 hM hreg.le hb

lemma coord_least (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hb : |b| ≤ M) : IsLeast (omegaValues lam0 lam2 M b) (psi lam0 lam2 M b) := by
  unfold psi
  split_ifs with h
  · exact case_one lam0 lam2 M b h0 h2 hM h hb
  · exact case_two lam0 lam2 M b h0 h2 hM (not_le.mp h) hb

end SparseProof

end

section

open Set L0BnB.Reduced

namespace SparseProof

lemma continuous_reverse : Continuous reverseHuber := by
  unfold reverseHuber
  apply (continuous_abs : Continuous (fun x : ℝ => |x|)).if_le
    (((continuous_id.pow 2).add continuous_const).div_const 2) continuous_abs continuous_const
  intro x hx
  change |x| = (x ^ 2 + 1) / 2
  nlinarith [sq_abs x]

lemma continuous_psi (lam0 lam2 M : ℝ) : Continuous (psi lam0 lam2 M) := by
  unfold psi
  split_ifs
  · exact continuous_const.mul (continuous_reverse.comp (continuous_id.mul_const _))
  · exact continuous_const.mul continuous_abs

lemma continuous_F {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ) :
    Continuous (F X y lam0 lam2 M) := by
  unfold F
  apply Continuous.add
  · unfold lsLoss Matrix.mulVec dotProduct
    fun_prop
  · apply continuous_finset_sum
    intro i hi
    exact (continuous_psi lam0 lam2 M).comp (continuous_apply i)

lemma compact_box (p : ℕ) (M : ℝ) : IsCompact (box p M) := by
  have he : box p M = Icc (fun _ : Fin p => -M) (fun _ => M) := by
    ext b
    simp only [box, mem_setOf_eq, mem_Icc, Pi.le_def]
    constructor
    · intro h
      exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩
    · rintro ⟨hl, hu⟩ i
      exact abs_le.mpr ⟨hl i, hu i⟩
  rw [he]
  exact isCompact_Icc

lemma obj_sum {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 : ℝ) (b z s : Fin p → ℝ) :
    PRObj X y lam0 lam2 b z s = lsLoss X y b + ∑ i, (lam0 * z i + lam2 * s i) := by
  simp only [PRObj, Finset.sum_add_distrib, Finset.mul_sum]
  ring

lemma fixed_least {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (b : Fin p → ℝ) (hb : b ∈ box p M) :
    IsLeast (PRValuesAt X y lam0 lam2 M b) (F X y lam0 lam2 M b) := by
  have hc := fun i => coord_least lam0 lam2 M (b i) h0 h2 hM (hb i)
  have hex : ∀ i, ∃ z s, CoordFeas M (b i) z s ∧ psi lam0 lam2 M (b i) = lam0 * z + lam2 * s :=
    fun i => (hc i).1
  choose z s hf he using hex
  refine ⟨⟨z, s, hf, ?_⟩, ?_⟩
  · rw [obj_sum, F]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => he i)
  · rintro v ⟨z', s', hf', rfl⟩
    rw [obj_sum, F]
    have hh : (∑ i, psi lam0 lam2 M (b i)) ≤ ∑ i, (lam0 * z' i + lam2 * s' i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hc i).2 ⟨z' i, s' i, hf' i, rfl⟩
    linarith

lemma full {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M) :
    (∀ b : Fin p → ℝ, (∃ z s : Fin p → ℝ, PRFeas M b z s) ↔ b ∈ box p M) ∧
    (∀ b ∈ box p M, IsLeast (PRValuesAt X y lam0 lam2 M b) (F X y lam0 lam2 M b)) ∧
    (IsLeast (PRValues X y lam0 lam2 M) (VPR X y lam0 lam2 M) ∧
      IsLeast (F X y lam0 lam2 M '' box p M) (VPR X y lam0 lam2 M)) := by
  have heq : ∀ b : Fin p → ℝ, (∃ z s : Fin p → ℝ, PRFeas M b z s) ↔ b ∈ box p M := by
    intro b
    constructor
    · rintro ⟨z, s, hf⟩ i
      exact feas_box hM (hf i)
    · intro hb
      exact ⟨fun _ => 1, fun i => (b i) ^ 2, fun i => simple_feas (hb i)⟩
  have hfixed := fun b hb => fixed_least X y lam0 lam2 M h0 h2 hM b hb
  have hne : (box p M).Nonempty := ⟨fun _ => 0, fun _ => by simpa using hM.le⟩
  obtain ⟨b, hb, hmin⟩ := (compact_box p M).exists_isMinOn hne (continuous_F X y lam0 lam2 M).continuousOn
  have hleast : IsLeast (F X y lam0 lam2 M '' box p M) (F X y lam0 lam2 M b) := by
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    rintro v ⟨b', hb', rfl⟩
    exact hmin hb'
  have hv : VPR X y lam0 lam2 M = F X y lam0 lam2 M b := hleast.csInf_eq
  refine ⟨heq, hfixed, ?_, ?_⟩
  · rw [hv]
    obtain ⟨z, s, hf, hval⟩ := (hfixed b hb).1
    refine ⟨⟨b, z, s, hf, hval⟩, ?_⟩
    rintro v ⟨b', z', s', hf', hval'⟩
    have hb' := (heq b').mp ⟨z', s', hf'⟩
    exact (hleast.2 ⟨b', hb', rfl⟩).trans ((hfixed b' hb').2 ⟨z', s', hf', hval'⟩)
  · rwa [hv]

end SparseProof

end

open L0BnB.Reduced


/-- Proof of Theorem 1, Case II, p. 28: if `√(λ₀/λ₂) > M` and `|b| ≤ M`, then
`ω(b; λ₀, λ₂, M) = (λ₀/M + λ₂M)|b| = ψ₂(b; λ₀, λ₂, M)`. -/
theorem solution (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2)) (hb : |b| ≤ M) :
    IsLeast (omegaValues lam0 lam2 M b) (psi2 lam0 lam2 M b) := by
  exact SparseProof.case_two lam0 lam2 M b h0 h2 hM hreg hb

