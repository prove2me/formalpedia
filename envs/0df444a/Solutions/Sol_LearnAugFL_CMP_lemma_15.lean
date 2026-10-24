-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:05:20.001749+00:00
-- url     : https://prove2.me/submissions/d66c2f10-35e3-4d23-9001-c9bd26d62847

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting
import Theorems.Thm_LearnAugFL_CMP_lemma_28

-- Inline checked local helper: Median.lean

namespace LearnAugFL.CMP.HalfAxisProof

lemma sign_monotone : Monotone Real.sign := by
  intro a b hab
  unfold Real.sign
  split_ifs <;> norm_num <;> linarith

lemma sort_sign (s : Multiset ℝ) :
    (s.map Real.sign).sort (· ≤ ·) = (s.sort (· ≤ ·)).map Real.sign := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Multiset.pairwise_sort _ _
  · exact (Multiset.pairwise_sort s (· ≤ ·)).map Real.sign (fun _ _ h => sign_monotone h)
  · apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq, ← Multiset.map_coe, Multiset.sort_eq]

lemma median_sign (s : Multiset ℝ) :
    lowerMedian (s.map Real.sign) = Real.sign (lowerMedian s) := by
  unfold lowerMedian
  rw [sort_sign]
  simp only [Multiset.card_map]
  simpa only [Real.sign_zero] using (List.getD_map (l := s.sort (· ≤ ·)) (d := (0 : ℝ)) Real.sign)

lemma median_zero_of_sign (s t : Multiset ℝ) (h : s.map Real.sign = t.map Real.sign)
    (hs : lowerMedian s = 0) : lowerMedian t = 0 := by
  apply Real.sign_eq_zero_iff.mp
  rw [← median_sign, ← h, median_sign, hs, Real.sign_zero]

lemma cmp_zero_of_sign {n k : ℕ} (P Q : Fin n → Pt) (b d : Pt)
    (hPQ : ∀ i j, Real.sign (P i j) = Real.sign (Q i j))
    (hbd : ∀ j, Real.sign (b j) = Real.sign (d j))
    (hP : cmp P b k = 0) : cmp Q d k = 0 := by
  have hm (j : Fin 2) : lowerMedian (coordValues P b k j) = 0 := by
    have hh := congrArg (fun x : Pt => x j) hP
    fin_cases j <;> simpa [cmp] using hh
  have hs (j : Fin 2) : (coordValues P b k j).map Real.sign =
      (coordValues Q d k j).map Real.sign := by
    simp only [coordValues, Multiset.map_add, Multiset.map_map,
      Multiset.map_replicate, Function.comp_def]
    congr 2
    · funext i
      exact hPQ i j
    · exact hbd j
  ext j
  fin_cases j <;> simpa [cmp] using median_zero_of_sign _ _ (hs _) (hm _)

end LearnAugFL.CMP.HalfAxisProof

-- Inline checked local helper: Geometry.lean

namespace LearnAugFL.CMP.HalfAxisProof

noncomputable def move (p q : Pt) (ε : ℝ) : Pt := (1 - ε) • p + ε • q

lemma move_eq (p q : Pt) (ε : ℝ) : move p q ε = p + ε • (q - p) := by
  unfold move
  simp only [sub_smul, one_smul, smul_sub]
  abel

lemma move_apply (p q : Pt) (ε : ℝ) (j : Fin 2) :
    move p q ε j = (1 - ε) * p j + ε * q j := rfl

lemma norm_axis_x (p : Pt) (hp : p 1 = 0) : ‖p‖ = |p 0| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs,
    Real.sqrt_sq_eq_abs]

lemma norm_axis_y (p : Pt) (hp : p 0 = 0) : ‖p‖ = |p 1| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs,
    Real.sqrt_sq_eq_abs]

lemma sign_mix (a b ε : ℝ) (h : Real.sign a = Real.sign b)
    (hε : 0 < ε) (hε1 : ε < 1) :
    Real.sign ((1 - ε) * a + ε * b) = Real.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : b < 0 := by
      by_contra hb
      have hb' : 0 ≤ b := le_of_not_gt hb
      rw [Real.sign_of_neg ha] at h
      unfold Real.sign at h
      split_ifs at h <;> linarith
    rw [Real.sign_of_neg ha, Real.sign_of_neg]
    exact add_neg (mul_neg_of_pos_of_neg (sub_pos.mpr hε1) ha) (mul_neg_of_pos_of_neg hε hb)
  · subst a
    have hb : b = 0 := Real.sign_eq_zero_iff.mp (by rw [← h, Real.sign_zero])
    simp [hb]
  · have hb : 0 < b := by
      by_contra hb
      have hb' : b ≤ 0 := le_of_not_gt hb
      rw [Real.sign_of_pos ha] at h
      unfold Real.sign at h
      split_ifs at h <;> linarith
    rw [Real.sign_of_pos ha, Real.sign_of_pos]
    exact add_pos (mul_pos (sub_pos.mpr hε1) ha) (mul_pos hε hb)

def SameHalf (p q : Pt) : Prop :=
  (posX' p ∧ posX' q) ∨ (negX' p ∧ negX' q) ∨
    (posY' p ∧ posY' q) ∨ (negY' p ∧ negY' q)

lemma half_sign (p q : Pt) (h : SameHalf p q) (j : Fin 2) :
    Real.sign (p j) = Real.sign (q j) := by
  rcases h with ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩ | ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩ |
    ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩ | ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩
  all_goals fin_cases j <;> simp_all [Real.sign_of_pos, Real.sign_of_neg]

lemma half_zero_coord (p q : Pt) (h : SameHalf p q) :
    ∃ j : Fin 2, p j = 0 ∧ q j = 0 := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact ⟨1, hp.1, hq.1⟩
  · exact ⟨1, hp.1, hq.1⟩
  · exact ⟨0, hp.1, hq.1⟩
  · exact ⟨0, hp.1, hq.1⟩

lemma axis_noncollinear (p q o : Pt) (hpq : p ≠ q) (h : SameHalf p q)
    (ho : ∀ j, 0 < o j) : ¬ Collinear ℝ ({p, q, o} : Set Pt) := by
  intro hc
  obtain ⟨j, hp, hq⟩ := half_zero_coord p q h
  have hm := hc.mem_affineSpan_of_mem_of_ne (by simp : p ∈ ({p,q,o} : Set Pt))
    (by simp : q ∈ ({p,q,o} : Set Pt)) (by simp : o ∈ ({p,q,o} : Set Pt)) hpq
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hm
  have he := congrArg (fun v : Pt => v j) ht
  simp [AffineMap.lineMap_apply_module, hp, hq] at he
  exact (ne_of_gt (ho j)) he.symm

lemma half_norm_move (p q : Pt) (h : SameHalf p q) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ‖move p q ε‖ = (1 - ε) * ‖p‖ + ε * ‖q‖ := by
  rcases h with ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩ | ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩ |
    ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩ | ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩
  · have hm : move p q ε 1 = 0 := by simp [move_apply, hp, hq]
    rw [norm_axis_x _ hm, norm_axis_x _ hp, norm_axis_x _ hq, move_apply,
      abs_of_pos hp', abs_of_pos hq', abs_of_pos]
    exact add_pos (mul_pos (sub_pos.mpr hε1) hp') (mul_pos hε hq')
  · have hm : move p q ε 1 = 0 := by simp [move_apply, hp, hq]
    rw [norm_axis_x _ hm, norm_axis_x _ hp, norm_axis_x _ hq, move_apply,
      abs_of_neg hp', abs_of_neg hq', abs_of_neg]
    · ring
    · exact add_neg (mul_neg_of_pos_of_neg (sub_pos.mpr hε1) hp') (mul_neg_of_pos_of_neg hε hq')
  · have hm : move p q ε 0 = 0 := by simp [move_apply, hp, hq]
    rw [norm_axis_y _ hm, norm_axis_y _ hp, norm_axis_y _ hq, move_apply,
      abs_of_pos hp', abs_of_pos hq', abs_of_pos]
    exact add_pos (mul_pos (sub_pos.mpr hε1) hp') (mul_pos hε hq')
  · have hm : move p q ε 0 = 0 := by simp [move_apply, hp, hq]
    rw [norm_axis_y _ hm, norm_axis_y _ hp, norm_axis_y _ hq, move_apply,
      abs_of_neg hp', abs_of_neg hq', abs_of_neg]
    · ring
    · exact add_neg (mul_neg_of_pos_of_neg (sub_pos.mpr hε1) hp') (mul_neg_of_pos_of_neg hε hq')

end LearnAugFL.CMP.HalfAxisProof

-- Inline checked local helper: Total.lean

namespace LearnAugFL.CMP.HalfAxisProof

noncomputable def total {n : ℕ} (P : Fin n → Pt) (f : Pt) : ℝ := ∑ i, dist f (P i)

lemma total_nonneg {n : ℕ} (P : Fin n → Pt) (f : Pt) : 0 ≤ total P f :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma total_zero {n : ℕ} (P : Fin n → Pt) (o : Pt) (h : total P o = 0) :
    P = fun _ => o := by
  funext i
  have hi : dist o (P i) ≤ total P o := Finset.single_le_sum
    (fun _ _ => dist_nonneg) (Finset.mem_univ i)
  have hdist : dist o (P i) = 0 := le_antisymm (by simpa [h] using hi) dist_nonneg
  exact (dist_eq_zero.mp hdist).symm

lemma ratio_total {n k : ℕ} (hn : n ≠ 0) (P : Fin n → Pt) (b o : Pt) :
    ratio P b o k = total P (cmp P b k) / total P o := by
  unfold ratio ucost total
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) _ _

lemma total_update {n : ℕ} (P : Fin n → Pt) (i : Fin n) (p f : Pt) :
    total (Function.update P i p) f = total P f - dist f (P i) + dist f p := by
  classical
  unfold total
  have hfun : (fun j => dist f (Function.update P i p j)) =
      Function.update (fun j => dist f (P j)) i (dist f p) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => dist f (P j)) (Finset.mem_univ i)
  linarith

lemma total_pos {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (hij : P i ≠ P j) (z : Pt) :
    0 < total P z := by
  refine lt_of_le_of_ne (total_nonneg P z) ?_
  intro he
  have hh := total_zero P z he.symm
  exact hij (by simp [hh])

lemma isOpt_iff {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt) :
    IsOpt P o ↔ ∀ z, total P o ≤ total P z := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  simp only [IsOpt, ucost, total, div_le_div_iff_of_pos_right hnR]

lemma continuous_total {n : ℕ} (P : Fin n → Pt) : Continuous (total P) := by
  unfold total
  fun_prop

noncomputable def perturb {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (ε : ℝ) : Fin n → Pt :=
  Function.update (Function.update P i (move (P i) (P j) ε)) j (move (P j) (P i) ε)

lemma total_perturb {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (hij : i ≠ j)
    (ε : ℝ) (z : Pt) :
    total (perturb P i j ε) z = total P z - dist z (P i) - dist z (P j) +
      dist z (move (P i) (P j) ε) + dist z (move (P j) (P i) ε) := by
  unfold perturb
  rw [total_update, total_update, Function.update_of_ne hij.symm]
  ring

lemma half_symm {p q : Pt} (h : SameHalf p q) : SameHalf q p := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr h.symm))

lemma perturb_origin {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (hij : i ≠ j)
    (hh : SameHalf (P i) (P j)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    total (perturb P i j ε) 0 = total P 0 := by
  rw [total_perturb P i j hij]
  simp only [dist_zero_left, half_norm_move _ _ hh ε hε hε1,
    half_norm_move _ _ (half_symm hh) ε hε hε1]
  ring

lemma perturb_sign {n : ℕ} (P : Fin n → Pt) (i j : Fin n)
    (hh : SameHalf (P i) (P j)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ l a, Real.sign (P l a) = Real.sign (perturb P i j ε l a) := by
  intro l a
  unfold perturb
  by_cases hlj : l = j
  · subst l
    simp only [Function.update_self, move_apply]
    exact (sign_mix _ _ ε (half_sign _ _ hh a).symm hε hε1).symm
  · rw [Function.update_of_ne hlj]
    by_cases hli : l = i
    · subst l
      simp only [Function.update_self, move_apply]
      exact (sign_mix _ _ ε (half_sign _ _ hh a) hε hε1).symm
    · rw [Function.update_of_ne hli]

lemma perturb_distinct {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (hij : P i ≠ P j)
    (ε : ℝ) (hε : ε < 1 / 2) : perturb P i j ε i ≠ perturb P i j ε j := by
  have hij' : i ≠ j := fun h => hij (congrArg P h)
  simp only [perturb, Function.update_of_ne hij', Function.update_self]
  intro he
  have hh : (1 - 2 * ε) • (P i - P j) = 0 := by
    have : move (P i) (P j) ε - move (P j) (P i) ε = 0 := sub_eq_zero.mpr he
    convert this using 1 <;> (unfold move; module)
  exact hij (sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (by linarith)))

end LearnAugFL.CMP.HalfAxisProof

-- Inline checked local helper: Stability.lean

namespace LearnAugFL.CMP.HalfAxisProof

lemma stability_total_le {n : ℕ} (P Q : Fin n → Pt) (δ : ℝ)
    (h : ∀ i, dist (Q i) (P i) ≤ δ) (z : Pt) :
    total Q z ≤ total P z + n * δ := by
  have hpoint (i : Fin n) : dist z (Q i) ≤ dist z (P i) + δ := by
    have ht := dist_triangle z (P i) (Q i)
    rw [dist_comm (P i) (Q i)] at ht
    exact ht.trans (add_le_add le_rfl (h i))
  have hs := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => hpoint i)
  simpa only [total, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using hs

lemma stability_total_convex {n : ℕ} (P : Fin n → Pt) :
    ConvexOn ℝ Set.univ (total P) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change (∑ i, dist (a • x + b • y) (P i)) ≤
    a * (∑ i, dist x (P i)) + b * (∑ i, dist y (P i))
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact (convexOn_univ_dist (P i)).2 hx hy ha hb hab

lemma opt_stable {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (hP : IsOpt P o) (huniq : ∀ z, IsOpt P z → z = o) (r : ℝ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Fin n → Pt, (∀ i, dist (Q i) (P i) < δ) →
      ∃ oQ : Pt, IsOpt Q oQ ∧ dist oQ o < r := by
  have hmin := (isOpt_iff hn P o).mp hP
  have hstrict (z : Pt) (hz : z ∈ Metric.sphere o r) : total P o < total P z := by
    apply lt_of_le_of_ne (hmin z)
    intro he
    have hzopt : IsOpt P z := (isOpt_iff hn P z).mpr (fun w => by rw [← he]; exact hmin w)
    have hzo := huniq z hzopt
    subst z
    have heq : (0 : ℝ) = r := by simpa using hz
    linarith
  obtain ⟨α, hα, hbound⟩ := (isCompact_sphere o r).exists_forall_le'
    (continuous_total P).continuousOn hstrict
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let δ := (α - total P o) / (4 * n)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hα) (by positivity)
  have hδeq : 4 * (n : ℝ) * δ = α - total P o := by
    dsimp [δ]
    field_simp
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ
  have hQP (z : Pt) : total Q z ≤ total P z + n * δ :=
    stability_total_le P Q δ (fun i => (hQ i).le) z
  have hPQ (z : Pt) : total P z ≤ total Q z + n * δ :=
    stability_total_le Q P δ (fun i => by simpa only [dist_comm] using (hQ i).le) z
  have hboundary (z : Pt) (hz : z ∈ Metric.sphere o r) : total Q o < total Q z := by
    have hp := hbound z hz
    have hleft := hQP o
    have hright := hPQ z
    nlinarith only [hp, hleft, hright, hδeq, hα]
  obtain ⟨oQ, hoQ, hQmin⟩ := (isCompact_closedBall o r).exists_isMinOn
    ⟨o, Metric.mem_closedBall_self hr.le⟩ (continuous_total Q).continuousOn
  have hinside : dist oQ o < r := by
    have hle : dist oQ o ≤ r := hoQ
    apply lt_of_le_of_ne hle
    intro he
    have hsphere : oQ ∈ Metric.sphere o r := he
    have hb := hboundary oQ hsphere
    have hm : total Q oQ ≤ total Q o := hQmin (Metric.mem_closedBall_self hr.le)
    linarith
  refine ⟨oQ, ?_, hinside⟩
  apply (isOpt_iff hn Q oQ).mpr
  exact IsMinOn.of_isLocalMin_of_convex_univ
    (hQmin.isLocalMin (Metric.closedBall_mem_nhds_of_mem hinside)) (stability_total_convex Q)

end LearnAugFL.CMP.HalfAxisProof

-- Inline checked local helper: Uniqueness.lean

namespace LearnAugFL.CMP.HalfAxisProof

lemma midpoint_dist (x y p : Pt) :
    dist ((1 / 2 : ℝ) • (x + y)) p ≤ (dist x p + dist y p) / 2 := by
  have he : (1 / 2 : ℝ) • (x + y) - p = (1 / 2 : ℝ) • ((x - p) + (y - p)) := by module
  rw [dist_eq_norm, he, norm_smul, Real.norm_of_nonneg (by norm_num)]
  have h := norm_add_le (x - p) (y - p)
  simp only [dist_eq_norm]
  linarith

lemma optimal_sameRay {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o z : Pt)
    (ho : IsOpt P o) (hz : IsOpt P z) (i : Fin n) : SameRay ℝ (o - P i) (z - P i) := by
  by_contra hh
  have he : (1 / 2 : ℝ) • (o + z) - P i = (1 / 2 : ℝ) • ((o - P i) + (z - P i)) := by module
  have hs : dist ((1 / 2 : ℝ) • (o + z)) (P i) < (dist o (P i) + dist z (P i)) / 2 := by
    rw [dist_eq_norm, he, norm_smul, Real.norm_of_nonneg (by norm_num)]
    have h := norm_add_lt_of_not_sameRay hh
    simp only [dist_eq_norm]
    linarith
  have hsum : total P ((1 / 2 : ℝ) • (o + z)) < (total P o + total P z) / 2 := by
    unfold total
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_lt_sum (s := Finset.univ)
      (fun j _ => midpoint_dist o z (P j)) ⟨i, Finset.mem_univ _, hs⟩
  have hm := (isOpt_iff hn P o).mp ho ((1 / 2 : ℝ) • (o + z))
  have hz' := (isOpt_iff hn P z).mp hz o
  linarith

lemma sameRay_collinear (p o z : Pt) (hpo : p ≠ o) (h : SameRay ℝ (o - p) (z - p)) :
    Collinear ℝ ({o, z, p} : Set Pt) := by
  obtain ⟨r, _, hr⟩ := h.exists_nonneg_left (sub_ne_zero.mpr hpo.symm)
  apply (collinear_iff_of_mem (by simp : p ∈ ({o, z, p} : Set Pt))).2
  refine ⟨o - p, ?_⟩
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with hw | hw | hw
  · subst w
    exact ⟨1, by simp⟩
  · subst w
    refine ⟨r, ?_⟩
    change z = r • (o - p) + p
    rw [hr]
    simp
  · subst w
    exact ⟨0, by simp⟩

lemma optimum_unique {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (ho : IsOpt P o) (i j : Fin n) (hc : ¬ Collinear ℝ ({P i, P j, o} : Set Pt)) :
    ∀ z, IsOpt P z → z = o := by
  intro z hz
  by_contra hzo
  have h1 := sameRay_collinear (P i) o z (ne₁₃_of_not_collinear hc)
    (optimal_sameRay hn P o z ho hz i)
  have h2 := sameRay_collinear (P j) o z (ne₂₃_of_not_collinear hc)
    (optimal_sameRay hn P o z ho hz j)
  have hp1 := h1.mem_affineSpan_of_mem_of_ne (by simp : o ∈ ({o,z,P i} : Set Pt))
    (by simp : z ∈ ({o,z,P i} : Set Pt)) (by simp : P i ∈ ({o,z,P i} : Set Pt)) (Ne.symm hzo)
  have hp2 := h2.mem_affineSpan_of_mem_of_ne (by simp : o ∈ ({o,z,P j} : Set Pt))
    (by simp : z ∈ ({o,z,P j} : Set Pt)) (by simp : P j ∈ ({o,z,P j} : Set Pt)) (Ne.symm hzo)
  exact hc (collinear_triple_of_mem_affineSpan_pair hp1 hp2 (left_mem_affineSpan_pair ℝ o z))

end LearnAugFL.CMP.HalfAxisProof

-- Inline checked local helper: Perturbation.lean

namespace LearnAugFL.CMP.HalfAxisProof

lemma move_distance (p q : Pt) (ε : ℝ) (hε : 0 ≤ ε) :
    dist (move p q ε) p = ε * dist p q := by
  rw [move_eq, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε]
  rw [← dist_eq_norm, dist_comm]

lemma perturb_close {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hclose : ε * dist (P i) (P j) < δ) :
    ∀ l, dist (perturb P i j ε l) (P l) < δ := by
  intro l
  by_cases hlj : l = j
  · subst l
    simpa only [perturb, Function.update_self, move_distance _ _ ε hε, dist_comm (P j) (P i)] using hclose
  · simp only [perturb, Function.update_of_ne hlj]
    by_cases hli : l = i
    · subst l
      simpa only [Function.update_self, move_distance _ _ ε hε] using hclose
    · simpa only [Function.update_of_ne hli, dist_self] using hδ

lemma perturb_decreases {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (o : Pt)
    (hc : ¬ Collinear ℝ ({P i, P j, o} : Set Pt))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    total (perturb P i j ε) o < total P o := by
  have hij : i ≠ j := fun h => ne₁₂_of_not_collinear hc (congrArg P h)
  have hstrict := (LearnAugFL.CMP.lemma_28 (P i) (P j) o (ne₁₂_of_not_collinear hc)
    (ne₁₃_of_not_collinear hc) (ne₂₃_of_not_collinear hc) ε hε hε1).2 hc
  rw [total_perturb P i j hij]
  simp only [← move_eq, dist_comm _ o] at hstrict
  linarith

lemma positive_of_close (o q : Pt) (ho : ∀ j, 0 < o j)
    (hq : dist q o < min (o 0) (o 1)) : ∀ j, 0 < q j := by
  intro j
  have hd : |q j - o j| ≤ dist q o := PiLp.dist_apply_le q o j
  have hmin : min (o 0) (o 1) ≤ o j := by fin_cases j <;> simp
  have hh := (abs_le.mp hd).1
  linarith

lemma improved_instance {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (hP : IsOpt P o) (ho : ∀ j, 0 < o j) (i j : Fin n)
    (hij : P i ≠ P j) (hh : SameHalf (P i) (P j))
    (hstability : ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧
      ∀ Q : Fin n → Pt, (∀ i, dist (Q i) (P i) < δ) →
        ∃ oQ : Pt, IsOpt Q oQ ∧ dist oQ o < r) :
    ∃ (Q : Fin n → Pt) (oQ : Pt), IsOpt Q oQ ∧
      (∀ l a, Real.sign (P l a) = Real.sign (Q l a)) ∧ (∀ a, 0 < oQ a) ∧
      total Q 0 = total P 0 ∧ 0 < total Q oQ ∧ total Q oQ < total P o := by
  obtain ⟨δ, hδ, hδQ⟩ := hstability (min (o 0) (o 1)) (lt_min (ho 0) (ho 1))
  have hd : 0 < dist (P i) (P j) + 1 := by positivity
  obtain ⟨ε, hε, hεub⟩ := exists_between
    (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (div_pos hδ hd))
  have hεhalf : ε < 1 / 2 := (lt_min_iff.mp hεub).1
  have hε1 : ε < 1 := by linarith
  have hεd : ε * dist (P i) (P j) < δ := by
    have hh := (lt_div_iff₀ hd).mp (lt_min_iff.mp hεub).2
    nlinarith
  let Q := perturb P i j ε
  obtain ⟨oQ, hQ, hoQ⟩ := hδQ Q (perturb_close P i j ε δ hε.le hδ hεd)
  refine ⟨Q, oQ, hQ, perturb_sign P i j hh ε hε hε1,
    positive_of_close o oQ ho hoQ, ?_, ?_, ?_⟩
  · exact perturb_origin P i j (fun h => hij (congrArg P h)) hh ε hε hε1
  · exact total_pos Q i j (perturb_distinct P i j hij ε hεhalf) oQ
  · exact lt_of_le_of_lt ((isOpt_iff hn Q oQ).mp hQ o)
      (perturb_decreases P i j o (axis_noncollinear _ _ _ hij hh ho) ε hε hε1)

end LearnAugFL.CMP.HalfAxisProof

-- Inline checked local helper: Assembly.lean

namespace LearnAugFL.CMP.HalfAxisProof

lemma main_of_stability (c : ℝ) {n k : ℕ} (hnk : Admissible c n k)
    (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (hpair : ∃ i j : Fin n, P i ≠ P j ∧ SameHalf (P i) (P j))
    (hstability : ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧
      ∀ Q : Fin n → Pt, (∀ i, dist (Q i) (P i) < δ) →
        ∃ oQ : Pt, IsOpt Q oQ ∧ dist oQ o < r) :
    (cmp P o k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P o o k < ratio Q oQ oQ k') ∧
    (cmp P 0 k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P 0 o k < ratio Q 0 oQ k') := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnk.1
  have ho : ∀ j, 0 < o j := by intro j; fin_cases j <;> assumption
  obtain ⟨i, j, hij, hh⟩ := hpair
  obtain ⟨Q, oQ, hQ, hsign, hoQ, hcost, hpos, hdrop⟩ :=
    improved_instance hn P o hP ho i j hij hh hstability
  have hratio (b d : Pt) (hcmpP : cmp P b k = 0) (hcmpQ : cmp Q d k = 0) :
      ratio P b o k < ratio Q d oQ k := by
    rw [ratio_total hn.ne', ratio_total hn.ne', hcmpP, hcmpQ, hcost]
    exact div_lt_div_of_pos_left (total_pos P i j hij 0) hpos hdrop
  constructor
  · intro hcmp
    refine ⟨n, k, Q, oQ, hnk, hQ, hratio o oQ hcmp ?_⟩
    apply cmp_zero_of_sign P Q o oQ hsign _ hcmp
    intro a
    rw [Real.sign_of_pos (ho a), Real.sign_of_pos (hoQ a)]
  · intro hcmp
    refine ⟨n, k, Q, oQ, hnk, hQ, hratio 0 0 hcmp ?_⟩
    exact cmp_zero_of_sign P Q 0 0 hsign (fun _ => rfl) hcmp

end LearnAugFL.CMP.HalfAxisProof

open LearnAugFL.CMP LearnAugFL.CMP.HalfAxisProof

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ} (hnk : Admissible c n k)
    (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (hpair : ∃ i j : Fin n, P i ≠ P j ∧
      ((posX' (P i) ∧ posX' (P j)) ∨ (negX' (P i) ∧ negX' (P j)) ∨
        (posY' (P i) ∧ posY' (P j)) ∨ (negY' (P i) ∧ negY' (P j)))) :
    (cmp P o k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P o o k < ratio Q oQ oQ k') ∧
    (cmp P 0 k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P 0 o k < ratio Q 0 oQ k') := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnk.1
  have ho : ∀ j, 0 < o j := by intro j; fin_cases j <;> assumption
  obtain ⟨i, j, hij, hh⟩ := hpair
  have huniq := optimum_unique hn P o hP i j (axis_noncollinear _ _ _ hij hh ho)
  exact main_of_stability c hnk P o hP ho0 ho1 ⟨i, j, hij, hh⟩
    (fun r hr => opt_stable hn P o hP huniq r hr)
