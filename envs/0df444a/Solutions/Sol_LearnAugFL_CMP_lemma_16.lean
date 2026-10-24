-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:27:55.581116+00:00
-- url     : https://prove2.me/submissions/4db075d9-38e6-4586-a7f8-8ebd53f15d5b

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

-- Complete inline local helper: Median.lean

namespace LearnAugFL.CMP.NegativeProof

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

end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: Total.lean

namespace LearnAugFL.CMP.NegativeProof

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


end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: Stability.lean

namespace LearnAugFL.CMP.NegativeProof

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

end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: Uniqueness.lean

namespace LearnAugFL.CMP.NegativeProof

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

end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: ShiftGeometry.lean

namespace LearnAugFL.CMP.NegativeProof

noncomputable def step (a : Fin 2) (ε : ℝ) : Pt := EuclideanSpace.single a ε

lemma step_apply (a b : Fin 2) (ε : ℝ) : step a ε b = if b = a then ε else 0 := by
  simp [step, PiLp.single_apply]

lemma step_norm (a : Fin 2) (ε : ℝ) (hε : 0 ≤ ε) : ‖step a ε‖ = ε := by
  simp [step, Real.norm_eq_abs, abs_of_nonneg hε]

lemma norm_sq_coords (p : Pt) (a b : Fin 2) (hab : a ≠ b) :
    ‖p‖ ^ 2 = (p a) ^ 2 + (p b) ^ 2 := by
  fin_cases a <;> fin_cases b <;> simp_all [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, add_comm]

lemma norm_axis (p : Pt) (a b : Fin 2) (hab : a ≠ b) (hp : p b = 0) : ‖p‖ = |p a| := by
  have hh := norm_sq_coords p a b hab
  simp only [hp, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
  have ha := sq_abs (p a)
  nlinarith [norm_nonneg p, abs_nonneg (p a)]

lemma shifted_coords (p : Pt) (a b : Fin 2) (hab : a ≠ b) (ε : ℝ) :
    (p - step a ε) a = p a - ε ∧ (p - step a ε) b = p b := by
  simp [step_apply, hab.symm]

lemma shift_distance (p : Pt) (a : Fin 2) (ε : ℝ) (hε : 0 ≤ ε) :
    dist (p - step a ε) p = ε := by
  rw [dist_eq_norm]
  have he : p - step a ε - p = -step a ε := by abel
  rw [he, norm_neg, step_norm a ε hε]

lemma shift_perpendicular_strict (o p : Pt) (a b : Fin 2) (hab : a ≠ b)
    (hp : p a = 0) (ε : ℝ) (hε : 0 < ε) (hεo : ε < o a) :
    dist (o - step a ε) p < dist o p := by
  have h1 := norm_sq_coords (o - step a ε - p) a b hab
  have h2 := norm_sq_coords (o - p) a b hab
  have hcoords := shifted_coords o a b hab ε
  simp only [PiLp.sub_apply, hcoords.1, hcoords.2, hp, sub_zero] at h1 h2
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg (o - p), norm_nonneg (o - step a ε - p)]

lemma shift_negative_norm (p : Pt) (a b : Fin 2) (hab : a ≠ b)
    (hpa : p a < 0) (hpb : p b = 0) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖p - step a ε‖ = ‖p‖ + ε := by
  have hcoords := shifted_coords p a b hab ε
  rw [norm_axis _ a b hab (hcoords.2.trans hpb), norm_axis p a b hab hpb,
    hcoords.1, abs_of_neg hpa, abs_of_neg (by linarith : p a - ε < 0)]
  ring

lemma shift_norm_lower (p : Pt) (a : Fin 2) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖p‖ - ε ≤ ‖p - step a ε‖ := by
  have h := norm_sub_norm_le p (p - step a ε)
  have he : p - (p - step a ε) = step a ε := by abel
  rw [he, step_norm a ε hε] at h
  linarith

lemma shift_positive_strict (o : Pt) (a b : Fin 2) (hab : a ≠ b)
    (hob : 0 < o b) (ε : ℝ) (hε : 0 < ε) :
    ‖o‖ - ε < ‖o - step a ε‖ := by
  have hn : step a ε ≠ 0 := by
    intro hh
    have he := congrArg (fun p : Pt => p a) hh
    simp [step_apply, hε.ne'] at he
  have hnot : ¬ SameRay ℝ (step a ε) (o - step a ε) := by
    intro hr
    obtain ⟨r, _, he⟩ := hr.exists_nonneg_left hn
    have hb := congrArg (fun p : Pt => p b) he
    simp [step_apply, hab.symm] at hb
    linarith
  have h := norm_add_lt_of_not_sameRay hnot
  have he : step a ε + (o - step a ε) = o := by abel
  rw [he, step_norm a ε hε.le] at h
  linarith

end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: ShiftProfile.lean

namespace LearnAugFL.CMP.NegativeProof

lemma count_filter {n : ℕ} (P : Fin n → Pt) (p : Pt → Prop) [DecidablePred p] :
    count P p = (Finset.univ.filter (fun i => p (P i))).card := by
  classical
  simp [count, Set.ncard_eq_toFinset_card']

noncomputable def shifted {n : ℕ} (P : Fin n → Pt) (a : Fin 2) (ε : ℝ) : Fin n → Pt :=
  fun i => if P i a = 0 then P i else P i - step a ε

noncomputable def budget {n : ℕ} (P : Fin n → Pt) (a : Fin 2) (ε : ℝ) (i : Fin n) : ℝ :=
  (if P i a < 0 then ε else 0) - (if 0 < P i a then ε else 0)

lemma budget_sum {n : ℕ} (P : Fin n → Pt) (a : Fin 2) (ε : ℝ) :
    (∑ i, budget P a ε i) =
      ((count P (fun p => p a < 0) : ℝ) - count P (fun p => 0 < p a)) * ε := by
  classical
  simp [budget, Finset.sum_sub_distrib, ← Finset.sum_filter, count_filter, sub_mul]

lemma shifted_bound {n : ℕ} (P : Fin n → Pt) (o : Pt) (a b : Fin 2) (hab : a ≠ b)
    (hoa : 0 < o a) (haxes : ∀ i, P i a = 0 ∨ P i b = 0 ∨ P i = o)
    (ε : ℝ) (hε : 0 ≤ ε) (i : Fin n) :
    ‖P i‖ + budget P a ε i ≤ ‖shifted P a ε i‖ := by
  by_cases hneg : P i a < 0
  · have hz : P i a ≠ 0 := ne_of_lt hneg
    have hb : P i b = 0 := by
      rcases haxes i with hh | hh | hh
      · exact (hz hh).elim
      · exact hh
      · rw [hh] at hneg
        linarith
    simp only [shifted, hz, if_false, budget, hneg, if_true, not_lt_of_ge hneg.le]
    simpa using (shift_negative_norm (P i) a b hab hneg hb ε hε).ge
  · by_cases hpos : 0 < P i a
    · have hz : P i a ≠ 0 := ne_of_gt hpos
      simp only [shifted, hz, if_false, budget, hneg, hpos, if_true, zero_sub]
      simpa only [sub_eq_add_neg] using shift_norm_lower (P i) a ε hε
    · have hz : P i a = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [shifted, budget, hz]

lemma shifted_origin_le {n : ℕ} (P : Fin n → Pt) (o : Pt) (a b : Fin 2) (hab : a ≠ b)
    (hoa : 0 < o a) (haxes : ∀ i, P i a = 0 ∨ P i b = 0 ∨ P i = o)
    (hcount : count P (fun p => 0 < p a) ≤ count P (fun p => p a < 0))
    (ε : ℝ) (hε : 0 ≤ ε) : total P 0 ≤ total (shifted P a ε) 0 := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => shifted_bound P o a b hab hoa haxes ε hε i)
  simp only [Finset.sum_add_distrib, budget_sum] at hsum
  have hc : (count P (fun p => 0 < p a) : ℝ) ≤ count P (fun p => p a < 0) := by exact_mod_cast hcount
  have hh := mul_nonneg (sub_nonneg.mpr hc) hε
  simpa only [total, dist_zero_left] using (by linarith : (∑ i, ‖P i‖) ≤ ∑ i, ‖shifted P a ε i‖)

lemma shifted_origin_lt {n : ℕ} (P : Fin n → Pt) (o : Pt) (a b : Fin 2) (hab : a ≠ b)
    (ho : ∀ j, 0 < o j) (haxes : ∀ i, P i a = 0 ∨ P i b = 0 ∨ P i = o)
    (hcount : count P (fun p => 0 < p a) ≤ count P (fun p => p a < 0))
    (hoagent : ∃ i, P i = o) (ε : ℝ) (hε : 0 < ε) :
    total P 0 < total (shifted P a ε) 0 := by
  obtain ⟨i, hi⟩ := hoagent
  have histrict : ‖P i‖ + budget P a ε i < ‖shifted P a ε i‖ := by
    simpa [budget, shifted, hi, (ho a).ne', not_lt_of_ge (ho a).le, ho a, sub_eq_add_neg]
      using shift_positive_strict o a b hab (ho b) ε hε
  have hsum := Finset.sum_lt_sum
    (fun i (_ : i ∈ Finset.univ) => shifted_bound P o a b hab (ho a) haxes ε hε.le i)
    ⟨i, Finset.mem_univ _, histrict⟩
  simp only [Finset.sum_add_distrib, budget_sum] at hsum
  have hc : (count P (fun p => 0 < p a) : ℝ) ≤ count P (fun p => p a < 0) := by exact_mod_cast hcount
  have hh := mul_nonneg (sub_nonneg.mpr hc) hε.le
  simpa only [total, dist_zero_left] using (by linarith : (∑ i, ‖P i‖) < ∑ i, ‖shifted P a ε i‖)

lemma shifted_close {n : ℕ} (P : Fin n → Pt) (a : Fin 2) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ i, dist (shifted P a ε i) (P i) ≤ ε := by
  intro i
  unfold shifted
  split_ifs
  · simpa using hε
  · exact (shift_distance (P i) a ε hε).le

lemma shifted_sign {n : ℕ} (P : Fin n → Pt) (a : Fin 2) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ∀ i, P i a ≠ 0 → ε < |P i a|) :
    ∀ i j, Real.sign (P i j) = Real.sign (shifted P a ε i j) := by
  intro i j
  by_cases hz : P i a = 0
  · simp [shifted, hz]
  simp only [shifted, hz, if_false, PiLp.sub_apply, step_apply]
  by_cases hja : j = a
  · subst j
    simp only [ite_true]
    rcases lt_or_gt_of_ne hz with hh | hh
    · rw [Real.sign_of_neg hh, Real.sign_of_neg (by linarith : P i a - ε < 0)]
    · have hs := hsmall i hz
      rw [abs_of_pos hh] at hs
      rw [Real.sign_of_pos hh, Real.sign_of_pos (by linarith : 0 < P i a - ε)]
  · simp [hja]

lemma small_coordinates {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (a : Fin 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ i, P i a ≠ 0 → η ≤ |P i a| := by
  classical
  let f : Fin n → ℝ := fun i => if P i a = 0 then 1 else |P i a|
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne f, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro i hi
    dsimp [f]
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr h
  · intro i hi
    simpa only [f, if_neg hi] using Finset.inf'_le f (Finset.mem_univ i)

end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: Optimality.lean

namespace LearnAugFL.CMP.NegativeProof

lemma distance_translate (x y v : Pt) : dist (x - v) (y - v) = dist x y := by
  simp only [dist_eq_norm]
  congr 1
  abel

lemma project_nonpos_strict (o p : Pt) (a b : Fin 2) (hab : a ≠ b)
    (hoa : 0 < o a) (hp : p a ≤ 0) :
    dist (o - step a (o a)) p < dist o p := by
  have h1 := norm_sq_coords (o - step a (o a) - p) a b hab
  have h2 := norm_sq_coords (o - p) a b hab
  have hcoords := shifted_coords o a b hab (o a)
  simp only [PiLp.sub_apply, hcoords.1, hcoords.2, sub_self, zero_sub] at h1 h2
  rw [dist_eq_norm, dist_eq_norm]
  have hh := mul_nonpos_of_nonneg_of_nonpos hoa.le hp
  nlinarith [norm_nonneg (o - p), norm_nonneg (o - step a (o a) - p)]

lemma exists_positive_agent {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (hP : IsOpt P o) (a b : Fin 2) (hab : a ≠ b) (hoa : 0 < o a) :
    ∃ i, 0 < P i a := by
  by_contra hh
  push Not at hh
  have hs : total P (o - step a (o a)) < total P o := by
    unfold total
    exact Finset.sum_lt_sum (fun i _ => (project_nonpos_strict o (P i) a b hab hoa (hh i)).le)
      ⟨⟨0, hn⟩, Finset.mem_univ _, project_nonpos_strict o (P ⟨0, hn⟩) a b hab hoa (hh _)⟩
  have hm := (isOpt_iff hn P o).mp hP (o - step a (o a))
  linarith

lemma signs_witnesses {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (hP : IsOpt P o) (a b : Fin 2) (hab : a ≠ b) (hoa : 0 < o a)
    (hcount : count P (fun p => 0 < p a) ≤ count P (fun p => p a < 0)) :
    (∃ i, 0 < P i a) ∧ ∃ i, P i a < 0 := by
  classical
  obtain ⟨i, hi⟩ := exists_positive_agent hn P o hP a b hab hoa
  refine ⟨⟨i, hi⟩, ?_⟩
  have hp : 0 < count P (fun p => 0 < p a) := by
    rw [count_filter]
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hn' := lt_of_lt_of_le hp hcount
  rw [count_filter] at hn'
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hn'
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

lemma total_pos_of_signs {n : ℕ} (P Q : Fin n → Pt) (a : Fin 2)
    (hp : ∃ i, 0 < P i a) (hn : ∃ i, P i a < 0)
    (hPQ : ∀ i j, Real.sign (P i j) = Real.sign (Q i j)) (z : Pt) : 0 < total Q z := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hn
  apply total_pos Q i j _ z
  intro he
  have h1 := hPQ i a
  have h2 := hPQ j a
  rw [he] at h1
  rw [Real.sign_of_pos hi] at h1
  rw [Real.sign_of_neg hj] at h2
  linarith

lemma shifted_cost_lt {n : ℕ} (P : Fin n → Pt) (o : Pt) (a b : Fin 2) (hab : a ≠ b)
    (hperp : ∃ i, P i a = 0) (ε : ℝ) (hε : 0 < ε) (hεo : ε < o a) :
    total (shifted P a ε) (o - step a ε) < total P o := by
  have hle (i : Fin n) : dist (o - step a ε) (shifted P a ε i) ≤ dist o (P i) := by
    unfold shifted
    split_ifs with hz
    · exact (shift_perpendicular_strict o (P i) a b hab hz ε hε hεo).le
    · exact (distance_translate _ _ _).le
  obtain ⟨i, hi⟩ := hperp
  unfold total
  apply Finset.sum_lt_sum (fun i _ => hle i)
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simpa only [shifted, hi, if_true] using shift_perpendicular_strict o (P i) a b hab hi ε hε hεo

lemma translated_optimum {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o)
    (a : Fin 2) (hperp : ¬ ∃ i, P i a = 0) (ε : ℝ) :
    IsOpt (shifted P a ε) (o - step a ε) ∧
      total (shifted P a ε) (o - step a ε) = total P o := by
  have hp (i : Fin n) : P i a ≠ 0 := fun hh => hperp ⟨i, hh⟩
  have ht (z : Pt) : total (shifted P a ε) (z - step a ε) = total P z := by
    simp [total, shifted, hp, distance_translate]
  refine ⟨?_, ht o⟩
  apply (isOpt_iff hn _ _).mpr
  intro z
  have hh := (isOpt_iff hn P o).mp hP (z + step a ε)
  rw [← ht o, ← ht (z + step a ε)] at hh
  simpa only [add_sub_cancel_right] using hh

lemma no_perp_has_opt_agent {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (hP : IsOpt P o) (a b : Fin 2) (hab : a ≠ b) (hob : 0 < o b)
    (haxes : ∀ i, P i a = 0 ∨ P i b = 0 ∨ P i = o)
    (hperp : ¬ ∃ i, P i a = 0) : ∃ i, P i = o := by
  obtain ⟨i, hi⟩ := exists_positive_agent hn P o hP b a hab.symm hob
  rcases haxes i with hh | hh | hh
  · exact (hperp ⟨i, hh⟩).elim
  · rw [hh] at hi
    exact (lt_irrefl _ hi).elim
  · exact ⟨i, hh⟩

end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: CountConvert.lean

namespace LearnAugFL.CMP.NegativeProof

lemma count_congr_on {n : ℕ} (P : Fin n → Pt) (f g : Pt → Prop)
    (h : ∀ i, f (P i) ↔ g (P i)) : count P f = count P g := by
  unfold count
  congr 1
  ext i
  exact h i

lemma positive_equiv (p o : Pt) (a b : Fin 2) (hoa : 0 < o a)
    (haxes : p a = 0 ∨ p b = 0 ∨ p = o) :
    (0 < p a) ↔ (p b = 0 ∧ 0 < p a) ∨ p = o := by
  constructor
  · intro hp
    rcases haxes with hh | hh | hh
    · rw [hh] at hp
      exact (lt_irrefl _ hp).elim
    · exact Or.inl ⟨hh, hp⟩
    · exact Or.inr hh
  · rintro (hh | rfl)
    · exact hh.2
    · exact hoa

lemma negative_equiv (p o : Pt) (a b : Fin 2) (hoa : 0 < o a)
    (haxes : p a = 0 ∨ p b = 0 ∨ p = o) :
    (p a < 0) ↔ p b = 0 ∧ p a < 0 := by
  constructor
  · intro hp
    rcases haxes with hh | hh | hh
    · rw [hh] at hp
      exact (lt_irrefl _ hp).elim
    · exact ⟨hh, hp⟩
    · rw [hh] at hp
      linarith
  · exact And.right

lemma coordinate_axis_choice {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho : ∀ j, 0 < o j)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o)
    (hcount : count P (fun p => posX' p ∨ p = o) ≤ count P negX' ∨
      count P (fun p => posY' p ∨ p = o) ≤ count P negY') :
    ∃ a b : Fin 2, a ≠ b ∧ (∀ i, P i a = 0 ∨ P i b = 0 ∨ P i = o) ∧
      count P (fun p => 0 < p a) ≤ count P (fun p => p a < 0) := by
  have hax (i : Fin n) : P i 0 = 0 ∨ P i 1 = 0 ∨ P i = o := by
    rcases haxes i with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hay (i : Fin n) : P i 1 = 0 ∨ P i 0 = 0 ∨ P i = o := haxes i
  rcases hcount with hx | hy
  · refine ⟨0, 1, by decide, hax, ?_⟩
    have hp := count_congr_on P (fun p => 0 < p 0) (fun p => posX' p ∨ p = o)
      (fun i => positive_equiv (P i) o 0 1 (ho 0) (hax i))
    have hn := count_congr_on P (fun p => p 0 < 0) negX'
      (fun i => negative_equiv (P i) o 0 1 (ho 0) (hax i))
    rwa [hp, hn]
  · refine ⟨1, 0, by decide, hay, ?_⟩
    have hp := count_congr_on P (fun p => 0 < p 1) (fun p => posY' p ∨ p = o)
      (fun i => positive_equiv (P i) o 1 0 (ho 1) (hay i))
    have hn := count_congr_on P (fun p => p 1 < 0) negY'
      (fun i => negative_equiv (P i) o 1 0 (ho 1) (hay i))
    rwa [hp, hn]

end LearnAugFL.CMP.NegativeProof

-- Complete inline local helper: CountUniqueness.lean

namespace LearnAugFL.CMP.NegativeProof

lemma line_distance_add (q o p : Pt) (a : Fin 2) (hq : q a = 0) (ho : 0 < o a)
    (hp : p a ≤ 0) (hline : p ∈ affineSpan ℝ ({q, o} : Set Pt)) :
    dist o p = dist o q + dist q p := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
  have he : p = t • (o - q) + q := by
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] using ht.symm
  have hpa : p a = t * o a := by
    rw [he]
    simp [hq]
  have ht0 : t ≤ 0 := by
    rw [hpa] at hp
    nlinarith
  have hqsub : q - p = (-t) • (o - q) := by rw [he]; module
  have hosub : o - p = (1 - t) • (o - q) := by rw [he]; module
  rw [dist_eq_norm, hosub, norm_smul, Real.norm_of_nonneg (by linarith),
    dist_eq_norm o q, dist_eq_norm q p, hqsub, norm_smul,
    Real.norm_of_nonneg (by linarith)]
  ring

open Classical in
lemma count_weight_sum {n : ℕ} (P : Fin n → Pt) (f : Pt → Prop) (D : ℝ) :
    (∑ i : Fin n, if f (P i) then D else 0) = (count P f : ℝ) * D := by
  classical
  rw [← Finset.sum_filter]
  simp [count, Set.ncard_eq_toFinset_card', nsmul_eq_mul]

lemma count_optimum_unique {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (hP : IsOpt P o) (a : Fin 2) (hoa : 0 < o a)
    (hcount : count P (fun p => 0 < p a) ≤ count P (fun p => p a < 0))
    (hperp : ∃ i, P i a = 0) : ∀ z, IsOpt P z → z = o := by
  classical
  intro z hz
  by_contra hzo
  obtain ⟨i₀, hi₀⟩ := hperp
  let q := P i₀
  have hqa : q a = 0 := hi₀
  have hqo : q ≠ o := by
    intro h
    have he := congrArg (fun p : Pt => p a) h
    linarith
  have hm (i : Fin n) : P i ∈ affineSpan ℝ ({o, z} : Set Pt) := by
    by_cases hi : P i = o
    · rw [hi]
      exact left_mem_affineSpan_pair ℝ o z
    · have hc := sameRay_collinear (P i) o z hi (optimal_sameRay hn P o z hP hz i)
      exact hc.mem_affineSpan_of_mem_of_ne (by simp : o ∈ ({o, z, P i} : Set Pt))
        (by simp : z ∈ ({o, z, P i} : Set Pt)) (by simp : P i ∈ ({o, z, P i} : Set Pt))
        (Ne.symm hzo)
  have hpair : affineSpan ℝ ({q, o} : Set Pt) = affineSpan ℝ ({o, z} : Set Pt) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hm i₀) (left_mem_affineSpan_pair ℝ o z) hqo
  have hline (i : Fin n) : P i ∈ affineSpan ℝ ({q, o} : Set Pt) := by
    rw [hpair]
    exact hm i
  let D := dist o q
  have hD : 0 < D := dist_pos.mpr hqo.symm
  let B : Fin n → ℝ := fun i =>
    (if 0 < P i a then D else 0) - (if P i a < 0 then D else 0)
  have hb (i : Fin n) : dist q (P i) - dist o (P i) ≤ B i := by
    by_cases hp : 0 < P i a
    · have hn' : ¬ P i a < 0 := not_lt_of_ge hp.le
      have ht := dist_triangle q o (P i)
      rw [dist_comm q o] at ht
      simp only [B, if_pos hp, if_neg hn', sub_zero]
      dsimp [D]
      linarith
    · have hdist := line_distance_add q o (P i) a hqa hoa (le_of_not_gt hp) (hline i)
      by_cases hn' : P i a < 0
      · simp only [B, if_neg hp, if_pos hn', zero_sub]
        dsimp [D]
        linarith
      · simp only [B, if_neg hp, if_neg hn', sub_self]
        dsimp [D] at hD
        linarith
  have hstrict : dist q (P i₀) - dist o (P i₀) < B i₀ := by
    simp only [B, hi₀, lt_self_iff_false, if_false, sub_self]
    change dist q q - D < 0
    simp only [dist_self, zero_sub]
    linarith
  have hsum : total P q - total P o < ∑ i, B i := by
    unfold total
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_lt_sum (fun i _ => hb i) ⟨i₀, Finset.mem_univ _, hstrict⟩
  have hbound : (∑ i, B i) ≤ 0 := by
    dsimp [B]
    rw [Finset.sum_sub_distrib, count_weight_sum P (fun p => 0 < p a) D,
      count_weight_sum P (fun p => p a < 0) D]
    have hc : (count P (fun p => 0 < p a) : ℝ) ≤ count P (fun p => p a < 0) := by
      exact_mod_cast hcount
    nlinarith
  have hopt := (isOpt_iff hn P o).mp hP q
  linarith

end LearnAugFL.CMP.NegativeProof


-- Complete inline local helper: Construction.lean

namespace LearnAugFL.CMP.NegativeProof

lemma positive_near (o q : Pt) (hq : dist q o < min (o 0) (o 1)) : ∀ j, 0 < q j := by
  intro j
  have hd : |q j - o j| ≤ dist q o := PiLp.dist_apply_le q o j
  have hmin : min (o 0) (o 1) ≤ o j := by fin_cases j <;> simp
  have hh := (abs_le.mp hd).1
  linarith

lemma positive_shift (o : Pt) (ho : ∀ j, 0 < o j) (a : Fin 2) (ε : ℝ)
    (hε : ε < o a) : ∀ j, 0 < (o - step a ε) j := by
  intro j
  by_cases hj : j = a
  · subst j
    simpa [step_apply] using sub_pos.mpr hε
  · simpa [step_apply, hj] using ho j

lemma improved_data {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt)
    (hP : IsOpt P o) (ho : ∀ j, 0 < o j) (a b : Fin 2) (hab : a ≠ b)
    (haxes : ∀ i, P i a = 0 ∨ P i b = 0 ∨ P i = o)
    (hcount : count P (fun p => 0 < p a) ≤ count P (fun p => p a < 0)) :
    ∃ (Q : Fin n → Pt) (oQ : Pt), IsOpt Q oQ ∧
      (∀ i j, Real.sign (P i j) = Real.sign (Q i j)) ∧ (∀ j, 0 < oQ j) ∧
      0 < total Q oQ ∧
      ((total P 0 ≤ total Q 0 ∧ total Q oQ < total P o) ∨
        (total P 0 < total Q 0 ∧ total Q oQ = total P o)) := by
  obtain ⟨hpos, hneg⟩ := signs_witnesses hn P o hP a b hab (ho a) hcount
  obtain ⟨η, hη, hηP⟩ := small_coordinates hn P a
  by_cases hperp : ∃ i, P i a = 0
  · have huniq := count_optimum_unique hn P o hP a (ho a) hcount hperp
    obtain ⟨δ, hδ, hδQ⟩ := opt_stable hn P o hP huniq (min (o 0) (o 1)) (lt_min (ho 0) (ho 1))
    obtain ⟨ε, hε, hεub⟩ := exists_between (lt_min hη (lt_min (ho a) hδ))
    have hεη : ε < η := (lt_min_iff.mp hεub).1
    have hεo : ε < o a := (lt_min_iff.mp (lt_min_iff.mp hεub).2).1
    have hεδ : ε < δ := (lt_min_iff.mp (lt_min_iff.mp hεub).2).2
    let Q := shifted P a ε
    have hsign := shifted_sign P a ε hε.le (fun i hi => hεη.trans_le (hηP i hi))
    obtain ⟨oQ, hQ, hnear⟩ := hδQ Q (fun i => (shifted_close P a ε hε.le i).trans_lt hεδ)
    refine ⟨Q, oQ, hQ, hsign, positive_near o oQ hnear,
      total_pos_of_signs P Q a hpos hneg hsign oQ, Or.inl ⟨?_, ?_⟩⟩
    · exact shifted_origin_le P o a b hab (ho a) haxes hcount ε hε.le
    · exact ((isOpt_iff hn Q oQ).mp hQ (o - step a ε)).trans_lt
        (shifted_cost_lt P o a b hab hperp ε hε hεo)
  · obtain ⟨ε, hε, hεub⟩ := exists_between (lt_min hη (ho a))
    have hεη : ε < η := (lt_min_iff.mp hεub).1
    have hεo : ε < o a := (lt_min_iff.mp hεub).2
    let Q := shifted P a ε
    let oQ := o - step a ε
    have hsign := shifted_sign P a ε hε.le (fun i hi => hεη.trans_le (hηP i hi))
    obtain ⟨hQ, hcost⟩ := translated_optimum hn P o hP a hperp ε
    refine ⟨Q, oQ, hQ, hsign, positive_shift o ho a ε hεo,
      total_pos_of_signs P Q a hpos hneg hsign oQ, Or.inr ⟨?_, hcost⟩⟩
    exact shifted_origin_lt P o a b hab ho haxes hcount
      (no_perp_has_opt_agent hn P o hP a b hab (ho b) haxes hperp) ε hε

lemma main_coordinate (c : ℝ) {n k : ℕ} (hnk : Admissible c n k)
    (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o) (ho : ∀ j, 0 < o j)
    (a b : Fin 2) (hab : a ≠ b) (haxes : ∀ i, P i a = 0 ∨ P i b = 0 ∨ P i = o)
    (hcount : count P (fun p => 0 < p a) ≤ count P (fun p => p a < 0)) :
    (cmp P o k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P o o k < ratio Q oQ oQ k') ∧
    (cmp P 0 k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P 0 o k < ratio Q 0 oQ k') := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnk.1
  obtain ⟨Q, oQ, hQ, hsign, hoQ, hden, hcost⟩ := improved_data hn P o hP ho a b hab haxes hcount
  obtain ⟨hpos, hneg⟩ := signs_witnesses hn P o hP a b hab (ho a) hcount
  have hnum : 0 < total P 0 := total_pos_of_signs P P a hpos hneg (fun _ _ => rfl) 0
  have hratio (u v : Pt) (hu : cmp P u k = 0) (hv : cmp Q v k = 0) :
      ratio P u o k < ratio Q v oQ k := by
    rw [ratio_total hn.ne', ratio_total hn.ne', hu, hv]
    rcases hcost with ⟨hup, hdown⟩ | ⟨hup, heq⟩
    · exact (div_lt_div_of_pos_left hnum hden hdown).trans_le (div_le_div_of_nonneg_right hup hden.le)
    · rw [← heq]
      exact div_lt_div_of_pos_right hup hden
  constructor
  · intro hcmp
    refine ⟨n, k, Q, oQ, hnk, hQ, hratio o oQ hcmp ?_⟩
    apply cmp_zero_of_sign P Q o oQ hsign _ hcmp
    intro j
    rw [Real.sign_of_pos (ho j), Real.sign_of_pos (hoQ j)]
  · intro hcmp
    refine ⟨n, k, Q, oQ, hnk, hQ, hratio 0 0 hcmp ?_⟩
    exact cmp_zero_of_sign P Q 0 0 hsign (fun _ => rfl) hcmp

end LearnAugFL.CMP.NegativeProof

open LearnAugFL.CMP LearnAugFL.CMP.NegativeProof

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ} (hnk : Admissible c n k)
    (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o) (ho0 : 0 < o 0) (ho01 : o 0 ≤ o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o)
    (hcount : count P (fun p => posX' p ∨ p = o) ≤ count P negX' ∨
      count P (fun p => posY' p ∨ p = o) ≤ count P negY') :
    (cmp P o k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P o o k < ratio Q oQ oQ k') ∧
    (cmp P 0 k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P 0 o k < ratio Q 0 oQ k') := by
  have ho : ∀ j, 0 < o j := by
    intro j
    fin_cases j
    · exact ho0
    · exact ho0.trans_le ho01
  obtain ⟨a, b, hab, hax, hcnt⟩ := coordinate_axis_choice P o ho haxes hcount
  exact main_coordinate c hnk P o hP ho a b hab hax hcnt
