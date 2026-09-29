-- Prove2me | solution 1 for HeldWolfeCrowder.CoreProblem.core_problem_solves_dual
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:31:49.294961+00:00
-- url     : https://prove2.me/submissions/98411da4-bfe5-4d6f-abf7-c346748dd144

import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting



namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

lemma hwc_w_le {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (i : ι) :
    w c v p ≤ c i + ⟪p, v i⟫_ℝ :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma hwc_w_eq {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) :
    ∃ i, w c v p = c i + ⟪p, v i⟫_ℝ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι))
    (fun k => c k + ⟪p, v k⟫_ℝ)
  exact ⟨i, hi⟩

lemma hwc_weak {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (y : ι → ℝ) (hy : DualFeasible v y)
    (p : EuclideanSpace ℝ (Fin n)) : w c v p ≤ dualObj c y := by
  obtain ⟨h0, h1, h2⟩ := hy
  have : ∑ k, y k * w c v p ≤ ∑ k, y k * (c k + ⟪p, v k⟫_ℝ) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hwc_w_le c v p k) (h0 k)
  have e1 : ∑ k, y k * w c v p = w c v p := by rw [← Finset.sum_mul, h1, one_mul]
  have e2 : ∑ k, y k * (c k + ⟪p, v k⟫_ℝ) = dualObj c y + ⟪p, ∑ k, y k • v k⟫_ℝ := by
    simp only [dualObj, inner_sum, inner_smul_right, mul_add, Finset.sum_add_distrib]
    congr 1; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e1, e2, h2, inner_zero_right, add_zero] at this
  exact this

/-- Farkas-type strong duality (one direction) via compact/closed separation. -/
lemma hwc_farkas {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (W : ℝ) (hW : ∀ p, w c v p ≤ W) :
    ∃ y, DualFeasible v y ∧ dualObj c y ≤ W := by
  classical
  let Lm : (ι → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)) × ℝ :=
    LinearMap.prod (∑ k, (LinearMap.proj k : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (v k))
      (∑ k, (LinearMap.proj k : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (c k))
  have hLm : ∀ y, Lm y = (∑ k, y k • v k, ∑ k, y k * c k) := by
    intro y; simp [Lm]
  set K := Lm '' stdSimplex ℝ ι
  set L : Set ((EuclideanSpace ℝ (Fin n)) × ℝ) := ({0} : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Set.Iic W
  by_contra hcon
  push Not at hcon
  have hdisj : Disjoint K L := by
    rw [Set.disjoint_left]
    rintro ⟨x, s⟩ ⟨y, hy, hyx⟩ ⟨hx0, hsW⟩
    rw [hLm] at hyx
    simp only [Prod.mk.injEq] at hyx
    simp only [Set.mem_singleton_iff] at hx0
    simp only [Set.mem_Iic] at hsW
    have hf : DualFeasible v y := ⟨hy.1, hy.2, by rw [hyx.1, hx0]⟩
    have := hcon y hf
    simp only [dualObj] at this
    have e : ∑ k, c k * y k = s := by
      rw [← hyx.2]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  have hKc : Convex ℝ K := (convex_stdSimplex ℝ ι).linear_image Lm
  have hKk : IsCompact K := (isCompact_stdSimplex (𝕜 := ℝ) (ι := ι)).image
    Lm.continuous_of_finiteDimensional
  have hLc : Convex ℝ L := (convex_singleton _).prod (convex_Iic W)
  have hLk : IsClosed L := isClosed_singleton.prod isClosed_Iic
  obtain ⟨f, u, u', hfK, huu, hfL⟩ := geometric_hahn_banach_compact_closed hKc hKk hLc hLk hdisj
  set r := f (0, 1)
  let g : (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  have hf : ∀ x s, f (x, s) = g x + s * r := by
    intro x s
    have : ((x, s) : (EuclideanSpace ℝ (Fin n)) × ℝ) = (x, 0) + s • ((0 : (EuclideanSpace ℝ (Fin n))), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul]; simp [g, r]
  have hL : ∀ s ≤ W, u' < s * r := by
    intro s hs
    have := hfL (0, s) ⟨rfl, hs⟩
    rw [hf, map_zero, zero_add] at this; exact this
  have hr : r ≤ 0 := by
    by_contra hr; push Not at hr
    have := hL (min W (u' / r - 1)) (min_le_left _ _)
    have h2 : min W (u' / r - 1) * r ≤ (u' / r - 1) * r :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le
    have h3 : (u' / r - 1) * r = u' - r := by field_simp
    linarith
  have hK : ∀ k, g (v k) + c k * r < u := by
    intro k
    have hmem : Lm (Pi.single k 1) ∈ K := ⟨_, single_mem_stdSimplex ℝ k, rfl⟩
    have := hfK _ hmem
    rw [hLm] at this
    have e1 : ∑ i, (Pi.single k (1:ℝ) : ι → ℝ) i • v i = v k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    have e2 : ∑ i, (Pi.single k (1:ℝ) : ι → ℝ) i * c i = c k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    rw [e1, e2, hf] at this; exact this
  have hWr := hL W le_rfl
  set π0 : (EuclideanSpace ℝ (Fin n)) := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm g
  have hπ0 : ∀ x, ⟪π0, x⟫_ℝ = g x := fun x => InnerProductSpace.toDual_symm_apply
  rcases hr.lt_or_eq with hr | hr
  · -- r < 0
    obtain ⟨i, hi⟩ := hwc_w_eq c v (r⁻¹ • π0)
    have := hW (r⁻¹ • π0)
    rw [hi, inner_smul_left, hπ0] at this
    have hk := hK i
    simp only [conj_trivial] at this
    have e : r * (c i + r⁻¹ * g (v i)) = c i * r + g (v i) := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hr.ne, one_mul]; ring
    have := mul_le_mul_of_nonpos_left this hr.le
    linarith
  · -- r = 0
    rw [hr] at hWr hK
    set C := ∑ i, |c i|
    have hC : ∀ i, -C ≤ c i := fun i => by
      have := Finset.single_le_sum (f := fun i => |c i|) (fun i _ => abs_nonneg (c i))
        (Finset.mem_univ i)
      have := neg_abs_le (c i); simp only [C] at *; linarith
    have hu : u < 0 := by linarith
    set s := (|W| + C + 1) / (-u)
    have hs : s * (-u) = |W| + C + 1 := div_mul_cancel₀ _ (by linarith)
    obtain ⟨i, hi⟩ := hwc_w_eq c v ((-s) • π0)
    have := hW ((-s) • π0)
    rw [hi, inner_smul_left, hπ0] at this
    simp only [conj_trivial] at this
    have hk := hK i
    have hs0 : 0 < s := div_pos (by positivity) (by linarith)
    have := hC i
    have := le_abs_self W
    nlinarith

lemma hwc_aggregate {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ)
    (hy : CoreFeasible v k J Jstar y) :
    DualFeasible v (aggregate k J Jstar y) ∧
      dualObj c (aggregate k J Jstar y) = coreObj c k J Jstar y := by
  classical
  obtain ⟨h0, h1, h2⟩ := hy
  have fib : ∀ f : ℕ → ℝ, ∑ i, ∑ j ∈ (Finset.Icc J Jstar).filter (fun j => k j = i), f j =
      ∑ j ∈ Finset.Icc J Jstar, f j := fun f => by
    convert Finset.sum_fiberwise (Finset.Icc J Jstar) k f
  have fibv : ∀ f : ℕ → EuclideanSpace ℝ (Fin n),
      ∑ i, ∑ j ∈ (Finset.Icc J Jstar).filter (fun j => k j = i), f j =
      ∑ j ∈ Finset.Icc J Jstar, f j := fun f => by
    convert Finset.sum_fiberwise (Finset.Icc J Jstar) k f
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    unfold aggregate
    exact Finset.sum_nonneg fun j hj => h0 j (Finset.mem_filter.1 hj).1
  · unfold aggregate; rw [← h1]; convert fib y
  · unfold aggregate
    rw [← h2, ← fibv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    convert Finset.sum_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  · unfold dualObj coreObj aggregate
    rw [← fib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    convert Finset.sum_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]

theorem hwc_goal_core {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v)))
    (t : ℕ → ℝ) (π : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι)
    (hrun : IsSubgradientRun c v t π k) (ht : StepSizeCond t) :
    ∀ J : ℕ, ∃ Jstar : ℕ, J < Jstar ∧
      (∃ y : ℕ → ℝ, IsCoreOptimal c v k J Jstar y) ∧
      ∀ y : ℕ → ℝ, IsCoreOptimal c v k J Jstar y →
        IsDualOptimal c v (aggregate k J Jstar y) := by
  classical
  intro J
  set W := sSup (Set.range (w c v))
  have hwW : ∀ p, w c v p ≤ W := fun p => le_csSup hw ⟨p, rfl⟩
  have hWd : ∀ y, DualFeasible v y → W ≤ dualObj c y := fun y hy =>
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨p, rfl⟩; exact hwc_weak c v y hy p)
  -- indices chosen infinitely often
  set I : Finset ι := Finset.univ.filter (fun i => ∀ N, ∃ j, N ≤ j ∧ k j = i)
  have hnot : ∀ i, i ∉ I → ∃ N, ∀ j, N ≤ j → k j ≠ i := by
    intro i hi
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_exists,
      not_and] at hi
    exact hi
  choose! Nf hNf using hnot
  set N0 := J + ∑ i ∈ Finset.univ.filter (fun i => i ∉ I), Nf i
  have hN0 : ∀ j, N0 ≤ j → k j ∈ I := by
    intro j hj
    by_contra hkj
    have : Nf (k j) ≤ N0 := by
      have := Finset.single_le_sum (f := Nf) (s := Finset.univ.filter (fun i => i ∉ I))
        (fun _ _ => Nat.zero_le _) (a := k j) (by simp [hkj])
      omega
    exact hNf (k j) hkj j (le_trans this hj) rfl
  have : Nonempty I := ⟨⟨k N0, hN0 N0 le_rfl⟩⟩
  -- restricted function bounded by W
  have hWI : ∀ p, w (fun i : I => c i) (fun i : I => v i) p ≤ W := by
    intro p
    by_contra hp
    push Not at hp
    set δ := w (fun i : I => c i) (fun i : I => v i) p - W
    have hδ : 0 < δ := by simp only [δ]; linarith
    set M := ∑ i, ‖v i‖ ^ 2
    have hM : ∀ i, ‖v i‖ ^ 2 ≤ M := fun i =>
      Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
    have hM0 : 0 ≤ M := le_trans (by positivity) (hM (Classical.arbitrary ι))
    obtain ⟨N1, hN1⟩ := (ht.1.eventually (gt_mem_nhds (show (0:ℝ) < δ / (M + 1) by positivity))).exists_forall_of_atTop
    set N2 := max N0 N1
    have step : ∀ j, N2 ≤ j → ‖π (j + 1) - p‖ ^ 2 ≤ ‖π j - p‖ ^ 2 - δ * t j := by
      intro j hj
      have hj0 : N0 ≤ j := le_trans (le_max_left _ _) hj
      have hj1 : N1 ≤ j := le_trans (le_max_right _ _) hj
      have hkI := hN0 j hj0
      have htj := hN1 j hj1
      have htp := hrun.step_pos j
      have e : π (j + 1) - p = (π j - p) + t j • v (k j) := by rw [hrun.step]; abel
      rw [e, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      have hin : ⟪π j - p, v (k j)⟫_ℝ ≤ -δ := by
        have h1 := hrun.index_min j
        unfold IsMinIndex at h1
        have h2 : w (fun i : I => c i) (fun i : I => v i) p ≤ c (k j) + ⟪p, v (k j)⟫_ℝ :=
          hwc_w_le (fun i : I => c i) (fun i : I => v i) p ⟨k j, hkI⟩
        have h3 := hwW (π j)
        rw [inner_sub_left]
        simp only [δ]; linarith
      have hv := hM (k j)
      have : t j * ‖v (k j)‖ ^ 2 ≤ δ := by
        calc t j * ‖v (k j)‖ ^ 2 ≤ δ / (M + 1) * (M + 1) := by
              apply mul_le_mul htj.le (by linarith) (by positivity) (by positivity)
          _ = δ := by field_simp
      nlinarith
    set S := fun N => ∑ j ∈ Finset.range N, t j
    have bound : ∀ N, N2 ≤ N → ‖π N - p‖ ^ 2 ≤ ‖π N2 - p‖ ^ 2 - δ * (S N - S N2) := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => simp
      | succ N hN ih =>
        have := step N hN
        have e : S (N + 1) = S N + t N := Finset.sum_range_succ _ _
        rw [e]; nlinarith
    obtain ⟨N, hN⟩ := (ht.2.eventually (Filter.eventually_gt_atTop
      (S N2 + ‖π N2 - p‖ ^ 2 / δ + 1))).exists_forall_of_atTop
    have h1 := bound (max N N2) (le_max_right _ _)
    have h2 := hN (max N N2) (le_max_left _ _)
    have h3 : 0 ≤ ‖π (max N N2) - p‖ ^ 2 := by positivity
    have h4 : δ * (‖π N2 - p‖ ^ 2 / δ) = ‖π N2 - p‖ ^ 2 := by field_simp
    change S N2 + ‖π N2 - p‖ ^ 2 / δ + 1 < S (max N N2) at h2
    nlinarith
  obtain ⟨z, ⟨hz0, hz1, hz2⟩, hzW⟩ := hwc_farkas (fun i : I => c i) (fun i : I => v i) W hWI
  -- representatives
  have hrep : ∀ i : I, ∃ j, N0 ≤ j ∧ k j = i := fun i =>
    (Finset.mem_filter.1 i.2).2 N0
  choose rep hrepN hrepk using hrep
  set Jstar := N0 + 1 + ∑ i, rep i
  have hJ : J < Jstar := by simp only [Jstar, N0]; omega
  have hrepI : ∀ i, rep i ∈ Finset.Icc J Jstar := by
    intro i
    have := Finset.single_le_sum (f := rep) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := hrepN i
    simp only [Finset.mem_Icc, Jstar, N0] at *; omega
  set y0 : ℕ → ℝ := fun j => ∑ i : I, if rep i = j then z i else 0
  have hsum : ∀ (M : Type) [AddCommMonoid M] (f : ℕ → I → M),
      ∑ j ∈ Finset.Icc J Jstar, ∑ i : I, (if rep i = j then f j i else 0) =
        ∑ i : I, f (rep i) i := by
    intro M _ f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp [hrepI i]
  have hy0 : CoreFeasible v k J Jstar y0 := by
    refine ⟨fun j _ => Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hz0 i], ?_, ?_⟩
    · have := hsum ℝ (fun _ i => z i); simp only [y0]; rw [this, hz1]
    · simp only [y0, Finset.sum_smul]
      have := hsum (EuclideanSpace ℝ (Fin n)) (fun j i => z i • v (k j))
      simp only [ite_smul, zero_smul]; rw [this, ← hz2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrepk i]
  have hy0obj : coreObj c k J Jstar y0 ≤ W := by
    have := hsum ℝ (fun j i => c (k j) * z i)
    simp only [coreObj, y0, Finset.mul_sum, mul_ite, mul_zero]
    rw [this]
    refine le_trans (le_of_eq ?_) hzW
    unfold dualObj
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepk i]
  have hopt : ∀ y', CoreFeasible v k J Jstar y' → W ≤ coreObj c k J Jstar y' := by
    intro y' hy'
    obtain ⟨hf, he⟩ := hwc_aggregate c v k J Jstar y' hy'
    rw [← he]; exact hWd _ hf
  refine ⟨Jstar, hJ, ⟨y0, hy0, fun y' hy' => le_trans hy0obj (hopt y' hy')⟩, ?_⟩
  intro y ⟨hy, hymin⟩
  obtain ⟨hf, he⟩ := hwc_aggregate c v k J Jstar y hy
  refine ⟨hf, fun y'' hy'' => ?_⟩
  rw [he]
  exact le_trans (hymin y0 hy0) (le_trans hy0obj (hWd y'' hy''))

end HeldWolfeCrowder.CoreProblem

namespace HeldWolfeCrowder.CoreProblem

theorem hwc_feasible_core {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v)))
    (t : ℕ → ℝ) (π : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι)
    (hrun : IsSubgradientRun c v t π k) (ht : StepSizeCond t) :
    ∀ J : ℕ, ∃ Jstar : ℕ, J < Jstar ∧ ∃ y : ℕ → ℝ, CoreFeasible v k J Jstar y := by
  intro J
  obtain ⟨Js, h1, ⟨y, hy⟩, _⟩ := hwc_goal_core c v hw t π k hrun ht J
  exact ⟨Js, h1, y, hy.1⟩

end HeldWolfeCrowder.CoreProblem

open HeldWolfeCrowder.CoreProblem


theorem solution {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v)))
    (t : ℕ → ℝ) (π : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι)
    (hrun : IsSubgradientRun c v t π k) (ht : StepSizeCond t)
    (hbdd : Bornology.IsBounded (Set.range π)) :
    ∀ J : ℕ, ∃ Jstar : ℕ, J < Jstar ∧
      (∃ y : ℕ → ℝ, IsCoreOptimal c v k J Jstar y) ∧
      ∀ y : ℕ → ℝ, IsCoreOptimal c v k J Jstar y →
        IsDualOptimal c v (aggregate k J Jstar y) := by
  exact hwc_goal_core c v hw t π k hrun ht
