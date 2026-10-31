-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.proposition_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:22:41.296989+00:00
-- url     : https://prove2.me/submissions/f07e026b-e4b1-4ede-a261-229292888c8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_1_value

namespace HubSpoke31Aux

open HubSpokePricing.Lagrangian Finset

lemma rev_lower (rbar omega : ℝ) (r : ℝ → ℝ) (hr : RevenueAssumption rbar omega r) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : -omega ≤ r u := by
  obtain ⟨-, h0, -, hd, hb, -⟩ := hr
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_derivWithin_le hd
    (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx) hu ⟨le_rfl, zero_le_one⟩
  simp only [Real.norm_eq_abs, h0, zero_sub, abs_neg] at this
  have h1 : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  have h2 : 0 ≤ omega := le_trans (abs_nonneg _) (hb 0 ⟨le_rfl, zero_le_one⟩)
  have := this.trans (mul_le_mul_of_nonneg_left h1 h2)
  rw [abs_le] at this; linarith [this.1]

lemma sum_q (N : Network) (hN : N.Standing) : ∑ s : Req N, N.q s = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [Network.q, Sum.elim_inl, Sum.elim_inr]
  rw [← sum_add_distrib]; exact hN.2.2.2.1

lemma q_nonneg (N : Network) (hN : N.Standing) (s : Req N) : 0 ≤ N.q s := by
  cases s with
  | inl i => exact (hN.2.1 i).le
  | inr i => exact (hN.2.2.1 i).le

lemma r_bounds (N : Network) (hN : N.Standing) (s : Req N) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    -N.omega ≤ N.r s u ∧ N.r s u ≤ N.rbar := by
  obtain ⟨-, -, -, -, -, -, hr⟩ := hN
  cases s with
  | inl i => exact ⟨rev_lower _ _ _ (hr i).1 u hu, (hr i).1.2.2.1 u hu⟩
  | inr i => exact ⟨rev_lower _ _ _ (hr i).2 u hu, (hr i).2.2.2.1 u hu⟩

/-- `limsup u ≤ max C 0` whenever `u ≤ C` (the real `limsup` is `0` when unbounded below). -/
lemma limsup_le_max (u : ℕ → ℝ) (C : ℝ) (h : ∀ n, u n ≤ C) :
    Filter.limsup u Filter.atTop ≤ max C 0 := by
  rw [Filter.limsup_eq]
  by_cases hb : BddBelow {a | ∀ᶠ n in Filter.atTop, u n ≤ a}
  · exact (csInf_le hb (Filter.Eventually.of_forall h)).trans (le_max_left _ _)
  · rw [Real.sInf_of_not_bddBelow hb]; exact le_max_right _ _

lemma J_lower (N : Network) (hN : N.Standing) (π : Policy N)
    (hπ : ∀ h s, 0 ≤ π h s ∧ π h s ≤ 1) : ∀ T h, -(T * N.omega) ≤ J N π T h := by
  intro T
  induction T with
  | zero => intro h; simp [J]
  | succ T ih =>
    intro h
    simp only [J]
    have : ∑ s : Req N, N.q s * (-N.omega + π h s * (-(T * N.omega)) +
        (1 - π h s) * (-(T * N.omega))) ≤ ∑ s : Req N, N.q s *
        (N.r s (π h s) + π h s * J N π T (h ++ [(s, true)]) +
          (1 - π h s) * J N π T (h ++ [(s, false)])) := by
      apply sum_le_sum; intro s _
      apply mul_le_mul_of_nonneg_left _ (q_nonneg N hN s)
      have h1 := (r_bounds N hN s (π h s) ⟨(hπ h s).1, (hπ h s).2⟩).1
      have h2 := mul_le_mul_of_nonneg_left (ih (h ++ [(s, true)])) (hπ h s).1
      have h3 := mul_le_mul_of_nonneg_left (ih (h ++ [(s, false)]))
        (sub_nonneg.2 (hπ h s).2)
      linarith
    have e : ∑ s : Req N, N.q s * (-N.omega + π h s * (-(T * N.omega)) +
        (1 - π h s) * (-(T * N.omega))) = -(((T + 1 : ℕ) : ℝ) * N.omega) := by
      have : ∀ s : Req N, N.q s * (-N.omega + π h s * (-(T * N.omega)) +
          (1 - π h s) * (-(T * N.omega))) = N.q s * (-(((T + 1 : ℕ) : ℝ) * N.omega)) := by
        intro s; push_cast; ring
      rw [sum_congr rfl fun s _ => this s, ← sum_mul, sum_q N hN, one_mul]
    linarith

lemma JRelax_upper (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (x0 : Fin N.n → ℕ) (π : Policy N) (hπ : ∀ h s, 0 ≤ π h s ∧ π h s ≤ 1) :
    ∀ T h, JRelax N lam x0 π T h ≤ T * (lam * N.m + N.rbar) := by
  intro T
  induction T with
  | zero => intro h; simp [JRelax]
  | succ T ih =>
    intro h
    simp only [JRelax]
    have hpen : lam * ((N.m : ℝ) - ∑ i, ((stateAfter N x0 h i : ℕ) : ℝ)) ≤ lam * N.m := by
      apply mul_le_mul_of_nonneg_left _ hlam
      have : 0 ≤ ∑ i, ((stateAfter N x0 h i : ℕ) : ℝ) := sum_nonneg fun i _ => Nat.cast_nonneg _
      linarith
    have : ∑ s : Req N, N.q s *
        (N.r s (π h s) + π h s * JRelax N lam x0 π T (h ++ [(s, true)]) +
          (1 - π h s) * JRelax N lam x0 π T (h ++ [(s, false)])) ≤
        ∑ s : Req N, N.q s * (N.rbar + T * (lam * N.m + N.rbar)) := by
      apply sum_le_sum; intro s _
      apply mul_le_mul_of_nonneg_left _ (q_nonneg N hN s)
      have h1 := (r_bounds N hN s (π h s) ⟨(hπ h s).1, (hπ h s).2⟩).2
      have h2 := mul_le_mul_of_nonneg_left (ih (h ++ [(s, true)])) (hπ h s).1
      have h3 := mul_le_mul_of_nonneg_left (ih (h ++ [(s, false)]))
        (sub_nonneg.2 (hπ h s).2)
      nlinarith
    rw [← sum_mul, sum_q N hN, one_mul] at this
    push_cast
    linarith

lemma stateAfter_snoc (N : Network) (x0 : Fin N.n → ℕ) (h : History N) (e : Req N × Bool) :
    stateAfter N x0 (h ++ [e]) = stepState N (stateAfter N x0 h) e := by
  simp [stateAfter, List.foldl_append]

/-- weak duality along the paths of an originally-feasible policy -/
lemma J_le_JRelax (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (x0 : Fin N.n → ℕ) (π : Policy N) (hπ : Feasible N x0 π) :
    ∀ T h, ∑ i, stateAfter N x0 h i ≤ N.m → J N π T h ≤ JRelax N lam x0 π T h := by
  intro T
  induction T with
  | zero => intro h _; simp [J, JRelax]
  | succ T ih =>
    intro h hX
    simp only [J, JRelax]
    have hpen : 0 ≤ lam * ((N.m : ℝ) - ∑ i, ((stateAfter N x0 h i : ℕ) : ℝ)) := by
      apply mul_nonneg hlam
      have : (∑ i, ((stateAfter N x0 h i : ℕ) : ℝ)) ≤ N.m := by exact_mod_cast hX
      linarith
    have : ∑ s : Req N, N.q s *
        (N.r s (π h s) + π h s * J N π T (h ++ [(s, true)]) +
          (1 - π h s) * J N π T (h ++ [(s, false)])) ≤
        ∑ s : Req N, N.q s *
        (N.r s (π h s) + π h s * JRelax N lam x0 π T (h ++ [(s, true)]) +
          (1 - π h s) * JRelax N lam x0 π T (h ++ [(s, false)])) := by
      apply sum_le_sum; intro s _
      apply mul_le_mul_of_nonneg_left _ (q_nonneg N hN s)
      obtain ⟨hπ0, hπ1, hπe⟩ := hπ h s
      -- false branch: the state does not move
      have hf : J N π T (h ++ [(s, false)]) ≤ JRelax N lam x0 π T (h ++ [(s, false)]) := by
        apply ih
        rw [stateAfter_snoc]; simpa [stepState] using hX
      have hf' := mul_le_mul_of_nonneg_left hf (sub_nonneg.2 hπ1)
      -- true branch
      rcases hπ0.lt_or_eq with hpos | hzero
      · have ht : J N π T (h ++ [(s, true)]) ≤ JRelax N lam x0 π T (h ++ [(s, true)]) := by
          apply ih
          rw [stateAfter_snoc]
          set x := stateAfter N x0 h
          cases s with
          | inl i =>
            simp only [stepState]
            rw [Finset.sum_update_of_mem (mem_univ i)]
            have := Finset.add_sum_erase univ x (mem_univ i)
            rw [Finset.sdiff_singleton_eq_erase]
            omega
          | inr i =>
            simp only [stepState]
            have hne : ¬ originEmpty N x (Sum.inr i) := fun he => by
              rw [hπe he] at hpos; exact lt_irrefl _ hpos
            simp only [originEmpty, not_le] at hne
            rw [Finset.sum_update_of_mem (mem_univ i)]
            have := Finset.add_sum_erase univ x (mem_univ i)
            rw [Finset.sdiff_singleton_eq_erase]
            omega
        have ht' := mul_le_mul_of_nonneg_left ht hπ0
        linarith
      · rw [← hzero]; simp only [zero_mul, add_zero, sub_zero, one_mul] at hf' ⊢
        linarith
    linarith

end HubSpoke31Aux

open HubSpokePricing.Lagrangian Finset HubSpoke31Aux

theorem solution (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ x0 : Fin N.n → ℕ, InXbar N x0 → VbarRelax N lam x0 = Vbar N lam) ∧
      ∀ x0 : Fin N.n → ℕ, InX N x0 → VOPT N x0 ≤ VbarRelax N lam x0 := by
  refine ⟨proposition_3_1_value N hN lam hlam, ?_⟩
  intro x0 hx0
  set C : ℝ := lam * N.m + N.rbar with hC
  have hom : 0 < N.omega := hN.2.2.2.2.2.1
  have hC0 : 0 ≤ C := by rw [hC]; have := hN.2.2.2.2.1; positivity
  -- the relaxation's values are bounded above by `max C 0`
  have hbdd : BddAbove (Set.range fun π : {π : Policy N // FeasibleRelax N x0 π} =>
      Filter.limsup (fun T : ℕ => JRelax N lam x0 π.1 T [] / (T : ℝ)) Filter.atTop) := by
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨π, rfl⟩
    apply limsup_le_max
    intro T
    have hπ : ∀ h s, 0 ≤ π.1 h s ∧ π.1 h s ≤ 1 := fun h s => ⟨(π.2 h s).1, (π.2 h s).2.1⟩
    have := JRelax_upper N hN lam hlam x0 π.1 hπ T []
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT; simpa using hC0
    · rw [div_le_iff₀ (by exact_mod_cast hT)]; linarith
  have : Nonempty {π : Policy N // Feasible N x0 π} :=
    ⟨⟨fun _ _ => 0, fun _ _ => ⟨le_rfl, zero_le_one, fun _ => rfl⟩⟩⟩
  apply ciSup_le
  intro π
  -- the same policy is feasible in the relaxation
  have hrel : FeasibleRelax N x0 π.1 := by
    intro h s
    obtain ⟨h0, h1, he⟩ := π.2 h s
    refine ⟨h0, h1, fun hb => he ?_⟩
    cases s with
    | inl i => exact hb
    | inr i =>
      simp only [relaxBlocked] at hb
      simp only [originEmpty]
      exact le_trans hb (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i))
  have hπ : ∀ h s, 0 ≤ π.1 h s ∧ π.1 h s ≤ 1 := fun h s => ⟨(π.2 h s).1, (π.2 h s).2.1⟩
  refine le_trans ?_ (le_ciSup hbdd ⟨π.1, hrel⟩)
  apply Filter.limsup_le_limsup
  · apply Filter.Eventually.of_forall
    intro T
    have := J_le_JRelax N hN lam hlam x0 π.1 π.2 T [] (by simpa [stateAfter, InX] using hx0)
    exact div_le_div_of_nonneg_right this (Nat.cast_nonneg _)
  · apply Filter.isCoboundedUnder_le_of_le Filter.atTop (x := -N.omega)
    intro T
    have := J_lower N hN π.1 hπ T []
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT; simp; exact hom.le
    · rw [le_div_iff₀ (by exact_mod_cast hT)]; linarith
  · apply Filter.isBoundedUnder_of
    refine ⟨C, fun T => ?_⟩
    have := JRelax_upper N hN lam hlam x0 π.1 hπ T []
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT; simpa using hC0
    · rw [div_le_iff₀ (by exact_mod_cast hT)]; linarith
