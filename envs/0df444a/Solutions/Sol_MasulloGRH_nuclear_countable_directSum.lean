-- Prove2me | solution 1 for MasulloGRH.nuclear_countable_directSum
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-20T23:02:51.717677+00:00
-- url     : https://prove2.me/submissions/dfe491f1-f831-486c-acac-f6c0e999dd6b

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH DirectSum

namespace NuclearDirectSumAux

lemma seminorm_sum_le {X : Type*} [AddCommGroup X] [Module ℂ X] (p : Seminorm ℂ X)
    {ι : Type*} (s : Finset ι) (g : ι → X) : p (∑ i ∈ s, g i) ≤ ∑ i ∈ s, p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

/-- A locally convex topology given by a polynormable structure is locally convex in the sense
of the mission's definition file. -/
lemma lc_of_polynormable {X : Type*} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : @PolynormableSpace ℂ X _ _ _ t) : IsLocallyConvexTopology X t :=
  ⟨{p : Seminorm ℂ X // @Continuous X ℝ t _ p}, ⟨⟨0, @continuous_const X ℝ t _ 0⟩⟩,
    fun p => p.1, @PolynormableSpace.withSeminorms ℂ X _ _ _ t h⟩

lemma polynormable_of_lc {X : Type*} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : IsLocallyConvexTopology X t) : @PolynormableSpace ℂ X _ _ _ t := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact @WithSeminorms.toPolynormableSpace ℂ X ι _ _ _ t p hp

end NuclearDirectSumAux

open NuclearDirectSumAux

theorem solution (Y : ℕ → Type*) [∀ n, AddCommGroup (Y n)]
    [∀ n, Module ℂ (Y n)] (τ : ∀ n, TopologicalSpace (Y n))
    (hY : ∀ n, @IsNuclear (Y n) _ _ (τ n))
    (t : TopologicalSpace (DirectSum ℕ Y))
    (ht : t = sInf {t' | IsLocallyConvexTopology (DirectSum ℕ Y) t' ∧
      ∀ n, @Continuous (Y n) (DirectSum ℕ Y) (τ n) t' (DirectSum.lof ℂ ℕ Y n)}) :
    @IsNuclear (DirectSum ℕ Y) _ _ t := by
  classical
  letI : ∀ n, TopologicalSpace (Y n) := τ
  letI : TopologicalSpace (DirectSum ℕ Y) := t
  -- seminorm families on the summands
  choose κ hκ pY hpY using fun n => (hY n).1.1
  have hT2Y : ∀ n, T2Space (Y n) := fun n => (hY n).1.2
  have : ∀ n, IsTopologicalAddGroup (Y n) := fun n => (hpY n).topologicalAddGroup
  -- `t` is polynormable
  have hPol : @PolynormableSpace ℂ (DirectSum ℕ Y) _ _ _ t := by
    rw [ht]
    exact PolynormableSpace.sInf fun t' ht' => polynormable_of_lc t' ht'.1
  have hP : WithSeminorms (fun p : {p : Seminorm ℂ (DirectSum ℕ Y) // Continuous p} ↦ p.1) :=
    PolynormableSpace.withSeminorms ℂ (DirectSum ℕ Y)
  have : IsTopologicalAddGroup (DirectSum ℕ Y) := hP.topologicalAddGroup
  -- the canonical injections are continuous
  have hlof : ∀ n, @Continuous (Y n) (DirectSum ℕ Y) (τ n) t (DirectSum.lof ℂ ℕ Y n) := by
    intro n
    rw [ht]
    exact continuous_sInf_rng.2 fun t' ht' => ht'.2 n
  -- universal property: a seminorm is continuous if all its restrictions to summands are
  have hU : ∀ r : Seminorm ℂ (DirectSum ℕ Y),
      (∀ n, Continuous (r.comp (DirectSum.lof ℂ ℕ Y n))) → Continuous r := by
    intro r hr
    let tr : TopologicalSpace (DirectSum ℕ Y) :=
      (SeminormFamily.moduleFilterBasis (fun _ : Unit => r)).topology
    have hWr : WithSeminorms (topology := tr) (fun _ : Unit => r) := by
      letI := tr
      exact WithSeminorms.mk rfl
    have hle : t ≤ tr := by
      rw [ht]
      letI := tr
      refine sInf_le ⟨lc_of_polynormable tr (hWr.toPolynormableSpace), fun n => ?_⟩
      exact hWr.continuous_of_continuous_comp (DirectSum.lof ℂ ℕ Y n) (fun _ => hr n)
    have hrc : @Continuous _ ℝ tr _ r := by
      letI := tr
      exact hWr.continuous_seminorm ()
    exact continuous_le_dom hle hrc
  -- seminorms pulled back along a coordinate projection are continuous
  have hcomp : ∀ n (r : Seminorm ℂ (Y n)), Continuous r →
      Continuous (r.comp (DirectSum.component ℂ ℕ Y n)) := by
    intro n r hr
    apply hU
    intro m
    by_cases hmn : m = n
    · subst hmn
      have : (r.comp (DirectSum.component ℂ ℕ Y m)).comp (DirectSum.lof ℂ ℕ Y m) = r := by
        ext y; simp [Seminorm.comp_apply]
      rw [this]; exact hr
    · have : (r.comp (DirectSum.component ℂ ℕ Y n)).comp (DirectSum.lof ℂ ℕ Y m) = 0 := by
        ext y; simp [Seminorm.comp_apply, DirectSum.component.of, hmn]
      rw [this]; exact continuous_const
  -- the coordinate projections are continuous
  have hcompL : ∀ n, Continuous (DirectSum.component ℂ ℕ Y n) := fun n =>
    WithSeminorms.continuous_of_continuous_comp (hpY n) _ fun k => hcomp n _
      ((hpY n).continuous_seminorm k)
  let compL : ∀ n, DirectSum ℕ Y →L[ℂ] Y n := fun n => ⟨DirectSum.component ℂ ℕ Y n, hcompL n⟩
  -- Hausdorff
  have hT1 : T1Space (DirectSum ℕ Y) := by
    apply hP.T1_of_separating
    intro x hx
    obtain ⟨n, hn⟩ : ∃ n, x n ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (DFinsupp.ext h)
    obtain ⟨k, hk⟩ := ((hpY n).separating_iff_T1).2 inferInstance (x n) hn
    exact ⟨⟨(pY n k).comp (DirectSum.component ℂ ℕ Y n),
      hcomp n _ ((hpY n).continuous_seminorm k)⟩, hk⟩
  apply nuclear_of_quasinuclear_domination (DirectSum ℕ Y)
    ⟨lc_of_polynormable t hPol, inferInstance⟩
  intro p hp
  -- restrictions of `p`, scaled by `2^(n+1)`, and their dominations
  have hpn : ∀ n, Continuous (((2 : NNReal) ^ (n + 1)) • p.comp (DirectSum.lof ℂ ℕ Y n)) :=
    fun n => (hp.comp (hlof n)).const_smul _
  choose q f c hq hc0 hcs hfq hdom using fun n =>
    nuclear_quasinuclear_domination (Y n) (hY n) _ (hpn n)
  set a : ℕ → ℝ := fun n => (∑' k, c n k) + 1 with ha
  have hS0 : ∀ n, 0 ≤ ∑' k, c n k := fun n => tsum_nonneg (fun k => hc0 n k)
  have ha0 : ∀ n, 0 < a n := fun n => by
    have := hS0 n; show 0 < (∑' k, c n k) + 1; linarith
  -- the dominating seminorm on the direct sum
  have hfin : ∀ x : DirectSum ℕ Y, ∀ n ∉ DFinsupp.support x, a n * q n (x n) = 0 := by
    intro x n hn
    rw [DFinsupp.notMem_support_iff.1 hn, map_zero, mul_zero]
  have hQs : ∀ x : DirectSum ℕ Y, Summable fun n => a n * q n (x n) := fun x =>
    summable_of_ne_finset_zero (hfin x)
  let Q : Seminorm ℂ (DirectSum ℕ Y) := Seminorm.of (fun x => ∑' n, a n * q n (x n))
    (fun x y => by
      rw [← (hQs x).tsum_add (hQs y)]
      refine (hQs (x + y)).tsum_le_tsum (fun n => ?_) ((hQs x).add (hQs y))
      rw [DirectSum.add_apply, ← mul_add]
      exact mul_le_mul_of_nonneg_left (map_add_le_add _ _ _) (ha0 n).le)
    (fun r x => by
      rw [← tsum_mul_left]
      congr 1; funext n
      rw [DirectSum.smul_apply, map_smul_eq_mul]; ring)
  have hQ : ∀ x n, a n * q n (x n) ≤ Q x := fun x n =>
    (hQs x).le_tsum n fun j _ => mul_nonneg (ha0 j).le (apply_nonneg _ _)
  have hQc : Continuous Q := by
    apply hU
    intro m
    have : Q.comp (DirectSum.lof ℂ ℕ Y m) = (a m).toNNReal • q m := by
      ext y
      simp only [Seminorm.comp_apply, _root_.smul_apply, NNReal.smul_def, smul_eq_mul,
        Real.coe_toNNReal _ (ha0 m).le]
      show ∑' n, a n * q n ((DirectSum.lof ℂ ℕ Y m y) n) = _
      rw [tsum_eq_single m]
      · rw [DirectSum.lof_apply]
      · intro n hn
        have : (DirectSum.lof ℂ ℕ Y m y) n = 0 := by
          rw [DirectSum.lof_eq_of]; exact DirectSum.of_eq_of_ne _ _ _ hn
        rw [this, map_zero, mul_zero]
    rw [this]; exact (hq m).const_smul _

  -- assembling the countable family of functionals
  let e : ℕ × ℕ ≃ ℕ := Nat.pairEquiv
  let C : ℕ → ℝ := fun m =>
    (1 / 2 : ℝ) ^ ((e.symm m).1 + 1) * c (e.symm m).1 (e.symm m).2 / a (e.symm m).1
  let F : ℕ → StrongDual ℂ (DirectSum ℕ Y) := fun m =>
    (a (e.symm m).1 : ℂ) • (f (e.symm m).1 (e.symm m).2).comp (compL (e.symm m).1)
  have hC0 : ∀ m, 0 ≤ C m := fun m =>
    div_nonneg (mul_nonneg (by positivity) (hc0 _ _)) (ha0 _).le
  let G : ℕ × ℕ → ℝ := fun nk => (1 / 2 : ℝ) ^ (nk.1 + 1) * c nk.1 nk.2 / a nk.1
  have hG0 : 0 ≤ G := fun nk => div_nonneg (mul_nonneg (by positivity) (hc0 _ _)) (ha0 _).le
  have hGin : ∀ n, Summable fun k => G (n, k) := fun n =>
    ((hcs n).mul_left ((1 / 2 : ℝ) ^ (n + 1))).div_const (a n)
  have hGsum : ∀ n, ∑' k, G (n, k) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    show ∑' k, (1 / 2 : ℝ) ^ (n + 1) * c n k / a n ≤ _
    rw [tsum_div_const, tsum_mul_left, mul_div_assoc]
    have h1 : (∑' k, c n k) / a n ≤ 1 := by
      rw [div_le_one (ha0 n)]; show _ ≤ (∑' k, c n k) + 1; linarith
    calc (1 / 2 : ℝ) ^ (n + 1) * ((∑' k, c n k) / a n) ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _
  have hG : Summable G := by
    rw [summable_prod_of_nonneg hG0]
    refine ⟨hGin, ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => hG0 _) hGsum ?_
    exact (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left (1 / 2)
      |>.congr fun n => by ring
  have hCe : ∀ nk, C (e nk) = G nk := fun nk => by simp [C, G]
  refine ⟨Q, F, C, hQc, hC0, ?_, ?_, ?_⟩
  · rw [← e.summable_iff]
    exact hG.congr fun nk => (hCe nk).symm
  · intro m x
    show ‖(a (e.symm m).1 : ℂ) * (f (e.symm m).1 (e.symm m).2) (x (e.symm m).1)‖ ≤ Q x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha0 _).le]
    exact (mul_le_mul_of_nonneg_left (hfq _ _ _) (ha0 _).le).trans (hQ x _)
  · intro x
    let H : ℕ × ℕ → ℝ := fun nk => (1 / 2 : ℝ) ^ (nk.1 + 1) * (c nk.1 nk.2 * ‖f nk.1 nk.2 (x nk.1)‖)
    have hH0 : 0 ≤ H := fun nk => mul_nonneg (by positivity) (mul_nonneg (hc0 _ _) (norm_nonneg _))
    have hHe : ∀ nk, C (e nk) * ‖F (e nk) x‖ = H nk := by
      intro nk
      rw [hCe nk]
      show G nk * ‖(a (e.symm (e nk)).1 : ℂ) *
        (f (e.symm (e nk)).1 (e.symm (e nk)).2) (x (e.symm (e nk)).1)‖ = H nk
      rw [show e.symm (e nk) = nk from e.symm_apply_apply nk]
      simp only [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (ha0 _).le, G, H]
      field_simp [(ha0 nk.1).ne']
    have hHG : ∀ nk, H nk ≤ G nk * Q x := by
      intro nk
      rw [← hHe nk, hCe nk]
      refine mul_le_mul_of_nonneg_left ?_ (hG0 nk)
      show ‖(a (e.symm (e nk)).1 : ℂ) *
        (f (e.symm (e nk)).1 (e.symm (e nk)).2) (x (e.symm (e nk)).1)‖ ≤ Q x
      rw [show e.symm (e nk) = nk from e.symm_apply_apply nk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha0 _).le]
      exact (mul_le_mul_of_nonneg_left (hfq _ _ _) (ha0 _).le).trans (hQ x _)
    have hH : Summable H := Summable.of_nonneg_of_le hH0 hHG (hG.mul_right (Q x))
    have hHin := ((summable_prod_of_nonneg hH0).1 hH)
    have hstep : ∀ n, p (DirectSum.lof ℂ ℕ Y n (x n)) ≤ ∑' k, H (n, k) := by
      intro n
      have hd := hdom n (x n)
      simp only [_root_.smul_apply, NNReal.smul_def, smul_eq_mul, Seminorm.comp_apply,
        NNReal.coe_pow, NNReal.coe_ofNat] at hd
      show _ ≤ ∑' k, (1 / 2 : ℝ) ^ (n + 1) * (c n k * ‖f n k (x n)‖)
      rw [tsum_mul_left]
      have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
      calc p (DirectSum.lof ℂ ℕ Y n (x n))
          = (1 / 2 : ℝ) ^ (n + 1) * (2 ^ (n + 1) * p (DirectSum.lof ℂ ℕ Y n (x n))) := by
            rw [← mul_assoc, ← mul_pow]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
    calc p x = p (∑ n ∈ DFinsupp.support x, DirectSum.lof ℂ ℕ Y n (x n)) := by
          congr 1
          simp only [DirectSum.lof_eq_of]
          exact (DirectSum.sum_support_of x).symm
      _ ≤ ∑ n ∈ DFinsupp.support x, p (DirectSum.lof ℂ ℕ Y n (x n)) := seminorm_sum_le _ _ _
      _ ≤ ∑ n ∈ DFinsupp.support x, ∑' k, H (n, k) := Finset.sum_le_sum fun n _ => hstep n
      _ ≤ ∑' n, ∑' k, H (n, k) :=
          hHin.2.sum_le_tsum _ (fun n _ => tsum_nonneg fun k => hH0 _)
      _ = ∑' nk, H nk := (hH.tsum_prod).symm
      _ = ∑' m, C m * ‖F m x‖ := by
          rw [← e.tsum_eq]
          exact tsum_congr fun nk => (hHe nk).symm
