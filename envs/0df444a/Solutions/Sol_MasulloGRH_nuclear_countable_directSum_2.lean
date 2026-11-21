-- Prove2me | solution 2 for MasulloGRH.nuclear_countable_directSum
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:03:36.024188+00:00
-- url     : https://prove2.me/submissions/c18bb5f4-cf29-4df1-b9c1-682ec5b5a2a6

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination
import Theorems.Thm_RiemannMasullo_directSumSeminorm_lof

set_option autoImplicit false

open MasulloGRH RiemannMasullo Topology TopologicalSpace
open scoped DirectSum

private theorem polynormable_of_locallyConvex {E : Type*} [AddCommGroup E] [Module ℂ E]
    {t : TopologicalSpace E} (h : IsLocallyConvexTopology E t) :
    @PolynormableSpace ℂ E _ _ _ t := by
  obtain ⟨_, _, _, hp⟩ := h
  exact hp.toPolynormableSpace

private theorem locallyConvex_of_polynormable {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E] :
    IsLocallyConvexTopology E inferInstance :=
  ⟨_, ⟨⟨0, continuous_const⟩⟩, _, PolynormableSpace.withSeminorms ℂ E⟩

set_option maxHeartbeats 800000 in
theorem solution (Y : ℕ → Type*) [∀ n, AddCommGroup (Y n)]
    [∀ n, Module ℂ (Y n)] (τ : ∀ n, TopologicalSpace (Y n))
    (hY : ∀ n, @IsNuclear (Y n) _ _ (τ n))
    (t : TopologicalSpace (DirectSum ℕ Y))
    (ht : t = sInf {t' | IsLocallyConvexTopology (DirectSum ℕ Y) t' ∧
      ∀ n, @Continuous (Y n) (DirectSum ℕ Y) (τ n) t' (DirectSum.lof ℂ ℕ Y n)}) :
    @IsNuclear (DirectSum ℕ Y) _ _ t := by
  classical
  let D := DirectSum ℕ Y
  let _ : TopologicalSpace D := t
  let _ : ∀ n, TopologicalSpace (Y n) := τ
  let incl := DirectSum.lof ℂ ℕ Y
  let coord := DirectSum.component ℂ ℕ Y

  have hfinal {t' : TopologicalSpace D} (hlc : IsLocallyConvexTopology D t')
      (h : ∀ n, @Continuous (Y n) D (τ n) t' (incl n)) : t ≤ t' := by
    rw [ht]
    exact sInf_le ⟨hlc, h⟩
  have hincl (n : ℕ) : @Continuous (Y n) D (τ n) t (incl n) := by
    apply continuous_iff_coinduced_le.mpr
    rw [ht]
    exact le_sInf (fun _ hs => continuous_iff_coinduced_le.mp (hs.2 n))
  have hcoord (n : ℕ) : @Continuous D (Y n) t (τ n) (coord n) := by
    apply continuous_iff_le_induced.mpr
    obtain ⟨ι, hι, p, hp⟩ := (hY n).1.1
    refine hfinal ⟨ι, hι, p.comp (coord n), (coord n).withSeminorms_induced hp⟩ ?_
    intro m
    apply continuous_induced_rng.mpr
    by_cases h : m = n
    · subst m
      have heq : (coord n : D → Y n) ∘ incl n = id := by
        funext x
        exact DirectSum.component.lof_self ℂ n x
      rw [heq]
      exact continuous_id
    · simpa [Function.comp_def, coord, incl, DirectSum.component.of, h] using
        (@continuous_const (Y m) (Y n) (τ m) (τ n) 0)
  have : PolynormableSpace ℂ D := by
    change @PolynormableSpace ℂ D _ _ _ t
    rw [ht]
    exact PolynormableSpace.sInf (fun _ hs => polynormable_of_locallyConvex hs.1)
  have : ∀ n, T2Space (Y n) := fun n => (hY n).1.2
  have hD : IsHLCS D := by
    refine ⟨locallyConvex_of_polynormable, ?_⟩
    exact T2Space.of_injective_continuous
      (fun _ _ h => DirectSum.ext_component ℂ (fun i => congrFun h i))
      (continuous_pi hcoord : Continuous (fun x : D => fun n => coord n x))
  refine nuclear_of_quasinuclear_domination D hD ?_
  intro p hp

  -- Use the summand criterion on the restriction of the original seminorm.
  have hstage (n : ℕ) :=
    nuclear_quasinuclear_domination (Y n) (hY n) (p.comp (incl n)) (hp.comp (hincl n))
  choose q f c hq hc hcs hf hdom using hstage
  let a (n : ℕ) : ℝ := 1 / ((1 / 2 : ℝ) ^ n) * (1 + ∑' k, c n k)
  have ha (n : ℕ) : 0 < a n := by
    have hs : 0 ≤ ∑' k, c n k := tsum_nonneg (hc n)
    unfold a
    positivity
  let qScaled (n : ℕ) : Seminorm ℂ (Y n) :=
    (q n).comp ((a n : ℂ) • (LinearMap.id : Y n →ₗ[ℂ] Y n))
  let Q : Seminorm ℂ D := directSumSeminorm qScaled
  have hqScaled (n : ℕ) (x : Y n) : qScaled n x = a n * q n x := by
    change q n ((a n : ℂ) • x) = a n * q n x
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (ha n).le]
  have hQ : Continuous Q := by
    let family : SeminormFamily ℂ D (Fin 1) := fun _ => Q
    let tQ := family.moduleFilterBasis.topology
    have hfamily : @WithSeminorms ℂ D (Fin 1) _ _ _ family tQ := ⟨rfl⟩
    have hQlc : IsLocallyConvexTopology D tQ :=
      @locallyConvex_of_polynormable D _ _ tQ hfamily.toPolynormableSpace
    apply continuous_le_dom (hfinal hQlc ?_) (hfamily.continuous_seminorm 0)
    intro n
    let _ : TopologicalSpace D := tQ
    let _ : TopologicalSpace (Y n) := τ n
    have : IsTopologicalAddGroup (Y n) :=
      (polynormable_of_locallyConvex (hY n).1.1).withSeminorms'.topologicalAddGroup
    refine (hfamily.continuous_iff_continuous_comp (incl n)).2 (fun i => ?_)
    have hfun : ((family i).comp (incl n) : Y n → ℝ) = fun x => a n * q n x := by
      funext x
      change Q (incl n x) = _
      rw [show Q (incl n x) = qScaled n x from directSumSeminorm_lof qScaled n x, hqScaled]
    rw [hfun]
    exact continuous_const.mul (hq n)

  -- Rescale each summand to make the total coefficient mass summable over both indices.
  let C (nk : ℕ × ℕ) : ℝ := (a nk.1)⁻¹ * c nk.1 nk.2
  let F (nk : ℕ × ℕ) : StrongDual ℂ D :=
    (a nk.1 : ℂ) • (f nk.1 nk.2).comp ⟨coord nk.1, hcoord nk.1⟩
  have hC (nk : ℕ × ℕ) : 0 ≤ C nk := mul_nonneg (inv_nonneg.mpr (ha nk.1).le) (hc _ _)
  have hCs : Summable C := by
    refine (summable_prod_of_nonneg (f := C) hC).2
      ⟨fun n => (hcs n).mul_left ((a n)⁻¹), ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun k => hC (n, k)))
      (fun n => ?_) summable_geometric_two
    change (∑' k, (a n)⁻¹ * c n k) ≤ (1 / 2 : ℝ) ^ n
    rw [(hcs n).tsum_mul_left]
    have hs : 0 ≤ ∑' k, c n k := tsum_nonneg (hc n)
    have hr : 0 < (1 / 2 : ℝ) ^ n := by positivity
    dsimp [a]
    rw [mul_inv, one_div, inv_inv, mul_assoc]
    have hfrac : (1 + ∑' k, c n k)⁻¹ * (∑' k, c n k) ≤ 1 := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (div_le_one (by positivity)).2 (by linarith)
    calc
      _ ≤ (1 / 2 : ℝ) ^ n * 1 := mul_le_mul_of_nonneg_left hfrac hr.le
      _ = _ := mul_one _
  have hFnorm (nk : ℕ × ℕ) (x : D) : ‖F nk x‖ = a nk.1 * ‖f nk.1 nk.2 (x nk.1)‖ := by
    rw [show F nk x = (a nk.1 : ℂ) • f nk.1 nk.2 (x nk.1) from rfl,
      norm_smul, Complex.norm_real, Real.norm_of_nonneg (ha nk.1).le]
  have hQterm (n : ℕ) (x : D) : qScaled n (x n) ≤ Q x := by
    change qScaled n (x n) ≤ ∑ i ∈ x.support, qScaled i (x i)
    by_cases h : n ∈ x.support
    · exact Finset.single_le_sum (fun i _ => apply_nonneg (qScaled i) _) h
    · have hx : x n = 0 := by simpa [DFinsupp.mem_support_iff] using h
      rw [hx, map_zero]
      exact Finset.sum_nonneg (fun i _ => apply_nonneg (qScaled i) _)
  have hF (nk : ℕ × ℕ) (x : D) : ‖F nk x‖ ≤ Q x := by
    calc
      ‖F nk x‖ = a nk.1 * ‖f nk.1 nk.2 (x nk.1)‖ := hFnorm nk x
      _ ≤ a nk.1 * q nk.1 (x nk.1) :=
        mul_le_mul_of_nonneg_left (hf nk.1 nk.2 (x nk.1)) (ha nk.1).le
      _ = qScaled nk.1 (x nk.1) := (hqScaled nk.1 (x nk.1)).symm
      _ ≤ Q x := hQterm nk.1 x
  let e := Nat.pairEquiv.symm
  refine ⟨Q, F ∘ e, C ∘ e, hQ, fun n => hC (e n), e.summable_iff.mpr hCs,
    fun n x => hF (e n) x, ?_⟩
  intro x
  let term (nk : ℕ × ℕ) : ℝ := C nk * ‖F nk x‖
  have hterm (nk : ℕ × ℕ) : 0 ≤ term nk := mul_nonneg (hC nk) (norm_nonneg _)
  have hterms : Summable term :=
    Summable.of_nonneg_of_le hterm
      (fun nk => mul_le_mul_of_nonneg_left (hF nk x) (hC nk)) (hCs.mul_right (Q x))
  have hterm_eq (n k : ℕ) : term (n, k) = c n k * ‖f n k (x n)‖ := by
    dsimp [term, C]
    rw [hFnorm]
    field_simp [ne_of_gt (ha n)]
  have htriangle (s : Finset ℕ) :
      p (∑ n ∈ s, incl n (x n)) ≤ ∑ n ∈ s, p (incl n (x n)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hsum : (∑ n ∈ x.support, incl n (x n)) = x :=
    DirectSum.sum_support_of x
  calc
    p x = p (∑ n ∈ x.support, incl n (x n)) := congrArg p hsum.symm
    _ ≤ ∑ n ∈ x.support, p (incl n (x n)) := htriangle x.support
    _ ≤ ∑ n ∈ x.support, ∑' k, term (n, k) := by
      apply Finset.sum_le_sum
      intro n _
      change (p.comp (incl n)) (x n) ≤ ∑' k, term (n, k)
      simpa only [hterm_eq] using hdom n (x n)
    _ ≤ ∑' n, ∑' k, term (n, k) :=
      ((summable_prod_of_nonneg hterm).1 hterms).2.sum_le_tsum _
        (fun n _ => tsum_nonneg (fun k => hterm (n, k)))
    _ = ∑' nk, term nk := hterms.tsum_prod.symm
    _ = ∑' n, (C ∘ e) n * ‖(F ∘ e) n x‖ := (e.tsum_eq term).symm
