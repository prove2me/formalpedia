-- Prove2me | solution 1 for NestedSA.NASA.theorem_2_b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:08:33.808294+00:00
-- url     : https://prove2.me/submissions/3d1573f6-2c73-4c2e-8e2f-4423e3a096b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic
import Definitions.Def_NestedSA_NASA_Model
import Theorems.Thm_NestedSA_NASA_theorem_2_a
import Theorems.Thm_NestedSA_NASA_lemma_4
import Theorems.Thm_NestedSA_NASA_proposition_1_b
import Theorems.Thm_NestedSA_NASA_eq_3_29

open MeasureTheory ProbabilityTheory
open NestedSA.NASA
open scoped RealInnerProductSpace

/-- The projection `P` onto a convex set is nonexpansive. -/
private lemma nasa_proj_lip {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) : Continuous P := by
  have hvi : ∀ w, ∀ y ∈ X, ⟪w - P w, y - P w⟫ ≤ 0 := by
    intro w
    have hmem := (hP w).1
    have hne : Nonempty X := ⟨⟨P w, hmem⟩⟩
    have hbdd : BddBelow (Set.range fun y : X => ‖w - (y : EuclideanSpace ℝ (Fin n))‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact norm_nonneg _
    have heq : ‖w - P w‖ = ⨅ y : X, ‖w - (y : EuclideanSpace ℝ (Fin n))‖ := by
      apply le_antisymm
      · exact le_ciInf (fun y => (hP w).2 y y.2)
      · exact ciInf_le hbdd (⟨P w, hmem⟩ : X)
    exact (norm_eq_iInf_iff_real_inner_le_zero hX_cvx hmem).1 heq
  have hlip : ∀ w w', ‖P w - P w'‖ ≤ ‖w - w'‖ := by
    intro w w'
    have h1 := hvi w (P w') (hP w').1
    have h2 := hvi w' (P w) (hP w).1
    have h3 : ‖P w - P w'‖ ^ 2 ≤ ⟪w - w', P w - P w'⟫ := by
      have e : ⟪w - w', P w - P w'⟫ - ‖P w - P w'‖ ^ 2 =
          -⟪w - P w, P w' - P w⟫ - ⟪w' - P w', P w - P w'⟫ := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      linarith
    have h4 : ⟪w - w', P w - P w'⟫ ≤ ‖w - w'‖ * ‖P w - P w'‖ := real_inner_le_norm _ _
    rcases eq_or_lt_of_le (norm_nonneg (P w - P w')) with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro w w'
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact hlip w w'

private lemma nasa_gradF_cont {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) : Continuous (gradF f g) := by
  have hF : ContDiff ℝ 1 (fun y => f (g y)) := hf.comp hg
  have hc := hF.continuous_fderiv (by norm_num)
  unfold gradF
  have : (fun x => gradient (fun y => f (g y)) x) =
      fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (fun y => f (g y)) x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp hc

theorem solution {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (hF_bdd : BddBelow ((fun x => f (g x)) '' X))
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsStochRun X P a b β τ x0 z0 u0 x z u G s J)
    (σG σJ σs : ℝ) (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) (hcβ : c ≤ a * β) (hcγ : 2 * c ≤ γ * b)
    (h316 : Lg ^ 2 * (a * Ldf + γ) ^ 2 ≤ 2 * (a * β - c) * (γ * b - 2 * c))
    (hτ_one : ∀ k, τ k ≤ 1) (hbτ : ∀ k, b * τ k ≤ 1) (hτ0 : τ 0 = 1 / a)
    (cbar : ℝ) (hcbar : 0 < cbar)
    (h330 : ∀ k N : ℕ, 1 ≤ N →
      ∑ i ∈ Finset.Icc (k + 1) N, τ i * Gamma a τ i ≤ cbar * Gamma a τ (k + 1))
    (haτ : ∀ k, 1 ≤ k → a * τ k ≤ 1 / Real.sqrt 2) :
    ∀ N : ℕ, 2 ≤ N →
      (∀ k, Integrable (fun ω => V P f g (x k ω) (z k ω)) μ) ∧
      (∑ k ∈ Finset.Icc 1 (N - 1), τ k * ∫ ω, V P f g (x k ω) (z k ω) ∂μ) /
          (∑ k ∈ Finset.Icc 1 (N - 1), τ k) ≤
        1 / (∑ k ∈ Finset.Icc 1 (N - 1), τ k) *
          ((1 / c * (a * cbar * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) + max 1 (β ^ 2)) *
                sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0
              + 2 * a ^ 2 * cbar * σJ ^ 2 * σs ^ 2) * (∑ k ∈ Finset.range N, τ k ^ 2)
            + 1 / c * (a * cbar * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) + max 1 (β ^ 2)) *
                W P f g X a γ β x0 z0 u0) := by
  intro N hN
  -- a sample point
  have hΩ : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨ω0⟩ := hΩ
  have hτpos : ∀ k, 0 < τ k := (hrun ω0).τ_pos
  have hβpos : 0 < β := (hrun ω0).β_pos
  -- iterates stay in `X`
  have hxX : ∀ k ω, x k ω ∈ X := by
    intro k ω
    induction k with
    | zero => rw [(hrun ω).init_x]; exact (hrun ω).x0_mem
    | succ k ih =>
      rw [(hrun ω).step_x k]
      exact hX_cvx.add_smul_sub_mem ih (hP _).1 ⟨(hτpos k).le, hτ_one k⟩
  -- measurability
  have hPc := nasa_proj_lip X hX_cvx P hP
  have hGc := nasa_gradF_cont f g hA2.contDiff_f hA2.contDiff_g
  have hxm : ∀ k, AEStronglyMeasurable (x k) μ :=
    fun k => ((hA1.adapted_x k).mono (ℱ.le k)).aestronglyMeasurable
  have hzm : ∀ k, AEStronglyMeasurable (z k) μ :=
    fun k => ((hA1.adapted_z k).mono (ℱ.le k)).aestronglyMeasurable
  have hDm' : ∀ (β' : ℝ) k, AEStronglyMeasurable
      (fun ω => ‖ybar P (x k ω) (z k ω) β' - x k ω‖ ^ 2) μ := by
    intro β' k
    have h1 : AEStronglyMeasurable (fun ω => x k ω - β'⁻¹ • z k ω) μ :=
      (hxm k).sub ((hzm k).const_smul β'⁻¹)
    have h2 : AEStronglyMeasurable (fun ω => P (x k ω - β'⁻¹ • z k ω)) μ :=
      hPc.comp_aestronglyMeasurable h1
    have h3 : AEStronglyMeasurable (fun ω => P (x k ω - β'⁻¹ • z k ω) - x k ω) μ :=
      h2.sub (hxm k)
    have h4 : AEStronglyMeasurable (fun ω => ‖P (x k ω - β'⁻¹ • z k ω) - x k ω‖ ^ 2) μ :=
      h3.norm.pow 2
    exact h4
  have hDm : ∀ k, AEStronglyMeasurable
      (fun ω => ‖ybar P (x k ω) (z k ω) β - x k ω‖ ^ 2) μ := hDm' β
  have hVm : ∀ k, AEStronglyMeasurable (fun ω => V P f g (x k ω) (z k ω)) μ := by
    intro k
    have h1 := hDm' 1 k
    have h2 : AEStronglyMeasurable (fun ω => gradF f g (x k ω)) μ :=
      hGc.comp_aestronglyMeasurable (hxm k)
    have h3 : AEStronglyMeasurable (fun ω => ‖z k ω - gradF f g (x k ω)‖ ^ 2) μ :=
      ((hzm k).sub h2).norm.pow 2
    exact h1.add h3
  -- the milestone results
  obtain ⟨hEint, h2a⟩ := theorem_2_a μ ℱ X hX_cl hX_cvx P hP f g Lf Lg Ldf Ldg hA2 hF_bdd a b β τ
    x0 z0 u0 x z u G s J hrun σG σJ σs hA1 c γ hc hγ hcβ hcγ h316 hτ_one hbτ hτ0 cbar hcbar
    h330 haτ N hN
  have hp1b := fun N' => proposition_1_b μ ℱ X hX_cl hX_cvx P hP f g Lf Lg Ldf Ldg hA2 a b β τ
    x0 z0 u0 x z u G s J hrun σG σJ σs hA1 γ hγ hτ_one hτ0 haτ N'
  have hrint := (hp1b 0).2.1
  have hrsum := (hp1b N).2.2.2
  set r : ℕ → Ω → ℝ := fun k ω => rTerm P f g a b γ β Lf Lg Ldf Ldg τ (fun i => x i ω)
    (fun i => z i ω) (fun i => u i ω) (fun i => G i ω) (fun i => s i ω) (fun i => J i ω) k with hr
  set D : ℕ → Ω → ℝ := fun k ω => ‖ybar P (x k ω) (z k ω) β - x k ω‖ ^ 2 with hD
  set Wc := W P f g X a γ β x0 z0 u0 with hWc
  have hL4 : ∀ N' : ℕ, 1 ≤ N' → ∀ ω,
      c * ∑ k ∈ Finset.range N', τ k * (D k ω + ‖g (x k ω) - u k ω‖ ^ 2) ≤
        Wc + ∑ k ∈ Finset.range N', r k ω := by
    intro N' hN' ω
    have := lemma_4 X hX_cl hX_cvx P hP f g Lf Lg Ldf Ldg hA2 hF_bdd a b β τ x0 z0 u0
      (fun i => x i ω) (fun i => z i ω) (fun i => u i ω) (fun i => G i ω) (fun i => s i ω)
      (fun i => J i ω) (hrun ω) c γ hc hγ hcβ hcγ h316 hτ_one hbτ N' hN'
    exact this
  have hsumnn : ∀ N' ω, 0 ≤ ∑ k ∈ Finset.range N', τ k * (D k ω + ‖g (x k ω) - u k ω‖ ^ 2) :=
    fun N' ω => Finset.sum_nonneg (fun k _ => mul_nonneg (hτpos k).le (by positivity))
  -- integrability of `‖d^k‖²`
  have hDint : ∀ k, Integrable (D k) μ := by
    intro k
    have hb : Integrable (fun ω => (Wc + ∑ j ∈ Finset.range (k + 1), r j ω) / (c * τ k)) μ :=
      ((integrable_const Wc).add (integrable_finsetSum _ (fun j _ => hrint j))).div_const _
    refine hb.mono' (hDm k) (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), le_div_iff₀ (mul_pos hc (hτpos k))]
    have h1 := hL4 (k + 1) (by omega) ω
    have h2 : τ k * (D k ω + ‖g (x k ω) - u k ω‖ ^ 2) ≤
        ∑ j ∈ Finset.range (k + 1), τ j * (D j ω + ‖g (x j ω) - u j ω‖ ^ 2) :=
      Finset.single_le_sum (f := fun j => τ j * (D j ω + ‖g (x j ω) - u j ω‖ ^ 2))
        (fun j _ => mul_nonneg (hτpos j).le (by positivity)) (Finset.self_mem_range_succ k)
    have h3 : τ k * D k ω ≤ τ k * (D k ω + ‖g (x k ω) - u k ω‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by have := sq_nonneg ‖g (x k ω) - u k ω‖; linarith) (hτpos k).le
    nlinarith
  set B := max 1 (β ^ 2) with hB
  have hB0 : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  -- pathwise (3.29)
  have hVle : ∀ k ω, V P f g (x k ω) (z k ω) ≤ B * D k ω + ‖gradF f g (x k ω) - z k ω‖ ^ 2 := by
    intro k ω
    have := eq_3_29 X hX_cl hX_cvx P hP f g (x k ω) (hxX k ω) (z k ω) β hβpos
    rw [norm_sub_rev (z k ω)] at this
    exact this
  have hVnn : ∀ k ω, 0 ≤ V P f g (x k ω) (z k ω) := fun k ω => by unfold V; positivity
  have hVint : ∀ k, Integrable (fun ω => V P f g (x k ω) (z k ω)) μ := by
    intro k
    refine (((hDint k).const_mul B).add (hEint k)).mono' (hVm k)
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hVnn k ω)]
    exact hVle k ω
  refine ⟨hVint, ?_⟩
  -- the main estimate
  set S := ∑ k ∈ Finset.Icc 1 (N - 1), τ k with hS
  have hSpos : 0 < S := by
    rw [hS]
    exact Finset.sum_pos (fun k _ => hτpos k) ⟨1, by rw [Finset.mem_Icc]; omega⟩
  set E : ℕ → ℝ := fun k => ∫ ω, ‖gradF f g (x k ω) - z k ω‖ ^ 2 ∂μ with hE
  have hEnn : ∀ k, 0 ≤ E k := fun k => integral_nonneg (fun ω => by positivity)
  have hDnn : ∀ k, 0 ≤ ∫ ω, D k ω ∂μ := fun k => integral_nonneg (fun ω => by positivity)
  -- (i) V ≤ B d + e in expectation
  have step1 : ∑ k ∈ Finset.Icc 1 (N - 1), τ k * ∫ ω, V P f g (x k ω) (z k ω) ∂μ ≤
      B * ∑ k ∈ Finset.Icc 1 (N - 1), τ k * ∫ ω, D k ω ∂μ +
        ∑ k ∈ Finset.Icc 1 (N - 1), τ k * E k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    have hi : ∫ ω, V P f g (x k ω) (z k ω) ∂μ ≤ B * ∫ ω, D k ω ∂μ + E k := by
      rw [hE, ← integral_const_mul, ← integral_add ((hDint k).const_mul B) (hEint k)]
      exact integral_mono (hVint k) (((hDint k).const_mul B).add (hEint k)) (hVle k)
    nlinarith [hτpos k]
  -- (ii) the `d` part from Lemma 4 and Proposition 1(b)
  have step2 : ∑ k ∈ Finset.Icc 1 (N - 1), τ k * ∫ ω, D k ω ∂μ ≤
      1 / c * (Wc + sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 *
        ∑ k ∈ Finset.range N, τ k ^ 2) := by
    have hsub : ∑ k ∈ Finset.Icc 1 (N - 1), τ k * ∫ ω, D k ω ∂μ ≤
        ∑ k ∈ Finset.range N, τ k * ∫ ω, D k ω ∂μ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro k _ _; exact mul_nonneg (hτpos k).le (hDnn k)
    have hswap : ∑ k ∈ Finset.range N, τ k * ∫ ω, D k ω ∂μ =
        ∫ ω, ∑ k ∈ Finset.range N, τ k * D k ω ∂μ := by
      rw [integral_finsetSum _ (fun k _ => (hDint k).const_mul (τ k))]
      simp_rw [integral_const_mul]
    have hint1 : Integrable (fun ω => ∑ k ∈ Finset.range N, τ k * D k ω) μ :=
      integrable_finsetSum _ (fun k _ => (hDint k).const_mul (τ k))
    have hint2 : Integrable (fun ω => 1 / c * (Wc + ∑ k ∈ Finset.range N, r k ω)) μ :=
      ((integrable_const Wc).add (integrable_finsetSum _ (fun j _ => hrint j))).const_mul _
    have hpt : ∀ ω, ∑ k ∈ Finset.range N, τ k * D k ω ≤
        1 / c * (Wc + ∑ k ∈ Finset.range N, r k ω) := by
      intro ω
      have h1 := hL4 N (by omega) ω
      have h2 : ∑ k ∈ Finset.range N, τ k * D k ω ≤
          ∑ k ∈ Finset.range N, τ k * (D k ω + ‖g (x k ω) - u k ω‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (by have := sq_nonneg ‖g (x k ω) - u k ω‖; linarith)
          (hτpos k).le
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
      nlinarith
    have hmono := integral_mono hint1 hint2 hpt
    have hrhs : ∫ ω, 1 / c * (Wc + ∑ k ∈ Finset.range N, r k ω) ∂μ =
        1 / c * (Wc + ∑ k ∈ Finset.range N, ∫ ω, r k ω ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const Wc)
        (integrable_finsetSum _ (fun j _ => hrint j)), integral_finsetSum _ (fun j _ => hrint j)]
      simp only [integral_const, probReal_univ, one_smul]
      rfl
    have hrs : ∑ k ∈ Finset.range N, ∫ ω, r k ω ∂μ ≤
        sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ k ∈ Finset.range N, τ k ^ 2 := hrsum
    have hc' : 0 ≤ 1 / c := by positivity
    calc _ ≤ _ := hsub
      _ = _ := hswap
      _ ≤ _ := hmono
      _ = _ := hrhs
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hc'
  -- (iii) the tracking-error part from Theorem 2(a)
  have step3 : ∑ k ∈ Finset.Icc 1 (N - 1), τ k * E k ≤ ∑ k ∈ Finset.Icc 1 N, τ k * E k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro k _ _; exact mul_nonneg (hτpos k).le (hEnn k)
  have h2a' : ∑ k ∈ Finset.Icc 1 N, τ k * E k ≤ _ := h2a
  rw [one_div_mul_eq_div]
  apply div_le_div_of_nonneg_right _ hSpos.le
  have := mul_le_mul_of_nonneg_left step2 hB0
  have hfin : B * (1 / c * (Wc + sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 *
        ∑ k ∈ Finset.range N, τ k ^ 2)) +
      (a * cbar * (1 / c * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) *
            sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 + 2 * a * σJ ^ 2 * σs ^ 2) *
          (∑ k ∈ Finset.range N, τ k ^ 2)
        + a * cbar / c * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) * Wc) =
      (1 / c * (a * cbar * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) + B) *
                sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0
              + 2 * a ^ 2 * cbar * σJ ^ 2 * σs ^ 2) * (∑ k ∈ Finset.range N, τ k ^ 2)
            + 1 / c * (a * cbar * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) + B) * Wc := by
    ring
  linarith
