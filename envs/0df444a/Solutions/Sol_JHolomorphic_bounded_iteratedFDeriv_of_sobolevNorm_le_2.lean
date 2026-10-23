-- Prove2me | solution 2 for JHolomorphic.bounded_iteratedFDeriv_of_sobolevNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T22:42:10.85104+00:00
-- url     : https://prove2.me/submissions/4f12fa20-5030-4b69-864b-26fe5cf6d56a

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_isAlmostComplexOn_tangent
import Theorems.Thm_JHolomorphic_exists_eLpNorm_fderiv_fderiv_le
import Theorems.Thm_JHolomorphic_exists_norm_le_of_eLpNorm_fderiv_le
import Theorems.Thm_JHolomorphic_isJHolomorphicOn_tangent
import Theorems.Thm_JHolomorphic_tendstoCInftyLocOn_tangent
import Theorems.Thm_JHolomorphic_norm_fderiv_lift_le
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_lift_le
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.FDeriv.Measurable



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

universe w

set_option maxHeartbeats 1000000 in
theorem bounded_iteratedFDeriv_aux (m : ℕ) :
    ∀ (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (p : ℝ) (_ : 2 < p) (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
      (_ : IsAlmostComplexOn J O) (_ : ∀ ν, IsAlmostComplexOn (Jν ν) O)
      (_ : TendstoCInftyLocOn Jν J O) (_ : IsCompact K₀) (_ : K₀ ⊆ O)
      (U : Set ℂ) (_ : IsOpen U) (u : ℕ → ℂ → E) (_ : ∀ ν, ContDiffOn ℝ ∞ (u ν) U)
      (_ : ∀ ν, IsJHolomorphicOn (Jν ν) U (u ν)) (_ : ∀ ν, Set.MapsTo (u ν) U K₀)
      (_ : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
        eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C),
      ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ ν, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (u ν) z‖ ≤ M := by
  induction m with
  | zero =>
    intro E _ _ _ p hp J Jν O K₀ hJ hJν hconv hK₀ hK₀O U hU u hu hhol hmaps hbd K hKU hK
    obtain ⟨R, hR⟩ := hK₀.isBounded.subset_closedBall 0
    refine ⟨R, fun ν z hz => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    simpa using hR (hmaps ν (hKU hz))
  | succ m ih =>
    intro E _ _ _ p hp J Jν O K₀ hJ hJν hconv hK₀ hK₀O U hU u hu hhol hmaps hbd K hKU hK
    obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
    have hA := exists_eLpNorm_fderiv_fderiv_le p hp J Jν O K₀ hJ hJν hconv hK₀ hK₀O U hU u hu
      hhol hmaps hbd
    have hDu : ∀ ν, ContDiffOn ℝ ∞ (fderiv ℝ (u ν)) U := fun ν =>
      (hu ν).fderiv_of_isOpen hU (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from le_of_eq (by norm_cast))
    have hD2 : ∀ ν, ContinuousOn (fderiv ℝ (fderiv ℝ (u ν))) U := fun ν =>
      ((hDu ν).fderiv_of_isOpen hU (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from le_of_eq (by norm_cast))).continuousOn
    obtain ⟨R, hR⟩ := exists_norm_le_of_eLpNorm_fderiv_le p hp U hU (fun ν => fderiv ℝ (u ν))
      (fun ν => (hDu ν).of_le (by exact_mod_cast le_top)) (by
        intro K' hK'U hK'
        obtain ⟨C₁, hC₁⟩ := hbd K' hK'U hK'
        obtain ⟨C₂, hC₂⟩ := hA K' hK'U hK'
        refine ⟨max C₁ C₂, fun ν => ⟨(hC₁ ν).trans ?_, (hC₂ ν).trans ?_⟩⟩ <;>
          exact_mod_cast (by simp : _)) L hLU hL
    set V := interior L with hV
    have hVU : V ⊆ U := interior_subset.trans hLU
    -- the tangent lifts `z ↦ (u z, Du(z) e)` for `‖e‖ ≤ 1`
    have lift : ∀ e : ℂ, ‖e‖ ≤ 1 → ∃ M : ℝ, ∀ ν, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ (u ν) z e) z‖ ≤ M := by
      intro e he
      have hve : ∀ ν, ContDiffOn ℝ ∞ (fun z => fderiv ℝ (u ν) z e) U := fun ν =>
        (hDu ν).clm_apply contDiffOn_const
      have hv : ∀ ν, ContDiffOn ℝ ∞ (fun z => (u ν z, fderiv ℝ (u ν) z e)) U := fun ν =>
        (hu ν).prodMk (hve ν)
      obtain ⟨M, hM⟩ := ih (E × E) p hp _ _ (O ×ˢ Set.univ) (K₀ ×ˢ closedBall 0 R)
        (isAlmostComplexOn_tangent J O hJ)
        (fun ν => isAlmostComplexOn_tangent (Jν ν) O (hJν ν))
        (tendstoCInftyLocOn_tangent J Jν O hJ hJν hconv)
        (hK₀.prod (isCompact_closedBall 0 R)) (Set.prod_mono hK₀O (Set.subset_univ _))
        V isOpen_interior (fun ν z => (u ν z, fderiv ℝ (u ν) z e))
        (fun ν => (hv ν).mono hVU)
        (fun ν => isJHolomorphicOn_tangent (Jν ν) O (hJν ν) V isOpen_interior (u ν)
          (((hu ν).of_le (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤))).mono hVU)
          (fun z hz => hhol ν z (hVU hz)) (fun z hz => hK₀O (hmaps ν (hVU hz))) e)
        (fun ν z hz => ⟨hmaps ν (hVU hz), by
          rw [mem_closedBall_zero_iff]
          calc ‖fderiv ℝ (u ν) z e‖ ≤ ‖fderiv ℝ (u ν) z‖ * ‖e‖ :=
                (fderiv ℝ (u ν) z).le_opNorm e
            _ ≤ ‖fderiv ℝ (u ν) z‖ := mul_le_of_le_one_right (norm_nonneg _) he
            _ ≤ R := hR ν z (interior_subset hz)⟩)
        (fun K' hK'V hK' => by
          obtain ⟨C₁, hC₁⟩ := hbd K' (hK'V.trans hVU) hK'
          obtain ⟨C₂, hC₂⟩ := hA K' (hK'V.trans hVU) hK'
          exact ⟨C₁ + C₂, fun ν => eLpNorm_fderiv_lift_le p (by linarith) U hU (u ν) (hu ν) e he K'
            (hK'V.trans hVU) hK' C₁ C₂ (hC₁ ν) (hC₂ ν)⟩)
        K hKL hK
      refine ⟨M, fun ν z hz => le_trans ?_ (hM ν z hz)⟩
      have hcd : ContDiffAt ℝ m (fun z => (u ν z, fderiv ℝ (u ν) z e)) z :=
        ((hv ν).contDiffAt (hU.mem_nhds (hKU hz))).of_le (by exact_mod_cast le_top)
      have h := (ContinuousLinearMap.snd ℝ E E).iteratedFDeriv_comp_left hcd (le_refl _)
      have hfun : ((ContinuousLinearMap.snd ℝ E E) ∘ fun z => (u ν z, fderiv ℝ (u ν) z e)) =
          fun z => fderiv ℝ (u ν) z e := rfl
      rw [hfun] at h
      rw [h]
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E E)
    obtain ⟨M₁, hM₁⟩ := lift 1 (by simp)
    obtain ⟨M₂, hM₂⟩ := lift Complex.I (by simp)
    set A := ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM
    set B := ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM
    refine ⟨‖A‖ * M₁ + ‖B‖ * M₂, fun ν z hz => ?_⟩
    have hDsplit : fderiv ℝ (u ν) = fun w => A (fderiv ℝ (u ν) w 1) +
        B (fderiv ℝ (u ν) w Complex.I) := by
      funext w
      refine ContinuousLinearMap.ext fun a => ?_
      have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
        apply Complex.ext <;> simp
      conv_lhs => rw [ha, map_add, map_smul, map_smul]
      simp [A, B]
    have hzU : U ∈ 𝓝 z := hU.mem_nhds (hKU hz)
    have hc : ∀ e : ℂ, ContDiffAt ℝ m (fun w => fderiv ℝ (u ν) w e) z := fun e =>
      (((hDu ν).clm_apply contDiffOn_const).contDiffAt hzU).of_le (by exact_mod_cast le_top)
    rw [← norm_iteratedFDeriv_fderiv, hDsplit,
      fun_iteratedFDeriv_add_apply
        (show ContDiffAt ℝ m (fun w => A (fderiv ℝ (u ν) w 1)) z from
          (A.contDiff.contDiffAt).comp z (hc 1))
        (show ContDiffAt ℝ m (fun w => B (fderiv ℝ (u ν) w Complex.I)) z from
          (B.contDiff.contDiffAt).comp z (hc Complex.I))]
    have h1 := A.iteratedFDeriv_comp_left (hc 1) (le_refl _)
    have h2 := B.iteratedFDeriv_comp_left (hc Complex.I) (le_refl _)
    simp only [Function.comp_def] at h1 h2
    rw [h1, h2]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (A.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left (hM₁ ν z hz) (norm_nonneg _))
    · exact (B.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left (hM₂ ν z hz) (norm_nonneg _))

end JHolomorphic

open JHolomorphic MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem bounded_iteratedFDeriv_main {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (C : ℝ≥0)
    (hC : ∀ ν, sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν) ≤ C) :
    ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ,
      ∃ M : ℝ, ∀ ν, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (u ν) z‖ ≤ M := by
  intro K hK hKc m
  refine bounded_iteratedFDeriv_aux m E p hp J Jν O K₀ hJ hJν hconv hK₀ hK₀O (ball 0 1)
    isOpen_ball u hu hhol hmaps (fun K' hK' _ => ⟨C, fun ν => ?_⟩) K hK hKc
  calc eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict K')
      ≤ eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hK' le_rfl)
    _ = eLpNorm (iteratedFDeriv ℝ 1 (u ν)) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun z => (norm_iteratedFDeriv_one _).symm)
    _ ≤ sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν) := by
        unfold sobolevNorm
        exact Finset.single_le_sum (f := fun j => eLpNorm (iteratedFDeriv ℝ j (u ν))
          (ENNReal.ofReal p) (volume.restrict (ball 0 1))) (fun _ _ => zero_le)
          (by simp)
    _ ≤ C := hC ν

open JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (C : ℝ≥0)
    (hC : ∀ ν, sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν) ≤ C) :
    ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ,
      ∃ M : ℝ, ∀ ν, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (u ν) z‖ ≤ M :=
  bounded_iteratedFDeriv_main p hp J Jν O K₀ hJ hJν hconv hK₀ hK₀O u hu hhol hmaps C hC
