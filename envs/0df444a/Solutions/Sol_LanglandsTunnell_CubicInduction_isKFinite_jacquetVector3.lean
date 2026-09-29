-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isKFinite_jacquetVector3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2b41e08b-59cb-51df-a1ab-2d14cfcb94b8

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetIntegrand3_integrable_and_jacquetVector3_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

noncomputable section

open MeasureTheory

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 orth3 IsKFinite jacquetIntegrand3_integrable_and_jacquetVector3_continuous"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem psiArch_eq_psi_realCoord (w : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch w = ArchR.psi (StandardKernel.realCoord w) := by
  have h1 : NumberField.StandardAddChar.psiArch w =
      NumberField.StandardAddChar.psiArchPlace Rat.infinitePlace (w Rat.infinitePlace) := by
    rw [NumberField.StandardAddChar.psiArch_apply]
    exact finprod_eq_single _ Rat.infinitePlace fun v hv => absurd (Subsingleton.elim v Rat.infinitePlace) hv
  rw [h1, NumberField.StandardAddChar.psiArchPlace_apply, ArchR.psi, StandardKernel.realCoord_apply]

private theorem realCoord_ratCast (a : ℚ) :
    StandardKernel.realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) a) = (a : ℝ) := by
  rw [← RingHom.comp_apply]
  exact eq_ratCast (StandardKernel.realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem psiInf_ofReal_neg (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) (t : ℝ) :
    psiInf (StandardKernel.ofReal (-t)) =
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  rw [hpsiInf, psiArch_eq_psi_realCoord, map_mul, realCoord_ratCast, realCoord_ofReal, ArchR.psi]
  congr 1
  push_cast
  ring

section SchwartzSlices

open scoped BigOperators SchwartzMap FourierTransform

private theorem exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (ι : Type) [Fintype ι] (N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢((ι → ℝ), ℂ)) (ξ : ι → ℝ),
      ‖∫ u : ι → ℝ, φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (s.sup (schwartzSeminormFamily ℝ (ι → ℝ) ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  classical

  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let T : 𝓢((ι → ℝ), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
    (SchwartzMap.fourierTransformCLM ℂ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)

  have hcont : ∀ k : ℕ, Continuous
      ((schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ (k, 0)).comp (T : 𝓢((ι → ℝ), ℂ) →ₗ[ℂ] _)) := by
    intro k
    exact ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ ι) ℂ).continuous_seminorm (k, 0)).comp T.continuous
  obtain ⟨s₀, C₀, -, h₀⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (ι → ℝ) ℂ) _ (hcont 0)
  obtain ⟨s₁, C₁, -, h₁⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (ι → ℝ) ℂ) _ (hcont N)
  refine ⟨s₀ ∪ s₁, 2 ^ N * ((C₀ : ℝ) + C₁), by positivity, ?_⟩
  intro φ ξ
  set S : ℝ := ((s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ (ι → ℝ) ℂ)) φ with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hbridge : ((s₀ ∪ s₁).sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ)) φ = S := by
    rw [hS]
    simp only [Seminorm.finset_sup_apply]
    rfl

  have hb : ∀ (k : ℕ) (sk : Finset (ℕ × ℕ)) (Ck : NNReal),
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ (k, 0)).comp (T : 𝓢((ι → ℝ), ℂ) →ₗ[ℂ] _) ≤
        Ck • sk.sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ) → sk ⊆ s₀ ∪ s₁ →
        SchwartzMap.seminorm ℂ k 0 (T φ) ≤ (Ck : ℝ) * S := by
    intro k sk Ck hk hsub
    have h1 := Seminorm.le_def.1 hk φ
    have h2 : (sk.sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ)) φ ≤ S := by
      rw [← hbridge]
      exact Seminorm.le_def.1 (Finset.sup_mono hsub) φ
    simp only [Seminorm.comp_apply, SchwartzMap.schwartzSeminormFamily_apply, Seminorm.smul_apply, NNReal.smul_def,
      smul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 Ck.coe_nonneg)
  have hq₀ := hb 0 s₀ C₀ h₀ Finset.subset_union_left
  have hqN := hb N s₁ C₁ h₁ Finset.subset_union_right

  set x : EuclideanSpace ℝ ι := WithLp.toLp 2 ξ with hx
  have hξx : ‖ξ‖ ≤ ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
    exact PiLp.norm_apply_le x i
  have hTx : T φ x = (𝓕 (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ)) : EuclideanSpace ℝ ι → ℂ) x := by
    simp only [T, ContinuousLinearMap.comp_apply]
    rfl
  have hmp : MeasureTheory.MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)) := by
    simpa using (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm _
  have hId : (∫ u : ι → ℝ, φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I)) =
      T φ x := by
    rw [hTx, Real.fourier_eq', ← hmp.integral_comp']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hinner : @inner ℝ _ _ (WithLp.toLp 2 u : EuclideanSpace ℝ ι) x = ∑ i, ξ i * u i := by
      simp only [hx, PiLp.inner_apply]
      rfl
    simp only [smul_eq_mul, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, e,
      PiLp.coe_continuousLinearEquiv, MeasurableEquiv.coe_toLp, hinner]
    rw [mul_comm]
    congr 2
    push_cast
    ring

  have hpow : ∀ a : ℝ, 0 ≤ a → (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
    intro a ha
    calc (1 + a) ^ N ≤ (2 * max 1 a) ^ N :=
          pow_le_pow_left₀ (by positivity) (by linarith [le_max_left 1 a, le_max_right 1 a]) N
      _ = 2 ^ N * (max 1 a) ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) := by
          gcongr
          rcases max_cases 1 a with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
          · rw [one_pow]; linarith [pow_nonneg ha N]
          · linarith
  have hdecay : (1 + ‖x‖) ^ N * ‖T φ x‖ ≤
      2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := by
    have hA := SchwartzMap.norm_le_seminorm ℂ (T φ) x
    have hB := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T φ) N x
    calc (1 + ‖x‖) ^ N * ‖T φ x‖ ≤ 2 ^ N * (1 + ‖x‖ ^ N) * ‖T φ x‖ :=
          mul_le_mul_of_nonneg_right (hpow _ (norm_nonneg x)) (norm_nonneg _)
      _ = 2 ^ N * (‖T φ x‖ + ‖x‖ ^ N * ‖T φ x‖) := by ring
      _ ≤ 2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := by gcongr

  have hbase : 0 < 1 + ‖ξ‖ := by positivity
  rw [hId, Real.rpow_neg hbase.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hmono : (1 + ‖ξ‖) ^ N ≤ (1 + ‖x‖) ^ N := pow_le_pow_left₀ hbase.le (by linarith) N
  calc ‖T φ x‖ * (1 + ‖ξ‖) ^ N ≤ ‖T φ x‖ * (1 + ‖x‖) ^ N :=
        mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
    _ = (1 + ‖x‖) ^ N * ‖T φ x‖ := mul_comm _ _
    _ ≤ 2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := hdecay
    _ ≤ 2 ^ N * ((C₀ : ℝ) * S + (C₁ : ℝ) * S) := by gcongr
    _ = 2 ^ N * ((C₀ : ℝ) + C₁) * S := by ring

namespace G0

private theorem iteratedDeriv_real_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]

private theorem norm_iteratedFDeriv_real_exp_le (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp y‖ ≤ Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos y)]

private theorem exists_forall_pow_mul_exp_neg_pi_sq_le (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t ^ m * Real.exp (-(Real.pi * t ^ 2)) ≤ C := by
  refine ⟨1 + m.factorial / Real.pi ^ m, fun t ht => ?_⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  have hexp : (Real.pi * t ^ 2) ^ m / m.factorial ≤ Real.exp (Real.pi * t ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have hpos : 0 < Real.exp (Real.pi * t ^ 2) := Real.exp_pos _
  rw [Real.exp_neg]
  rcases le_or_gt t 1 with h1 | h1
  · calc t ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ 1 * 1 := by
          gcongr
          · exact pow_le_one₀ ht h1
          · exact inv_le_one_of_one_le₀ (Real.one_le_exp (by positivity))
      _ ≤ 1 + m.factorial / Real.pi ^ m := by
          have : (0 : ℝ) ≤ m.factorial / Real.pi ^ m := by positivity
          linarith
  ·
    have htm : t ^ m ≤ (t ^ 2) ^ m := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ h1.le (by omega)
    have key : (t ^ 2) ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ m.factorial / Real.pi ^ m := by
      rw [mul_inv_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have := hexp
      rw [div_le_iff₀ (by positivity), mul_pow] at this
      nlinarith [this, pow_pos hπ m, pow_nonneg (sq_nonneg t) m]
    calc t ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ (t ^ 2) ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ := by
          gcongr
      _ ≤ m.factorial / Real.pi ^ m := key
      _ ≤ 1 + m.factorial / Real.pi ^ m := by linarith

private theorem norm_sq_le_sum_sq {ι : Type} [Fintype ι] (x : ι → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim x 0]
  · obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖x i‖
    have hnorm : ‖x‖ = ‖x i‖ := by
      apply le_antisymm
      · exact pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 hi
      · exact norm_le_pi_norm x i
    rw [hnorm, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

variable {ι : Type} [Fintype ι]

private def quad (x : ι → ℝ) : ℝ := -(Real.pi * ∑ i, x i ^ 2)

private theorem contDiff_quad : ContDiff ℝ (⊤ : ℕ∞) (quad (ι := ι)) := by
  unfold quad
  apply ContDiff.neg
  apply ContDiff.mul contDiff_const
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

private theorem norm_proj_le_one (i : ι) : ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x i

private theorem norm_iteratedFDeriv_proj_le (i : ι) (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖ ≤ max ‖x‖ 1 := by
  rcases j with _ | j
  · rw [norm_iteratedFDeriv_zero]
    exact (norm_le_pi_norm x i).trans (le_max_left _ _)
  · rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) =
        fun _ => (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) := funext fun _ => ContinuousLinearMap.fderiv _
    rw [hfd]
    rcases j with _ | j
    · rw [norm_iteratedFDeriv_zero]
      exact (norm_proj_le_one i).trans (le_max_right _ _)
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
      simp

private theorem contDiff_proj (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
  exact ContinuousLinearMap.contDiff _

private theorem norm_iteratedFDeriv_coord_sq_le (i : ι) (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ι → ℝ => y i ^ 2) x‖ ≤ 2 ^ j * max ‖x‖ 1 ^ 2 := by
  have hfun : (fun y : ι → ℝ => y i ^ 2) = fun y => (ContinuousLinearMap.mul ℝ ℝ)
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) y) ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) y) := by
    funext y; simp [sq]
  rw [hfun]
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear (contDiff_proj i) (contDiff_proj i) x
    (n := j) (by exact_mod_cast le_top)).trans ?_
  have hm : (0 : ℝ) ≤ max ‖x‖ 1 := le_max_of_le_right zero_le_one
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖ *
            ‖iteratedFDeriv ℝ (j - k) (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖
        ≤ 1 * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * max ‖x‖ 1 * max ‖x‖ 1 := by
          gcongr with k _ <;>
            first
              | exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
              | exact norm_iteratedFDeriv_proj_le i _ x
              | exact Finset.sum_nonneg fun k _ => by positivity
              | positivity
      _ = 2 ^ j * max ‖x‖ 1 ^ 2 := by
          rw [one_mul, ← Finset.sum_mul, ← Finset.sum_mul]
          have h2 : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) = 2 ^ j := by
            exact_mod_cast Nat.sum_range_choose j
          rw [h2]; ring

private theorem norm_iteratedFDeriv_quad_le (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (quad (ι := ι)) x‖ ≤ Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) := by
  have hq : quad (ι := ι) = fun y => (-Real.pi) • ∑ i, (fun z : ι → ℝ => z i ^ 2) y := by
    funext y; simp [quad]
  rw [hq]
  have hcd : ∀ i : ι, ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => z i ^ 2) := fun i => (contDiff_apply ℝ ℝ i).pow 2
  have hcdj : ∀ i : ι, ContDiff ℝ (j : ℕ) (fun z : ι → ℝ => z i ^ 2) := fun i => (hcd i).of_le (by exact_mod_cast le_top)
  have hS : ContDiff ℝ (j : ℕ) (fun y : ι → ℝ => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) :=
    ContDiff.sum fun i _ => hcdj i
  have hsplit := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (f := fun i : ι => fun z : ι → ℝ => z i ^ 2) (u := Finset.univ)
    (i := j) (fun i _ => hcdj i)) x
  simp only [Finset.sum_apply] at hsplit
  calc ‖iteratedFDeriv ℝ j (fun y => (-Real.pi) • ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖
      = ‖(-Real.pi) • iteratedFDeriv ℝ j (fun y => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖ := by
        rw [iteratedFDeriv_const_smul_apply' hS.contDiffAt]
    _ = Real.pi * ‖iteratedFDeriv ℝ j (fun y => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖ := by
        rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi * ∑ i : ι, ‖iteratedFDeriv ℝ j (fun z : ι → ℝ => z i ^ 2) x‖ := by
        gcongr
        rw [hsplit]
        exact norm_sum_le _ _
    _ ≤ Real.pi * ∑ _i : ι, 2 ^ j * max ‖x‖ 1 ^ 2 := by
        gcongr with i _
        exact norm_iteratedFDeriv_coord_sq_le i j x
    _ = Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private def gauss (x : ι → ℝ) : ℝ := Real.exp (quad x)

private theorem contDiff_gauss : ContDiff ℝ (⊤ : ℕ∞) (gauss (ι := ι)) :=
  Real.contDiff_exp.comp contDiff_quad

private theorem norm_iteratedFDeriv_quad_le_pow (j : ℕ) (hj : 1 ≤ j) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (quad (ι := ι)) x‖ ≤ (2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2) ^ j := by
  set A : ℝ := Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hD2 : (2 : ℝ) ≤ 2 * A + 2 := by linarith
  refine (norm_iteratedFDeriv_quad_le j x).trans ?_
  have hre : Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) = 2 ^ j * A := by rw [hA]; ring
  have hD : 2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2 = 2 * A + 2 := by rw [hA]; ring
  rw [hre, hD]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  calc (2 : ℝ) ^ (k + 1) * A = 2 ^ k * (2 * A) := by ring
    _ ≤ (2 * A + 2) ^ k * (2 * A + 2) := by
        gcongr
        linarith
    _ = (2 * A + 2) ^ (k + 1) := by ring

private theorem norm_iteratedFDeriv_gauss_le (n : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤
      n.factorial * Real.exp (quad x) * (2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2) ^ n := by
  have h : gauss (ι := ι) = Real.exp ∘ quad := rfl
  rw [h]
  exact norm_iteratedFDeriv_comp_le Real.contDiff_exp contDiff_quad (by exact_mod_cast le_top) x
    (fun i _ => norm_iteratedFDeriv_real_exp_le i (quad x))
    (fun i hi _ => norm_iteratedFDeriv_quad_le_pow i hi x)

private theorem exp_quad_le (x : ι → ℝ) : Real.exp (quad x) ≤ Real.exp (-(Real.pi * ‖x‖ ^ 2)) := by
  apply Real.exp_le_exp.2
  unfold quad
  have := norm_sq_le_sum_sq x
  nlinarith [Real.pi_pos]

private theorem gauss_decay (k n : ℕ) : ∃ C : ℝ, ∀ x : ι → ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤ C := by

  set c₁ : ℝ := 2 * Real.pi * Fintype.card ι + 2 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  obtain ⟨C₀, hC₀⟩ := exists_forall_pow_mul_exp_neg_pi_sq_le (k + 2 * n)
  refine ⟨n.factorial * c₁ ^ n * (2 ^ (k + 2 * n) * (1 + C₀)), fun x => ?_⟩
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  set t : ℝ := ‖x‖ with ht
  have hmax : max t 1 ≤ 1 + t := max_le (by linarith) (by linarith)
  have hD : 2 * Real.pi * Fintype.card ι * max t 1 ^ 2 + 2 ≤ c₁ * (1 + t) ^ 2 := by
    have h1 : max t 1 ^ 2 ≤ (1 + t) ^ 2 := pow_le_pow_left₀ (le_max_of_le_right zero_le_one) hmax 2
    have h2 : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Fintype.card ι)
    rw [hc₁]; nlinarith [h3, h2]
  have hgauss : Real.exp (quad x) ≤ Real.exp (-(Real.pi * t ^ 2)) := exp_quad_le x
  have hexp0 : 0 < Real.exp (-(Real.pi * t ^ 2)) := Real.exp_pos _
  have hpow : t ^ k * (1 + t) ^ (2 * n) ≤ (1 + t) ^ (k + 2 * n) := by
    rw [pow_add]; gcongr; linarith
  have hkey : (1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2)) ≤ 2 ^ (k + 2 * n) * (1 + C₀) := by
    have hC₀' := hC₀ t hx0
    have hexp1 : Real.exp (-(Real.pi * t ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have hbin : (1 + t) ^ (k + 2 * n) ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) := by
      have hm : (1 + t) ≤ 2 * max 1 t := by linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
      calc (1 + t) ^ (k + 2 * n) ≤ (2 * max 1 t) ^ (k + 2 * n) := by gcongr
        _ = 2 ^ (k + 2 * n) * max 1 t ^ (k + 2 * n) := mul_pow _ _ _
        _ ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) := by
            gcongr
            rcases le_total t 1 with h | h
            · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx0 (k + 2 * n)]
            · rw [max_eq_right h]; linarith
    calc (1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))
        ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) * Real.exp (-(Real.pi * t ^ 2)) := by gcongr
      _ = 2 ^ (k + 2 * n) * (Real.exp (-(Real.pi * t ^ 2)) + t ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))) := by
          ring
      _ ≤ 2 ^ (k + 2 * n) * (1 + C₀) := by gcongr
  calc t ^ k * ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖
      ≤ t ^ k * (n.factorial * Real.exp (quad x) * (2 * Real.pi * Fintype.card ι * max t 1 ^ 2 + 2) ^ n) := by
        gcongr; exact norm_iteratedFDeriv_gauss_le n x
    _ ≤ t ^ k * (n.factorial * Real.exp (-(Real.pi * t ^ 2)) * (c₁ * (1 + t) ^ 2) ^ n) := by
        gcongr
    _ = n.factorial * c₁ ^ n * ((t ^ k * (1 + t) ^ (2 * n)) * Real.exp (-(Real.pi * t ^ 2))) := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ n.factorial * c₁ ^ n * ((1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))) := by gcongr
    _ ≤ n.factorial * c₁ ^ n * (2 ^ (k + 2 * n) * (1 + C₀)) := by gcongr

private theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq' :
    ∃ Φ : SchwartzMap (ι → ℝ) ℝ, ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) :=
  ⟨⟨gauss, contDiff_gauss, gauss_decay⟩, fun _ => rfl⟩

private abbrev Arr : Type := Fin 2 → Fin 3 → ℝ

private abbrev Pl : Type := Fin 2 → ℝ

private def blk (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : Arr := fun i => ![h i 0, h i 1, w i]

private def rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : Arr := fun i b => (Matrix.of X * T) i b

private theorem rmul_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) (i : Fin 2) (b : Fin 3) :
    rmul T X i b = ∑ k : Fin 3, X i k * T k b := by
  simp [rmul, Matrix.mul_apply]

private theorem rmul_add (T : Matrix (Fin 3) (Fin 3) ℝ) (X Y : Arr) : rmul T (X + Y) = rmul T X + rmul T Y := by
  funext i b; simp [rmul_apply, add_mul, Finset.sum_add_distrib]

private theorem rmul_smul (T : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (X : Arr) : rmul T (c • X) = c • rmul T X := by
  funext i b; simp [rmul_apply, Finset.mul_sum, mul_assoc]

private theorem rmul_rmul (T S : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : rmul S (rmul T X) = rmul (T * S) X := by
  funext i b
  simp only [rmul_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem rmul_inv_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (X : Arr) : rmul T⁻¹ (rmul T X) = X := by
  rw [rmul_rmul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hT)]
  funext i b; simp [rmul_apply, Matrix.one_apply]

private theorem blk_add (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : blk h w = blk h 0 + blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

private theorem blk_zero_add_smul (w w' : Pl) : blk 0 (w + w') = blk 0 w + blk 0 w' := by
  funext i b; fin_cases b <;> simp [blk]

private theorem blk_zero_smul (c : ℝ) (w : Pl) : blk 0 (c • w) = c • blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

private def mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ‖(fun i j => T i j : Fin 3 → Fin 3 → ℝ)‖

private theorem mnorm_nonneg (T : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ mnorm T := norm_nonneg _

private theorem abs_entry_le_mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) (k b : Fin 3) : |T k b| ≤ mnorm T := by
  have h1 := norm_le_pi_norm (fun i j => T i j : Fin 3 → Fin 3 → ℝ) k
  have h2 := norm_le_pi_norm (fun j => T k j : Fin 3 → ℝ) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

private theorem abs_entry_le_norm (X : Arr) (i : Fin 2) (b : Fin 3) : |X i b| ≤ ‖X‖ := by
  have h1 := norm_le_pi_norm X i
  have h2 := norm_le_pi_norm (X i) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

private theorem norm_rmul_le (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : ‖rmul T X‖ ≤ 3 * ‖X‖ * mnorm T := by
  have hnn : (0 : ℝ) ≤ 3 * ‖X‖ * mnorm T := mul_nonneg (by positivity) (mnorm_nonneg T)
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => (pi_norm_le_iff_of_nonneg hnn).2 fun b => ?_
  rw [Real.norm_eq_abs, rmul_apply]
  calc |∑ k : Fin 3, X i k * T k b| ≤ ∑ k : Fin 3, |X i k * T k b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, ‖X‖ * mnorm T := by
        gcongr with k _
        rw [abs_mul]
        exact mul_le_mul (abs_entry_le_norm X i k) (abs_entry_le_mnorm T k b) (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖X‖ * mnorm T := by simp [Finset.sum_const]; ring

private theorem norm_le_norm_blk_left (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖h‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  fin_cases j
  · have h2 := norm_le_pi_norm (blk h w i) 0
    simp only [blk, Matrix.cons_val_zero] at h2
    exact h2.trans h1
  · have h2 := norm_le_pi_norm (blk h w i) 1
    simp only [blk, Matrix.cons_val_one] at h2
    exact h2.trans h1

private theorem norm_le_norm_blk_right (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖w‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  have h2 := norm_le_pi_norm (blk h w i) 2
  simp only [blk] at h2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  exact h2.trans h1

private def sliceLin (T : Matrix (Fin 3) (Fin 3) ℝ) : Pl →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => rmul T (blk 0 w)
      map_add' := fun w w' => by rw [blk_zero_add_smul, rmul_add]
      map_smul' := fun c w => by rw [blk_zero_smul, rmul_smul]; rfl }

private theorem sliceLin_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (w : Pl) : sliceLin T w = rmul T (blk 0 w) := rfl

private theorem rmul_blk_eq (T : Matrix (Fin 3) (Fin 3) ℝ) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    rmul T (blk h w) = sliceLin T w + rmul T (blk h 0) := by
  rw [blk_add, rmul_add, sliceLin_apply, add_comm]

private theorem norm_blk_zero_le (w : Pl) : ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  fin_cases b <;> simp [blk]
  exact norm_le_pi_norm w i

private theorem norm_sliceLin_le (T : Matrix (Fin 3) (Fin 3) ℝ) : ‖sliceLin T‖ ≤ 3 * mnorm T := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (mnorm_nonneg T)) fun w => ?_
  rw [sliceLin_apply]
  calc ‖rmul T (blk 0 w)‖ ≤ 3 * ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ * mnorm T := norm_rmul_le T _
    _ ≤ 3 * ‖w‖ * mnorm T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_blk_zero_le w) (by norm_num)) (mnorm_nonneg T)
    _ = 3 * mnorm T * ‖w‖ := by ring

private theorem norm_iteratedFDeriv_slice_le {F : Arr → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (T : Matrix (Fin 3) (Fin 3) ℝ)
    (h : Fin 2 → Fin 2 → ℝ) (n : ℕ) (w : Pl) :
    ‖iteratedFDeriv ℝ n (fun w' : Pl => F (rmul T (blk h w'))) w‖ ≤
      ‖sliceLin T‖ ^ n * ‖iteratedFDeriv ℝ n F (rmul T (blk h w))‖ := by
  have hfun : (fun w' : Pl => F (rmul T (blk h w'))) = (fun X => F (X + rmul T (blk h 0))) ∘ (sliceLin T) := by
    funext w'; simp only [Function.comp]; rw [rmul_blk_eq T h w']
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun X : Arr => F (X + rmul T (blk h 0))) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [hfun, (sliceLin T).iteratedFDeriv_comp_right hG w (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]
  gcongr
  rw [iteratedFDeriv_comp_add_right, rmul_blk_eq T h w]

open scoped SchwartzMap

private theorem norm_blk_le_norm_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    ‖blk h w‖ ≤ 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by
  calc ‖blk h w‖ = ‖rmul T⁻¹ (rmul T (blk h w))‖ := by rw [rmul_inv_rmul T hT]
    _ ≤ 3 * ‖rmul T (blk h w)‖ * mnorm T⁻¹ := norm_rmul_le _ _
    _ = 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by ring

private theorem exists_bound_mnorm_of_isCompact (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hKdet : ∀ T ∈ K, T.det ≠ 0) : ∃ R : ℝ, 1 ≤ R ∧ ∀ T ∈ K, mnorm T ≤ R ∧ mnorm T⁻¹ ≤ R := by
  have hc1 : Continuous (fun T : Matrix (Fin 3) (Fin 3) ℝ => (fun i j => T i j : Fin 3 → Fin 3 → ℝ)) :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  have hinv : ContinuousOn (fun T : Matrix (Fin 3) (Fin 3) ℝ => T⁻¹) K := fun T hT =>
    (continuousAt_matrix_inv T (by
      have hdet : T.det ≠ 0 := hKdet T hT
      simpa [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet))).continuousWithinAt
  have hc2 : ContinuousOn (fun T : Matrix (Fin 3) (Fin 3) ℝ => (fun i j => T⁻¹ i j : Fin 3 → Fin 3 → ℝ)) K :=
    hc1.comp_continuousOn hinv
  obtain ⟨R₁, hR₁⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨R₂, hR₂⟩ := hK.exists_bound_of_continuousOn hc2
  refine ⟨max 1 (max R₁ R₂), le_max_left _ _, fun T hT => ⟨?_, ?_⟩⟩
  · exact (hR₁ T hT).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hR₂ T hT).trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ K, ∀ (h : Fin 2 → Fin 2 → ℝ) (w : Pl),
      ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (fun w' : Pl => Ψ (rmul T (blk h w'))) w‖ ≤ C * ((1 + ‖h‖) ^ N)⁻¹ := by
  obtain ⟨R, hR1, hR⟩ := exists_bound_mnorm_of_isCompact K hK hKdet
  set m : ℕ := k + N with hm

  set B : ℝ := 2 ^ m * (Finset.Iic (m, n)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) Ψ with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  have hΨ : ∀ P : Arr, (1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ ≤ B := fun P =>
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (m, n)) le_rfl le_rfl Ψ P
  have h3R : (1 : ℝ) ≤ 3 * R := by linarith
  refine ⟨(3 * R) ^ n * (3 * R) ^ m * B, by positivity, fun T hT h w => ?_⟩
  obtain ⟨hTn, hTi⟩ := hR T hT
  set P : Arr := rmul T (blk h w) with hP
  have hpos : (0 : ℝ) < (1 + ‖h‖) ^ N := by positivity
  rw [le_mul_inv_iff₀ hpos]

  have hblk : 1 + ‖blk h w‖ ≤ 3 * R * (1 + ‖P‖) := by
    have h1 := norm_blk_le_norm_rmul T (hKdet T hT) h w
    have h2 : 3 * mnorm T⁻¹ * ‖P‖ ≤ 3 * R * ‖P‖ := by
      gcongr
    nlinarith [norm_nonneg P]
  have hsl : ‖sliceLin T‖ ≤ 3 * R := (norm_sliceLin_le T).trans (by gcongr)
  have hD := norm_iteratedFDeriv_slice_le (F := ⇑Ψ) (Ψ.smooth (⊤ : ℕ∞)) T h n w
  have hw : ‖w‖ ≤ ‖blk h w‖ := norm_le_norm_blk_right h w
  have hh : ‖h‖ ≤ ‖blk h w‖ := norm_le_norm_blk_left h w
  have hD0 : 0 ≤ ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ := norm_nonneg _
  calc ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (fun w' : Pl => Ψ (rmul T (blk h w'))) w‖ * (1 + ‖h‖) ^ N
      ≤ (1 + ‖blk h w‖) ^ k * (‖sliceLin T‖ ^ n * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) * (1 + ‖blk h w‖) ^ N := by
        gcongr
        linarith
    _ ≤ (1 + ‖blk h w‖) ^ k * ((3 * R) ^ n * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) * (1 + ‖blk h w‖) ^ N := by
        gcongr
    _ = (3 * R) ^ n * ((1 + ‖blk h w‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        rw [hm, pow_add]; ring
    _ ≤ (3 * R) ^ n * ((3 * R * (1 + ‖P‖)) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        gcongr
    _ = (3 * R) ^ n * (3 * R) ^ m * ((1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        rw [mul_pow (3 * R) (1 + ‖P‖) m]; ring
    _ ≤ (3 * R) ^ n * (3 * R) ^ m * B := by
        gcongr
        exact hΨ P

private def sliceSchwartz (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) :
    𝓢(Pl, ℂ) where
  toFun := fun w => Ψ (rmul T (blk h w))
  smooth' := by
    have hfun : (fun w : Pl => rmul T (blk h w)) = fun w => sliceLin T w + rmul T (blk h 0) :=
      funext fun w => rmul_blk_eq T h w
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun w : Pl => rmul T (blk h w)) := by
      rw [hfun]; exact (sliceLin T).contDiff.add contDiff_const
    exact (Ψ.smooth (⊤ : ℕ∞)).comp hc
  decay' := by
    intro k n
    obtain ⟨C, -, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Ψ {T} isCompact_singleton
      (by simpa using hT) k n 0
    refine ⟨C, fun w => ?_⟩
    simpa using hC T (Set.mem_singleton T) h w

private theorem sliceSchwartz_apply (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ)
    (w : Pl) : sliceSchwartz Ψ T hT h w = Ψ (rmul T (blk h w)) := rfl

private theorem exists_forall_seminorm_sliceSchwartz_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hKdet : ∀ T ∈ K, T.det ≠ 0) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T ∈ K) (h : Fin 2 → Fin 2 → ℝ),
      SchwartzMap.seminorm ℝ k n (sliceSchwartz Ψ T (hKdet T hT) h) ≤ C * ((1 + ‖h‖) ^ N)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Ψ K hK hKdet k n N
  refine ⟨C, hC0, fun T hT h => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun w => ?_
  exact hC T hT h w

private theorem character_eq (c : ℝ) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) (v : Pl) :
    c * v 1 = ∑ i, (c • ((Matrix.of h)⁻¹ 1)) i * ((Matrix.of h).mulVec v) i := by
  have hv : (Matrix.of h)⁻¹.mulVec ((Matrix.of h).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have h1 : v 1 = ∑ i, (Matrix.of h)⁻¹ 1 i * ((Matrix.of h).mulVec v) i := by
    conv_lhs => rw [← hv]
    simp [Matrix.mulVec, dotProduct]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem integral_comp_mulVec_eq {G : Pl → ℂ} (hG : Continuous G) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) :
    ∫ v : Pl, G ((Matrix.of h).mulVec v) = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) * ∫ u : Pl, G u := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 2) hdet
  have hmeas : Measurable (Matrix.toLin' (Matrix.of h)) := (Matrix.toLin' (Matrix.of h)).continuous_of_finiteDimensional.measurable
  have hfun : (fun v : Pl => G ((Matrix.of h).mulVec v)) = fun v => G (Matrix.toLin' (Matrix.of h) v) := by
    funext v; simp [Matrix.toLin'_apply]
  rw [hfun, ← MeasureTheory.integral_map hmeas.aemeasurable (hG.aestronglyMeasurable), hmap,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (by positivity), abs_inv]
  exact Complex.real_smul

private theorem inv_pow_mul_inv_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    ((1 + a) ^ N)⁻¹ * ((1 + b) ^ N)⁻¹ ≤ ((1 + a + b) ^ N)⁻¹ := by
  rw [← mul_inv, ← mul_pow]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg ha hb]

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (c : ℝ) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨s, C₂, hC₂0, hB2⟩ :=
    LanglandsTunnell.CubicInduction.exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (Fin 2) N

  choose C₁ hC₁0 hC₁ using fun p : ℕ × ℕ => exists_forall_seminorm_sliceSchwartz_le Ψ K hK hKdet p.1 p.2 N
  set C₁s : ℝ := ∑ p ∈ s, C₁ p with hC₁s
  have hC₁s0 : 0 ≤ C₁s := Finset.sum_nonneg fun p _ => hC₁0 p
  refine ⟨C₂ * C₁s, fun T hT h hdet => ?_⟩
  set φ : 𝓢(Pl, ℂ) := sliceSchwartz Ψ T (hKdet T hT) h with hφ
  set ξ : Pl := c • ((Matrix.of h)⁻¹ 1) with hξ

  set G : Pl → ℂ := fun u => φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := by
    rw [hG]
    refine φ.continuous.mul (Complex.continuous_exp.comp ?_)
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).neg
  have hint : (fun v : Pl =>
      Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
        Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) = fun v => G ((Matrix.of h).mulVec v) := by
    funext v
    rw [hG]
    simp only []
    rw [hφ, sliceSchwartz_apply]
    congr 2
    rw [mul_assoc (2 * Real.pi) c (v 1), character_eq c h hdet v]
  rw [hint, integral_comp_mulVec_eq hGc h hdet, norm_mul, Complex.norm_of_nonneg (by positivity)]

  have hsup : (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ ≤ C₁s * ((1 + ‖h‖) ^ N)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
    obtain ⟨a, b⟩ := p
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hC₁ (a, b) T hT h).trans (by gcongr; exact Finset.single_le_sum (fun q _ => hC₁0 q) hp)
  have hξn : ‖ξ‖ = |c| * ‖(Matrix.of h)⁻¹ 1‖ := by rw [hξ, norm_smul, Real.norm_eq_abs]
  have hrpow : ∀ x : ℝ, 0 ≤ x → x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx, Real.rpow_natCast]
  have hdetpos : 0 < |(Matrix.of h).det|⁻¹ := by positivity
  calc |(Matrix.of h).det|⁻¹ * ‖∫ u : Pl, G u‖
      ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
        gcongr
        exact hB2 φ ξ
    _ ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (C₁s * ((1 + ‖h‖) ^ N)⁻¹) * ((1 + ‖ξ‖) ^ N)⁻¹) := by
        rw [hrpow _ (by positivity)]
        gcongr
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖ξ‖) ^ N)⁻¹) := by ring
    _ ≤ C₂ * C₁s * |(Matrix.of h).det|⁻¹ * ((1 + ‖h‖ + ‖ξ‖) ^ N)⁻¹ := by
        gcongr
        exact inv_pow_mul_inv_pow_le _ _ (norm_nonneg _) (norm_nonneg _) N
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
        rw [hrpow _ (by positivity), hξn]

end G0

private theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq (ι : Type) [Fintype ι] :
    ∃ Φ : 𝓢((ι → ℝ), ℝ), ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) := by
  exact G0.exists_schwartzMap_eq_exp_neg_pi_sum_sq' (ι := ι)

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (c : ℝ) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (_hK : IsCompact K) (_hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  exact G0.norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' Ψ N c K _hK _hKdet

namespace G0

private def entryL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj v.2 : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj v.1 : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))

private theorem entryL_apply (v : Fin 2 × Fin 3) (M : Fin 2 → Fin 3 → ℝ) : entryL v M = M v.1 v.2 := rfl

private def uncurryL : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 2 × Fin 3 → ℝ) :=
  ContinuousLinearMap.pi entryL

private theorem uncurryL_apply (M : Fin 2 → Fin 3 → ℝ) (v : Fin 2 × Fin 3) : uncurryL M v = M v.1 v.2 := rfl

private def coordL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (entryL v)

private theorem norm_le_norm_uncurryL (M : Fin 2 → Fin 3 → ℝ) : ‖M‖ ≤ ‖uncurryL M‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  have := norm_le_pi_norm (uncurryL M) (i, b)
  simpa [uncurryL_apply] using this

private theorem hasTemperateGrowth_eval (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq => simpa [MvPolynomial.eval_add, Pi.add_def] using hp.add hq
  | mul_X p v hp =>
    have hX : Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ => ((M v.1 v.2 : ℝ) : ℂ) := by
      have h := (coordL v).hasTemperateGrowth
      convert h using 1 <;> first | with_reducible_and_instances rfl | rfl | exact funext fun _ => rfl
    simpa [MvPolynomial.eval_mul, Pi.mul_def] using hp.mul hX

private theorem exists_schwartzMap_eq_gaussian3 :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℝ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ,
      Φ (fun i b => M i b) = Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2)) := by
  obtain ⟨Φ₀, hΦ₀⟩ := LanglandsTunnell.CubicInduction.exists_schwartzMap_eq_exp_neg_pi_sum_sq (Fin 2 × Fin 3)
  refine ⟨SchwartzMap.compCLM ℝ uncurryL.hasTemperateGrowth ⟨1, 1, fun M => ?_⟩ Φ₀, fun M => ?_⟩
  · have := norm_le_norm_uncurryL M
    nlinarith [norm_nonneg (uncurryL M)]
  · rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦ₀]
    simp only [uncurryL_apply, Fintype.sum_prod_type]

private theorem exists_schwartzMap_eq_of_mem_polyGauss3' {S : Matrix (Fin 2) (Fin 3) ℝ → ℂ} (hS : S ∈ polyGauss3) :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Φ (fun i b => M i b) = S M := by
  obtain ⟨p, rfl⟩ := hS
  obtain ⟨Φg, hΦg⟩ := exists_schwartzMap_eq_gaussian3
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p) (Φg.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM), fun M => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_eval p), SchwartzMap.postcompCLM_apply, hΦg M, smul_eq_mul]
  rfl

end G0

end SchwartzSlices

private theorem godementInner3_eq_integral (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (Φ : SchwartzMap (Fin 2 → Fin 3 → ℝ) ℂ)
    (hΦ : ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Φ (fun i b => M i b) = S M)
    (h : Fin 2 → Fin 2 → ℝ) (T : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 psiInf S (Matrix.of h) T =
      ∫ v : Fin 2 → ℝ, Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) *
        Complex.exp (((-(2 * Real.pi * (a : ℝ) * v 1) : ℝ) : ℂ) * Complex.I) := by
  unfold godementInner3
  congr 1
  funext v
  rw [psiInf_ofReal_neg a psiInf hpsiInf (v 1)]
  show _ = Φ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) * _
  rw [hΦ]
  congr 2
  ext i b
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring

namespace SingularArrays

private theorem volume_setOf_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} :=
    measurableSet_eq_fun (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  refine Filter.Eventually.of_forall fun u => ?_
  have hsub : Prod.mk u ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} ⊆ {r₁ * u / r₀} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith [hv]
  exact measure_mono_null hsub (Real.volume_singleton)

private theorem volume_setOf_vector_on_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (Fin 2 → ℝ)) {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} = 0 := by
  have hpre : {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} =
      MeasurableEquiv.piFinTwo (fun _ => ℝ) ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} := by
    ext q; rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).map_eq]
  exact volume_setOf_line_eq_zero r₀ r₁ h

private theorem volume_setOf_det_eq_zero :
    (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0 := by
  have hdet : ∀ x : Fin 2 → Fin 2 → ℝ, (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := fun x => by
    rw [Matrix.det_fin_two]; rfl
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hpre : {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} =
      MeasurableEquiv.piFinTwo (fun _ => Fin 2 → ℝ) ⁻¹' S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hdet, hS]
    rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).map_eq]
  have hmeas : MeasurableSet S := by
    refine measurableSet_eq_fun ?_ measurable_const
    exact ((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_pi_apply 1).comp measurable_snd) |>.sub
      (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_pi_apply 0).comp measurable_snd))
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  have hae : ∀ᵐ r : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), r 0 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 (0 : ℝ)
  filter_upwards [hae] with r hr
  have hfib : Prod.mk r ⁻¹' S ⊆ {q : Fin 2 → ℝ | r 0 * q 1 = r 1 * q 0} := by
    intro q hq
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hq
    simp only [Set.mem_setOf_eq]
    linarith [hq]
  exact measure_mono_null hfib (volume_setOf_vector_on_line_eq_zero (r 0) (r 1) hr)

end SingularArrays

section

open MvPolynomial

namespace OrthogonalTranslates

private theorem sum_sq_mul_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m n ℝ) (κ : Matrix n n ℝ)
    (hκ : κ * κ.transpose = 1) :
    ∑ i, ∑ b, (M * κ) i b ^ 2 = ∑ i, ∑ b, M i b ^ 2 := by
  have h1 : ∀ (N : Matrix m n ℝ) (i : m), ∑ b, N i b ^ 2 = (N * N.transpose) i i := by
    intro N i
    simp [Matrix.mul_apply, pow_two]
  simp_rw [h1]
  have h2 : M * κ * (M * κ).transpose = M * M.transpose := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κ, hκ, Matrix.one_mul]
  rw [h2]

private theorem sum_sq_mul_eq_of_transpose_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m n ℝ)
    (κ : Matrix n n ℝ)
    (hκ : κ.transpose * κ = 1) :
    ∑ i, ∑ b, (M * κ) i b ^ 2 = ∑ i, ∑ b, M i b ^ 2 :=
  sum_sq_mul_eq M κ (mul_eq_one_comm.1 hκ)

private noncomputable def shift {m n : Type*} [Fintype n] (κ : Matrix n n ℝ) (v : m × n) : MvPolynomial (m × n) ℂ :=
  ∑ c, C ((κ c v.2 : ℝ) : ℂ) * X (v.1, c)

private theorem totalDegree_sum_le {m n : Type*} {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (m × n) ℂ) (d : ℕ)
    (h : ∀ i ∈ s, (f i).totalDegree ≤ d) : (∑ i ∈ s, f i).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (totalDegree_add _ _).trans (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => ?_))
    exact h i (Finset.mem_insert_of_mem hi)

private theorem totalDegree_prod_le {m n : Type*} {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (m × n) ℂ) (e : ι → ℕ)
    (h : ∀ i ∈ s, (f i).totalDegree ≤ e i) : (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine (totalDegree_mul _ _).trans (Nat.add_le_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => ?_))
    exact h i (Finset.mem_insert_of_mem hi)

private theorem totalDegree_shift_le {m n : Type*} [Fintype n] (κ : Matrix n n ℝ) (v : m × n) :
    (shift κ v : MvPolynomial (m × n) ℂ).totalDegree ≤ 1 := by
  refine totalDegree_sum_le _ _ _ fun c _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X _).le

private theorem totalDegree_bind₁_shift_le {m n : Type*} [Fintype n] (κ : Matrix n n ℝ) (p : MvPolynomial (m × n) ℂ) :
    (bind₁ (shift κ) p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_sum_le _ _ _ fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_prod_le _ _ (fun i => s i) fun i _ => ?_).trans (le_totalDegree hs)
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (totalDegree_shift_le κ i)

private theorem eval_bind₁_shift {m n : Type*} [Fintype n] (κ : Matrix n n ℝ) (p : MvPolynomial (m × n) ℂ) (M : Matrix m n ℝ) :
    eval (fun v : m × n => ((M v.1 v.2 : ℝ) : ℂ)) (bind₁ (shift κ) p) =
      eval (fun v : m × n => (((M * κ) v.1 v.2 : ℝ) : ℂ)) p := by
  simp only [MvPolynomial.eval, eval₂Hom_bind₁]
  congr 1
  congr 1
  funext v
  simp [shift, Matrix.mul_apply, mul_comm]

private theorem exists_finset_span {m n : Type*} [Fintype m] [Fintype n] (d : ℕ) :
    ∃ T : Finset (MvPolynomial (m × n) ℂ), (∀ q ∈ T, q.totalDegree ≤ d) ∧
      ∀ q : MvPolynomial (m × n) ℂ, q.totalDegree ≤ d → q ∈ Submodule.span ℂ (T : Set (MvPolynomial (m × n) ℂ)) := by
  obtain ⟨T, hT⟩ := (Module.Finite.iff_fg (N := restrictTotalDegree (m × n) ℂ d)).1 inferInstance
  refine ⟨T, fun q hq => ?_, fun q hq => ?_⟩
  · have : q ∈ restrictTotalDegree (m × n) ℂ d := hT ▸ Submodule.subset_span hq
    exact (mem_restrictTotalDegree _ _ _).1 this
  · rw [hT]
    exact (mem_restrictTotalDegree _ _ _).2 hq

end OrthogonalTranslates

end

open LanglandsTunnell.Converse.ArchR

private theorem zmod_two_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide

private theorem zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private theorem quasiChar_mul_arg (u : ℂ) (b : ZMod 2) (c d : ℝ) :
    quasiChar u b (c * d) = quasiChar u b c * quasiChar u b d := by
  have hc' : (0 : ℝ) ≤ |c| := abs_nonneg c
  unfold quasiChar
  rw [abs_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc' (abs_nonneg d), sign_mul]
  push_cast
  rcases zmod_two_cases b with rfl | rfl
  · simp
  · rw [if_neg zmod_two_one_ne_zero, if_neg zmod_two_one_ne_zero, if_neg zmod_two_one_ne_zero]
    ring

private theorem det_realMat_ne_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (StandardKernel.realMat g).det ≠ 0 := by
  have hu : IsUnit (StandardKernel.realMat g) := (StandardKernel.realGL g).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

private theorem realMat_transpose_mul_self_of_mem_orth3 {k : GL (Fin 3) (InfiniteAdeleRing ℚ)} (hk : k ∈ orth3) :
    (StandardKernel.realMat k).transpose * StandardKernel.realMat k = 1 := by
  have h : (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * k = 1 := hk
  have h' := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => M.map StandardKernel.realCoord) h
  rw [Matrix.map_mul, Matrix.transpose_map,
    Matrix.map_one StandardKernel.realCoord (map_zero _) (map_one _)] at h'
  rw [StandardKernel.realMat_eq]
  exact h'

private def sectionTranslate (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (κ : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 2) (Fin 3) ℝ → ℂ :=
  fun M => S (M * κ)

private theorem inner_argument_mul (m κ : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    Matrix.of ![fun b => (m * κ) 0 b + v 0 * (m * κ) 2 b, fun b => (m * κ) 1 b + v 1 * (m * κ) 2 b] =
      Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b] * κ := by
  ext i b
  fin_cases i <;> simp [Matrix.mul_apply, Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]

private theorem godementInner3_mul_right (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m κ : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 ψ S h (m * κ) = godementInner3 ψ (sectionTranslate S κ) h m := by
  unfold godementInner3
  congr 1
  funext v
  rw [inner_argument_mul, ← Matrix.mul_assoc]
  rfl

private theorem jacquetIntegrand3_mul_orth {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g k : GL (Fin 3) (InfiniteAdeleRing ℚ)) (e : Fin 2 → Fin 2 → ℝ) :
    jacquetIntegrand3 D u₃ a₃ a ψ S (g * k) e =
      jacquetIntegrand3 D u₃ a₃ a ψ (sectionTranslate S (StandardKernel.realMat k)) g e := by
  unfold jacquetIntegrand3
  rw [StandardKernel.realMat_mul, godementInner3_mul_right]

private theorem jacquetVector3_mul_orth {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D u₃ a₃ a ψ S (g * k) =
      quasiChar (u₃ + 1) a₃ (StandardKernel.realMat k).det *
        jacquetVector3 D u₃ a₃ a ψ (sectionTranslate S (StandardKernel.realMat k)) g := by
  unfold jacquetVector3
  rw [StandardKernel.realMat_mul, Matrix.det_mul, quasiChar_mul_arg]
  simp_rw [jacquetIntegrand3_mul_orth]
  ring

private def polySection (q : MvPolynomial (Fin 2 × Fin 3) ℂ) : Matrix (Fin 2) (Fin 3) ℝ → ℂ :=
  fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) q * gaussian3 M

private theorem polySection_mem_polyGauss3 (q : MvPolynomial (Fin 2 × Fin 3) ℂ) : polySection q ∈ polyGauss3 :=
  ⟨q, rfl⟩

private theorem gaussian3_mul_of_transpose_mul (M : Matrix (Fin 2) (Fin 3) ℝ) (κ : Matrix (Fin 3) (Fin 3) ℝ)
    (hκ : κ.transpose * κ = 1) : gaussian3 (M * κ) = gaussian3 M := by
  unfold gaussian3
  rw [OrthogonalTranslates.sum_sq_mul_eq_of_transpose_mul M κ hκ]

private theorem sectionTranslate_polySection (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (κ : Matrix (Fin 3) (Fin 3) ℝ)
    (hκ : κ.transpose * κ = 1) :
    sectionTranslate (polySection p) κ =
      polySection (MvPolynomial.bind₁ (OrthogonalTranslates.shift κ) p) := by
  funext M
  simp only [sectionTranslate, polySection]
  rw [gaussian3_mul_of_transpose_mul M κ hκ, OrthogonalTranslates.eval_bind₁_shift]

private theorem polySection_sum (t : Finset (MvPolynomial (Fin 2 × Fin 3) ℂ)) (c : MvPolynomial (Fin 2 × Fin 3) ℂ → ℂ)
    (M : Matrix (Fin 2) (Fin 3) ℝ) :
    polySection (∑ r ∈ t, c r • r) M = ∑ r ∈ t, c r * polySection r M := by
  simp only [polySection, map_sum, MvPolynomial.smul_eval, Finset.sum_mul, mul_assoc]

private theorem integrable_inner_integrand (a : ℚ) (Φ : SchwartzMap (Fin 2 → Fin 3 → ℝ) ℂ) (h : Fin 2 → Fin 2 → ℝ)
    (hh : (Matrix.of h).det ≠ 0) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) :
    Integrable (fun v : Fin 2 → ℝ => Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) *
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * v 1) : ℝ) : ℂ) * Complex.I)) volume := by
  have hslice :
      Integrable (fun v : Fin 2 → ℝ => G0.sliceSchwartz Φ T hT h ((Matrix.of h).mulVec v)) volume := by
    have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 2) hh
    have hint : Integrable (G0.sliceSchwartz Φ T hT h) (Measure.map (Matrix.toLin' (Matrix.of h)) volume) := by
      rw [hmap]
      exact (G0.sliceSchwartz Φ T hT h).integrable.smul_measure ENNReal.ofReal_ne_top
    have hmeas : AEMeasurable (Matrix.toLin' (Matrix.of h)) volume :=
      (Matrix.toLin' (Matrix.of h)).continuous_of_finiteDimensional.measurable.aemeasurable
    have := (integrable_map_measure (G0.sliceSchwartz Φ T hT h).continuous.aestronglyMeasurable hmeas).1 hint
    simpa only [Function.comp_def, Matrix.toLin'_apply] using this
  simp only [G0.sliceSchwartz_apply] at hslice
  refine hslice.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact (by fun_prop : Continuous fun v : Fin 2 → ℝ =>
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * v 1) : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
  · exact (Complex.norm_exp_ofReal_mul_I _).le

private theorem godementInner3_polySection_sum (a : ℚ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hψ : ∀ x : InfiniteAdeleRing ℚ,
      ψ x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (t : Finset (MvPolynomial (Fin 2 × Fin 3) ℂ)) (c : MvPolynomial (Fin 2 × Fin 3) ℂ → ℂ)
    (h : Fin 2 → Fin 2 → ℝ) (hh : (Matrix.of h).det ≠ 0) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) :
    godementInner3 ψ (polySection (∑ r ∈ t, c r • r)) (Matrix.of h) T =
      ∑ r ∈ t, c r * godementInner3 ψ (polySection r) (Matrix.of h) T := by
  have hrep : ∀ r : MvPolynomial (Fin 2 × Fin 3) ℂ, ∃ Φ : SchwartzMap (Fin 2 → Fin 3 → ℝ) ℂ,
      ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Φ (fun i b => M i b) = polySection r M :=
    fun r => G0.exists_schwartzMap_eq_of_mem_polyGauss3' (polySection_mem_polyGauss3 r)
  choose Φ hΦ using hrep
  obtain ⟨Φs, hΦs⟩ :=
    G0.exists_schwartzMap_eq_of_mem_polyGauss3' (polySection_mem_polyGauss3 (∑ r ∈ t, c r • r))
  have hpt : ∀ X : Fin 2 → Fin 3 → ℝ, Φs X = ∑ r ∈ t, c r * Φ r X := by
    intro X
    have h1 : Φs X = polySection (∑ r ∈ t, c r • r) (Matrix.of X) := hΦs (Matrix.of X)
    have h2 : ∀ r, Φ r X = polySection r (Matrix.of X) := fun r => hΦ r (Matrix.of X)
    rw [h1, polySection_sum]
    simp only [h2]
  rw [godementInner3_eq_integral a ψ hψ _ Φs hΦs h T]
  simp_rw [hpt, Finset.sum_mul]
  have hI : ∀ r ∈ t, Integrable (fun v : Fin 2 → ℝ => c r * Φ r (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) *
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * v 1) : ℝ) : ℂ) * Complex.I)) volume := fun r _ => by
    simpa only [mul_assoc] using (integrable_inner_integrand a (Φ r) h hh T hT).const_mul (c r)
  rw [integral_finsetSum t hI]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [godementInner3_eq_integral a ψ hψ _ (Φ r) (hΦ r) h T, ← integral_const_mul]
  congr 1
  funext v
  ring

private theorem jacquetIntegrand3_polySection_sum {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hψ : ∀ x : InfiniteAdeleRing ℚ,
      ψ x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (t : Finset (MvPolynomial (Fin 2 × Fin 3) ℂ)) (c : MvPolynomial (Fin 2 × Fin 3) ℂ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    jacquetIntegrand3 D u₃ a₃ (a : ℝ) ψ (polySection (∑ r ∈ t, c r • r)) g e =
      ∑ r ∈ t, c r * jacquetIntegrand3 D u₃ a₃ (a : ℝ) ψ (polySection r) g e := by
  unfold jacquetIntegrand3
  rw [godementInner3_polySection_sum a ψ hψ t c e he _ (det_realMat_ne_zero g)]
  simp only [Finset.sum_mul, mul_assoc]

private theorem jacquetVector3_polySection_sum {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hψ : ∀ x : InfiniteAdeleRing ℚ,
      ψ x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hint : ∀ S ∈ polyGauss3, ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      Integrable (jacquetIntegrand3 D u₃ a₃ (a : ℝ) ψ S g) volume)
    (t : Finset (MvPolynomial (Fin 2 × Fin 3) ℂ)) (c : MvPolynomial (Fin 2 × Fin 3) ℂ → ℂ) :
    jacquetVector3 D u₃ a₃ (a : ℝ) ψ (polySection (∑ r ∈ t, c r • r)) =
      ∑ r ∈ t, c r • jacquetVector3 D u₃ a₃ (a : ℝ) ψ (polySection r) := by
  funext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold jacquetVector3
  have hae : (fun e => jacquetIntegrand3 D u₃ a₃ (a : ℝ) ψ (polySection (∑ r ∈ t, c r • r)) g e) =ᵐ[volume]
      fun e => ∑ r ∈ t, c r * jacquetIntegrand3 D u₃ a₃ (a : ℝ) ψ (polySection r) g e := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun e he => ?_) SingularArrays.volume_setOf_det_eq_zero
    by_contra hdet
    exact he (jacquetIntegrand3_polySection_sum D u₃ a₃ a ψ hψ t c g e hdet)
  rw [integral_congr_ae hae,
    integral_finsetSum t fun r _ => (hint _ (polySection_mem_polyGauss3 r) g).const_mul (c r), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul]
  ring

end LanglandsTunnell.CubicInduction

end

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    IsKFinite (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) := by
  obtain ⟨p, rfl⟩ := hS
  show IsKFinite (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf (polySection p))
  obtain ⟨T, -, hTspan⟩ := OrthogonalTranslates.exists_finset_span (m := Fin 2) (n := Fin 3) p.totalDegree
  have hint : ∀ S ∈ polyGauss3, ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      MeasureTheory.Integrable (jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S g) :=
    fun S hS g => (jacquetIntegrand3_integrable_and_jacquetVector3_continuous K hdeg μ hμ uR aR uC kC huR huC ω hω
      E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS).1 g
  unfold IsKFinite
  refine ⟨T.image fun q => jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf (polySection q), fun k hk => ?_⟩
  have hκ := realMat_transpose_mul_self_of_mem_orth3 hk
  have htr : (fun x => jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf (polySection p) (x * k)) =
      ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (StandardKernel.realMat k).det •
        jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf
          (polySection (MvPolynomial.bind₁ (OrthogonalTranslates.shift (StandardKernel.realMat k)) p)) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, jacquetVector3_mul_orth, sectionTranslate_polySection p _ hκ]
  rw [htr]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨cf, -, hcf⟩ :=
    Submodule.mem_span_finset.1
      (hTspan _ (OrthogonalTranslates.totalDegree_bind₁_shift_le (StandardKernel.realMat k) p))
  rw [← hcf, jacquetVector3_polySection_sum D (uR w₀ h₀) (aR w₀ h₀) a psiInf hpsiInf hint T cf]
  refine Submodule.sum_mem _ fun q hq => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hq)

end S_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3 (solution)
