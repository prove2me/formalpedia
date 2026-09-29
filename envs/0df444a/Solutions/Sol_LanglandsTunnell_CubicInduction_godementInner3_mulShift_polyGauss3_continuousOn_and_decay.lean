-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.godementInner3_mulShift_polyGauss3_continuousOn_and_decay
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dbf59a7e-a958-5a9f-b3fd-af349577e397

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_RatIdele_Normalizer
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse MeasureTheory

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory

theorem psiArch_eq_psi_realCoord (w : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch w = ArchR.psi (StandardKernel.realCoord w) := by
  have h1 : NumberField.StandardAddChar.psiArch w =
      NumberField.StandardAddChar.psiArchPlace Rat.infinitePlace (w Rat.infinitePlace) := by
    rw [NumberField.StandardAddChar.psiArch_apply]
    exact finprod_eq_single _ Rat.infinitePlace fun v hv => absurd (Subsingleton.elim v Rat.infinitePlace) hv
  rw [h1, NumberField.StandardAddChar.psiArchPlace_apply, ArchR.psi, StandardKernel.realCoord_apply]

theorem realCoord_ratCast (a : ℚ) :
    StandardKernel.realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) a) = (a : ℝ) := by
  rw [← RingHom.comp_apply]
  exact eq_ratCast (StandardKernel.realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

theorem psiInf_ofReal_neg (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
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

theorem exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (ι : Type) [Fintype ι] (N : ℕ) :
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

theorem iteratedDeriv_real_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]

theorem norm_iteratedFDeriv_real_exp_le (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp y‖ ≤ Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos y)]

theorem exists_forall_pow_mul_exp_neg_pi_sq_le (m : ℕ) :
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

theorem norm_sq_le_sum_sq {ι : Type} [Fintype ι] (x : ι → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
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

def quad (x : ι → ℝ) : ℝ := -(Real.pi * ∑ i, x i ^ 2)

theorem contDiff_quad : ContDiff ℝ (⊤ : ℕ∞) (quad (ι := ι)) := by
  unfold quad
  apply ContDiff.neg
  apply ContDiff.mul contDiff_const
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

theorem norm_proj_le_one (i : ι) : ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x i

theorem norm_iteratedFDeriv_proj_le (i : ι) (j : ℕ) (x : ι → ℝ) :
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

theorem contDiff_proj (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
  exact ContinuousLinearMap.contDiff _

theorem norm_iteratedFDeriv_coord_sq_le (i : ι) (j : ℕ) (x : ι → ℝ) :
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
          gcongr with k _
          · exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
          · exact norm_iteratedFDeriv_proj_le i k x
          · exact norm_iteratedFDeriv_proj_le i (j - k) x
      _ = 2 ^ j * max ‖x‖ 1 ^ 2 := by
          rw [one_mul, ← Finset.sum_mul, ← Finset.sum_mul]
          have h2 : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) = 2 ^ j := by
            exact_mod_cast Nat.sum_range_choose j
          rw [h2]; ring

theorem norm_iteratedFDeriv_quad_le (j : ℕ) (x : ι → ℝ) :
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

def gauss (x : ι → ℝ) : ℝ := Real.exp (quad x)

theorem contDiff_gauss : ContDiff ℝ (⊤ : ℕ∞) (gauss (ι := ι)) :=
  Real.contDiff_exp.comp contDiff_quad

theorem norm_iteratedFDeriv_quad_le_pow (j : ℕ) (hj : 1 ≤ j) (x : ι → ℝ) :
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

theorem norm_iteratedFDeriv_gauss_le (n : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤
      n.factorial * Real.exp (quad x) * (2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2) ^ n := by
  have h : gauss (ι := ι) = Real.exp ∘ quad := rfl
  rw [h]
  exact norm_iteratedFDeriv_comp_le Real.contDiff_exp contDiff_quad (by exact_mod_cast le_top) x
    (fun i _ => norm_iteratedFDeriv_real_exp_le i (quad x))
    (fun i hi _ => norm_iteratedFDeriv_quad_le_pow i hi x)

theorem exp_quad_le (x : ι → ℝ) : Real.exp (quad x) ≤ Real.exp (-(Real.pi * ‖x‖ ^ 2)) := by
  apply Real.exp_le_exp.2
  unfold quad
  have := norm_sq_le_sum_sq x
  nlinarith [Real.pi_pos]

theorem gauss_decay (k n : ℕ) : ∃ C : ℝ, ∀ x : ι → ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤ C := by

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

theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq' :
    ∃ Φ : SchwartzMap (ι → ℝ) ℝ, ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) :=
  ⟨⟨gauss, contDiff_gauss, gauss_decay⟩, fun _ => rfl⟩

abbrev Arr : Type := Fin 2 → Fin 3 → ℝ

abbrev Pl : Type := Fin 2 → ℝ

def blk (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : Arr := fun i => ![h i 0, h i 1, w i]

def rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : Arr := fun i b => (Matrix.of X * T) i b

theorem rmul_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) (i : Fin 2) (b : Fin 3) :
    rmul T X i b = ∑ k : Fin 3, X i k * T k b := by
  simp [rmul, Matrix.mul_apply]

theorem rmul_add (T : Matrix (Fin 3) (Fin 3) ℝ) (X Y : Arr) : rmul T (X + Y) = rmul T X + rmul T Y := by
  funext i b; simp [rmul_apply, add_mul, Finset.sum_add_distrib]

theorem rmul_smul (T : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (X : Arr) : rmul T (c • X) = c • rmul T X := by
  funext i b; simp [rmul_apply, Finset.mul_sum, mul_assoc]

theorem rmul_rmul (T S : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : rmul S (rmul T X) = rmul (T * S) X := by
  funext i b
  simp only [rmul_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem rmul_inv_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (X : Arr) : rmul T⁻¹ (rmul T X) = X := by
  rw [rmul_rmul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hT)]
  funext i b; simp [rmul_apply, Matrix.one_apply]

theorem blk_add (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : blk h w = blk h 0 + blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

theorem blk_zero_add_smul (w w' : Pl) : blk 0 (w + w') = blk 0 w + blk 0 w' := by
  funext i b; fin_cases b <;> simp [blk]

theorem blk_zero_smul (c : ℝ) (w : Pl) : blk 0 (c • w) = c • blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

def mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ‖(fun i j => T i j : Fin 3 → Fin 3 → ℝ)‖

theorem mnorm_nonneg (T : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ mnorm T := norm_nonneg _

theorem abs_entry_le_mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) (k b : Fin 3) : |T k b| ≤ mnorm T := by
  have h1 := norm_le_pi_norm (fun i j => T i j : Fin 3 → Fin 3 → ℝ) k
  have h2 := norm_le_pi_norm (fun j => T k j : Fin 3 → ℝ) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

theorem abs_entry_le_norm (X : Arr) (i : Fin 2) (b : Fin 3) : |X i b| ≤ ‖X‖ := by
  have h1 := norm_le_pi_norm X i
  have h2 := norm_le_pi_norm (X i) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

theorem norm_rmul_le (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : ‖rmul T X‖ ≤ 3 * ‖X‖ * mnorm T := by
  have hnn : (0 : ℝ) ≤ 3 * ‖X‖ * mnorm T := mul_nonneg (by positivity) (mnorm_nonneg T)
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => (pi_norm_le_iff_of_nonneg hnn).2 fun b => ?_
  rw [Real.norm_eq_abs, rmul_apply]
  calc |∑ k : Fin 3, X i k * T k b| ≤ ∑ k : Fin 3, |X i k * T k b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, ‖X‖ * mnorm T := by
        gcongr with k _
        rw [abs_mul]
        exact mul_le_mul (abs_entry_le_norm X i k) (abs_entry_le_mnorm T k b) (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖X‖ * mnorm T := by simp [Finset.sum_const]; ring

theorem norm_le_norm_blk_left (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖h‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  fin_cases j
  · have h2 := norm_le_pi_norm (blk h w i) 0
    simp only [blk, Matrix.cons_val_zero] at h2
    exact h2.trans h1
  · have h2 := norm_le_pi_norm (blk h w i) 1
    simp only [blk, Matrix.cons_val_one] at h2
    exact h2.trans h1

theorem norm_le_norm_blk_right (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖w‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  have h2 := norm_le_pi_norm (blk h w i) 2
  simp only [blk] at h2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  exact h2.trans h1

def sliceLin (T : Matrix (Fin 3) (Fin 3) ℝ) : Pl →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => rmul T (blk 0 w)
      map_add' := fun w w' => by rw [blk_zero_add_smul, rmul_add]
      map_smul' := fun c w => by rw [blk_zero_smul, rmul_smul]; rfl }

theorem sliceLin_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (w : Pl) : sliceLin T w = rmul T (blk 0 w) := rfl

theorem rmul_blk_eq (T : Matrix (Fin 3) (Fin 3) ℝ) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    rmul T (blk h w) = sliceLin T w + rmul T (blk h 0) := by
  rw [blk_add, rmul_add, sliceLin_apply, add_comm]

theorem norm_blk_zero_le (w : Pl) : ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  fin_cases b <;> simp [blk]
  exact norm_le_pi_norm w i

theorem norm_sliceLin_le (T : Matrix (Fin 3) (Fin 3) ℝ) : ‖sliceLin T‖ ≤ 3 * mnorm T := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (mnorm_nonneg T)) fun w => ?_
  rw [sliceLin_apply]
  calc ‖rmul T (blk 0 w)‖ ≤ 3 * ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ * mnorm T := norm_rmul_le T _
    _ ≤ 3 * ‖w‖ * mnorm T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_blk_zero_le w) (by norm_num)) (mnorm_nonneg T)
    _ = 3 * mnorm T * ‖w‖ := by ring

theorem norm_iteratedFDeriv_slice_le {F : Arr → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (T : Matrix (Fin 3) (Fin 3) ℝ)
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

theorem norm_blk_le_norm_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    ‖blk h w‖ ≤ 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by
  calc ‖blk h w‖ = ‖rmul T⁻¹ (rmul T (blk h w))‖ := by rw [rmul_inv_rmul T hT]
    _ ≤ 3 * ‖rmul T (blk h w)‖ * mnorm T⁻¹ := norm_rmul_le _ _
    _ = 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by ring

theorem exists_bound_mnorm_of_isCompact (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
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

theorem exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ))
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

def sliceSchwartz (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) :
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

theorem sliceSchwartz_apply (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ)
    (w : Pl) : sliceSchwartz Ψ T hT h w = Ψ (rmul T (blk h w)) := rfl

theorem exists_forall_seminorm_sliceSchwartz_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hKdet : ∀ T ∈ K, T.det ≠ 0) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T ∈ K) (h : Fin 2 → Fin 2 → ℝ),
      SchwartzMap.seminorm ℝ k n (sliceSchwartz Ψ T (hKdet T hT) h) ≤ C * ((1 + ‖h‖) ^ N)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Ψ K hK hKdet k n N
  refine ⟨C, hC0, fun T hT h => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun w => ?_
  exact hC T hT h w

theorem character_eq (c : ℝ) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) (v : Pl) :
    c * v 1 = ∑ i, (c • ((Matrix.of h)⁻¹ 1)) i * ((Matrix.of h).mulVec v) i := by
  have hv : (Matrix.of h)⁻¹.mulVec ((Matrix.of h).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have h1 : v 1 = ∑ i, (Matrix.of h)⁻¹ 1 i * ((Matrix.of h).mulVec v) i := by
    conv_lhs => rw [← hv]
    simp [Matrix.mulVec, dotProduct]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem integral_comp_mulVec_eq {G : Pl → ℂ} (hG : Continuous G) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) :
    ∫ v : Pl, G ((Matrix.of h).mulVec v) = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) * ∫ u : Pl, G u := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 2) hdet
  have hmeas : Measurable (Matrix.toLin' (Matrix.of h)) := (Matrix.toLin' (Matrix.of h)).continuous_of_finiteDimensional.measurable
  have hfun : (fun v : Pl => G ((Matrix.of h).mulVec v)) = fun v => G (Matrix.toLin' (Matrix.of h) v) := by
    funext v; simp [Matrix.toLin'_apply]
  rw [hfun, ← MeasureTheory.integral_map hmeas.aemeasurable (hG.aestronglyMeasurable), hmap,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (by positivity), abs_inv]
  exact Complex.real_smul

theorem inv_pow_mul_inv_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    ((1 + a) ^ N)⁻¹ * ((1 + b) ^ N)⁻¹ ≤ ((1 + a + b) ^ N)⁻¹ := by
  rw [← mul_inv, ← mul_pow]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg ha hb]

theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
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

theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq (ι : Type) [Fintype ι] :
    ∃ Φ : 𝓢((ι → ℝ), ℝ), ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) := by
  exact G0.exists_schwartzMap_eq_exp_neg_pi_sum_sq' (ι := ι)

theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (c : ℝ) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (_hK : IsCompact K) (_hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  exact G0.norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' Ψ N c K _hK _hKdet

namespace G0

def entryL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj v.2 : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj v.1 : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))

theorem entryL_apply (v : Fin 2 × Fin 3) (M : Fin 2 → Fin 3 → ℝ) : entryL v M = M v.1 v.2 := rfl

def uncurryL : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 2 × Fin 3 → ℝ) :=
  ContinuousLinearMap.pi entryL

theorem uncurryL_apply (M : Fin 2 → Fin 3 → ℝ) (v : Fin 2 × Fin 3) : uncurryL M v = M v.1 v.2 := rfl

def coordL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (entryL v)

theorem norm_le_norm_uncurryL (M : Fin 2 → Fin 3 → ℝ) : ‖M‖ ≤ ‖uncurryL M‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  have := norm_le_pi_norm (uncurryL M) (i, b)
  simpa [uncurryL_apply] using this

theorem hasTemperateGrowth_eval (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq => simp only [MvPolynomial.eval_add]; exact hp.add hq
  | mul_X p v hp =>
    have hX : Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ => ((M v.1 v.2 : ℝ) : ℂ) := by
      have h := (coordL v).hasTemperateGrowth
      convert h using 1
      all_goals try rfl
    simpa [MvPolynomial.eval_mul, Pi.mul_def] using hp.mul hX

theorem exists_schwartzMap_eq_gaussian3 :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℝ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ,
      Φ (fun i b => M i b) = Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2)) := by
  obtain ⟨Φ₀, hΦ₀⟩ := LanglandsTunnell.CubicInduction.exists_schwartzMap_eq_exp_neg_pi_sum_sq (Fin 2 × Fin 3)
  refine ⟨SchwartzMap.compCLM ℝ uncurryL.hasTemperateGrowth ⟨1, 1, fun M => ?_⟩ Φ₀, fun M => ?_⟩
  · have := norm_le_norm_uncurryL M
    nlinarith [norm_nonneg (uncurryL M)]
  · rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦ₀]
    simp only [uncurryL_apply, Fintype.sum_prod_type]

theorem exists_schwartzMap_eq_of_mem_polyGauss3' {S : Matrix (Fin 2) (Fin 3) ℝ → ℂ} (hS : S ∈ polyGauss3) :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Φ (fun i b => M i b) = S M := by
  obtain ⟨p, rfl⟩ := hS
  obtain ⟨Φg, hΦg⟩ := exists_schwartzMap_eq_gaussian3
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p) (Φg.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM), fun M => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_eval p), SchwartzMap.postcompCLM_apply, hΦg M, smul_eq_mul]
  rfl

end G0

end SchwartzSlices

end LanglandsTunnell.CubicInduction

end

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
open scoped SchwartzMap

theorem hasTemperateGrowth_coord_pow (i : Fin 2) (n : ℕ) :
    Function.HasTemperateGrowth fun w : Fin 2 → ℝ => (((w i : ℝ) : ℂ)) ^ n := by
  induction n with
  | zero => simpa using Function.HasTemperateGrowth.const (1 : ℂ)
  | succ n ih =>
    have h1 : Function.HasTemperateGrowth fun w : Fin 2 → ℝ => ((w i : ℝ) : ℂ) := by
      have h := (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)).hasTemperateGrowth
      convert h using 1
      all_goals try rfl
    simp only [pow_succ]
    exact ih.mul h1

theorem exists_schwartzMap_monomial_gauss (n₀ n₁ : ℕ) :
    ∃ Φ : 𝓢((Fin 2 → ℝ), ℂ), ∀ w : Fin 2 → ℝ,
      Φ w = ((w 0 : ℝ) : ℂ) ^ n₀ * ((w 1 : ℝ) : ℂ) ^ n₁ * ((Real.exp (-(Real.pi * ∑ i, w i ^ 2)) : ℝ) : ℂ) := by
  obtain ⟨Φg, hΦg⟩ := exists_schwartzMap_eq_exp_neg_pi_sum_sq (Fin 2)
  have hg : Function.HasTemperateGrowth fun w : Fin 2 → ℝ => ((w 0 : ℝ) : ℂ) ^ n₀ * ((w 1 : ℝ) : ℂ) ^ n₁ :=
    (hasTemperateGrowth_coord_pow 0 n₀).mul (hasTemperateGrowth_coord_pow 1 n₁)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun w : Fin 2 → ℝ => ((w 0 : ℝ) : ℂ) ^ n₀ * ((w 1 : ℝ) : ℂ) ^ n₁)
    (Φg.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM), fun w => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.postcompCLM_apply, smul_eq_mul]
  simp [hΦg w]

theorem continuous_integral_schwartzMap_mul_exp (φ : 𝓢((Fin 2 → ℝ), ℂ)) :
    Continuous fun ξ : Fin 2 → ℝ =>
      ∫ u : Fin 2 → ℝ, φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I) := by
  refine MeasureTheory.continuous_of_dominated (bound := fun u => ‖φ u‖) ?_ ?_ (φ.integrable.norm) ?_
  · intro ξ
    exact (φ.continuous.mul (by fun_prop)).aestronglyMeasurable
  · intro ξ
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  · refine Filter.Eventually.of_forall fun u => ?_
    fun_prop

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
open scoped SchwartzMap

set_option maxHeartbeats 1600000 in

theorem godementInner3_mulShift_eq_sum (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    (Φ : ((Fin 2 × Fin 3) →₀ ℕ) → 𝓢((Fin 2 → ℝ), ℂ))
    (hΦ : ∀ d (w : Fin 2 → ℝ), Φ d w =
      ((w 0 : ℝ) : ℂ) ^ d (0, 2) * ((w 1 : ℝ) : ℂ) ^ d (1, 2) * ((Real.exp (-(Real.pi * ∑ i, w i ^ 2)) : ℝ) : ℂ))
    (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) (y : ℝ) :
    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y))
        (fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M) e 1 =
      ((|e.det|⁻¹ : ℝ) : ℂ) * ((((Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2))) : ℝ) : ℂ) *
        ∑ d ∈ p.support, p.coeff d * (∏ i : Fin 2, ((e i 0 : ℝ) : ℂ) ^ d (i, 0) * ((e i 1 : ℝ) : ℂ) ^ d (i, 1)) *
          ∫ u : Fin 2 → ℝ, Φ d u *
            Complex.exp (((-(2 * Real.pi * ∑ i, (((a : ℝ) * y) • (e⁻¹ 1)) i * u i) : ℝ) : ℂ) * Complex.I)) := by
  classical
  set c : ℝ := (a : ℝ) * y with hc

  set χ : (Fin 2 → ℝ) → ℂ := fun w =>
    Complex.exp (((-(2 * Real.pi * ∑ i, (c • (e⁻¹ 1)) i * w i) : ℝ) : ℂ) * Complex.I) with hχ
  have hχcont : Continuous χ := by
    simp only [hχ]
    fun_prop
  have hχnorm : ∀ w, ‖χ w‖ = 1 := fun w => by simp only [hχ]; exact Complex.norm_exp_ofReal_mul_I _

  set H : (Fin 2 → ℝ) → ℂ := fun w =>
    (MvPolynomial.eval (fun v : Fin 2 × Fin 3 => (((![e v.1 0, e v.1 1, w v.1] : Fin 3 → ℝ) v.2 : ℝ) : ℂ)) p *
        gaussian3 (Matrix.of fun i b => (![e i 0, e i 1, w i] : Fin 3 → ℝ) b)) * χ w with hH
  have hHcont : Continuous H := by
    simp only [hH]
    refine Continuous.mul (Continuous.mul ?_ ?_) hχcont
    · refine (MvPolynomial.continuous_eval p).comp ?_
      refine continuous_pi fun v => Complex.continuous_ofReal.comp ?_
      obtain ⟨i, b⟩ := v
      fin_cases b <;> simp <;> fun_prop
    · unfold gaussian3
      refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
      refine (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun b _ => ?_)).neg
      fin_cases b <;> simp <;> fun_prop

  have hint : godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y))
      (fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M) e 1 =
      ∫ v : Fin 2 → ℝ, H (e.mulVec v) := by
    unfold godementInner3
    congr 1
    funext v
    have hchar : (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y))
        (AutomorphicForm.StandardKernel.ofReal (-(v 1))) = χ (e.mulVec v) := by
      simp only [hχ]
      have hce : c * v 1 = ∑ i, (c • (e⁻¹ 1)) i * e.mulVec v i := G0.character_eq c e he v
      rw [AddChar.mulShift_apply, hpsiInf, psiArch_eq_psi_realCoord, map_mul, map_mul, realCoord_ratCast,
        realCoord_ofReal, realCoord_ofReal, ArchR.psi, ← hce]
      congr 1
      simp only [hc]
      push_cast
      ring
    have hmat : e * Matrix.of ![fun b => (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 b + v 0 * (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 b,
        fun b => (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 b + v 1 * (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 b] =
        Matrix.of (fun i b => (![e i 0, e i 1, e.mulVec v i] : Fin 3 → ℝ) b) := by
      ext i b
      fin_cases i <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.mulVec, dotProduct]
    rw [hchar, hmat]
    simp only [hH, Matrix.of_apply]

  have hcv : ∫ v : Fin 2 → ℝ, H (e.mulVec v) = ((|e.det|⁻¹ : ℝ) : ℂ) * ∫ u : Fin 2 → ℝ, H u :=
    G0.integral_comp_mulVec_eq hHcont e he
  rw [hint, hcv]

  have hHu : ∀ u : Fin 2 → ℝ, H u =
      ((((Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2))) : ℝ) : ℂ) *
        ∑ d ∈ p.support, p.coeff d * (∏ i : Fin 2, ((e i 0 : ℝ) : ℂ) ^ d (i, 0) * ((e i 1 : ℝ) : ℂ) ^ d (i, 1)) *
          (Φ d u * χ u)) := by
    intro u
    have hg : gaussian3 (Matrix.of fun i b => (![e i 0, e i 1, u i] : Fin 3 → ℝ) b) =
        ((((Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2))) : ℝ) : ℂ) *
          ((Real.exp (-(Real.pi * ∑ i, u i ^ 2)) : ℝ) : ℂ)) := by
      unfold gaussian3
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      simp only [Matrix.of_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring
    have hev : MvPolynomial.eval (fun v : Fin 2 × Fin 3 => (((![e v.1 0, e v.1 1, u v.1] : Fin 3 → ℝ) v.2 : ℝ) : ℂ)) p =
        ∑ d ∈ p.support, p.coeff d * ((∏ i : Fin 2, ((e i 0 : ℝ) : ℂ) ^ d (i, 0) * ((e i 1 : ℝ) : ℂ) ^ d (i, 1)) *
          (((u 0 : ℝ) : ℂ) ^ d (0, 2) * ((u 1 : ℝ) : ℂ) ^ d (1, 2))) := by
      rw [MvPolynomial.eval_eq']
      refine Finset.sum_congr rfl fun d _ => ?_
      congr 1
      rw [Fintype.prod_prod_type]
      simp only [Fin.prod_univ_three, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring
    simp only [hH]
    rw [hev, hg]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hΦ]
    simp only [Finset.mul_sum]
    ring
  simp_rw [hHu]
  rw [integral_const_mul, integral_finsetSum _ (fun d _ => ?_)]
  · congr 1
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul]
  · exact ((((Φ d).integrable.bdd_mul hχcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (hχnorm u).le))).const_mul
      (p.coeff d * ∏ i : Fin 2, ((e i 0 : ℝ) : ℂ) ^ d (i, 0) * ((e i 1 : ℝ) : ℂ) ^ d (i, 1))).congr
      (Filter.Eventually.of_forall fun u => by ring)

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    ContinuousOn
        (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
          godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal p.1)) S p.2 1)
        {p | p.2.det ≠ 0} ∧
      ∀ N : ℕ, ∃ C : ℝ, ∃ A : ℕ, 0 ≤ C ∧
        ∀ (e : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ), e.det ≠ 0 →
          ‖godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S e 1‖ ≤
            C * |e.det|⁻¹ * Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2)) * (1 + ∑ i, ∑ j, e i j ^ 2) ^ A *
              ((1 + y ^ 2 * ∑ i, (e⁻¹ 1 i) ^ 2) ^ N)⁻¹ := by
  classical
  obtain ⟨p, rfl⟩ := hS
  choose Φ hΦ using fun d : (Fin 2 × Fin 3) →₀ ℕ =>
    LanglandsTunnell.CubicInduction.exists_schwartzMap_monomial_gauss (d (0, 2)) (d (1, 2))
  have hformula := fun (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) (y : ℝ) =>
    LanglandsTunnell.CubicInduction.godementInner3_mulShift_eq_sum a psiInf hpsiInf p Φ hΦ e he y

  set I : ((Fin 2 × Fin 3) →₀ ℕ) → (Fin 2 → ℝ) → ℂ := fun d ξ =>
    ∫ u : Fin 2 → ℝ, Φ d u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I) with hI
  have hIcont : ∀ d, Continuous (I d) := fun d =>
    LanglandsTunnell.CubicInduction.continuous_integral_schwartzMap_mul_exp (Φ d)

  set Em : ((Fin 2 × Fin 3) →₀ ℕ) → Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun d e =>
    ∏ i : Fin 2, ((e i 0 : ℝ) : ℂ) ^ d (i, 0) * ((e i 1 : ℝ) : ℂ) ^ d (i, 1) with hEm

  have hrow : ∀ e : Matrix (Fin 2) (Fin 2) ℝ, e.det ≠ 0 →
      e⁻¹ 1 = fun i => (e.det)⁻¹ * (![-e 1 0, e 0 0] : Fin 2 → ℝ) i := by
    intro e he
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    funext i
    fin_cases i <;> simp [Matrix.smul_apply]
  have hformula' : ∀ (e : Matrix (Fin 2) (Fin 2) ℝ), e.det ≠ 0 → ∀ y : ℝ,
      godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y))
        (fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M) e 1 =
      ((|e.det|⁻¹ : ℝ) : ℂ) * ((((Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2))) : ℝ) : ℂ) *
        ∑ d ∈ p.support, p.coeff d * Em d e * I d (((a : ℝ) * y) • (e⁻¹ 1))) := by
    intro e he y
    simp only [hEm, hI]
    exact hformula e he y
  refine ⟨?_, ?_⟩
  ·
    have hF : ContinuousOn (fun q : ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
        ((|q.2.det|⁻¹ : ℝ) : ℂ) * ((((Real.exp (-(Real.pi * ∑ i, ∑ j, q.2 i j ^ 2))) : ℝ) : ℂ) *
          ∑ d ∈ p.support, p.coeff d * Em d q.2 *
            I d (fun i => ((a : ℝ) * q.1) * ((q.2.det)⁻¹ * (![-q.2 1 0, q.2 0 0] : Fin 2 → ℝ) i))))
        {q | q.2.det ≠ 0} := by
      have hdet : Continuous fun q : ℝ × Matrix (Fin 2) (Fin 2) ℝ => q.2.det :=
        (continuous_id.matrix_det).comp continuous_snd
      refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
      · exact Complex.continuous_ofReal.continuousOn.comp
          ((continuous_abs.comp hdet).continuousOn.inv₀ fun q hq => abs_ne_zero.mpr hq) (Set.mapsTo_univ _ _)
      · exact Continuous.continuousOn (by fun_prop)
      · refine continuousOn_finset_sum _ fun d _ => ?_
        refine ContinuousOn.mul (Continuous.continuousOn ?_) ?_
        · simp only [hEm]
          fun_prop
        · refine ((hIcont d).comp_continuousOn ?_)
          refine continuousOn_pi.mpr fun i => ?_
          refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
          refine ContinuousOn.mul (hdet.continuousOn.inv₀ fun q hq => hq) ?_
          fin_cases i <;> simp <;> fun_prop
    refine hF.congr fun q hq => ?_
    simp only [Set.mem_setOf_eq] at hq
    rw [hformula' q.2 hq q.1, hrow q.2 hq]
    first
      | rfl
      | simp only [Pi.smul_def, smul_eq_mul]
  ·
    intro N
    obtain ⟨s, CF, hCF0, hF⟩ :=
      LanglandsTunnell.CubicInduction.exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (Fin 2) (2 * N)
    set m : ℝ := min 1 |(a : ℝ)| with hm
    have hm0 : 0 < m := lt_min one_pos (abs_pos.mpr (by exact_mod_cast ha))
    have hm1 : m ≤ 1 := min_le_left _ _
    have hma : m ≤ |(a : ℝ)| := min_le_right _ _
    set K : ℝ := (m ^ (2 * N))⁻¹ * 2 ^ N with hK
    have hK0 : 0 ≤ K := by positivity
    set B : ℝ := ∑ d ∈ p.support, ‖p.coeff d‖ * ((s.sup (schwartzSeminormFamily ℝ (Fin 2 → ℝ) ℂ)) (Φ d)) with hB
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (apply_nonneg _ _)
    refine ⟨B * CF * K, p.totalDegree, by positivity, ?_⟩
    intro e y he
    rw [hformula' e he y, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (abs_nonneg _)), Real.norm_of_nonneg (Real.exp_pos _).le]

    set ξ : Fin 2 → ℝ := ((a : ℝ) * y) • (e⁻¹ 1) with hξ
    set T : ℝ := ∑ i, (e⁻¹ 1 i) ^ 2 with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hTle : T ≤ 2 * ‖e⁻¹ 1‖ ^ 2 := by
      have h0 : (e⁻¹ 1 0) ^ 2 ≤ ‖e⁻¹ 1‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm (e⁻¹ 1) 0) 2
      have h1 : (e⁻¹ 1 1) ^ 2 ≤ ‖e⁻¹ 1‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm (e⁻¹ 1) 1) 2
      simp only [hT, Fin.sum_univ_two]
      linarith
    have hξnorm : ‖ξ‖ = |(a : ℝ)| * |y| * ‖e⁻¹ 1‖ := by
      rw [hξ, norm_smul, Real.norm_eq_abs, abs_mul]

    have hfreq : (1 + ‖ξ‖) ^ (-((2 * N : ℕ) : ℝ)) ≤ K * ((1 + y ^ 2 * T) ^ N)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, hξnorm]
      set t : ℝ := |y| * ‖e⁻¹ 1‖ with ht
      have ht0 : 0 ≤ t := by positivity
      have h1 : m * (1 + t) ≤ 1 + |(a : ℝ)| * |y| * ‖e⁻¹ 1‖ := by
        have : |(a : ℝ)| * |y| * ‖e⁻¹ 1‖ = |(a : ℝ)| * t := by rw [ht]; ring
        rw [this]
        nlinarith [hm1, hma, ht0, hm0]
      have h2 : 1 + y ^ 2 * T ≤ 2 * (1 + t) ^ 2 := by
        have : y ^ 2 * T ≤ 2 * t ^ 2 := by
          rw [ht, mul_pow, ← sq_abs y]
          nlinarith [hTle, sq_nonneg (|y|)]
        nlinarith [ht0]
      have h3 : (m * (1 + t)) ^ (2 * N) ≤ (1 + |(a : ℝ)| * |y| * ‖e⁻¹ 1‖) ^ (2 * N) :=
        pow_le_pow_left₀ (by positivity) h1 _
      have h4 : (1 + y ^ 2 * T) ^ N ≤ (2 * (1 + t) ^ 2) ^ N := pow_le_pow_left₀ (by positivity) h2 _
      rw [hK]
      calc ((1 + |(a : ℝ)| * |y| * ‖e⁻¹ 1‖) ^ (2 * N))⁻¹ ≤ ((m * (1 + t)) ^ (2 * N))⁻¹ :=
            inv_anti₀ (by positivity) h3
        _ = (m ^ (2 * N))⁻¹ * (((1 + t) ^ 2) ^ N)⁻¹ := by rw [mul_pow, mul_inv, ← pow_mul]
        _ = (m ^ (2 * N))⁻¹ * 2 ^ N * ((2 * (1 + t) ^ 2) ^ N)⁻¹ := by
            rw [mul_pow, mul_inv, ← mul_assoc, mul_assoc ((m ^ (2 * N))⁻¹), mul_inv_cancel₀ (by positivity), mul_one]
        _ ≤ (m ^ (2 * N))⁻¹ * 2 ^ N * ((1 + y ^ 2 * T) ^ N)⁻¹ := by
            gcongr

    set F2 : ℝ := ∑ i, ∑ j, e i j ^ 2 with hF2
    have hF20 : 0 ≤ F2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hent : ∀ i j, |e i j| ≤ 1 + F2 := by
      intro i j
      have hij : e i j ^ 2 ≤ F2 := by
        rw [hF2]
        exact (Finset.single_le_sum (f := fun j => e i j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, e i j ^ 2) (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
            (Finset.mem_univ i))
      nlinarith [abs_nonneg (e i j), sq_abs (e i j)]
    have hEm_le : ∀ d ∈ p.support, ‖Em d e‖ ≤ (1 + F2) ^ p.totalDegree := by
      intro d hd
      have hdeg : (d (0, 0) + d (0, 1)) + (d (1, 0) + d (1, 1)) ≤ p.totalDegree := by
        refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
        simp only [Fin.sum_univ_two, Fin.sum_univ_three]
        omega
      simp only [hEm, Fin.prod_univ_two, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have h1 : (1 : ℝ) ≤ 1 + F2 := by linarith
      calc |e 0 0| ^ d (0, 0) * |e 0 1| ^ d (0, 1) * (|e 1 0| ^ d (1, 0) * |e 1 1| ^ d (1, 1))
          ≤ (1 + F2) ^ d (0, 0) * (1 + F2) ^ d (0, 1) * ((1 + F2) ^ d (1, 0) * (1 + F2) ^ d (1, 1)) := by
            gcongr <;> first | exact abs_nonneg _ | exact hent _ _
        _ = (1 + F2) ^ ((d (0, 0) + d (0, 1)) + (d (1, 0) + d (1, 1))) := by ring
        _ ≤ (1 + F2) ^ p.totalDegree := pow_le_pow_right₀ h1 hdeg

    have hsum : ‖∑ d ∈ p.support, p.coeff d * Em d e * I d ξ‖ ≤
        B * CF * K * (1 + F2) ^ p.totalDegree * ((1 + y ^ 2 * T) ^ N)⁻¹ := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ d ∈ p.support, ‖p.coeff d * Em d e * I d ξ‖ ≤
          ‖p.coeff d‖ * ((s.sup (schwartzSeminormFamily ℝ (Fin 2 → ℝ) ℂ)) (Φ d)) *
            (CF * K * (1 + F2) ^ p.totalDegree * ((1 + y ^ 2 * T) ^ N)⁻¹) := by
        intro d hd
        rw [norm_mul, norm_mul]
        have hId : ‖I d ξ‖ ≤ CF * ((s.sup (schwartzSeminormFamily ℝ (Fin 2 → ℝ) ℂ)) (Φ d)) *
            (K * ((1 + y ^ 2 * T) ^ N)⁻¹) :=
          (hF (Φ d) ξ).trans (mul_le_mul_of_nonneg_left hfreq (mul_nonneg hCF0 (apply_nonneg _ _)))
        have hS0 : 0 ≤ (s.sup (schwartzSeminormFamily ℝ (Fin 2 → ℝ) ℂ)) (Φ d) := apply_nonneg _ _
        calc ‖p.coeff d‖ * ‖Em d e‖ * ‖I d ξ‖
            ≤ ‖p.coeff d‖ * (1 + F2) ^ p.totalDegree *
                (CF * ((s.sup (schwartzSeminormFamily ℝ (Fin 2 → ℝ) ℂ)) (Φ d)) * (K * ((1 + y ^ 2 * T) ^ N)⁻¹)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hEm_le d hd) (norm_nonneg _)) hId (norm_nonneg _)
                (mul_nonneg (norm_nonneg _) (by positivity))
          _ = _ := by ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul, ← hB]
      ring_nf
      rfl
    calc |e.det|⁻¹ * (Real.exp (-(Real.pi * F2)) * ‖∑ d ∈ p.support, p.coeff d * Em d e * I d ξ‖)
        ≤ |e.det|⁻¹ * (Real.exp (-(Real.pi * F2)) *
            (B * CF * K * (1 + F2) ^ p.totalDegree * ((1 + y ^ 2 * T) ^ N)⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le) (inv_nonneg.mpr (abs_nonneg _))
      _ = B * CF * K * |e.det|⁻¹ * Real.exp (-(Real.pi * F2)) * (1 + F2) ^ p.totalDegree *
            ((1 + y ^ 2 * T) ^ N)⁻¹ := by ring

end S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay (solution)
