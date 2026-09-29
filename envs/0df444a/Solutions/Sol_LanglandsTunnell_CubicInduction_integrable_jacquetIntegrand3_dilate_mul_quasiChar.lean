-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8c671a78-8a15-5467-96d4-84bd2ebf3383

import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_norm_iteratedFDerivWithin_diagOne_le
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar

set_option autoImplicit false

section
open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

open MeasureTheory

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.jacquetIntegrand3 RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "polyGauss3 godementInner3 jacquetIntegrand3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_eq_unip_mul_smul_diagOne_mul_of_det_ne_zero (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    ∃ (s z y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k ∧ 0 < z ∧
      z = Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ∧ |y| = |x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2) ∧
      x = ArchR.unip s * (z • (ArchR.diagOne y * k)) := by
  have hdet : x.det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := Matrix.det_fin_two x
  have hq : 0 < x 1 0 ^ 2 + x 1 1 ^ 2 := by
    by_contra hcon
    have h10 : x 1 0 = 0 := by nlinarith [sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    have h11 : x 1 1 = 0 := by nlinarith [sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    exact hx (by rw [hdet, h10, h11]; ring)
  have hq' : x 1 0 ^ 2 + x 1 1 ^ 2 ≠ 0 := hq.ne'
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) := ⟨_, rfl⟩
  have hz0 : 0 < z := by rw [hz]; exact Real.sqrt_pos.mpr hq
  have hz0' : z ≠ 0 := hz0.ne'
  have hz2 : z ^ 2 = x 1 0 ^ 2 + x 1 1 ^ 2 := by rw [hz]; exact Real.sq_sqrt hq.le
  refine ⟨(x 0 0 * x 1 0 + x 0 1 * x 1 1) / (x 1 0 ^ 2 + x 1 1 ^ 2), z, x.det / (x 1 0 ^ 2 + x 1 1 ^ 2),
    !![x 1 1 / z, -(x 1 0) / z; x 1 0 / z, x 1 1 / z], ?_, hz0, hz, ?_, ?_⟩
  · unfold ArchR.IsK
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> nlinarith [hz2]
  · rw [abs_div, abs_of_pos hq]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ArchR.unip, ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two, hdet] <;> field_simp <;> ring

private theorem norm_psi_le_one (s : ℝ) : ‖ArchR.psi s‖ ≤ 1 := by
  unfold ArchR.psi
  simp [Complex.norm_exp]

private theorem norm_quasiChar_le (u : ℂ) (b : ZMod 2) {z : ℝ} (hz : z ≠ 0) :
    ‖ArchR.quasiChar u b z‖ ≤ |z| ^ u.re := by
  unfold ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hz)]
  refine mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg z) _) ?_
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_or_gt_of_ne hz with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]

private theorem norm_W_smul_le {P : RealArchParam} (D : ArchDatumR P) {z : ℝ} (hz : 0 < z)
    (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖D.W (z • g)‖ ≤ z ^ (P.centralExponent.re + 1) * ‖D.W g‖ := by
  rw [D.central_law z g hz.ne', norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_of_pos hz,
    Real.rpow_add_one hz.ne']
  have h := norm_quasiChar_le P.centralExponent P.centralSign hz.ne'
  rw [abs_of_pos hz] at h
  unfold ArchR.centralChar
  gcongr

private theorem norm_W_unip_mul_le {P : RealArchParam} (D : ArchDatumR P) (s : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖D.W (ArchR.unip s * g)‖ ≤ ‖D.W g‖ := by
  rw [D.unip_law s g, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_psi_le_one s)

private theorem exists_forall_norm_W_diagOne_mul_le_of_le {P : RealArchParam} (D : ArchDatumR P) (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (q : ℝ) (hq : c₀ - 1 ≤ q) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖D.W (ArchR.diagOne y * k)‖ ≤ C * |y| ^ (-q) := by
  obtain ⟨C₁, h₁⟩ := ArchDatumR.norm_iteratedFDerivWithin_diagOne_le P D c₀ hc₀ 0
  obtain ⟨C₂, h₂⟩ := D.decay_top 0 ⌈max q 0⌉₊
  refine ⟨max (max C₁ C₂) 0, ?_⟩
  intro y k hk hy
  have hW : ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ =
      ‖D.W (ArchR.diagOne y * k)‖ := by
    rw [norm_iteratedFDerivWithin_zero]
    simp [ArchR.asPi, ArchR.diagOneMulCoords]
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hC0 : (0 : ℝ) ≤ max (max C₁ C₂) 0 := le_max_right _ _
  have hC₁ : C₁ ≤ max (max C₁ C₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC₂ : C₂ ≤ max (max C₁ C₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  rcases le_or_gt |y| 1 with hle | hlt
  · have h := h₁ y k hk hy hle
    rw [hW] at h
    calc ‖D.W (ArchR.diagOne y * k)‖ ≤ C₁ * |y| ^ (1 - c₀ - ((0 : ℕ) : ℝ)) := h
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (1 - c₀ - ((0 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hC₁ (Real.rpow_nonneg hy0.le _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-q) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy0 hle (by push_cast; linarith)) hC0
  · have h := h₂ y k hk hlt.le
    rw [hW] at h
    calc ‖D.W (ArchR.diagOne y * k)‖ ≤ C₂ * |y| ^ (-((⌈max q 0⌉₊ : ℕ) : ℝ)) := h
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-((⌈max q 0⌉₊ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hC₂ (Real.rpow_nonneg hy0.le _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-q) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hlt.le (neg_le_neg ((le_max_left _ _).trans (Nat.le_ceil _)))) hC0

private theorem archDatumR_exists_forall_norm_W_le_rpow_mul_rpow_of_le {P : RealArchParam} (D : ArchDatumR P)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (q : ℝ) (hq : c₀ - 1 ≤ q) :
    ∃ C : ℝ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      ‖D.W x‖ ≤ C * Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
        (|x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2)) ^ (-q) := by
  obtain ⟨C, hC⟩ := exists_forall_norm_W_diagOne_mul_le_of_le D c₀ hc₀ q hq
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨s, z, y, k, hk, hz, hzeq, hyabs, hxeq⟩ := exists_eq_unip_mul_smul_diagOne_mul_of_det_ne_zero x hx
  have hq : 0 < x 1 0 ^ 2 + x 1 1 ^ 2 := by
    have h := hz
    rw [hzeq] at h
    exact Real.sqrt_pos.mp h
  have hy : y ≠ 0 := by
    intro h
    rw [h, abs_zero, eq_comm, div_eq_zero_iff] at hyabs
    rcases hyabs with h0 | h0
    · exact hx (abs_eq_zero.mp h0)
    · exact hq.ne' h0
  calc ‖D.W x‖ = ‖D.W (ArchR.unip s * (z • (ArchR.diagOne y * k)))‖ := by rw [← hxeq]
    _ ≤ ‖D.W (z • (ArchR.diagOne y * k))‖ := norm_W_unip_mul_le D s _
    _ ≤ z ^ (P.centralExponent.re + 1) * ‖D.W (ArchR.diagOne y * k)‖ := norm_W_smul_le D hz _
    _ ≤ z ^ (P.centralExponent.re + 1) * (C * |y| ^ (-q)) :=
        mul_le_mul_of_nonneg_left (hC y k hk hy) (Real.rpow_nonneg hz.le _)
    _ = C * Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
          (|x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2)) ^ (-q) := by
        rw [← hzeq, ← hyabs]
        ring

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

private theorem exists_forall_norm_godementInner3_le (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (N : ℕ)
    (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (_hK : IsCompact K) (_hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖godementInner3 psiInf S (Matrix.of h) T‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |(a : ℝ)| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨Φ, hΦ⟩ := G0.exists_schwartzMap_eq_of_mem_polyGauss3' hS
  obtain ⟨C, hC⟩ := norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le Φ N (a : ℝ) K _hK _hKdet
  refine ⟨C, fun T hT h hh => ?_⟩
  rw [godementInner3_eq_integral a psiInf hpsiInf S Φ hΦ h T]
  exact hC T hT h hh

section ColumnIntegrability

open Real

namespace ColumnBracket

private theorem integrable_abs_rpow_mul_bracket {q m : ℝ} (hq : -1 < q) (hm : q + 1 < m) :
    Integrable fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m) := by
  have hmeas : Measurable fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m) :=
    (measurable_norm.pow_const q).mul ((measurable_const.add measurable_norm).pow_const (-m))
  have hIoi : IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ q) (Set.Ioc (0 : ℝ) 1) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hq
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    have h2 : IntegrableOn (fun t : ℝ => t ^ (q - m)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases h1 : t ≤ 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
      · rintro (⟨h, _⟩ | h)
        · exact h
        · linarith
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · refine h1.mono' hmeas.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos ht0]
      have hb : (1 + t) ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      calc t ^ q * (1 + t) ^ (-m) ≤ t ^ q * 1 := by gcongr
        _ = t ^ q := mul_one _
    · refine h2.mono' hmeas.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos ht0]
      have hb : (1 + t) ^ (-m) ≤ t ^ (-m) :=
        Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
      calc t ^ q * (1 + t) ^ (-m) ≤ t ^ q * t ^ (-m) := by gcongr
        _ = t ^ (q - m) := by rw [← Real.rpow_add ht0, sub_eq_add_neg]
  have hIci : IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hIoi
  have hIic : IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Iic 0) := by
    have h := (show IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Ici (-(0 : ℝ))) by
      simpa using hIci).comp_neg_Iic
    simpa [abs_neg] using h
  have hunion := hIic.union hIci
  rwa [Set.Iic_union_Ici, integrableOn_univ] at hunion

private theorem integrable_entrywise_prod (q : Fin 2 → Fin 2 → ℝ) (m : ℝ) (hq : ∀ i j, -1 < q i j)
    (hm : ∀ i j, q i j + 1 < m) :
    Integrable fun e : Fin 2 → Fin 2 → ℝ => ∏ i, ∏ j, |e i j| ^ (q i j) * (1 + |e i j|) ^ (-m) := by
  have hrow : ∀ i : Fin 2,
      Integrable fun r : Fin 2 → ℝ => ∏ j, |r j| ^ (q i j) * (1 + |r j|) ^ (-m) := by
    intro i
    have h := Integrable.fintype_prod (μ := fun _ : Fin 2 => (volume : Measure ℝ))
      (f := fun j (t : ℝ) => |t| ^ (q i j) * (1 + |t|) ^ (-m))
      (fun j => integrable_abs_rpow_mul_bracket (hq i j) (hm i j))
    rwa [← volume_pi] at h
  have h := Integrable.fintype_prod (μ := fun _ : Fin 2 => (volume : Measure (Fin 2 → ℝ)))
    (f := fun i (r : Fin 2 → ℝ) => ∏ j, |r j| ^ (q i j) * (1 + |r j|) ^ (-m)) hrow
  rwa [← volume_pi] at h

private theorem measurable_column_rpow_mul_bracket (p : ℝ) :
    Measurable fun e : Fin 2 → Fin 2 → ℝ =>
      Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8)) := by
  have h00 : Measurable fun e : Fin 2 → Fin 2 → ℝ => e 0 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 0)
  have h10 : Measurable fun e : Fin 2 → Fin 2 → ℝ => e 1 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 1)
  refine Measurable.mul ?_ ?_
  · exact (Real.continuous_sqrt.measurable.comp ((h00.pow_const 2).add (h10.pow_const 2))).pow_const p
  · exact (measurable_const.add measurable_norm).pow_const _

private theorem abs_entry_le_norm (e : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) : |e i j| ≤ ‖e‖ := by
  calc |e i j| = ‖e i j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖e i‖ := norm_le_pi_norm (e i) j
    _ ≤ ‖e‖ := norm_le_pi_norm e i

private theorem bracket_le_prod (e : Fin 2 → Fin 2 → ℝ) {m : ℝ} (hm : 0 ≤ m) :
    (1 + ‖e‖) ^ (-(4 * m)) ≤ ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-m) := by
  have hpos : (0 : ℝ) < 1 + ‖e‖ := by positivity
  have hfac : ∀ i j : Fin 2, (1 + ‖e‖) ^ (-m) ≤ (1 + |e i j|) ^ (-m) := fun i j =>
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [abs_entry_le_norm e i j]) (by linarith)
  have hsplit : (1 + ‖e‖) ^ (-(4 * m)) = ∏ i : Fin 2, ∏ j : Fin 2, (1 + ‖e‖) ^ (-m) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
    ring_nf
  rw [hsplit]
  refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by positivity) fun i _ => ?_
  exact Finset.prod_le_prod (fun j _ => by positivity) fun j _ => hfac i j

private theorem column_rpow_le_of_nonpos {p : ℝ} (hp : p ≤ 0) {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sqrt (x ^ 2 + y ^ 2) ^ p ≤ (2 : ℝ) ^ (p / 2) * (|x| ^ (p / 2) * |y| ^ (p / 2)) := by
  have hxy : 0 < 2 * (|x| * |y|) := by positivity
  have hle : 2 * (|x| * |y|) ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have hsq : Real.sqrt (x ^ 2 + y ^ 2) ^ p = (x ^ 2 + y ^ 2) ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    ring_nf
  rw [hsq, ← Real.mul_rpow (abs_nonneg x) (abs_nonneg y), ← Real.mul_rpow (by norm_num) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos hxy hle (by linarith)

private theorem column_rpow_le_of_pos {p : ℝ} (hp : 0 < p) (x y : ℝ) :
    Real.sqrt (x ^ 2 + y ^ 2) ^ p ≤ (2 : ℝ) ^ p * (|x| ^ p + |y| ^ p) := by
  have hs : Real.sqrt (x ^ 2 + y ^ 2) ≤ 2 * max |x| |y| := by
    have hx : |x| ≤ max |x| |y| := le_max_left _ _
    have hy : |y| ≤ max |x| |y| := le_max_right _ _
    have hm : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) hx
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
  calc Real.sqrt (x ^ 2 + y ^ 2) ^ p ≤ (2 * max |x| |y|) ^ p :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) hs hp.le
    _ = (2 : ℝ) ^ p * max |x| |y| ^ p := Real.mul_rpow (by norm_num) (le_max_of_le_left (abs_nonneg x))
    _ ≤ (2 : ℝ) ^ p * (|x| ^ p + |y| ^ p) := by
        gcongr
        rcases le_total |x| |y| with h | h
        · rw [max_eq_right h]
          linarith [Real.rpow_nonneg (abs_nonneg x) p]
        · rw [max_eq_left h]
          linarith [Real.rpow_nonneg (abs_nonneg y) p]

private theorem ae_column_entries_ne_zero :
    ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e 0 0 ≠ 0 ∧ e 1 0 ≠ 0 := by
  have hrow : ∀ᵐ r : Fin 2 → ℝ, r 0 ≠ 0 := by
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ => volume) 0 0
  have h0 : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e 0 0 ≠ 0 := by
    rw [volume_pi]
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => (volume : Measure (Fin 2 → ℝ))) (i := 0)).eventually hrow
  have h1 : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e 1 0 ≠ 0 := by
    rw [volume_pi]
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => (volume : Measure (Fin 2 → ℝ))) (i := 1)).eventually hrow
  exact h0.and h1

private theorem integrable_column_rpow_mul_bracket {p : ℝ} (hp : -2 < p) :
    Integrable fun e : Fin 2 → Fin 2 → ℝ =>
      Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8)) := by
  have hmeas : AEStronglyMeasurable (fun e : Fin 2 → Fin 2 → ℝ =>
      Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8))) volume :=
    (measurable_column_rpow_mul_bracket p).aestronglyMeasurable
  rcases le_or_gt p 0 with hp0 | hp0
  ·
    rw [max_eq_right hp0] at hmeas ⊢
    set q : Fin 2 → Fin 2 → ℝ := fun _ j => if j = 0 then p / 2 else 0 with hq_def
    have hdom := (integrable_entrywise_prod q 2 (fun i j => by
        simp only [hq_def]; split_ifs <;> linarith) (fun i j => by
        simp only [hq_def]; split_ifs <;> linarith)).const_mul ((2 : ℝ) ^ (p / 2))
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_column_entries_ne_zero] with e he
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hcol := column_rpow_le_of_nonpos hp0 he.1 he.2
    have hbr : (1 + ‖e‖) ^ (-(4 * 0 + 8 : ℝ)) ≤ ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ)) := by
      have := bracket_le_prod e (m := 2) (by norm_num)
      norm_num at this ⊢
      exact this
    have hprod : ∏ i : Fin 2, ∏ j : Fin 2, |e i j| ^ (q i j) * (1 + |e i j|) ^ (-(2 : ℝ)) =
        (|e 0 0| ^ (p / 2) * |e 1 0| ^ (p / 2)) * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ)) := by
      simp only [hq_def, Fin.prod_univ_two, Fin.isValue, if_true, one_ne_zero, if_false, Real.rpow_zero, one_mul]
      ring
    rw [hprod]
    calc Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * 0 + 8 : ℝ))
        ≤ ((2 : ℝ) ^ (p / 2) * (|e 0 0| ^ (p / 2) * |e 1 0| ^ (p / 2))) *
            ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ)) := by
          gcongr
      _ = (2 : ℝ) ^ (p / 2) * ((|e 0 0| ^ (p / 2) * |e 1 0| ^ (p / 2)) *
            ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ))) := by ring
  ·
    rw [max_eq_left hp0.le] at hmeas ⊢
    set q0 : Fin 2 → Fin 2 → ℝ := fun i j => if i = 0 ∧ j = 0 then p else 0 with hq0_def
    set q1 : Fin 2 → Fin 2 → ℝ := fun i j => if i = 1 ∧ j = 0 then p else 0 with hq1_def
    have hi0 := integrable_entrywise_prod q0 (p + 2) (fun i j => by
        simp only [hq0_def]; split_ifs <;> linarith) (fun i j => by simp only [hq0_def]; split_ifs <;> linarith)
    have hi1 := integrable_entrywise_prod q1 (p + 2) (fun i j => by
        simp only [hq1_def]; split_ifs <;> linarith) (fun i j => by simp only [hq1_def]; split_ifs <;> linarith)
    have hdom := (hi0.add hi1).const_mul ((2 : ℝ) ^ p)
    refine hdom.mono' hmeas (Filter.Eventually.of_forall fun e => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hcol := column_rpow_le_of_pos hp0 (e 0 0) (e 1 0)
    have hbr : (1 + ‖e‖) ^ (-(4 * p + 8)) ≤ ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
      have := bracket_le_prod e (m := p + 2) (by linarith)
      rwa [show -(4 * (p + 2)) = -(4 * p + 8) by ring] at this
    have h0 : ∏ i : Fin 2, ∏ j : Fin 2, |e i j| ^ (q0 i j) * (1 + |e i j|) ^ (-(p + 2)) =
        |e 0 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
      simp only [hq0_def, Fin.prod_univ_two, Fin.isValue]
      simp
      ring
    have h1 : ∏ i : Fin 2, ∏ j : Fin 2, |e i j| ^ (q1 i j) * (1 + |e i j|) ^ (-(p + 2)) =
        |e 1 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
      simp only [hq1_def, Fin.prod_univ_two, Fin.isValue]
      simp
      ring
    simp only [Pi.add_apply]
    rw [h0, h1]
    calc Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * p + 8))
        ≤ ((2 : ℝ) ^ p * (|e 0 0| ^ p + |e 1 0| ^ p)) * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
          gcongr
      _ = (2 : ℝ) ^ p * (|e 0 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) +
            |e 1 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2))) := by ring

end ColumnBracket

end ColumnIntegrability

private theorem integrable_sqrt_col_rpow_mul_one_add_norm_rpow_neg (p : ℝ) (hp : -2 < p) :
    Integrable
      (fun e : Fin 2 → Fin 2 → ℝ =>
        Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8)))
      volume := by
  exact ColumnBracket.integrable_column_rpow_mul_bracket hp

private def integrandT {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (A : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 ψ S (Matrix.of e) T *
    ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (ArchR.diagOne A * (Matrix.of e)⁻¹)

private theorem jacquetIntegrand3_eq_integrandT {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (A : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetIntegrand3 D u₃ a₃ A ψ S g = integrandT D u₃ a₃ A ψ S (StandardKernel.realMat g) :=
  rfl

private theorem continuous_realCoord : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) := by
  show Continuous (fun x : InfiniteAdeleRing ℚ =>
    InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (x Rat.infinitePlace))
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private theorem continuous_realMat : Continuous StandardKernel.realMat := by
  have h : StandardKernel.realMat = fun g : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).map StandardKernel.realCoord :=
    funext StandardKernel.realMat_eq
  rw [h]
  exact Units.continuous_val.matrix_map continuous_realCoord

private theorem det_realMat_ne_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (StandardKernel.realMat g).det ≠ 0 := by
  have hu : IsUnit (StandardKernel.realMat g) := (StandardKernel.realGL g).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

private theorem exists_compact_nhds_of_det_ne_zero (T₀ : Matrix (Fin 3) (Fin 3) ℝ) (hT₀ : T₀.det ≠ 0) :
    ∃ K : Set (Matrix (Fin 3) (Fin 3) ℝ), K ∈ nhds T₀ ∧ IsCompact K ∧ ∀ T ∈ K, T.det ≠ 0 := by
  have hφ : Continuous (fun T : Matrix (Fin 3) (Fin 3) ℝ => (fun i j => T i j : Fin 3 → Fin 3 → ℝ)) :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  have hψ : Continuous (fun M : Fin 3 → Fin 3 → ℝ => Matrix.of M) :=
    continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)
  have hopen : IsOpen {M : Fin 3 → Fin 3 → ℝ | (Matrix.of M).det ≠ 0} :=
    isOpen_ne.preimage (Continuous.matrix_det hψ)
  have hmem : {M : Fin 3 → Fin 3 → ℝ | (Matrix.of M).det ≠ 0} ∈ nhds (fun i j => T₀ i j : Fin 3 → Fin 3 → ℝ) :=
    hopen.mem_nhds hT₀
  obtain ⟨K', hK', hK'sub, hK'c⟩ := local_compact_nhds hmem
  refine ⟨Matrix.of '' K', ?_, hK'c.image hψ, ?_⟩
  · refine Filter.mem_of_superset (hφ.continuousAt.preimage_mem_nhds hK') ?_
    intro T hT
    exact ⟨fun i j => T i j, hT, rfl⟩
  · rintro T ⟨M, hM, rfl⟩
    exact hK'sub hM

private theorem of_inv_lower_line (e : Fin 2 → Fin 2 → ℝ) :
    (Matrix.of e)⁻¹ 1 0 = (Matrix.of e).det⁻¹ * -(e 1 0) ∧ (Matrix.of e)⁻¹ 1 1 = (Matrix.of e).det⁻¹ * e 0 0 := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp

private theorem sqrt_col_pos (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    0 < Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := by
  refine Real.sqrt_pos.2 ?_
  by_contra hcon
  have h00 : e 0 0 = 0 := by nlinarith [sq_nonneg (e 0 0), sq_nonneg (e 1 0)]
  have h10 : e 1 0 = 0 := by nlinarith [sq_nonneg (e 0 0), sq_nonneg (e 1 0)]
  apply he
  rw [Matrix.det_fin_two]
  simp [h00, h10]

private theorem sqrt_col_div_le_norm_inv_lower (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / (2 * |(Matrix.of e).det|) ≤ ‖(Matrix.of e)⁻¹ 1‖ := by
  obtain ⟨h10, h11⟩ := of_inv_lower_line e
  have hd : 0 < |(Matrix.of e).det| := abs_pos.2 he
  have hr0 : |(Matrix.of e).det|⁻¹ * |e 1 0| ≤ ‖(Matrix.of e)⁻¹ 1‖ := by
    have h := norm_le_pi_norm ((Matrix.of e)⁻¹ 1) 0
    rwa [Real.norm_eq_abs, h10, abs_mul, abs_inv, abs_neg] at h
  have hr1 : |(Matrix.of e).det|⁻¹ * |e 0 0| ≤ ‖(Matrix.of e)⁻¹ 1‖ := by
    have h := norm_le_pi_norm ((Matrix.of e)⁻¹ 1) 1
    rwa [Real.norm_eq_abs, h11, abs_mul, abs_inv] at h
  have hsqrt : Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ≤ |e 0 0| + |e 1 0| := by
    rw [show e 0 0 ^ 2 + e 1 0 ^ 2 = |e 0 0| ^ 2 + |e 1 0| ^ 2 by simp [sq_abs]]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [abs_nonneg (e 0 0), abs_nonneg (e 1 0)]
  have h0' : |e 1 0| ≤ |(Matrix.of e).det| * ‖(Matrix.of e)⁻¹ 1‖ := by
    have := mul_le_mul_of_nonneg_left hr0 hd.le
    rwa [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at this
  have h1' : |e 0 0| ≤ |(Matrix.of e).det| * ‖(Matrix.of e)⁻¹ 1‖ := by
    have := mul_le_mul_of_nonneg_left hr1 hd.le
    rwa [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at this
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hsqrt, h0', h1']

private theorem abs_det_le_sqrt_col_mul (e : Fin 2 → Fin 2 → ℝ) :
    |(Matrix.of e).det| ≤ 2 * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * (1 + ‖e‖) := by
  have hdet : (Matrix.of e).det = e 0 0 * e 1 1 - e 0 1 * e 1 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have hρ0 : 0 ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := Real.sqrt_nonneg _
  have h00 : |e 0 0| ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg (e 1 0)])
  have h10 : |e 1 0| ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg (e 0 0)])
  have h11 : |e 1 1| ≤ ‖e‖ := by
    have h1 := norm_le_pi_norm (e 1) 1
    have h2 := norm_le_pi_norm e 1
    rw [Real.norm_eq_abs] at h1
    linarith
  have h01 : |e 0 1| ≤ ‖e‖ := by
    have h1 := norm_le_pi_norm (e 0) 1
    have h2 := norm_le_pi_norm e 0
    rw [Real.norm_eq_abs] at h1
    linarith
  rw [hdet]
  calc |e 0 0 * e 1 1 - e 0 1 * e 1 0| ≤ |e 0 0 * e 1 1| + |e 0 1 * e 1 0| := abs_sub _ _
    _ = |e 0 0| * |e 1 1| + |e 0 1| * |e 1 0| := by rw [abs_mul, abs_mul]
    _ ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * ‖e‖ + ‖e‖ * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := by
        gcongr
    _ ≤ 2 * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * (1 + ‖e‖) := by nlinarith [norm_nonneg e]

private theorem gauge_coords {A : ℝ} (hA : A ≠ 0) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    Real.sqrt ((ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 ^ 2 + (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 ^ 2) =
        Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det| ∧
      |(ArchR.diagOne A * (Matrix.of e)⁻¹).det| /
          ((ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 ^ 2 + (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 ^ 2) =
        |A| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2 ∧
      (ArchR.diagOne A * (Matrix.of e)⁻¹).det ≠ 0 := by
  obtain ⟨h10, h11⟩ := of_inv_lower_line e
  have hx10 : (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 = (Matrix.of e)⁻¹ 1 0 := by
    simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]
  have hx11 : (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 = (Matrix.of e)⁻¹ 1 1 := by
    simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]
  have hxdet : (ArchR.diagOne A * (Matrix.of e)⁻¹).det = A * (Matrix.of e).det⁻¹ := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    congr 1
    rw [Matrix.det_fin_two]
    simp [ArchR.diagOne]
  have hsum : (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 ^ 2 + (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 ^ 2 =
      (e 0 0 ^ 2 + e 1 0 ^ 2) / (Matrix.of e).det ^ 2 := by
    rw [hx10, hx11, h10, h11]
    field_simp
    ring
  have hcol : 0 ≤ e 0 0 ^ 2 + e 1 0 ^ 2 := by positivity
  have hcolpos : 0 < e 0 0 ^ 2 + e 1 0 ^ 2 := by
    have := sqrt_col_pos e he
    exact Real.sqrt_pos.1 this
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, Real.sqrt_div hcol, Real.sqrt_sq_eq_abs]
  · rw [hsum, hxdet, abs_mul, abs_inv, Real.sq_sqrt hcol]
    have hd : |(Matrix.of e).det| ≠ 0 := abs_ne_zero.2 he
    rw [show (Matrix.of e).det ^ 2 = |(Matrix.of e).det| ^ 2 by rw [sq_abs]]
    field_simp
  · rw [hxdet]
    exact mul_ne_zero hA (inv_ne_zero he)

private theorem majorant_core (u γ' q' : ℝ) (N₂ N₃ : ℕ) (hm : 0 ≤ (N₂ : ℝ) + u - γ' - q' - 3)
    (hN₃ : (N₂ : ℝ) + u - γ' - q' - 3 + (4 * max (u + q' - 3) 0 + 8) ≤ N₃)
    {a₀ d ρ x r A : ℝ} (ha₀ : 0 < a₀) (hd : 0 < d) (hρ : 0 < ρ) (hx : 0 ≤ x) (hA : 0 < A)
    (hr : ρ / (2 * d) ≤ r) (hdn : d ≤ 2 * ρ * (1 + x)) :
    d⁻¹ * (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) * d ^ u * (d ^ 2)⁻¹ *
        ((ρ / d) ^ γ' * (A * d / ρ ^ 2) ^ (-q')) ≤
      (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
        (A ^ (-q') * ρ ^ (u + q' - 3) * (1 + x) ^ (-(4 * max (u + q' - 3) 0 + 8))) := by
  have hn0 : 0 < 1 + x := by linarith
  have hn : (1 : ℝ) ≤ 1 + x := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hρr : 0 < a₀ * r := mul_pos ha₀ hr0
  have hX : 0 < 1 + x + a₀ * r := by positivity
  have ha₀' : a₀ ≠ 0 := ha₀.ne'
  have hd' : d ≠ 0 := hd.ne'
  have hρ' : ρ ≠ 0 := hρ.ne'

  have h1 : (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) ≤ (a₀ * r) ^ (-(N₂ : ℝ)) * (1 + x) ^ (-(N₃ : ℝ)) := by
    have hXn : 1 + x ≤ 1 + x + a₀ * r := by linarith
    have hXr : a₀ * r ≤ 1 + x + a₀ * r := by linarith
    rw [Nat.cast_add, neg_add, Real.rpow_add hX]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hρr hXr (by simp)) (Real.rpow_le_rpow_of_nonpos hn0 hXn (by simp))
      (by positivity) (by positivity)

  have hlow : a₀ * (ρ / (2 * d)) ≤ a₀ * r := mul_le_mul_of_nonneg_left hr ha₀.le
  have hpos : 0 < a₀ * (ρ / (2 * d)) := by positivity
  have h2 : (a₀ * r) ^ (-(N₂ : ℝ)) ≤ (2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) := by
    calc (a₀ * r) ^ (-(N₂ : ℝ)) ≤ (a₀ * (ρ / (2 * d))) ^ (-(N₂ : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hlow (by simp)
      _ = (2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) := by
          rw [Real.rpow_neg hpos.le, Real.rpow_neg hρ.le, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast,
            ← inv_pow, ← inv_pow, ← mul_pow, ← mul_pow]
          congr 1
          rw [div_eq_mul_inv, div_eq_mul_inv]
          simp only [mul_inv, inv_inv]
          ring
  have hB : (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) ≤
      (2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) * (1 + x) ^ (-(N₃ : ℝ)) :=
    h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))

  have e1 : (ρ / d) ^ γ' = ρ ^ γ' * d ^ (-γ') := by
    rw [Real.div_rpow hρ.le hd.le, Real.rpow_neg hd.le, div_eq_mul_inv]
  have hAd : 0 ≤ A * d := by positivity
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have e2 : (A * d / ρ ^ 2) ^ (-q') = A ^ (-q') * d ^ (-q') * ρ ^ (2 * q') := by
    rw [Real.div_rpow hAd hρ2, Real.mul_rpow hA.le hd.le, Real.rpow_mul hρ.le, Real.rpow_two, Real.rpow_neg hρ2,
      div_inv_eq_mul]

  have hdm : d⁻¹ * d ^ (N₂ : ℝ) * d ^ u * (d ^ 2)⁻¹ * d ^ (-γ') * d ^ (-q') = d ^ ((N₂ : ℝ) + u - γ' - q' - 3) := by
    rw [← Real.rpow_neg_one d, ← Real.rpow_natCast d 2, ← Real.rpow_neg hd.le, ← Real.rpow_add hd, ← Real.rpow_add hd,
      ← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    push_cast
    ring
  have hρm : ρ ^ (-(N₂ : ℝ)) * ρ ^ γ' * ρ ^ (2 * q') = ρ ^ (γ' + 2 * q' - N₂) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    congr 1
    ring
  have hdet : d ^ ((N₂ : ℝ) + u - γ' - q' - 3) ≤
      2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
        (1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) := by
    have h2ρ : (0 : ℝ) ≤ 2 * ρ := by positivity
    rw [← Real.mul_rpow (by norm_num) hρ.le, ← Real.mul_rpow h2ρ hn0.le]
    exact Real.rpow_le_rpow hd.le hdn hm
  have hρ2m : ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ (γ' + 2 * q' - N₂) = ρ ^ (u + q' - 3) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  have hxm : (1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) * (1 + x) ^ (-(N₃ : ℝ)) ≤
      (1 + x) ^ (-(4 * max (u + q' - 3) 0 + 8)) := by
    rw [← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)

  have hG : 0 ≤ ρ ^ γ' * d ^ (-γ') * (A ^ (-q') * d ^ (-q') * ρ ^ (2 * q')) := by positivity
  calc d⁻¹ * (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) * d ^ u * (d ^ 2)⁻¹ * ((ρ / d) ^ γ' * (A * d / ρ ^ 2) ^ (-q'))
        = d⁻¹ * (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) * d ^ u * (d ^ 2)⁻¹ *
          (ρ ^ γ' * d ^ (-γ') * (A ^ (-q') * d ^ (-q') * ρ ^ (2 * q'))) := by rw [e1, e2]
    _ ≤ d⁻¹ * ((2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) * (1 + x) ^ (-(N₃ : ℝ))) * d ^ u * (d ^ 2)⁻¹ *
          (ρ ^ γ' * d ^ (-γ') * (A ^ (-q') * d ^ (-q') * ρ ^ (2 * q'))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hB (by positivity)) (by positivity)) (by positivity)) hG
    _ = (2 / a₀) ^ N₂ * (d⁻¹ * d ^ (N₂ : ℝ) * d ^ u * (d ^ 2)⁻¹ * d ^ (-γ') * d ^ (-q')) *
          (ρ ^ (-(N₂ : ℝ)) * ρ ^ γ' * ρ ^ (2 * q')) * A ^ (-q') * (1 + x) ^ (-(N₃ : ℝ)) := by ring
    _ = (2 / a₀) ^ N₂ * d ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ (γ' + 2 * q' - N₂) * A ^ (-q') *
          (1 + x) ^ (-(N₃ : ℝ)) := by rw [hdm, hρm]
    _ ≤ (2 / a₀) ^ N₂ *
          (2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
            (1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3)) * ρ ^ (γ' + 2 * q' - N₂) * A ^ (-q') * (1 + x) ^ (-(N₃ : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdet (by positivity)) (by positivity)) (by positivity)) (by positivity)
    _ = (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
          (A ^ (-q') * (ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ (γ' + 2 * q' - N₂)) *
            ((1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) * (1 + x) ^ (-(N₃ : ℝ)))) := by ring
    _ = (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
          (A ^ (-q') * ρ ^ (u + q' - 3) * ((1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) * (1 + x) ^ (-(N₃ : ℝ)))) := by
        rw [hρ2m]
    _ ≤ (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
          (A ^ (-q') * ρ ^ (u + q' - 3) * (1 + x) ^ (-(4 * max (u + q' - 3) 0 + 8))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxm (by positivity)) (by positivity)

private theorem exists_nhds_exists_integrable_forall_norm_integrandT_le
    {P : RealArchParam} (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (D : ArchDatumR P)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (T₀ : Matrix (Fin 3) (Fin 3) ℝ) (hT₀ : T₀.det ≠ 0) (q : ℝ) (hq : max c₀ (-u₃.re) < q) :
    ∃ K ∈ nhds T₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
      ∀ T ∈ K, ∀ A : ℝ, A ≠ 0 → ∀ e : Fin 2 → Fin 2 → ℝ,
        ‖integrandT D u₃ a₃ A psiInf S T e‖ ≤ |A| ^ (1 - q) * F e := by

  set u : ℝ := (u₃ + 2).re with hu_def
  have hure : u = u₃.re + 2 := by simp [hu_def]
  set γ' : ℝ := P.centralExponent.re + 1 with hγ'_def
  set q' : ℝ := q - 1 with hq'_def
  have hq'c₀ : c₀ - 1 ≤ q' := by
    have := le_max_left c₀ (-u₃.re)
    linarith
  have hp : -2 < u + q' - 3 := by
    have := le_max_right c₀ (-u₃.re)
    linarith
  set N₂ : ℕ := ⌈γ' + q' + 3 - u⌉₊ with hN₂_def
  have hm : 0 ≤ (N₂ : ℝ) + u - γ' - q' - 3 := by
    have := Nat.le_ceil (γ' + q' + 3 - u)
    linarith
  set N₃ : ℕ := ⌈(N₂ : ℝ) + u - γ' - q' - 3 + (4 * max (u + q' - 3) 0 + 8)⌉₊ with hN₃_def
  have hN₃ : (N₂ : ℝ) + u - γ' - q' - 3 + (4 * max (u + q' - 3) 0 + 8) ≤ N₃ := Nat.le_ceil _

  obtain ⟨K, hKnhds, hKc, hKdet⟩ := exists_compact_nhds_of_det_ne_zero T₀ hT₀
  obtain ⟨C₁, hC₁⟩ := exists_forall_norm_godementInner3_le a psiInf hpsiInf S hS (N₂ + N₃) K hKc hKdet
  obtain ⟨C₂, hC₂⟩ := archDatumR_exists_forall_norm_W_le_rpow_mul_rpow_of_le D c₀ hc₀ q' hq'c₀
  have ha' : (0 : ℝ) < |(a : ℝ)| := abs_pos.2 (by exact_mod_cast ha)
  set cst : ℝ := max C₁ 0 * max C₂ 0 * ((2 / |(a : ℝ)|) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3)) with hcst_def
  have hcst : 0 ≤ cst := by positivity
  refine ⟨K, hKnhds,
    fun e => cst * (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) * (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8))),
    (integrable_sqrt_col_rpow_mul_one_add_norm_rpow_neg (u + q' - 3) hp).const_mul cst, ?_⟩
  intro T hT A hA e
  have hFnn : 0 ≤ cst * (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) *
      (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8))) :=
    mul_nonneg hcst (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (by positivity) _))
  by_cases he : (Matrix.of e).det = 0
  ·
    have h0 : integrandT D u₃ a₃ A psiInf S T e = 0 := by simp [integrandT, he]
    rw [h0, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (abs_nonneg A) _) hFnn

  have hd : 0 < |(Matrix.of e).det| := abs_pos.2 he
  have hρ : 0 < Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := sqrt_col_pos e he
  have hAabs : 0 < |A| := abs_pos.2 hA
  obtain ⟨hρx, hτx, hxdet⟩ := gauge_coords hA e he
  have hI : ‖godementInner3 psiInf S (Matrix.of e) T‖ ≤
      max C₁ 0 * (|(Matrix.of e).det|⁻¹ *
        (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ))) := by
    have h := hC₁ T hT e he
    calc ‖godementInner3 psiInf S (Matrix.of e) T‖
        ≤ C₁ * |(Matrix.of e).det|⁻¹ *
          (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)) := h
      _ ≤ max C₁ 0 * |(Matrix.of e).det|⁻¹ *
          (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)) := by
          gcongr
          exact le_max_left _ _
      _ = _ := by ring
  have hQ : ‖ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det‖ ≤ |(Matrix.of e).det| ^ u := norm_quasiChar_le _ _ he
  have hJ : ‖(((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)‖ = (|(Matrix.of e).det| ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hW : ‖D.W (ArchR.diagOne A * (Matrix.of e)⁻¹)‖ ≤ max C₂ 0 *
      ((Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
        (|A| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q')) := by
    have h := hC₂ _ hxdet
    rw [hρx, hτx] at h
    calc ‖D.W (ArchR.diagOne A * (Matrix.of e)⁻¹)‖
        ≤ C₂ * (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
          (|A| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q') := h
      _ ≤ max C₂ 0 * (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
          (|A| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q') := by
          gcongr
          exact le_max_left _ _
      _ = _ := by ring
  have hcore := majorant_core u γ' q' N₂ N₃ hm hN₃ ha' hd hρ (norm_nonneg e) hAabs
    (sqrt_col_div_le_norm_inv_lower e he) (abs_det_le_sqrt_col_mul e)
  have hnorm : ‖integrandT D u₃ a₃ A psiInf S T e‖ =
      ‖godementInner3 psiInf S (Matrix.of e) T‖ *
        ‖ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det‖ * ‖(((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)‖ *
          ‖D.W (ArchR.diagOne A * (Matrix.of e)⁻¹)‖ := by
    simp only [integrandT, norm_mul]
  rw [hnorm, hJ]
  calc ‖godementInner3 psiInf S (Matrix.of e) T‖ *
        ‖ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det‖ * (|(Matrix.of e).det| ^ 2)⁻¹ *
          ‖D.W (ArchR.diagOne A * (Matrix.of e)⁻¹)‖
      ≤ (max C₁ 0 * (|(Matrix.of e).det|⁻¹ *
            (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)))) *
          |(Matrix.of e).det| ^ u * (|(Matrix.of e).det| ^ 2)⁻¹ *
            (max C₂ 0 * ((Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
              (|A| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q'))) := by
        gcongr
    _ = max C₁ 0 * max C₂ 0 *
          (|(Matrix.of e).det|⁻¹ * (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)) *
            |(Matrix.of e).det| ^ u * (|(Matrix.of e).det| ^ 2)⁻¹ *
              ((Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
                (|A| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q'))) := by ring
    _ ≤ max C₁ 0 * max C₂ 0 *
          ((2 / |(a : ℝ)|) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
            (|A| ^ (-q') * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) *
              (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8)))) := by
        gcongr
    _ = |A| ^ (1 - q) * (cst * (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) *
          (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8)))) := by
        rw [hcst_def, show (1 : ℝ) - q = -q' by rw [hq'_def]; ring]
        ring

private theorem exists_nhds_exists_integrable_forall_norm_jacquetIntegrand3_le_abs_rpow_mul
    {P : RealArchParam} (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (D : ArchDatumR P)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)) (q : ℝ) (hq : max c₀ (-u₃.re) < q) :
    ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
      ∀ g ∈ U, ∀ A : ℝ, A ≠ 0 → ∀ e : Fin 2 → Fin 2 → ℝ,
        ‖jacquetIntegrand3 D u₃ a₃ A psiInf S g e‖ ≤ |A| ^ (1 - q) * F e := by
  obtain ⟨K, hK, F, hF, hbound⟩ := exists_nhds_exists_integrable_forall_norm_integrandT_le u₃ a₃ a psiInf hpsiInf ha D
    S hS c₀ hc₀ _ (det_realMat_ne_zero g₀) q hq
  refine ⟨StandardKernel.realMat ⁻¹' K, continuous_realMat.continuousAt.preimage_mem_nhds hK, F, hF,
    fun g hg A hA e => ?_⟩
  rw [jacquetIntegrand3_eq_integrandT]
  exact hbound _ hg A hA e

private theorem stronglyMeasurable_godementInner3 (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    StronglyMeasurable (fun e : Fin 2 → Fin 2 → ℝ => godementInner3 psiInf S (Matrix.of e) m) := by
  obtain ⟨Φ, hΦ⟩ := G0.exists_schwartzMap_eq_of_mem_polyGauss3' hS
  have hent : Continuous (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → ℝ) => (fun i b =>
      (Matrix.of p.1 * Matrix.of ![fun b => m 0 b + p.2 0 * m 2 b, fun b => m 1 b + p.2 1 * m 2 b]) i b :
        Fin 2 → Fin 3 → ℝ)) := by
    refine continuous_pi fun i => continuous_pi fun b => ?_
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    fun_prop
  have hchar : Continuous (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      psiInf (StandardKernel.ofReal (-(p.2 1)))) := by
    simp only [psiInf_ofReal_neg a psiInf hpsiInf]
    fun_prop
  have hcont : Continuous (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      S (Matrix.of p.1 * Matrix.of ![fun b => m 0 b + p.2 0 * m 2 b, fun b => m 1 b + p.2 1 * m 2 b]) *
        psiInf (StandardKernel.ofReal (-(p.2 1)))) := by
    have hS' : ∀ p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → ℝ),
        S (Matrix.of p.1 * Matrix.of ![fun b => m 0 b + p.2 0 * m 2 b, fun b => m 1 b + p.2 1 * m 2 b]) =
          Φ (fun i b =>
            (Matrix.of p.1 * Matrix.of ![fun b => m 0 b + p.2 0 * m 2 b, fun b => m 1 b + p.2 1 * m 2 b]) i b) :=
      fun p => (hΦ _).symm
    simp only [hS']
    exact (Φ.continuous.comp hent).mul hchar
  unfold godementInner3
  exact hcont.stronglyMeasurable.integral_prod_right'

private theorem continuousOn_quasiChar (u : ℂ) (b : ZMod 2) :
    ContinuousOn (ArchR.quasiChar u b) {y : ℝ | y ≠ 0} := by
  intro y hy
  have hy' : (y : ℝ) ≠ 0 := hy
  apply ContinuousAt.continuousWithinAt
  unfold ArchR.quasiChar
  refine ContinuousAt.mul ?_ ?_
  · have hbase : ContinuousAt (fun y : ℝ => ((|y| : ℝ) : ℂ)) y :=
      (Complex.continuous_ofReal.comp continuous_abs).continuousAt
    refine ContinuousAt.comp (g := fun z : ℂ => z ^ u) ?_ hbase
    exact continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 (abs_pos.2 hy'))
  · split_ifs
    · exact continuousAt_const
    · exact ((continuous_of_discreteTopology (f := fun s : SignType => ((s : ℝ) : ℂ))).continuousAt).comp
        (continuousAt_sign_of_ne_zero hy')

private theorem continuousOn_arrayFactors {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) :
    ContinuousOn
      (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of p.2).det *
        (((|(Matrix.of p.2).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (ArchR.diagOne p.1 * (Matrix.of p.2)⁻¹))
      {p : ℝ × (Fin 2 → Fin 2 → ℝ) | p.1 ≠ 0 ∧ (Matrix.of p.2).det ≠ 0} := by
  have hdet : Continuous (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => (Matrix.of p.2).det) := by
    exact Continuous.matrix_det (by fun_prop)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact (continuousOn_quasiChar (u₃ + 2) a₃).comp hdet.continuousOn fun p hp => hp.2
  · refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact ((hdet.abs.pow 2).continuousOn).inv₀ fun p hp => by
      exact pow_ne_zero 2 (abs_ne_zero.2 hp.2)
  ·

    have hdiag : Continuous (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => ArchR.diagOne p.1) := by
      unfold ArchR.diagOne
      fun_prop
    have hsnd : Continuous (fun q : ℝ × (Fin 2 → Fin 2 → ℝ) => Matrix.of q.2) := by fun_prop
    have hprod : ContinuousOn (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) =>
        Matrix.of.symm (ArchR.diagOne p.1 * (Matrix.of p.2)⁻¹))
        {p : ℝ × (Fin 2 → Fin 2 → ℝ) | p.1 ≠ 0 ∧ (Matrix.of p.2).det ≠ 0} := by
      refine continuousOn_of_forall_continuousAt fun p hp => ?_
      have h1 : ContinuousAt (Inv.inv : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Matrix.of p.2) :=
        continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt (Units.mk0 _ hp.2))
      have h2 : ContinuousAt (fun q : ℝ × (Fin 2 → Fin 2 → ℝ) => (Matrix.of q.2)⁻¹) p :=
        ContinuousAt.comp (g := (Inv.inv : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ))
          (f := fun q : ℝ × (Fin 2 → Fin 2 → ℝ) => Matrix.of q.2) (x := p) h1 hsnd.continuousAt
      have h3 : ContinuousAt (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => ArchR.diagOne p.1 * (Matrix.of p.2)⁻¹) p :=
        hdiag.continuousAt.mul h2
      exact h3
    have hmaps : Set.MapsTo (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => Matrix.of.symm (ArchR.diagOne p.1 * (Matrix.of p.2)⁻¹))
        {p : ℝ × (Fin 2 → Fin 2 → ℝ) | p.1 ≠ 0 ∧ (Matrix.of p.2).det ≠ 0} ArchR.glSet := by
      intro p hp
      show (ArchR.diagOne p.1 * (Matrix.of p.2)⁻¹).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact mul_ne_zero (by simpa [ArchR.diagOne] using hp.1) (inv_ne_zero hp.2)
    have hW := D.smooth.continuousOn.comp hprod hmaps
    exact hW

private theorem aestronglyMeasurable_integrandT {P : RealArchParam} (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (D : ArchDatumR P)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (T : Matrix (Fin 3) (Fin 3) ℝ) :
    AEStronglyMeasurable (integrandT D u₃ a₃ (a : ℝ) psiInf S T) volume := by
  have hmeasU : MeasurableSet {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} :=
    (isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Fin 2 → Fin 2 → ℝ)))).measurableSet
  have hF : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det *
      (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹))
      {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} := by
    have hslice : Continuous (fun e : Fin 2 → Fin 2 → ℝ => ((a : ℝ), e)) := by fun_prop
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℝ => ((a : ℝ), e)) {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0}
        {p : ℝ × (Fin 2 → Fin 2 → ℝ) | p.1 ≠ 0 ∧ (Matrix.of p.2).det ≠ 0} := fun e he => ⟨ha', he⟩
    have hcomp := ContinuousOn.comp
      (g := fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of p.2).det *
        (((|(Matrix.of p.2).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (ArchR.diagOne p.1 * (Matrix.of p.2)⁻¹))
      (f := fun e : Fin 2 → Fin 2 → ℝ => ((a : ℝ), e)) (continuousOn_arrayFactors D u₃ a₃) hslice.continuousOn hmaps
    exact hcomp
  have hpw : Measurable ({e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0}.piecewise
      (fun e : Fin 2 → Fin 2 → ℝ => ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det *
        (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) (fun _ => (0 : ℂ))) :=
    hF.measurable_piecewise continuousOn_const hmeasU
  have heq : integrandT D u₃ a₃ (a : ℝ) psiInf S T = fun e =>
      godementInner3 psiInf S (Matrix.of e) T *
        {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0}.piecewise
          (fun e : Fin 2 → Fin 2 → ℝ => ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det *
            (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹))
          (fun _ => (0 : ℂ)) e := by
    funext e
    by_cases he : (Matrix.of e).det = 0
    · simp [integrandT, Set.piecewise, he]
    · have he' : e ∈ {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} := he
      simp only [integrandT, Set.piecewise, he', if_true, mul_assoc]
  rw [heq]
  exact ((stronglyMeasurable_godementInner3 a psiInf hpsiInf S hS _).measurable.mul hpw).aestronglyMeasurable

private theorem aestronglyMeasurable_jacquetIntegrand3 {P : RealArchParam} (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (D : ArchDatumR P)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g) volume := by
  rw [jacquetIntegrand3_eq_integrandT]
  exact aestronglyMeasurable_integrandT u₃ a₃ a psiInf hpsiInf ha D S hS _

private theorem aestronglyMeasurable_prod_jacquetIntegrand3 {P : RealArchParam} (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (D : ArchDatumR P)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    AEStronglyMeasurable
      (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => jacquetIntegrand3 D u₃ a₃ p.1 psiInf S g p.2) (volume.prod volume) := by
  have _ := ha
  set U : Set (ℝ × (Fin 2 → Fin 2 → ℝ)) := {p | p.1 ≠ 0 ∧ (Matrix.of p.2).det ≠ 0} with hU
  have hUopen : IsOpen U := by
    have h1 : IsOpen {p : ℝ × (Fin 2 → Fin 2 → ℝ) | p.1 ≠ 0} := isOpen_ne.preimage continuous_fst
    have h2 : IsOpen {p : ℝ × (Fin 2 → Fin 2 → ℝ) | (Matrix.of p.2).det ≠ 0} :=
      isOpen_ne.preimage (Continuous.matrix_det (by fun_prop))
    exact h1.inter h2
  set F : ℝ × (Fin 2 → Fin 2 → ℝ) → ℂ := fun p => ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of p.2).det *
    (((|(Matrix.of p.2).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (ArchR.diagOne p.1 * (Matrix.of p.2)⁻¹) with hF
  have hpw : Measurable (U.piecewise F (fun _ => (0 : ℂ))) :=
    (continuousOn_arrayFactors D u₃ a₃).measurable_piecewise continuousOn_const hUopen.measurableSet
  have hG : Measurable (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) =>
      godementInner3 psiInf S (Matrix.of p.2) (StandardKernel.realMat g)) :=
    (stronglyMeasurable_godementInner3 a psiInf hpsiInf S hS _).measurable.comp measurable_snd

  have hnull : (volume.prod volume : Measure (ℝ × (Fin 2 → Fin 2 → ℝ))) ({(0 : ℝ)} ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, Real.volume_singleton, zero_mul]
  refine (hG.mul hpw).aestronglyMeasurable.congr ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun p hp => ?_) hnull
  simp only [Set.mem_setOf_eq] at hp
  by_contra hp1
  apply hp
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hp1
  by_cases he : (Matrix.of p.2).det = 0
  · have hpU : p ∉ U := fun h => h.2 he
    simp [jacquetIntegrand3, Set.piecewise, he, hpU]
  · have hpU : p ∈ U := ⟨hp1, he⟩
    simp only [jacquetIntegrand3, Pi.mul_apply, Set.piecewise, hpU, if_true, hF, mul_assoc]

private theorem exists_norm_le_mul_norm_mulVec (h : Fin 2 → Fin 2 → ℝ) (hh : (Matrix.of h).det ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ c * ‖(Matrix.of h).mulVec v‖ := by
  set L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.of h)⁻¹) with hL
  refine ⟨‖L‖, norm_nonneg _, fun v => ?_⟩
  have hv : L ((Matrix.of h).mulVec v) = v := by
    simp only [hL, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hh), Matrix.one_mulVec]
  calc ‖v‖ = ‖L ((Matrix.of h).mulVec v)‖ := by rw [hv]
    _ ≤ ‖L‖ * ‖(Matrix.of h).mulVec v‖ := L.le_opNorm _

private theorem continuous_rmul_left (X : Fin 2 → Fin 3 → ℝ) :
    Continuous (fun T : Matrix (Fin 3) (Fin 3) ℝ => G0.rmul T X) := by
  unfold G0.rmul
  exact continuous_pi fun i => continuous_pi fun b => (continuous_const.matrix_mul continuous_id).matrix_elem i b

private theorem continuous_inner_integrand (Φ : SchwartzMap (Fin 2 → Fin 3 → ℝ) ℂ) (h : Fin 2 → Fin 2 → ℝ)
    (T : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) :
    Continuous (fun v : Fin 2 → ℝ => Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) *
      Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) := by
  have h1 : Continuous (fun v : Fin 2 → ℝ => G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) := by
    have hfun : (fun v : Fin 2 → ℝ => G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) =
        fun v => G0.sliceLin T ((Matrix.of h).mulVec v) + G0.rmul T (G0.blk h 0) :=
      funext fun v => G0.rmul_blk_eq T h _
    rw [hfun]
    exact ((G0.sliceLin T).continuous.comp (continuous_const.matrix_mulVec continuous_id)).add continuous_const
  have h2 : Continuous (fun v : Fin 2 → ℝ => Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) := by
    refine Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
    exact (continuous_const.mul (continuous_apply 1)).neg
  exact (Φ.continuous.comp h1).mul h2

private theorem one_add_pow_three_le (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 3 ≤ 4 * (1 + t ^ 3) := by
  nlinarith [mul_nonneg (sq_nonneg (t - 1)) (by linarith : (0 : ℝ) ≤ t + 1)]

private theorem continuousAt_godementInner3_right (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (h : Fin 2 → Fin 2 → ℝ) (hh : (Matrix.of h).det ≠ 0) (T₀ : Matrix (Fin 3) (Fin 3) ℝ) (hT₀ : T₀.det ≠ 0) :
    ContinuousAt (fun T : Matrix (Fin 3) (Fin 3) ℝ => godementInner3 psiInf S (Matrix.of h) T) T₀ := by
  obtain ⟨Φ, hΦ⟩ := G0.exists_schwartzMap_eq_of_mem_polyGauss3' hS
  obtain ⟨K, hK, hKc, hKdet⟩ := exists_compact_nhds_of_det_ne_zero T₀ hT₀
  obtain ⟨C₀, -, hC₀⟩ := G0.exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Φ K hKc hKdet 0 0 0
  obtain ⟨C₃, -, hC₃⟩ := G0.exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Φ K hKc hKdet 3 0 0
  obtain ⟨c, hc0, hc⟩ := exists_norm_le_mul_norm_mulVec h hh
  have hform : (fun T : Matrix (Fin 3) (Fin 3) ℝ => godementInner3 psiInf S (Matrix.of h) T) = fun T =>
      ∫ v : Fin 2 → ℝ, Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) *
        Complex.exp (((-(2 * Real.pi * (a : ℝ) * v 1) : ℝ) : ℂ) * Complex.I) :=
    funext fun T => godementInner3_eq_integral a psiInf hpsiInf S Φ hΦ h T
  rw [hform]
  have hfin : ((Module.finrank ℝ (Fin 2 → ℝ) : ℕ) : ℝ) < ((3 : ℕ) : ℝ) := by
    simp only [Module.finrank_fin_fun]
    norm_num
  haveI : FirstCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → ℝ))
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun v : Fin 2 → ℝ => 4 * (C₀ + c ^ 3 * C₃) * (1 + ‖v‖) ^ (-((3 : ℕ) : ℝ))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun T => (continuous_inner_integrand Φ h T (a : ℝ)).aestronglyMeasurable
  ·
    refine Filter.mem_of_superset hK fun T hT => MeasureTheory.ae_of_all _ fun v => ?_
    have h0 := hC₀ T hT h ((Matrix.of h).mulVec v)
    have h3 := hC₃ T hT h ((Matrix.of h).mulVec v)
    simp only [pow_zero, one_mul, inv_one, mul_one, norm_iteratedFDeriv_zero] at h0 h3
    have hφ0 : 0 ≤ ‖Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v)))‖ := norm_nonneg _
    have hv3 : ‖v‖ ^ 3 ≤ c ^ 3 * ‖(Matrix.of h).mulVec v‖ ^ 3 := by
      have := pow_le_pow_left₀ (norm_nonneg v) (hc v) 3
      rwa [mul_pow] at this
    have hcube := one_add_pow_three_le ‖v‖ (norm_nonneg v)
    have hpos : (0 : ℝ) < (1 + ‖v‖) ^ 3 := by positivity
    beta_reduce
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖v‖),
      Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v)))‖ * (1 + ‖v‖) ^ 3
        ≤ ‖Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v)))‖ * (4 * (1 + ‖v‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hcube hφ0
      _ = 4 * (‖Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v)))‖ +
            ‖v‖ ^ 3 * ‖Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v)))‖) := by ring
      _ ≤ 4 * (C₀ + c ^ 3 * ‖(Matrix.of h).mulVec v‖ ^ 3 * ‖Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v)))‖) := by
          gcongr
      _ = 4 * (C₀ + c ^ 3 * (‖(Matrix.of h).mulVec v‖ ^ 3 * ‖Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v)))‖)) := by
          ring
      _ ≤ 4 * (C₀ + c ^ 3 * C₃) := by gcongr
  · exact (integrable_one_add_norm hfin).const_mul _
  · refine MeasureTheory.ae_of_all _ fun v => ?_
    exact ((Φ.continuous.comp (continuous_rmul_left _)).mul continuous_const).continuousAt

end LanglandsTunnell.CubicInduction

end

end

open NumberField AutomorphicForm LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.jacquetIntegrand3 RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "polyGauss3 godementInner3 jacquetIntegrand3"
namespace JacquetJoint
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory Set

private theorem measurable_signCast : Measurable fun y : ℝ => ((SignType.sign y : ℝ) : ℂ) := by
  have h : (fun y : ℝ => ((SignType.sign y : ℝ) : ℂ)) =
      fun y => if y < 0 then (-1 : ℂ) else if 0 < y then 1 else 0 := by
    funext y
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [sign_neg hy, if_pos hy]; simp
    · simp
    · rw [sign_pos hy, if_neg (not_lt.mpr hy.le), if_pos hy]; simp
  rw [h]
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

private theorem measurable_absCpow (u : ℂ) : Measurable fun y : ℝ => ((|y| : ℝ) : ℂ) ^ u :=
  (Complex.measurable_ofReal.comp measurable_abs).pow_const u

private theorem measurable_quasiChar (u : ℂ) (a : ZMod 2) : Measurable (ArchR.quasiChar u a) := by
  unfold ArchR.quasiChar
  by_cases ha : a = 0
  · simp only [ha, if_true, mul_one]; exact measurable_absCpow u
  · simp only [ha, if_false]; exact (measurable_absCpow u).mul measurable_signCast

private theorem norm_absCpow (u : ℂ) {y : ℝ} (hy : y ≠ 0) : ‖((|y| : ℝ) : ℂ) ^ u‖ = |y| ^ u.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hy) u

private theorem norm_quasiChar (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : y ≠ 0) : ‖ArchR.quasiChar u a y‖ = |y| ^ u.re := by
  unfold ArchR.quasiChar
  rw [norm_mul, norm_absCpow u hy]
  by_cases ha : a = 0
  · simp [ha]
  · simp only [ha, if_false]
    rcases hy.lt_or_gt with h | h
    · rw [sign_neg h]; simp
    · rw [sign_pos h]; simp

private theorem integrableOn_abs_rpow_Icc {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-1) 1) := by

  have h01 : IntegrableOn (fun y : ℝ => |y| ^ r) (Icc 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' hr (a := 0) (b := 1))
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at h
    refine h.congr_fun (fun y hy => ?_) measurableSet_Icc
    rw [abs_of_nonneg hy.1]
  have h10 : IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-1) 0) := by
    have hneg : (Icc (-1 : ℝ) 0) = Neg.neg ⁻¹' (Icc (0 : ℝ) 1) := by
      ext y; simp only [mem_Icc, mem_preimage]; constructor <;> intro h <;> constructor <;> linarith
    rw [hneg]
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
    have := (hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding).mpr h01
    simpa only [Function.comp_def, abs_neg] using this
  have hU : Icc (-1 : ℝ) 1 = Icc (-1) 0 ∪ Icc 0 1 := by
    ext y; simp only [mem_Icc, mem_union]; constructor
    · intro h; rcases le_total y 0 with hy | hy
      · exact Or.inl ⟨h.1, hy⟩
      · exact Or.inr ⟨hy, h.2⟩
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
  rw [hU]
  exact h10.union h01

private theorem integrableOn_abs_rpow_compl_Icc {r : ℝ} (hr : r < -1) :
    IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-1) 1)ᶜ := by
  have hIoi : IntegrableOn (fun y : ℝ => |y| ^ r) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt hr zero_lt_one).congr_fun (fun y hy => ?_) measurableSet_Ioi
    rw [abs_of_pos (lt_trans zero_lt_one hy)]
  have hIio : IntegrableOn (fun y : ℝ => |y| ^ r) (Iio (-1)) := by
    have hneg : (Iio (-1 : ℝ)) = Neg.neg ⁻¹' (Ioi (1 : ℝ)) := by
      ext y; simp only [mem_Iio, mem_preimage, mem_Ioi]; constructor <;> intro h <;> linarith
    rw [hneg]
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
    have := (hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding).mpr hIoi
    simpa only [Function.comp_def, abs_neg] using this
  have hU : (Icc (-1 : ℝ) 1)ᶜ = Iio (-1) ∪ Ioi 1 := by
    ext y; simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  rw [hU]
  exact hIio.union hIoi

private theorem integrable_indicator_abs_rpow_inner {r : ℝ} (hr : -1 < r) :
    Integrable ((Icc (-1 : ℝ) 1).indicator fun y : ℝ => |y| ^ r) volume :=
  (integrableOn_abs_rpow_Icc hr).integrable_indicator measurableSet_Icc

private theorem integrable_indicator_abs_rpow_outer {r : ℝ} (hr : r < -1) :
    Integrable ((Icc (-1 : ℝ) 1)ᶜ.indicator fun y : ℝ => |y| ^ r) volume :=
  (integrableOn_abs_rpow_compl_Icc hr).integrable_indicator measurableSet_Icc.compl

private theorem quasiMeasurePreserving_dilate {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    (a : ℝ) (ha : a ≠ 0) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × X => (a * p.1, p.2)) (volume.prod ν) (volume.prod ν) := by
  have h1 : MeasurePreserving (fun y : ℝ => a * y) volume (ENNReal.ofReal |a⁻¹| • volume) :=
    ⟨measurable_const_mul a, Real.map_volume_mul_left ha⟩
  have h2 : MeasurePreserving (fun p : ℝ × X => (a * p.1, p.2)) (volume.prod ν)
      ((ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ)).prod ν) :=
    h1.prod (MeasurePreserving.id ν)
  refine ⟨h2.measurable, ?_⟩
  rw [h2.map_eq, Measure.prod_smul_left]
  exact Measure.smul_absolutelyContinuous

private theorem close {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    (J : ℝ → X → ℂ) (a : ℝ) (ha : a ≠ 0) (thr σ : ℝ) (hσ : thr < σ)
    (hexp : ∀ q : ℝ, thr < q → ∃ F : X → ℝ, Integrable F ν ∧ ∀ A : ℝ, A ≠ 0 → ∀ e, ‖J A e‖ ≤ |A| ^ (1 - q) * F e)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × X => J p.1 p.2) (volume.prod ν))
    (t s : ℂ) (hts : s.re + t.re = σ) (ē : ZMod 2) :
    Integrable (fun p : ℝ × X =>
      J (a * p.1) p.2 * ArchR.quasiChar t ē p.1 * ((|p.1| : ℝ) : ℂ) ^ (s - 1) * ((|p.1| : ℝ) : ℂ)⁻¹)
      (volume.prod ν) := by

  obtain ⟨F₁, hF₁, hb₁⟩ := hexp ((thr + σ) / 2) (by linarith)
  obtain ⟨F₂, hF₂, hb₂⟩ := hexp (σ + 1) (by linarith)
  set q₁ : ℝ := (thr + σ) / 2 with hq₁
  set q₂ : ℝ := σ + 1 with hq₂

  set G : ℝ × X → ℝ := fun p =>
    |a| ^ (1 - q₁) * (Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y| ^ (σ - q₁ - 1)) p.1 * F₁ p.2 +
      |a| ^ (1 - q₂) * (Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ => |y| ^ (σ - q₂ - 1)) p.1 * F₂ p.2 with hG
  have hGi : Integrable G (volume.prod ν) := by
    have i1 := ((integrable_indicator_abs_rpow_inner (r := σ - q₁ - 1) (by rw [hq₁]; linarith)).const_mul
      (|a| ^ (1 - q₁))).mul_prod hF₁
    have i2 := ((integrable_indicator_abs_rpow_outer (r := σ - q₂ - 1) (by rw [hq₂]; linarith)).const_mul
      (|a| ^ (1 - q₂))).mul_prod hF₂
    exact i1.add i2

  have hm : AEStronglyMeasurable (fun p : ℝ × X =>
      J (a * p.1) p.2 * ArchR.quasiChar t ē p.1 * ((|p.1| : ℝ) : ℂ) ^ (s - 1) * ((|p.1| : ℝ) : ℂ)⁻¹)
    (volume.prod ν) := by
    have hJ : AEStronglyMeasurable (fun p : ℝ × X => J (a * p.1) p.2) (volume.prod ν) :=
      hmeas.comp_quasiMeasurePreserving (quasiMeasurePreserving_dilate ν a ha)
    have hw : Measurable fun p : ℝ × X =>
        ArchR.quasiChar t ē p.1 * ((|p.1| : ℝ) : ℂ) ^ (s - 1) * ((|p.1| : ℝ) : ℂ)⁻¹ :=
      (((measurable_quasiChar t ē).comp measurable_fst).mul ((measurable_absCpow (s - 1)).comp measurable_fst)).mul
        ((Complex.measurable_ofReal.comp (measurable_abs.comp measurable_fst)).inv)
    have := hJ.mul hw.aestronglyMeasurable
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]; ring

  refine hGi.mono' hm ?_
  have hnull : ∀ᵐ p : ℝ × X ∂(volume.prod ν), p.1 ≠ 0 := by
    rw [ae_iff]
    have hs : {p : ℝ × X | ¬p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (univ : Set X) := by
      ext p; simp
    rw [hs, Measure.prod_prod, Real.volume_singleton, zero_mul]
  filter_upwards [hnull] with p hp
  have hA : a * p.1 ≠ 0 := mul_ne_zero ha hp
  have ypos : 0 < |p.1| := abs_pos.mpr hp
  have hw : |p.1| ^ t.re * |p.1| ^ (s - 1).re * |p.1|⁻¹ = |p.1| ^ (σ - 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ypos, ← Real.rpow_add ypos, Complex.sub_re, Complex.one_re]
    congr 1; linarith
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_abs, norm_absCpow _ hp,
    norm_quasiChar _ _ hp, mul_assoc, mul_assoc, ← mul_assoc (|p.1| ^ t.re), hw]
  by_cases hy1 : |p.1| ≤ 1
  · have hin : p.1 ∈ Icc (-1 : ℝ) 1 := ⟨(abs_le.mp hy1).1, (abs_le.mp hy1).2⟩
    have hnot : p.1 ∉ (Icc (-1 : ℝ) 1)ᶜ := fun h => h hin
    have hJ : ‖J (a * p.1) p.2‖ ≤ |a| ^ (1 - q₁) * |p.1| ^ (1 - q₁) * F₁ p.2 := by
      have := hb₁ (a * p.1) hA p.2
      rwa [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg p.1)] at this
    have hGp : G p = |a| ^ (1 - q₁) * |p.1| ^ (σ - q₁ - 1) * F₁ p.2 := by
      simp only [hG, indicator_of_mem hin, indicator_of_notMem hnot, mul_zero, zero_mul, add_zero]
    rw [hGp]
    calc ‖J (a * p.1) p.2‖ * |p.1| ^ (σ - 2)
        ≤ |a| ^ (1 - q₁) * |p.1| ^ (1 - q₁) * F₁ p.2 * |p.1| ^ (σ - 2) :=
          mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg (abs_nonneg _) _)
      _ = |a| ^ (1 - q₁) * |p.1| ^ (σ - q₁ - 1) * F₁ p.2 := by
          rw [show σ - q₁ - 1 = (1 - q₁) + (σ - 2) by ring, Real.rpow_add ypos]; ring
  · have hout : p.1 ∈ (Icc (-1 : ℝ) 1)ᶜ := by
      intro h; exact hy1 (abs_le.mpr ⟨h.1, h.2⟩)
    have hnot : p.1 ∉ Icc (-1 : ℝ) 1 := hout
    have hJ : ‖J (a * p.1) p.2‖ ≤ |a| ^ (1 - q₂) * |p.1| ^ (1 - q₂) * F₂ p.2 := by
      have := hb₂ (a * p.1) hA p.2
      rwa [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg p.1)] at this
    have hGp : G p = |a| ^ (1 - q₂) * |p.1| ^ (σ - q₂ - 1) * F₂ p.2 := by
      simp only [hG, indicator_of_mem hout, indicator_of_notMem hnot, mul_zero, zero_mul, zero_add]
    rw [hGp]
    calc ‖J (a * p.1) p.2‖ * |p.1| ^ (σ - 2)
        ≤ |a| ^ (1 - q₂) * |p.1| ^ (1 - q₂) * F₂ p.2 * |p.1| ^ (σ - 2) :=
          mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg (abs_nonneg _) _)
      _ = |a| ^ (1 - q₂) * |p.1| ^ (σ - q₂ - 1) * F₂ p.2 := by
          rw [show σ - q₂ - 1 = (1 - q₂) + (σ - 2) by ring, Real.rpow_add ypos]; ring

end LanglandsTunnell.CubicInduction.JacquetJoint

open scoped Classical in
open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar.LanglandsTunnell.CubicInduction in

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
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀)) :
    ∀ (t : ℂ) (e : ℤ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ),
      max c₀ (-(uR w₀ h₀).re) - t.re < s.re →
      MeasureTheory.Integrable
        (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) =>
          jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) ((a : ℝ) * p.1) psiInf S gInf p.2 *
            ArchR.quasiChar t (e : ZMod 2) p.1 * ((|p.1| : ℝ) : ℂ) ^ (s - 1) * ((|p.1| : ℝ) : ℂ)⁻¹)
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
  intro t e gInf s hreg
  have _ := hdeg
  have _ := hμ
  have _ := huR
  have _ := huC
  have _ := hω
  have _ := hE
  have _ := haInf
  have _ := mA
  have _ := mT
  have _ := hν_add
  have _ := hP₂
  have hσ : max c₀ (-(uR w₀ h₀).re) < s.re + t.re := by linarith
  have hexp : ∀ q : ℝ, max c₀ (-(uR w₀ h₀).re) < q → ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ,
      MeasureTheory.Integrable F MeasureTheory.volume ∧ ∀ A : ℝ, A ≠ 0 → ∀ x : Fin 2 → Fin 2 → ℝ,
        ‖LanglandsTunnell.CubicInduction.jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) A psiInf S gInf x‖ ≤
          |A| ^ (1 - q) * F x := by
    intro q hq
    obtain ⟨U, hU, F, hF, hb⟩ :=
      LanglandsTunnell.CubicInduction.exists_nhds_exists_integrable_forall_norm_jacquetIntegrand3_le_abs_rpow_mul
        (uR w₀ h₀) (aR w₀ h₀) a psiInf hpsiInf ha D S hS c₀ hc₀ gInf q hq
    exact ⟨F, hF, hb gInf (mem_of_mem_nhds hU)⟩
  have hmeas :=
    LanglandsTunnell.CubicInduction.aestronglyMeasurable_prod_jacquetIntegrand3 (uR w₀ h₀) (aR w₀ h₀) a psiInf
      hpsiInf ha D S hS gInf
  exact LanglandsTunnell.CubicInduction.JacquetJoint.close MeasureTheory.volume
    (fun A x => LanglandsTunnell.CubicInduction.jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) A psiInf S gInf x) (a : ℝ)
    (Rat.cast_ne_zero.mpr ha) _ _ hσ hexp hmeas t s rfl (e : ZMod 2)

end S_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar (solution)
