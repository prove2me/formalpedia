-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7c752d35-6669-52af-977a-70cc25dd7e65

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul
p2m_attr_erase "instance" "LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false

open NumberField LanglandsTunnell.Converse

noncomputable section

open MeasureTheory LanglandsTunnell.Converse.ArchR AutomorphicForm.StandardKernel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.centralExponent RealArchParam.centralSign RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq apply_of_infPart_eq_of_isArchCompAt"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem sign_cases {c : ℝ} (hc : c ≠ 0) :
    ((SignType.sign c : ℝ) : ℂ) = 1 ∨ ((SignType.sign c : ℝ) : ℂ) = -1 := by
  rcases hc.lt_or_gt with h | h
  · right; simp [h]
  · left; simp [h]

private theorem zmod_two_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide

private theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private theorem quasiChar_zero_apply (u : ℂ) (c : ℝ) : quasiChar u 0 c = ((|c| : ℝ) : ℂ) ^ u := by
  simp [quasiChar]

private theorem quasiChar_one_apply (u : ℂ) (c : ℝ) :
    quasiChar u 1 c = ((|c| : ℝ) : ℂ) ^ u * ((SignType.sign c : ℝ) : ℂ) := by
  simp [quasiChar]

private theorem quasiChar_add_of_ne_zero (u u' : ℂ) (b b' : ZMod 2) {c : ℝ} (hc : c ≠ 0) :
    quasiChar u b c * quasiChar u' b' c = quasiChar (u + u') (b + b') c := by
  have habs : ((|c| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hc
  have hsq : ((SignType.sign c : ℝ) : ℂ) * ((SignType.sign c : ℝ) : ℂ) = 1 := by
    rcases sign_cases hc with h | h <;> rw [h] <;> norm_num
  rcases zmod_two_cases b with rfl | rfl <;> rcases zmod_two_cases b' with rfl | rfl
  · rw [zero_add, quasiChar_zero_apply, quasiChar_zero_apply, quasiChar_zero_apply, Complex.cpow_add _ _ habs]
  · rw [zero_add, quasiChar_zero_apply, quasiChar_one_apply, quasiChar_one_apply, Complex.cpow_add _ _ habs]
    ring
  · rw [add_zero, quasiChar_one_apply, quasiChar_zero_apply, quasiChar_one_apply, Complex.cpow_add _ _ habs]
    ring
  · rw [zmod_two_one_add_one, quasiChar_one_apply, quasiChar_one_apply, quasiChar_zero_apply,
      Complex.cpow_add _ _ habs]
    linear_combination (((|c| : ℝ) : ℂ) ^ u * ((|c| : ℝ) : ℂ) ^ u') * hsq

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

private theorem quasiChar_sq (u : ℂ) (b : ZMod 2) {c : ℝ} (hc : c ≠ 0) :
    quasiChar u b (c * c) = quasiChar (2 * u) 0 c := by
  rw [quasiChar_mul_arg u b c c, quasiChar_add_of_ne_zero _ _ _ _ hc, two_mul]
  rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [zmod_two_one_add_one]

private theorem quasiChar_cube (u : ℂ) (b : ZMod 2) {c : ℝ} (hc : c ≠ 0) :
    quasiChar u b (c * c * c) = quasiChar (3 * u) b c := by
  rw [quasiChar_mul_arg u b (c * c) c, quasiChar_sq u b hc, quasiChar_add_of_ne_zero _ _ _ _ hc,
    zero_add]
  congr 1
  ring

private theorem quasiChar_zero_sign (u : ℂ) (c : ℝ) : quasiChar u 0 c = ((|c| : ℝ) : ℂ) ^ u := by
  simp [quasiChar]

private theorem quasiChar_neg_four (c : ℝ) : quasiChar (-4) 0 c = (((|c| ^ 4)⁻¹ : ℝ) : ℂ) := by
  rw [quasiChar_zero_sign, show (-4 : ℂ) = -((4 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rfl

private theorem quasiChar_one_zero (c : ℝ) : quasiChar 1 0 c = ((|c| : ℝ) : ℂ) := by
  rw [quasiChar_zero_sign, Complex.cpow_one]

private theorem realMat_scalar_mul (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    realMat (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = realCoord (z : InfiniteAdeleRing ℚ) • realMat g := by
  rw [realMat_mul]
  have hs : realMat (Matrix.GeneralLinearGroup.scalar (Fin 3) z) =
      Matrix.diagonal fun _ => realCoord (z : InfiniteAdeleRing ℚ) := by
    rw [realMat_eq]
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [hs, ← Matrix.smul_eq_diagonal_mul]

private theorem realCoord_unit_ne_zero (z : (InfiniteAdeleRing ℚ)ˣ) : realCoord (z : InfiniteAdeleRing ℚ) ≠ 0 := by
  intro h
  have h1 : realCoord ((z : InfiniteAdeleRing ℚ) * ((z⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)) = 1 := by
    rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem godementInner3_smul (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 ψ S h (c • m) = godementInner3 ψ S (c • h) m := by
  unfold godementInner3
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  refine congrArg (· * ψ (ofReal (-(v 1)))) (congrArg S ?_)
  rw [Matrix.smul_mul, ← Matrix.mul_smul]
  congr 1
  ext i b
  fin_cases i <;> simp [Matrix.smul_apply] <;> ring

private theorem of_smul (c : ℝ) (e : Fin 2 → Fin 2 → ℝ) : Matrix.of (c • e) = c • Matrix.of e := by
  ext i j
  simp

private theorem jacquetIntegrand3_scalar_mul {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (z : (InfiniteAdeleRing ℚ)ˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (e : Fin 2 → Fin 2 → ℝ) :
    jacquetIntegrand3 D u₃ a₃ a ψ S (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) e =
      (quasiChar (1 - 2 * u₃) 0 (realCoord (z : InfiniteAdeleRing ℚ)) *
          centralChar P (realCoord (z : InfiniteAdeleRing ℚ))) *
        jacquetIntegrand3 D u₃ a₃ a ψ S g (realCoord (z : InfiniteAdeleRing ℚ) • e) := by
  set c : ℝ := realCoord (z : InfiniteAdeleRing ℚ) with hc_def
  have hc : c ≠ 0 := realCoord_unit_ne_zero z
  unfold jacquetIntegrand3
  rw [realMat_scalar_mul, godementInner3_smul, of_smul, Matrix.det_smul, Fintype.card_fin]
  by_cases hdet : (Matrix.of e).det = 0
  · simp [hdet]
  ·
    have hW : D.W (diagOne a * (Matrix.of e)⁻¹) =
        centralChar P c * ((|c| : ℝ) : ℂ) * D.W (diagOne a * (c • Matrix.of e)⁻¹) := by
      haveI : Invertible c := invertibleOfNonzero hc
      have hlaw := D.central_law c (c⁻¹ • (diagOne a * (Matrix.of e)⁻¹)) hc
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul] at hlaw
      rw [Matrix.inv_smul (Matrix.of e) c (isUnit_iff_ne_zero.2 hdet), invOf_eq_inv, Matrix.mul_smul]
      exact hlaw
    rw [hW]

    have hq : quasiChar (u₃ + 2) a₃ (c ^ 2 * (Matrix.of e).det) =
        quasiChar (2 * (u₃ + 2)) 0 c * quasiChar (u₃ + 2) a₃ (Matrix.of e).det := by
      rw [quasiChar_mul_arg _ _ (c ^ 2) _, sq, quasiChar_sq _ _ hc]
    have hinv : ((((|c ^ 2 * (Matrix.of e).det| ^ 2)⁻¹ : ℝ)) : ℂ) =
        ((((c ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) * ((((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ)) : ℂ) := by
      have h1 : |c ^ 2 * (Matrix.of e).det| = c ^ 2 * |(Matrix.of e).det| := by
        rw [abs_mul, abs_pow, sq_abs]
      rw [h1, mul_pow, mul_inv, Complex.ofReal_mul]
    rw [hq, hinv]

    have hcollect : quasiChar (1 - 2 * u₃) 0 c * centralChar P c * (quasiChar (2 * (u₃ + 2)) 0 c *
        ((((c ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)) = centralChar P c * ((|c| : ℝ) : ℂ) := by
      have h4 : ((((c ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) = quasiChar (-4) 0 c := by
        rw [quasiChar_neg_four, show (|c| ^ 4 : ℝ) = (c ^ 2) ^ 2 by rw [← sq_abs c]; ring]
      have hprod : quasiChar (1 - 2 * u₃) 0 c * quasiChar (2 * (u₃ + 2)) 0 c * quasiChar (-4) 0 c =
          ((|c| : ℝ) : ℂ) := by
        rw [quasiChar_add_of_ne_zero _ _ _ _ hc, quasiChar_add_of_ne_zero _ _ _ _ hc,
          show 1 - 2 * u₃ + 2 * (u₃ + 2) + -4 = 1 by ring, show ((0 : ZMod 2) + 0 + 0) = 0 by simp,
          quasiChar_one_zero]
      rw [h4]
      linear_combination centralChar P c * hprod
    linear_combination (godementInner3 ψ S (c • Matrix.of e) (realMat g) * quasiChar (u₃ + 2) a₃ (Matrix.of e).det *
        ((((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ)) : ℂ) * D.W (diagOne a * (c • Matrix.of e)⁻¹)) * hcollect.symm

private theorem jacquetVector3_scalar_mul_quasiChar {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (z : (InfiniteAdeleRing ℚ)ˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D u₃ a₃ a ψ S (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) =
      quasiChar (u₃ + P.centralExponent) (a₃ + P.centralSign) (realCoord (z : InfiniteAdeleRing ℚ)) *
        jacquetVector3 D u₃ a₃ a ψ S g := by
  have hc : realCoord (z : InfiniteAdeleRing ℚ) ≠ 0 := realCoord_unit_ne_zero z
  have hint : ∫ e : Fin 2 → Fin 2 → ℝ,
      jacquetIntegrand3 D u₃ a₃ a ψ S (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) e =
        (quasiChar (1 - 2 * u₃) 0 (realCoord (z : InfiniteAdeleRing ℚ)) *
            centralChar P (realCoord (z : InfiniteAdeleRing ℚ))) *
          quasiChar (-4) 0 (realCoord (z : InfiniteAdeleRing ℚ)) *
            ∫ e, jacquetIntegrand3 D u₃ a₃ a ψ S g e := by
    simp_rw [jacquetIntegrand3_scalar_mul]
    rw [integral_const_mul,
      Measure.integral_comp_smul volume (jacquetIntegrand3 D u₃ a₃ a ψ S g) (realCoord (z : InfiniteAdeleRing ℚ))]
    have hrank : Module.finrank ℝ (Fin 2 → Fin 2 → ℝ) = 4 := by
      rw [Module.finrank_pi_fintype ℝ]
      simp
    rw [hrank, Complex.real_smul, quasiChar_neg_four, abs_inv, abs_pow]
    ring
  rw [jacquetVector3_eq, jacquetVector3_eq, realMat_scalar_mul, Matrix.det_smul, Fintype.card_fin, hint]
  set c : ℝ := realCoord (z : InfiniteAdeleRing ℚ) with hc_def
  rw [pow_succ, pow_two, quasiChar_mul_arg _ _ (c * c * c) _, quasiChar_cube _ _ hc]
  have hcollect : quasiChar (3 * (u₃ + 1)) a₃ c * ((quasiChar (1 - 2 * u₃) 0 c * centralChar P c) *
      quasiChar (-4) 0 c) = quasiChar (u₃ + P.centralExponent) (a₃ + P.centralSign) c := by
    unfold centralChar
    rw [mul_comm (quasiChar (1 - 2 * u₃) 0 c), mul_assoc, quasiChar_add_of_ne_zero _ _ _ _ hc, ← mul_assoc,
      quasiChar_add_of_ne_zero _ _ _ _ hc, quasiChar_add_of_ne_zero _ _ _ _ hc]
    congr 1 <;> [ring; simp]
  linear_combination (quasiChar (u₃ + 1) a₃ (realMat g).det * ∫ e, jacquetIntegrand3 D u₃ a₃ a ψ S g e) * hcollect

private theorem norm_apply_eq_abs_realCoord (z : InfiniteAdeleRing ℚ) :
    ‖z Rat.infinitePlace‖ = |realCoord z| := by
  rw [realCoord_apply, ← Real.norm_eq_abs,
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
      (map_zero _)]

private theorem extensionEmbedding_apply_eq_realCoord (z : InfiniteAdeleRing ℚ) :
    InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace (z Rat.infinitePlace) = ((realCoord z : ℝ) : ℂ) := by
  rw [realCoord_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

private theorem mult_rat_infinitePlace : (Rat.infinitePlace.mult : ℂ) = 1 := by
  simp [InfinitePlace.mult, Rat.isReal_infinitePlace]

private theorem div_abs_eq_sign {c : ℝ} (hc : c ≠ 0) : ((c : ℂ) / ((|c| : ℝ) : ℂ)) = ((SignType.sign c : ℝ) : ℂ) := by
  rcases hc.lt_or_gt with h | h
  · rw [abs_of_neg h]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hc)]
    simp [h]
  · rw [abs_of_pos h]
    rw [div_self (by exact_mod_cast hc)]
    simp [h]

private theorem sign_zpow_eq {c : ℝ} (hc : c ≠ 0) (n : ℤ) :
    ((SignType.sign c : ℝ) : ℂ) ^ n = if ((n : ZMod 2) = 0) then 1 else ((SignType.sign c : ℝ) : ℂ) := by
  have h2 : ((n : ZMod 2) = 0) ↔ Even n := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
    norm_cast
  rcases sign_cases hc with h | h <;> rw [h]
  · simp
  · rcases Int.even_or_odd n with he | ho
    · rw [he.neg_one_zpow, if_pos (h2.2 he)]
    · rw [ho.neg_one_zpow, if_neg (fun h0 => (Int.not_even_iff_odd.2 ho) (h2.1 h0))]

private theorem apply_section_eq_quasiChar (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (t : ℂ) (n : ℤ) (hω : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ ω v t n) (z : (InfiniteAdeleRing ℚ)ˣ) :
    ((ω (E z) : ℂˣ) : ℂ) = quasiChar t (n : ZMod 2) (realCoord (z : InfiniteAdeleRing ℚ)) := by
  have hc : realCoord (z : InfiniteAdeleRing ℚ) ≠ 0 := realCoord_unit_ne_zero z
  rw [apply_of_infPart_eq_of_isArchCompAt ω E hE t n hω z Rat.infinitePlace Rat.isReal_infinitePlace,
    norm_apply_eq_abs_realCoord, extensionEmbedding_apply_eq_realCoord, mult_rat_infinitePlace, one_mul,
    div_abs_eq_sign hc, sign_zpow_eq hc]
  unfold quasiChar
  rfl

section Places

variable {K : Type} [Field K] {M : Type} [AddCommMonoid M]

private theorem finsum_isReal_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (F : w.IsReal → M) :
    ∑ᶠ h : w.IsReal, F h = F hw := by
  classical
  rw [finsum_eq_dif, dif_pos hw]

private theorem finsum_isReal_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (F : w.IsReal → M) :
    ∑ᶠ h : w.IsReal, F h = 0 := by
  classical
  rw [finsum_eq_dif, dif_neg (InfinitePlace.not_isReal_iff_isComplex.2 hw)]

private theorem finsum_isComplex_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (F : w.IsComplex → M) :
    ∑ᶠ h : w.IsComplex, F h = 0 := by
  classical
  rw [finsum_eq_dif, dif_neg (InfinitePlace.not_isComplex_iff_isReal.2 hw)]

private theorem finsum_isComplex_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (F : w.IsComplex → M) :
    ∑ᶠ h : w.IsComplex, F h = F hw := by
  classical
  rw [finsum_eq_dif, dif_pos hw]

private theorem finsum_three (w₀ w₁ w₂ : InfinitePlace K) (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) (G : InfinitePlace K → M) :
    ∑ᶠ w, G w = G w₀ + G w₁ + G w₂ := by
  classical
  rw [finsum_eq_sum_of_support_subset G (s := {w₀, w₁, w₂}) (fun w _ => by
    rcases hall w with rfl | rfl | rfl <;> simp)]
  rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]), Finset.sum_singleton, add_assoc]

private theorem finsum_two (w₀ w₁ : InfinitePlace K) (h01 : w₀ ≠ w₁)
    (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁) (G : InfinitePlace K → M) : ∑ᶠ w, G w = G w₀ + G w₁ := by
  classical
  rw [finsum_eq_sum_of_support_subset G (s := {w₀, w₁}) (fun w _ => by rcases hall w with rfl | rfl <;> simp)]
  rw [Finset.sum_insert (by simp [h01]), Finset.sum_singleton]

end Places

private theorem val_cast_zmod_two (b : ZMod 2) : (((b.val : ℤ)) : ZMod 2) = b := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem natAbs_cast_zmod_two (k : ℤ) : (k.natAbs : ZMod 2) = (k : ZMod 2) := by
  rcases Int.natAbs_eq k with h | h
  · conv_rhs => rw [h]
    exact (Int.cast_natCast _).symm
  · conv_rhs => rw [h, Int.cast_neg, Int.cast_natCast, ZMod.neg_eq_self_mod_two]

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    :
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g)
            = ((ω (E z) : ℂˣ) : ℂ) * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) g) := by
  intro z g
  rw [jacquetVector3_scalar_mul_quasiChar, apply_section_eq_quasiChar ω E hE _ _ hω z]
  congr 2
  ·
    rcases hP₂ with ⟨w₁, w₂, h₁, h₂, h01, h02, h12, hall, rfl⟩ | ⟨wC, hC, hall, ⟨hk, rfl⟩ | ⟨hk0, rfl⟩⟩
    · simp only [finsum_three w₀ w₁ w₂ h01 h02 h12 hall, finsum_isReal_of_isReal h₀, finsum_isReal_of_isReal h₁,
        finsum_isReal_of_isReal h₂, finsum_isComplex_of_isReal h₀, finsum_isComplex_of_isReal h₁,
        finsum_isComplex_of_isReal h₂, RealArchParam.centralExponent]
      ring
    · have hne : wC ≠ w₀ := fun h => InfinitePlace.not_isReal_iff_isComplex.2 hC (h ▸ h₀)
      simp only [finsum_two wC w₀ hne hall, finsum_isReal_of_isComplex hC, finsum_isReal_of_isReal h₀,
        finsum_isComplex_of_isComplex hC, finsum_isComplex_of_isReal h₀, RealArchParam.centralExponent]
      ring
    · have hne : wC ≠ w₀ := fun h => InfinitePlace.not_isReal_iff_isComplex.2 hC (h ▸ h₀)
      simp only [finsum_two wC w₀ hne hall, finsum_isReal_of_isComplex hC, finsum_isReal_of_isReal h₀,
        finsum_isComplex_of_isComplex hC, finsum_isComplex_of_isReal h₀, RealArchParam.centralExponent]
      ring
  ·
    rcases hP₂ with ⟨w₁, w₂, h₁, h₂, h01, h02, h12, hall, rfl⟩ | ⟨wC, hC, hall, ⟨hk, rfl⟩ | ⟨hk0, rfl⟩⟩
    · simp only [finsum_three w₀ w₁ w₂ h01 h02 h12 hall, finsum_isReal_of_isReal h₀, finsum_isReal_of_isReal h₁,
        finsum_isReal_of_isReal h₂, finsum_isComplex_of_isReal h₀, finsum_isComplex_of_isReal h₁,
        finsum_isComplex_of_isReal h₂, RealArchParam.centralSign]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      ring
    · have hne : wC ≠ w₀ := fun h => InfinitePlace.not_isReal_iff_isComplex.2 hC (h ▸ h₀)
      simp only [finsum_two wC w₀ hne hall, finsum_isReal_of_isComplex hC, finsum_isReal_of_isReal h₀,
        finsum_isComplex_of_isComplex hC, finsum_isComplex_of_isReal h₀, RealArchParam.centralSign,
        natAbs_cast_zmod_two]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      ring
    · have hne : wC ≠ w₀ := fun h => InfinitePlace.not_isReal_iff_isComplex.2 hC (h ▸ h₀)
      simp only [finsum_two wC w₀ hne hall, finsum_isReal_of_isComplex hC, finsum_isReal_of_isReal h₀,
        finsum_isComplex_of_isComplex hC, finsum_isComplex_of_isReal h₀, RealArchParam.centralSign, hk0]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      ring

end

end S_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul (solution)
