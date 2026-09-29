-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/53ff0619-f985-5ad9-a832-bf27794911cd

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_norm_jacquetWhittaker3_le_of_rootSize_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace Ws31
namespace J1

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

section ModPow

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

theorem ofReal_modulus_ne_zero (u : Kˣ) : ((modulus (u : K) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2 (modulus_ne_zero u.ne_zero))

theorem cpow_modulus_ne_zero (u : Kˣ) (a : ℝ) : ((modulus (u : K) : ℝ) : ℂ) ^ (a : ℂ) ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  exact ofReal_modulus_ne_zero u h.1

noncomputable def modPow (a : ℝ) : Kˣ →* ℂˣ where
  toFun u := Units.mk0 (((modulus (u : K) : ℝ) : ℂ) ^ (a : ℂ)) (cpow_modulus_ne_zero u a)
  map_one' := Units.ext (by simp [modulus_one])
  map_mul' u w := Units.ext (by
    simp only [Units.val_mul, Units.val_mk0, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) _)

theorem modPow_apply (a : ℝ) (u : Kˣ) : ((modPow a u : ℂˣ) : ℂ) = ((modulus (u : K) : ℝ) : ℂ) ^ (a : ℂ) := rfl

theorem modulus_neg_one : modulus (-1 : K) = 1 := by
  have h : modulus (-1 : K) * modulus (-1 : K) = 1 := by
    rw [← modulus_mul, neg_one_mul, neg_neg, modulus_one]
  have h' : (modulus (-1 : K) : ℝ) * (modulus (-1 : K) : ℝ) = 1 := by exact_mod_cast h
  have hnn : (0 : ℝ) ≤ (modulus (-1 : K) : ℝ) := NNReal.coe_nonneg _
  rcases mul_self_eq_one_iff.1 h' with h1 | h1
  · exact_mod_cast h1
  · exfalso; linarith

end ModPow

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem isLocallyConstant_modPow (a : ℝ) : IsLocallyConstant (⇑(modPow (K := (p.adicCompletion ℚ)) a)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun u₀ => ?_
  have hopen : IsOpen {u : (p.adicCompletion ℚ)ˣ | ‖(u : (p.adicCompletion ℚ))‖ = ‖(u₀ : (p.adicCompletion ℚ))‖} := by
    have hs : IsOpen (Metric.sphere (0 : (p.adicCompletion ℚ)) ‖(u₀ : (p.adicCompletion ℚ))‖) :=
      IsUltrametricDist.isOpen_sphere _ (norm_ne_zero_iff.2 u₀.ne_zero)
    have := hs.preimage (Units.continuous_val (M := (p.adicCompletion ℚ)))
    convert this using 1
    ext u
    simp [Metric.mem_sphere, dist_zero_right]
  filter_upwards [hopen.mem_nhds (show u₀ ∈ {u : (p.adicCompletion ℚ)ˣ | ‖(u : (p.adicCompletion ℚ))‖ = ‖(u₀ : (p.adicCompletion ℚ))‖} from rfl)] with u hu
  apply Units.ext
  rw [modPow_apply, modPow_apply, modulus_adicCompletion_eq_nnnorm, modulus_adicCompletion_eq_nnnorm, coe_nnnorm,
    coe_nnnorm]
  exact congrArg (fun r : ℝ => ((r : ℂ)) ^ (a : ℂ)) hu

theorem exp_neg_one_pow (m : ℕ) :
    (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^ m = WithZero.exp (-(m : ℤ)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

variable (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

theorem translate_mem (g : LocalGL3 p) (f : ↥(principalSeries3 p lam)) :
    (gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 p → ℂ)) ∈ principalSeries3 p lam :=
  rightTranslate_mem_principalSeries3 f.2 g

theorem coefficientFn_apply (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)) (g : LocalGL3 p) :
    coefficientFn Λ f g = Λ ⟨gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 p → ℂ), translate_mem p lam g f⟩ := rfl

theorem coefficientFn_mul (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)) (g : LocalGL3 p) :
    (fun h => coefficientFn Λ f (h * g)) =
      coefficientFn Λ ⟨gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 p → ℂ), translate_mem p lam g f⟩ := by
  funext h
  rw [coefficientFn_apply, coefficientFn_apply]
  congr 1
  apply Subtype.ext
  funext x
  change (f : LocalGL3 p → ℂ) (x * (h * g)) = (f : LocalGL3 p → ℂ) (x * h * g)
  rw [mul_assoc]

theorem coefficientFn_add (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f f' : ↥(principalSeries3 p lam)) :
    coefficientFn Λ (f + f') = coefficientFn Λ f + coefficientFn Λ f' := by
  funext h
  rw [Pi.add_apply, coefficientFn_apply, coefficientFn_apply, coefficientFn_apply, ← map_add]
  congr 1

theorem coefficientFn_smul (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (c : ℂ) (f : ↥(principalSeries3 p lam)) :
    coefficientFn Λ (c • f) = c • coefficientFn Λ f := by
  funext h
  rw [Pi.smul_apply, coefficientFn_apply, coefficientFn_apply, ← map_smul]
  congr 1

theorem coefficientFn_zero (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) :
    coefficientFn Λ (0 : ↥(principalSeries3 p lam)) = 0 := by
  funext h
  rw [Pi.zero_apply, coefficientFn_apply, ← Λ.map_zero]
  congr 1

theorem exists_eq_coefficientFn_of_mem_gl3CyclicSubspace (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ)
    (f : ↥(principalSeries3 p lam)) (W : LocalGL3 p → ℂ) (hW : W ∈ gl3CyclicSubspace (coefficientFn Λ f)) :
    ∃ f' : ↥(principalSeries3 p lam), W = coefficientFn Λ f' := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, coefficientFn_mul p lam Λ f g⟩
  | zero => exact ⟨0, (coefficientFn_zero p lam Λ).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨fx, rfl⟩ := hx
    obtain ⟨fy, rfl⟩ := hy
    exact ⟨fx + fy, (coefficientFn_add p lam Λ fx fy).symm⟩
  | smul c x _ hx =>
    obtain ⟨fx, rfl⟩ := hx
    exact ⟨c • fx, (coefficientFn_smul p lam Λ c fx).symm⟩

theorem scalar_eq_diagonal3 (t : (p.adicCompletion ℚ)ˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 3) t : LocalGL3 p) = diagonal3 p (fun _ => t) := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.scalar, diagonal3_coe]

theorem scalar_comm (t : (p.adicCompletion ℚ)ˣ) (k : LocalGL3 p) :
    k * Matrix.GeneralLinearGroup.scalar (Fin 3) t = Matrix.GeneralLinearGroup.scalar (Fin 3) t * k := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.scalar]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem halfModulus3_const (t : (p.adicCompletion ℚ)ˣ) : halfModulus3 p (fun _ : Fin 3 => t) = 1 := by
  have h : ‖(t : (p.adicCompletion ℚ))‖ ≠ 0 := norm_ne_zero_iff.2 t.ne_zero
  simp [halfModulus3, div_self h]

theorem torusChar3_const (t : (p.adicCompletion ℚ)ˣ) :
    torusChar3 p lam (fun _ : Fin 3 => t) = (((lam 0 * lam 1 * lam 2) t : ℂˣ) : ℂ) := by
  simp [torusChar3, Fin.prod_univ_three, MonoidHom.mul_apply, Units.val_mul]

theorem diag_mul_entry (h : LocalGL3 p) (i j : Fin 3) :
    ((diagonal3 p ![1, -1, 1] * h : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      (((![1, -1, 1] : Fin 3 → (p.adicCompletion ℚ)ˣ) i : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) * (h : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j := by
  rw [Units.val_mul, diagonal3_coe, Matrix.diagonal_mul]

theorem lastRowSup_diag_mul (h : LocalGL3 p) : lastRowSup (diagonal3 p ![1, -1, 1] * h) = lastRowSup h := by
  simp only [lastRowSup, diag_mul_entry]
  simp

theorem minorSup_diag_mul (h : LocalGL3 p) : minorSup (diagonal3 p ![1, -1, 1] * h) = minorSup h := by
  have hb : ∀ j j' : Fin 3, bottomMinor (diagonal3 p ![1, -1, 1] * h) j j' = -bottomMinor h j j' := by
    intro j j'
    simp only [bottomMinor, diag_mul_entry]
    simp
    ring
  simp only [minorSup, hb, norm_neg]

theorem detSize_diag_mul (h : LocalGL3 p) : detSize (diagonal3 p ![1, -1, 1] * h) = detSize h := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, diagonal3_coe, Matrix.det_diagonal, norm_mul, Fin.prod_univ_three]
  simp

theorem gauge_diag_mul (W : LocalGL3 p → ℂ)
    (hW : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) →
        W (diagonal3 p ![1, -1, 1] * h) = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W (diagonal3 p ![1, -1, 1] * h)‖ ≤
          C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
  obtain ⟨B, t, C, hBtC⟩ := hW
  refine ⟨B, t, C, fun h => ?_⟩
  have := hBtC (diagonal3 p ![1, -1, 1] * h)
  rw [detSize_diag_mul, lastRowSup_diag_mul, minorSup_diag_mul] at this
  exact this

theorem modulus_det_diag : modulus ((Matrix.GeneralLinearGroup.det (diagonal3 p ![1, -1, 1]) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, diagonal3_coe, Matrix.det_diagonal, Fin.prod_univ_three]
  simp [modulus_neg_one]

theorem modulus_det_g₀ (x y z : (p.adicCompletion ℚ)) :
    modulus ((Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z * antidiagonal3 p) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, antidiagonal3_coe]
  simp [Matrix.det_fin_three, modulus_neg_one]

end Local

end Ws31.J1

open Ws31.J1 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (x y z : p.adicCompletion ℚ)
    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)))
    :
    ∃ (a : ℝ) (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (W' : LocalGL3 p → ℂ),
      (∀ h : LocalGL3 p, W' h =
        (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ)) *
          W₃ h) ∧
      IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W' ∧
      (∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 p, W' (g * k) = W' g) ∧
      (∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
        W' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W' h) ∧
      (∀ t : (p.adicCompletion ℚ)ˣ, ‖((ω₃ t : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
        ∃ B : Finset (LocalGL3 p → ℂ), ∀ F ∈ gl3CyclicSubspace W',
          (∀ k ∈ Uv, ∀ g : LocalGL3 p, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ))) ∧
      (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
        (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
        (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
          ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) := by
  classical

  have hlc3 : IsLocallyConstant (⇑(lam 0 * lam 1 * lam 2)) := by
    have e : (⇑(lam 0 * lam 1 * lam 2) : (p.adicCompletion ℚ)ˣ → ℂˣ) = fun u => lam 0 u * lam 1 u * lam 2 u := by
      funext u; simp only [MonoidHom.mul_apply]
    rw [e]
    exact ((hlam 0).comp₂ (hlam 1) (· * ·)).comp₂ (hlam 2) (· * ·)
  obtain ⟨c, hc⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ p
    (lam 0 * lam 1 * lam 2) hlc3.continuous
  obtain ⟨η, σ, hηu, -, hχη⟩ :=
    LanglandsTunnell.TateLocal.exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt ℚ p (lam 0 * lam 1 * lam 2) c hc
  obtain ⟨a, ha⟩ : ∃ a : ℝ, σ + a + a + a = 0 := ⟨-σ / 3, by ring⟩
  obtain ⟨μ, hμ, hμlc⟩ : ∃ μ : (p.adicCompletion ℚ)ˣ →* ℂˣ,
      (∀ u : (p.adicCompletion ℚ)ˣ, ((μ u : ℂˣ) : ℂ) = ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ)) ∧ IsLocallyConstant (⇑μ) :=
    ⟨modPow a, fun u => rfl, isLocallyConstant_modPow p a⟩
  obtain ⟨lam', hlam'⟩ : ∃ lam' : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ), lam' = fun i => lam i * μ := ⟨_, rfl⟩
  have hlam'i : ∀ i, lam' i = lam i * μ := fun i => by rw [hlam']
  have hlam'lc : ∀ i, IsLocallyConstant (⇑(lam' i)) := by
    intro i
    have e : (⇑(lam i * μ) : (p.adicCompletion ℚ)ˣ → ℂˣ) = fun u => lam i u * μ u := funext fun u => MonoidHom.mul_apply _ _ _
    rw [hlam'i i, e]
    exact (hlam i).comp₂ hμlc (· * ·)

  have hprod : ∀ u : (p.adicCompletion ℚ)ˣ, (((lam' 0 * lam' 1 * lam' 2) u : ℂˣ) : ℂ) = ((η u : ℂˣ) : ℂ) := by
    intro u
    have hm0 : ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ≠ 0 := ofReal_modulus_ne_zero u
    have h3 := hχη u
    simp only [MonoidHom.mul_apply, Units.val_mul] at h3
    simp only [MonoidHom.mul_apply, Units.val_mul, hlam'i, hμ u]
    have hexp : ((σ : ℝ) : ℂ) + (a : ℂ) + (a : ℂ) + (a : ℂ) = 0 := by exact_mod_cast ha
    calc ((lam 0 u : ℂˣ) : ℂ) * ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ) *
          (((lam 1 u : ℂˣ) : ℂ) * ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ)) *
          (((lam 2 u : ℂˣ) : ℂ) * ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ))
        = (((lam 0 u : ℂˣ) : ℂ) * ((lam 1 u : ℂˣ) : ℂ) * ((lam 2 u : ℂˣ) : ℂ)) *
          (((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ) * ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ) *
            ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ)) := by ring
      _ = ((η u : ℂˣ) : ℂ) * (((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ) *
          ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ) * ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ) *
            ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ)) := by rw [h3]; ring
      _ = ((η u : ℂˣ) : ℂ) * ((modulus (u : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (((σ : ℝ) : ℂ) + (a : ℂ) + (a : ℂ) + (a : ℂ)) := by
          rw [Complex.cpow_add _ _ hm0, Complex.cpow_add _ _ hm0, Complex.cpow_add _ _ hm0]
      _ = ((η u : ℂˣ) : ℂ) := by rw [hexp, Complex.cpow_zero, mul_one]
  have hωu : ∀ u : (p.adicCompletion ℚ)ˣ, ‖(((lam' 0 * lam' 1 * lam' 2) u : ℂˣ) : ℂ)‖ = 1 := fun u => by
    rw [hprod u]; exact hηu u

  obtain ⟨Λ₀, Λ₁, -, -, -, -, hΛ₁W, -, hΛ₁J⟩ :=
    LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum p lam' hlam'lc
  obtain ⟨hmem, hJcf⟩ := hΛ₁J Φ hΦ

  obtain ⟨W', hW'def⟩ : ∃ W' : LocalGL3 p → ℂ, W' = fun h =>
      (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ)) * W₃ h := ⟨_, rfl⟩
  have hW'J : ∀ h : LocalGL3 p, W' h =
      jacquetWhittaker3 p lam' Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)) := by
    intro h
    have hDT := LanglandsTunnell.CubicInduction.jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3 p lam Φ μ a hμ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))
    rw [← hlam'] at hDT
    have hmod : modulus ((Matrix.GeneralLinearGroup.det
          (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) =
        modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, modulus_mul, modulus_mul, modulus_det_diag, modulus_det_g₀,
        one_mul, mul_one]
    rw [hmod] at hDT
    have h1 : W' h = (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (a : ℂ)) * W₃ h := by
      rw [hW'def]
    have h2 : W₃ h = jacquetWhittaker3 p lam Φ
        (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)) := by
      rw [hW₃]
    rw [h1, h2, hDT]
  have hWcf : W' = coefficientFn Λ₁ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z * antidiagonal3 p)
      ((⟨cellSectionOf p lam' Φ, hmem⟩ : ↥(principalSeries3 p lam')) : LocalGL3 p → ℂ),
      translate_mem p lam' (upperUnipotent3 x y z * antidiagonal3 p) ⟨cellSectionOf p lam' Φ, hmem⟩⟩ := by
    rw [← coefficientFn_mul p lam' Λ₁ ⟨cellSectionOf p lam' Φ, hmem⟩ (upperUnipotent3 x y z * antidiagonal3 p), ← hJcf]
    funext h
    rw [hW'J h, mul_assoc]

  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : ↥(principalSeries3 p lam'), W' = coefficientFn Λ₁ f₁ := ⟨_, hWcf⟩
  clear hWcf
  refine ⟨a, lam' 0 * lam' 1 * lam' 2, W', fun h => by rw [hW'def], ?_, ?_, ?_, hωu, ?_, ?_⟩
  ·
    rw [hf₁]
    exact isGL3PsiWhittakerFn_coefficientFn hΛ₁W f₁
  ·
    obtain ⟨n, hn⟩ := LanglandsTunnell.CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 p lam'
      (f₁ : LocalGL3 p → ℂ) f₁.2
    let Uv : Subgroup (LocalGL3 p) :=
      { carrier := {k | ∀ g : LocalGL3 p, W' (g * k) = W' g}
        mul_mem' := fun {k k'} hk hk' g => by rw [← mul_assoc, hk' (g * k), hk g]
        one_mem' := fun g => by rw [mul_one]
        inv_mem' := fun {k} hk g => by rw [← hk (g * k⁻¹), inv_mul_cancel_right] }
    refine ⟨Uv, ?_, fun k hk g => hk g⟩
    apply Subgroup.isOpen_of_mem_nhds Uv (g := 1)
    have hV1 : {k : LocalGL3 p | ∀ i j : Fin 3,
        Valued.v (gl3Entry p k i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ))} ∈
        nhds (1 : LocalGL3 p) := by
      simp only [Set.setOf_forall]
      refine (Filter.iInter_mem).2 fun i => (Filter.iInter_mem).2 fun j => ?_
      have hcont : Continuous fun k : LocalGL3 p => gl3Entry p k i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j :=
        (continuous_gl3Entry p i j).sub continuous_const
      have h0 : gl3Entry p (1 : LocalGL3 p) i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j = 0 := by
        simp [gl3Entry]
      have hN : {w : (p.adicCompletion ℚ) | Valued.v w ≤ WithZero.exp (-(n : ℤ))} ∈
          nhds (gl3Entry p (1 : LocalGL3 p) i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) := by
        rw [h0]
        have hx₀ : Valued.v (((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n) =
            WithZero.exp (-(n : ℤ)) := by
          rw [map_pow, NumberField.AdelicLevel.valued_uniformizerUnit, exp_neg_one_pow]
        have hx₀0 : (Valued.v (((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n)) ≠ 0 := by
          rw [hx₀]; exact WithZero.exp_ne_zero
        have h1 := Valued.locally_const hx₀0
        have h2 : Filter.Tendsto (fun w : (p.adicCompletion ℚ) => w + ((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n)
            (nhds 0) (nhds ((((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n))) := by
          have := (continuous_add_right ((((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n))).tendsto (0 : (p.adicCompletion ℚ))
          rwa [zero_add] at this
        refine Filter.mem_of_superset (h2 h1) fun w hw => ?_
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hw
        show Valued.v w ≤ WithZero.exp (-(n : ℤ))
        calc Valued.v w = Valued.v ((w + ((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n) -
              ((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n) := by rw [add_sub_cancel_right]
          _ ≤ max (Valued.v (w + ((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n))
              (Valued.v (((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ^ n)) := Valuation.map_sub _ _ _
          _ = WithZero.exp (-(n : ℤ)) := by rw [hw, hx₀, max_self]
      exact hcont.continuousAt.preimage_mem_nhds hN
    refine Filter.mem_of_superset hV1 ?_
    intro k hk g
    show W' (g * k) = W' g
    rw [hf₁, coefficientFn_apply, coefficientFn_apply]
    congr 1
    apply Subtype.ext
    funext x'
    change (f₁ : LocalGL3 p → ℂ) (x' * (g * k)) = (f₁ : LocalGL3 p → ℂ) (x' * g)
    have := congrFun (hn k hk) (x' * g)
    rw [gl3AmbientRightTranslate_apply] at this
    rw [← mul_assoc]
    exact this
  ·
    intro t h
    rw [hf₁, coefficientFn_apply, coefficientFn_apply]
    have key : (⟨gl3AmbientRightTranslate (R := ℂ) (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) (f₁ : LocalGL3 p → ℂ),
          translate_mem p lam' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) f₁⟩ : ↥(principalSeries3 p lam')) =
        (torusChar3 p lam' (fun _ => t) * halfModulus3 p (fun _ => t)) •
          ⟨gl3AmbientRightTranslate (R := ℂ) h (f₁ : LocalGL3 p → ℂ), translate_mem p lam' h f₁⟩ := by
      apply Subtype.ext
      funext x'
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply]
      rw [← mul_assoc, scalar_comm p t x', mul_assoc, scalar_eq_diagonal3 p t, f₁.2.2.2 (fun _ => t) (x' * h)]
    rw [key, map_smul, smul_eq_mul, halfModulus3_const, mul_one, torusChar3_const]
  ·
    intro Uv hU
    obtain ⟨B, hB⟩ := LanglandsTunnell.CubicInduction.exists_finset_coefficientFn_mem_span_of_isOpen p lam' Λ₁ Uv hU
    refine ⟨B, fun F hF hFinv => ?_⟩
    rw [hf₁] at hF
    obtain ⟨f', rfl⟩ := exists_eq_coefficientFn_of_mem_gl3CyclicSubspace p lam' Λ₁ f₁ F hF
    exact hB f' hFinv
  ·
    obtain ⟨B₀, hB₀⟩ := LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt p lam' hlam'lc
      hωu Φ hΦ.1 hΦ.2
    obtain ⟨t₀, C₀, hC₀⟩ := LanglandsTunnell.CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le p lam' hlam'lc
      hωu Φ hΦ.1 hΦ.2 B₀
    have hJd := gauge_diag_mul p (jacquetWhittaker3 p lam' Φ)
      ⟨B₀, t₀, C₀, fun h => ⟨hB₀ h, fun hc' => hC₀ h hc'.1 hc'.2⟩⟩
    have hmemW : W' ∈ gl3CyclicSubspace (fun k : LocalGL3 p => jacquetWhittaker3 p lam' Φ (diagonal3 p ![1, -1, 1] * k)) := by
      refine Submodule.subset_span ⟨upperUnipotent3 x y z * antidiagonal3 p, ?_⟩
      show gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z * antidiagonal3 p)
          (fun k : LocalGL3 p => jacquetWhittaker3 p lam' Φ (diagonal3 p ![1, -1, 1] * k)) = W'
      funext h
      rw [gl3AmbientRightTranslate_apply, hW'J h, mul_assoc]
    exact ((LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3 _ hJd)
      W' hmemW).1

end S_LanglandsTunnell_CubicInduction_exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge (solution)
