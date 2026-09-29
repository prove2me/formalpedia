-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.hasSum_torusShells_rsLocalIntegral22_jacquetIntegral_schwartz_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e6195f7c-e049-5310-9540-d2f20176418a

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
import Theorems.Thm_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
import Theorems.Thm_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_torusShells_rsLocalIntegral22_jacquetIntegral_schwartz_of_integrable
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)
open scoped NNReal ENNReal Topology

namespace D2T

noncomputable section

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
  have : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
  positivity

theorem norm_eq_zpow_of_valued {x : F} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_eq_norm (x : F) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

variable (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

include hϖ in
theorem valued_varpi_zpow (m : ℤ) : Valued.v ((ϖ : F) ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

include hϖ in
theorem norm_varpi_zpow (m : ℤ) : ‖(ϖ : F) ^ m‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-m) :=
  norm_eq_zpow_of_valued p (valued_varpi_zpow p ϖ hϖ m)

include hϖ in
theorem varpi_le_one : Valued.v (ϖ : F) ≤ 1 := by
  rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num

def varpiO (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) : p.adicCompletionIntegers ℚ :=
  ⟨(ϖ : F), (Valuation.mem_valuationSubring_iff _ _).mpr (varpi_le_one p ϖ hϖ)⟩

theorem algebraMap_varpiO :
    algebraMap (p.adicCompletionIntegers ℚ) F (varpiO p ϖ hϖ) = (ϖ : F) := rfl

theorem unipotentGL2_eq_upperUnipotent2 (x : F) : (unipotentGL2 x : G₂) = upperUnipotent2 p x :=
  Units.ext (by simp [unipotentGL2_coe, upperUnipotent2_coe])

theorem unipotent_eq_upperUnipotent2 (x : F) : (UnramifiedWhittaker.unipotent x : G₂) = upperUnipotent2 p x :=
  Units.ext (by simp [UnramifiedWhittaker.unipotent, Matrix.GeneralLinearGroup.mkOfDetNeZero, upperUnipotent2_coe])

theorem exists_eq_upperUnipotent2_of_mem_range {x : G₂}
    (hx : x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range) :
    ∃ t : F, x = upperUnipotent2 p t := by
  obtain ⟨m, rfl⟩ := hx
  exact ⟨Multiplicative.toAdd m, unipotentGL2_eq_upperUnipotent2 p _⟩

theorem coe_range_eq (x : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range) :
    ((x : G₂) : Matrix (Fin 2) (Fin 2) F) = !![1, ((x : G₂) : Matrix (Fin 2) (Fin 2) F) 0 1; 0, 1] := by
  obtain ⟨t, ht⟩ := exists_eq_upperUnipotent2_of_mem_range p x.2
  rw [ht, upperUnipotent2_coe]
  simp

theorem coe_scalar (z : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G₂) : Matrix (Fin 2) (Fin 2) F) = (z : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem scalar_mul_comm (z : Fˣ) (g : G₂) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) z :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])

theorem scalarPi_eq_scalar :
    scalarPi (ϖ : F) ϖ.ne_zero = Matrix.GeneralLinearGroup.scalar (Fin 2) ϖ := by
  refine Units.ext ?_
  rw [coe_scalar]
  simp only [scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem scalarPi_zpow_eq_scalar (n : ℤ) :
    scalarPi (ϖ : F) ϖ.ne_zero ^ n = Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ n) := by
  rw [scalarPi_eq_scalar, map_zpow]

theorem scalar_eq_diagonal2 (z : Fˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G₂) = diagonal2 p (fun _ => z) :=
  Units.ext (by
    rw [coe_scalar, diagonal2_coe, Matrix.smul_one_eq_diagonal])

theorem coe_diagZ (m : ℤ) :
    ((diagZ (ϖ : F) ϖ.ne_zero m : G₂) : Matrix (Fin 2) (Fin 2) F) = !![(ϖ : F) ^ m, 0; 0, 1] := by
  simp [diagZ, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem diagZ_mul_apply_one (m : ℤ) (k : G₂) (j : Fin 2) :
    ((diagZ (ϖ : F) ϖ.ne_zero m * k : G₂) : Matrix (Fin 2) (Fin 2) F) 1 j = (k : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Units.val_mul, coe_diagZ, Matrix.mul_apply]
  simp [Fin.sum_univ_two]

theorem scalar_mul_apply (z : Fˣ) (g : G₂) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G₂) : Matrix (Fin 2) (Fin 2) F) i j
      = (z : F) * (g : Matrix (Fin 2) (Fin 2) F) i j := by
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]

theorem upperUnipotent2_mul_apply_one (x : F) (g : G₂) (j : Fin 2) :
    ((upperUnipotent2 p x * g : G₂) : Matrix (Fin 2) (Fin 2) F) 1 j = (g : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Units.val_mul, upperUnipotent2_coe, Matrix.mul_apply]
  simp [Fin.sum_univ_two]

theorem det_upperUnipotent2_mul (x : F) (g : G₂) :
    Matrix.GeneralLinearGroup.det (upperUnipotent2 p x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (upperUnipotent2 p x) = 1 :=
    Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent2_coe, Matrix.det_fin_two_of])
  rw [this, one_mul]

theorem coe_det_scalar (z : Fˣ) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) : Fˣ) : F) = (z : F) * z := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_scalar]
  simp [Matrix.det_smul, Fintype.card_fin, pow_two]

theorem coe_det_diagZ (m : ℤ) :
    ((Matrix.GeneralLinearGroup.det (diagZ (ϖ : F) ϖ.ne_zero m) : Fˣ) : F) = (ϖ : F) ^ m := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagZ, Matrix.det_fin_two_of]
  ring

theorem coe_diagZ_inv_mul_unipotent_mul_diagZ (d : ℤ) (t : F) :
    (((diagZ (ϖ : F) ϖ.ne_zero d)⁻¹ * upperUnipotent2 p t * diagZ (ϖ : F) ϖ.ne_zero d : G₂) : Matrix (Fin 2) (Fin 2) F)
      = !![1, (ϖ : F) ^ (-d) * t; 0, 1] := by
  have hinv : ((diagZ (ϖ : F) ϖ.ne_zero d)⁻¹ : G₂) = diagZ (ϖ : F) ϖ.ne_zero (-d) := by
    rw [inv_eq_iff_mul_eq_one]
    refine Units.ext ?_
    rw [Units.val_mul, coe_diagZ, coe_diagZ, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero d ϖ.ne_zero)]
  rw [hinv, Units.val_mul, Units.val_mul, coe_diagZ, coe_diagZ, upperUnipotent2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_neg, inv_mul_cancel₀ (zpow_ne_zero d ϖ.ne_zero)]

end

end D2T

namespace D2T

noncomputable section

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  set c : ℝ≥0 := (Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

def Wp (φ : G₂ → ℂ) (g : G₂) : ℂ :=
  ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)

theorem Wp_upperUnipotent2_mul (φ : G₂ → ℂ) (y : F) (g : G₂) :
    Wp p φ (upperUnipotent2 p y * g) = NumberField.StandardAddChar.psiLocal ℚ p (-y) * Wp p φ g := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  simp only [Wp]
  have h1 : ∀ x : F, antidiagonal2 p * upperUnipotent2 p x * (upperUnipotent2 p y * g)
      = antidiagonal2 p * upperUnipotent2 p (x + y) * g := by
    intro x; rw [← upperUnipotent2_mul]; simp only [mul_assoc]
  simp_rw [h1]
  have h2 : (fun x : F => NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p (x + y) * g))
      = fun x => (fun u : F => NumberField.StandardAddChar.psiLocal ℚ p (u - y) *
          φ (antidiagonal2 p * upperUnipotent2 p u * g)) (y + x) := by
    funext x; simp only [add_comm y x]; rw [add_sub_cancel_right]
  rw [h2, integral_add_left_eq_self
        (fun u : F => NumberField.StandardAddChar.psiLocal ℚ p (u - y) *
          φ (antidiagonal2 p * upperUnipotent2 p u * g)) y, ← integral_const_mul]
  congr 1; funext u
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]; ring

theorem phi_scalar_mul {μ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)} {φ : G₂ → ℂ}
    (hφ : φ ∈ principalSeries2 p μ) (z : Fˣ) (g : G₂) :
    φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((μ 0 z : ℂˣ) : ℂ) * ((μ 1 z : ℂˣ) : ℂ) * φ g := by
  obtain ⟨-, -, ht⟩ := mem_principalSeries2_iff.mp hφ
  rw [scalar_eq_diagonal2, ht]
  have h1 : torusChar2 p μ (fun _ => z) = ((μ 0 z : ℂˣ) : ℂ) * ((μ 1 z : ℂˣ) : ℂ) := by
    simp [torusChar2, Fin.prod_univ_two]
  have hz : ‖(z : F)‖ ≠ 0 := norm_ne_zero_iff.mpr z.ne_zero
  have h2 : halfModulus2 p (fun _ => z) = 1 := by
    simp [halfModulus2, div_self hz]
  rw [h1, h2]; ring

theorem Wp_scalar_mul {μ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)} {φ : G₂ → ℂ}
    (hφ : φ ∈ principalSeries2 p μ) (z : Fˣ) (g : G₂) :
    Wp p φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)
      = ((μ 0 z : ℂˣ) : ℂ) * ((μ 1 z : ℂˣ) : ℂ) * Wp p φ g := by
  simp only [Wp]
  have h : ∀ x : F, antidiagonal2 p * upperUnipotent2 p x * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) z * (antidiagonal2 p * upperUnipotent2 p x * g) := by
    intro x
    rw [scalar_mul_comm p z (antidiagonal2 p * upperUnipotent2 p x * g), scalar_mul_comm p z g]
    simp only [mul_assoc]
  simp_rw [h, phi_scalar_mul p hφ, ← integral_const_mul]
  congr 1; funext x; ring

theorem Wp_mul_right_of_forall (φ : G₂ → ℂ) {k : G₂} (hk : ∀ g : G₂, φ (g * k) = φ g) (g : G₂) :
    Wp p φ (g * k) = Wp p φ g := by
  simp only [Wp, ← mul_assoc _ g k, hk]

theorem continuous_of_forall_mul_eq (f : G₂ → ℂ) (U : Subgroup G₂) (hU : IsOpen (U : Set G₂))
    (hf : ∀ k ∈ U, ∀ g : G₂, f (g * k) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hev : f =ᶠ[𝓝 g] fun _ => f g := by
    have ho : IsOpen ((fun k : G₂ => g * k) '' (U : Set G₂)) := (Homeomorph.mulLeft g).isOpenMap _ hU
    have hm : g ∈ (fun k : G₂ => g * k) '' (U : Set G₂) := ⟨1, U.one_mem, mul_one g⟩
    filter_upwards [ho.mem_nhds hm] with h hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact hf k hk g
  exact (continuousAt_congr hev).mpr continuousAt_const

def WProps (θ₀ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ) (w : G₂ → ℂ) : Prop :=
  (∀ (x : F) (g : G₂), w (upperUnipotent2 p x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) ∧
  (∀ (z : Fˣ) (g : G₂), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g) ∧
  ∃ U : Subgroup G₂, IsOpen (U : Set G₂) ∧ ∀ k ∈ U, ∀ g : G₂, w (g * k) = w g

theorem wProps_of_mem_span (θ₀ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : G₂ → ℂ)
    (hw₂law : ∀ (x : F) (g : G₂),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G₂, w₂base (g * k) = w₂base g)
    (hcentral : ∀ (z : Fˣ) (g : G₂),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    {w : G₂ → ℂ}
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : G₂ => fun g : G₂ => w₂base (g * h))) :
    WProps p θ₀ w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine ⟨fun x g => ?_, fun z g => ?_, ?_⟩
    · show w₂base (upperUnipotent2 p x * g * h) = _ * w₂base (g * h)
      rw [mul_assoc, ← unipotent_eq_upperUnipotent2, hw₂law]
    · show w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g * h) = _ * w₂base (g * h)
      rw [mul_assoc, hcentral]
    · refine ⟨(AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N).comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have : ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N).comap (MulAut.conj h⁻¹).toMonoidHom : Set G₂)
            = (fun u : G₂ => h⁻¹ * u * h⁻¹⁻¹) ⁻¹' (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set G₂) := by
          ext u; simp [Subgroup.coe_comap, MulAut.conj_apply]
        rw [this]
        exact ((AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2).preimage
          ((continuous_const.mul continuous_id).mul continuous_const)
      · intro k hk g
        have hk' : h⁻¹ * k * h ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
          simpa [Subgroup.mem_comap, MulAut.conj_apply] using hk
        show w₂base (g * k * h) = w₂base (g * h)
        have : g * k * h = g * h * (h⁻¹ * k * h) := by group
        rw [this, hw₂K _ hk']
  | zero => exact ⟨fun _ _ => by simp, fun _ _ => by simp, ⊤, by simp, fun _ _ _ => rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨hx1, hx2, Ux, hUx, hx3⟩ := ihx
    obtain ⟨hy1, hy2, Uy, hUy, hy3⟩ := ihy
    refine ⟨fun t g => ?_, fun z g => ?_, Ux ⊓ Uy, ?_, fun k hk g => ?_⟩
    · simp only [Pi.add_apply, hx1, hy1]; ring
    · simp only [Pi.add_apply, hx2, hy2]; ring
    · rw [Subgroup.coe_inf]; exact hUx.inter hUy
    · simp only [Pi.add_apply, hx3 k (Subgroup.mem_inf.mp hk).1, hy3 k (Subgroup.mem_inf.mp hk).2]
  | smul a x hx ihx =>
    obtain ⟨hx1, hx2, Ux, hUx, hx3⟩ := ihx
    refine ⟨fun t g => ?_, fun z g => ?_, Ux, hUx, fun k hk g => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hx1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hx2]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hx3 k hk]

end

end D2T

namespace D2T

noncomputable section

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "K₀" => (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)

theorem norm_le_one_of_mem_integers {x : F} (hx : x ∈ p.adicCompletionIntegers ℚ) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr ((Valuation.mem_valuationSubring_iff _ _).mp hx)

theorem det_mem_integers {m : Matrix (Fin 2) (Fin 2) F} (hm : ∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) :
    m.det ∈ p.adicCompletionIntegers ℚ := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hm 0 0) (hm 1 1)) (mul_mem (hm 0 1) (hm 1 0))

theorem norm_det_eq_one_of_mem {k : G₂} (hk : k ∈ K₀) :
    ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ = 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  obtain ⟨h1, h2⟩ := hk
  have ha : ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ ≤ 1 :=
    norm_le_one_of_mem_integers p (det_mem_integers p h1.integral)
  have hb : ‖((k⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F).det‖ ≤ 1 :=
    norm_le_one_of_mem_integers p (det_mem_integers p h2.integral)
  have hmul : (k : Matrix (Fin 2) (Fin 2) F).det * ((k⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hn := norm_mul ((k : Matrix (Fin 2) (Fin 2) F).det) (((k⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F).det)
  rw [hmul, norm_one] at hn
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  nlinarith [norm_nonneg ((k : Matrix (Fin 2) (Fin 2) F).det),
    norm_nonneg (((k⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F).det)]

theorem isLocalLevelOne_top_unipotent_iff (u : F) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ (!![1, u; 0, 1] : Matrix (Fin 2) (Fin 2) F) ↔ Valued.v u ≤ 1 := by
  constructor
  · intro h
    exact (Valuation.mem_valuationSubring_iff _ _).mp (h.integral 0 1)
  · intro hu
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using one_mem (p.adicCompletionIntegers ℚ)
      · have h__ := (Valuation.mem_valuationSubring_iff _ _).mpr hu
        try simp at h__
        try simp
        exact h__
      · simpa using zero_mem (p.adicCompletionIntegers ℚ)
      · simpa using one_mem (p.adicCompletionIntegers ℚ)
    · simp
    · simp

theorem upperUnipotent2_mem_iff (u : F) : upperUnipotent2 p u ∈ K₀ ↔ Valued.v u ≤ 1 := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have hinv : (((upperUnipotent2 p u)⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F) = !![1, -u; 0, 1] := rfl
  rw [hinv, upperUnipotent2_coe, isLocalLevelOne_top_unipotent_iff, isLocalLevelOne_top_unipotent_iff,
    Valuation.map_neg, and_self]

variable (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

def rep (dn : ℤ × ℤ) : G₂ :=
  scalarPi (ϖ : F) ϖ.ne_zero ^ dn.2 * diagZ (ϖ : F) ϖ.ne_zero dn.1

theorem rep_eq (dn : ℤ × ℤ) :
    rep p ϖ dn = Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2) * diagZ (ϖ : F) ϖ.ne_zero dn.1 := by
  rw [rep, scalarPi_zpow_eq_scalar]

theorem slice_eq (dn : ℤ × ℤ) :
    {x : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range |
        (rep p ϖ dn)⁻¹ * (x : G₂) * rep p ϖ dn ∈ K₀}
      = (fun y : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range =>
            ((y : G₂) : Matrix (Fin 2) (Fin 2) F) 0 1) ⁻¹'
          ((fun z => (((ϖ ^ dn.1)⁻¹ : Fˣ) : F) * z) ⁻¹' {z : F | Valued.v z ≤ 1}) := by
  ext x
  obtain ⟨t, ht⟩ := exists_eq_upperUnipotent2_of_mem_range p x.2
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ht, upperUnipotent2_coe, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hconj : (rep p ϖ dn)⁻¹ * upperUnipotent2 p t * rep p ϖ dn
      = upperUnipotent2 p ((ϖ : F) ^ (-dn.1) * t) := by
    rw [rep_eq]
    have key : (Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2))⁻¹ * upperUnipotent2 p t
        * Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2) = upperUnipotent2 p t := by
      rw [mul_assoc, ← scalar_mul_comm p (ϖ ^ dn.2) (upperUnipotent2 p t), ← mul_assoc, inv_mul_cancel, one_mul]
    have : (Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2) * diagZ (ϖ : F) ϖ.ne_zero dn.1)⁻¹
        * upperUnipotent2 p t * (Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2) * diagZ (ϖ : F) ϖ.ne_zero dn.1)
        = (diagZ (ϖ : F) ϖ.ne_zero dn.1)⁻¹ * upperUnipotent2 p t * diagZ (ϖ : F) ϖ.ne_zero dn.1 := by
      calc _ = (diagZ (ϖ : F) ϖ.ne_zero dn.1)⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2))⁻¹
            * upperUnipotent2 p t * Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2)) * diagZ (ϖ : F) ϖ.ne_zero dn.1 := by
              simp only [mul_inv_rev, mul_assoc]
        _ = _ := by rw [key]
    rw [this]
    exact Units.ext (by rw [coe_diagZ_inv_mul_unipotent_mul_diagZ, upperUnipotent2_coe])
  rw [hconj, upperUnipotent2_mem_iff, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, ← zpow_neg]

include hϖ in

theorem measure_slice (dn : ℤ × ℤ) :
    letI := localGLBorel ℚ p
    ∀ (μN₂ : Measure ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range) [μN₂.IsHaarMeasure],
      μN₂ {x : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range |
          (rep p ϖ dn)⁻¹ * (x : G₂) * rep p ϖ dn ∈ K₀}
        = ((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-dn.1) : ℝ≥0) *
          μN₂ ((fun y : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range =>
              ((y : G₂) : Matrix (Fin 2) (Fin 2) F) 0 1) ⁻¹' {z : F | Valued.v z ≤ 1}) := by
  intro μN₂ _
  rw [slice_eq, measure_unipotentEntry_preimage_mul_eq p μN₂ (ϖ ^ dn.1)]
  congr 1
  have hv : Valued.v (((ϖ ^ dn.1 : Fˣ)) : F) = WithZero.exp (-dn.1) := by
    rw [Units.val_zpow_eq_zpow_val]; exact valued_varpi_zpow p ϖ hϖ dn.1
  have h := coe_modulus_eq_norm p (((ϖ ^ dn.1 : Fˣ)) : F)
  rw [norm_eq_zpow_of_valued p hv] at h
  have h' : modulus (((ϖ ^ dn.1 : Fˣ)) : F) = (Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-dn.1) := by
    apply NNReal.coe_injective
    rw [h, NNReal.coe_zpow, NNReal.coe_natCast]
  rw [h']

theorem cpow_key (q : ℝ) (hq : 0 < q) (m : ℤ) (s : ℂ) :
    (((q ^ (-m) : ℝ)) : ℂ) ^ (s + 1 / 2 - 1 / 2) = ((q : ℂ) ^ (-s)) ^ m := by
  have hs : s + 1 / 2 - 1 / 2 = s := by ring
  rw [hs]
  have hqm : (0 : ℝ) < q ^ (-m) := zpow_pos hq _
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Complex.cpow_int_mul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hqm.ne'),
    Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_log hqm.le, ← Complex.ofReal_log hq.le,
    Real.log_zpow]
  congr 1
  push_cast
  ring

include hϖ in

theorem modulus_det_rep_mul (dn : ℤ × ℤ) {k : G₂} (hk : k ∈ K₀) :
    ((modulus ((Matrix.GeneralLinearGroup.det (rep p ϖ dn * k) : Fˣ) : F) : ℝ))
      = (Ideal.absNorm p.asIdeal : ℝ) ^ (-(dn.1 + 2 * dn.2)) := by
  rw [coe_modulus_eq_norm, rep_eq, map_mul, map_mul, Units.val_mul, Units.val_mul, norm_mul, norm_mul,
    norm_det_eq_one_of_mem p hk, mul_one, coe_det_scalar, coe_det_diagZ, norm_mul,
    Units.val_zpow_eq_zpow_val]
  simp only [norm_varpi_zpow p ϖ hϖ]
  rw [← zpow_add₀ (absNorm_pos p).ne', ← zpow_add₀ (absNorm_pos p).ne']
  congr 1; ring

end

end D2T

namespace D2T

noncomputable section

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "K₀" => (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)

def fS (φ w₂ : G₂ → ℂ) (Φ₂ : F × F → ℂ) (s : ℂ) (g : G₂) : ℂ :=
  Wp p φ g * (w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1)) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)

private theorem alg1 {a e b c d m : ℂ} (h : a * e = 1) : a * b * (e * c * d) * m = b * (c * d) * m := by
  calc a * b * (e * c * d) * m = (a * e) * (b * (c * d) * m) := by ring
    _ = _ := by rw [h, one_mul]

theorem fS_upperUnipotent2_mul {θ₀ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ}
    {φ w₂ : G₂ → ℂ} {Φ₂ : F × F → ℂ} {s : ℂ} (hw : WProps p θ₀ w₂) (t : F) (g : G₂) :
    fS p φ w₂ Φ₂ s (upperUnipotent2 p t * g) = fS p φ w₂ Φ₂ s g := by
  obtain ⟨hw1, -, -⟩ := hw
  simp only [fS, Wp_upperUnipotent2_mul, hw1, upperUnipotent2_mul_apply_one, det_upperUnipotent2_mul]
  have h : NumberField.StandardAddChar.psiLocal ℚ p (-t) * NumberField.StandardAddChar.psiLocal ℚ p t = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  exact alg1 h

theorem measurable_fS {μ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)}
    {θ₀ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ}
    {φ w₂ : G₂ → ℂ} {Φ₂ : F × F → ℂ} (hφ : φ ∈ principalSeries2 p μ) (hw : WProps p θ₀ w₂)
    (hΦ : IsLocallyConstant Φ₂) (s : ℂ) :
    letI := localGLBorel ℚ p
    Measurable (fS p φ w₂ Φ₂ s) := by
  letI := localGLBorel ℚ p
  haveI : BorelSpace G₂ := borelSpace_localGLBorel ℚ p
  obtain ⟨U, hU, hφU⟩ := exists_isOpen_forall_mul_eq_of_mem_principalSeries2 p μ φ hφ
  have hWc : Continuous (Wp p φ) :=
    continuous_of_forall_mul_eq p _ U hU (fun k hk g => Wp_mul_right_of_forall p φ (hφU k hk) g)
  obtain ⟨-, -, V, hV, hwV⟩ := hw
  have hwc : Continuous w₂ := continuous_of_forall_mul_eq p _ V hV hwV
  have hval : Continuous fun g : G₂ => (g : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hrow : Continuous fun g : G₂ => ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1) :=
    (hval.matrix_elem 1 0).prodMk (hval.matrix_elem 1 1)
  have hΦc : Continuous Φ₂ := hΦ.continuous
  have hdet : Continuous fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) := by
    have : (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ))
        = fun g : G₂ => (((‖((g : G₂) : Matrix (Fin 2) (Fin 2) F).det‖ : ℝ)) : ℂ) := by
      funext g; rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Complex.continuous_ofReal.comp (continuous_norm.comp hval.matrix_det)
  exact ((hWc.mul (hwc.mul (hΦc.comp hrow))).measurable).mul (hdet.measurable.pow_const _)

variable (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

include hϖ in
theorem fS_rep_mul {μ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)}
    {θ₀ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ}
    {φ w₂ : G₂ → ℂ} {Φ₂ : F × F → ℂ} (hφ : φ ∈ principalSeries2 p μ) (hw : WProps p θ₀ w₂)
    (s : ℂ) (dn : ℤ × ℤ) {k : G₂} (hk : k ∈ K₀) :
    fS p φ w₂ Φ₂ s (rep p ϖ dn * k)
      = ((((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2)) *
        (Wp p φ (diagZ (ϖ : F) ϖ.ne_zero dn.1 * k) * w₂ (diagZ (ϖ : F) ϖ.ne_zero dn.1 * k) *
          Φ₂ ((ϖ : F) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) F) 1 0,
            (ϖ : F) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
  obtain ⟨-, hw2, -⟩ := hw
  have hmod := modulus_det_rep_mul p ϖ hϖ dn hk
  simp only [fS]
  rw [hmod, cpow_key (Ideal.absNorm p.asIdeal : ℝ) (absNorm_pos p) (dn.1 + 2 * dn.2) s]
  have hsplit : Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2) * diagZ (ϖ : F) ϖ.ne_zero dn.1 * k
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (ϖ ^ dn.2) * (diagZ (ϖ : F) ϖ.ne_zero dn.1 * k) := mul_assoc _ _ _
  rw [rep_eq, hsplit, Wp_scalar_mul p hφ, hw2, scalar_mul_apply, scalar_mul_apply,
    diagZ_mul_apply_one, diagZ_mul_apply_one]
  simp only [map_zpow, Units.val_zpow_eq_zpow_val, mul_zpow]
  push_cast
  ring

end

end D2T

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∀ s : ℂ,

            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →

            (∀ dn : ℤ × ℤ,
              IntegrableOn (fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))
                ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂) ∧

            Summable (fun dn : ℤ × ℤ =>
              ‖((((μN₂ ((fun y : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range =>
                    ((y : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹'
                    {z : p.adicCompletion ℚ | Valued.v z ≤ 1}))⁻¹).toReal : ℂ) *
                (Ideal.absNorm p.asIdeal : ℂ) ^ dn.1 *
                (((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2) *
                ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂)‖) ∧

            HasSum (fun dn : ℤ × ℤ =>
              ((((μN₂ ((fun y : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range =>
                    ((y : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹'
                    {z : p.adicCompletion ℚ | Valued.v z ≤ 1}))⁻¹).toReal : ℂ) *
                (Ideal.absNorm p.asIdeal : ℂ) ^ dn.1 *
                (((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2) *
                ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂))
              (RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) := by
  intro μ₂ _ μN₂ _ w₂ hw₂ s hInt
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  have hw : D2T.WProps p θ₀ w₂ := D2T.wProps_of_mem_span p θ₀ N hN w₂base hw₂law hw₂K hcentral hw₂
  have hfI : Integrable (D2T.fS p φ w₂ Φ₂ s)
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := hInt
  have hfm : Measurable (D2T.fS p φ w₂ Φ₂ s) := D2T.measurable_fS p hφ hw hΦ₂.1 s
  have hfN : ∀ x ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      D2T.fS p φ w₂ Φ₂ s (x * g) = D2T.fS p φ w₂ Φ₂ s g := by
    intro x hx g
    obtain ⟨t, rfl⟩ := D2T.exists_eq_upperUnipotent2_of_mem_range p hx
    exact D2T.fS_upperUnipotent2_mul p hw t g
  obtain ⟨hI1, hI2, hI3⟩ :=
    AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 ℚ p
      (D2T.varpiO p ϖ hϖ) ϖ.ne_zero hϖ μ₂ μN₂ (D2T.fS p φ w₂ Φ₂ s) hfm hfN hfI
  change ∀ dn : ℤ × ℤ, IntegrableOn (fun k => D2T.fS p φ w₂ Φ₂ s (D2T.rep p ϖ dn * k)) ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ at hI1
  change Summable (fun dn : ℤ × ℤ =>
      ((μN₂ {x : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range | (D2T.rep p ϖ dn)⁻¹ * (x : GL (Fin 2) (p.adicCompletion ℚ)) * D2T.rep p ϖ dn ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤})⁻¹).toReal *
        ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), ‖D2T.fS p φ w₂ Φ₂ s (D2T.rep p ϖ dn * k)‖ ∂μ₂) at hI2
  change HasSum (fun dn : ℤ × ℤ => ((((μN₂ {x : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range | (D2T.rep p ϖ dn)⁻¹ * (x : GL (Fin 2) (p.adicCompletion ℚ)) * D2T.rep p ϖ dn ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤})⁻¹).toReal : ℂ) *
          ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), D2T.fS p φ w₂ Φ₂ s (D2T.rep p ϖ dn * k) ∂μ₂))
      (∫ g, D2T.fS p φ w₂ Φ₂ s g ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) at hI3
  have hK₀ : MeasurableSet ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2.measurableSet
  have hq : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := D2T.absNorm_pos p
  have hqC : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hq.ne'

  have hCne : ∀ dn : ℤ × ℤ, ((((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2)) ≠ 0 := by
    intro dn
    refine mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)
    · exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _)
    · rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqC

  have key : ∀ dn : ℤ × ℤ, ((((μN₂ {x : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range | (D2T.rep p ϖ dn)⁻¹ * (x : GL (Fin 2) (p.adicCompletion ℚ)) * D2T.rep p ϖ dn ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤})⁻¹).toReal : ℂ) *
          ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), D2T.fS p φ w₂ Φ₂ s (D2T.rep p ϖ dn * k) ∂μ₂) =
      ((((μN₂ ((fun y : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range =>
                    ((y : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹'
                    {z : p.adicCompletion ℚ | Valued.v z ≤ 1}))⁻¹).toReal : ℂ) *
                (Ideal.absNorm p.asIdeal : ℂ) ^ dn.1 *
                (((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2) *
                ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂) := by
    intro dn
    rw [D2T.measure_slice p ϖ hϖ dn μN₂,
      setIntegral_congr_fun hK₀ (fun k hk => D2T.fS_rep_mul p ϖ hϖ hφ hw s dn hk), integral_const_mul]
    have hqnn : ((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-dn.1) : ℝ≥0) ≠ 0 :=
      zpow_ne_zero _ (by exact_mod_cast hq.ne')
    rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hqnn)) (Or.inl ENNReal.coe_ne_top),
      ENNReal.toReal_mul, ← ENNReal.coe_inv hqnn, ENNReal.coe_toReal, NNReal.coe_inv, NNReal.coe_zpow,
      NNReal.coe_natCast, ← zpow_neg, neg_neg]
    simp only [D2T.Wp]
    push_cast
    ring
  refine ⟨fun dn => ?_, ?_, ?_⟩
  ·
    refine IntegrableOn.congr_fun
      ((((hI1 dn).congr_fun (fun k hk => D2T.fS_rep_mul p ϖ hϖ hφ hw s dn hk) hK₀).const_mul
        ((((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2))⁻¹ : IntegrableOn _ _ μ₂))
      (fun k hk => ?_) hK₀
    simp only [D2T.Wp]
    rw [← mul_assoc, inv_mul_cancel₀ (hCne dn), one_mul]
  ·
    refine Summable.of_nonneg_of_le (fun dn => norm_nonneg _) (fun dn => ?_) hI2
    rw [← key dn, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) ENNReal.toReal_nonneg
  ·
    have e : (fun dn : ℤ × ℤ => ((((μN₂ {x : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range | (D2T.rep p ϖ dn)⁻¹ * (x : GL (Fin 2) (p.adicCompletion ℚ)) * D2T.rep p ϖ dn ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤})⁻¹).toReal : ℂ) *
          ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), D2T.fS p φ w₂ Φ₂ s (D2T.rep p ϖ dn * k) ∂μ₂)) = (fun dn : ℤ × ℤ =>
      ((((μN₂ ((fun y : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range =>
                    ((y : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹'
                    {z : p.adicCompletion ℚ | Valued.v z ≤ 1}))⁻¹).toReal : ℂ) *
                (Ideal.absNorm p.asIdeal : ℂ) ^ dn.1 *
                (((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2) *
                ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂)) := funext key
    rw [e] at hI3
    exact hI3

end S_LanglandsTunnell_RankinSelberg_hasSum_torusShells_rsLocalIntegral22_jacquetIntegral_schwartz_of_integrable
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_torusShells_rsLocalIntegral22_jacquetIntegral_schwartz_of_integrable (solution)
