-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8928a148-88b7-5020-b51b-62fcfbea33c4

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction NumberField.AdelicLevel Topology

open scoped NNReal ENNReal

namespace DualEulerGlue

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem norm_eq_zpow_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  positivity

theorem two_le_absNorm : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    omega
  exact_mod_cast h2

theorem isClosed_ball (k : ℤ) : IsClosed {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem isOpen_ball (k : ℤ) : IsOpen {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem sphere_eq_diff (k : ℤ) :
    {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k}
      = {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp k} \
          {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp (k - 1)} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨hy.le, fun h => ?_⟩
    rw [hy, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm]
    congr 1
    omega

theorem isClosed_sphere (k : ℤ) : IsClosed {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

theorem isOpen_sphere (k : ℤ) : IsOpen {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isOpen_ball v _).sdiff (isClosed_ball v _)

theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

theorem isCompact_ball_zero : IsCompact {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

def USet : Set (v.adicCompletion K)ˣ := {u : (v.adicCompletion K)ˣ | Valued.v (u : (v.adicCompletion K)) = 1}

theorem isOpen_USet : IsOpen (USet v) := by
  have := (isOpen_sphere v 0).preimage (Units.continuous_val (M := v.adicCompletion K))
  rwa [WithZero.exp_zero] at this

theorem one_mem_USet : (1 : (v.adicCompletion K)ˣ) ∈ USet v := by
  show Valued.v ((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1
  rw [Units.val_one, map_one]

theorem exists_valued_eq_exp (y : (v.adicCompletion K)ˣ) :
    ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m := by
  have hne : Valued.v (y : (v.adicCompletion K)) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  exact ⟨_, (WithZero.exp_log hne).symm⟩

theorem modulus_uniformizer_zpow_mul {n : ℤ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    (modulus ((uniformizerUnit K v ^ n * u : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) : ℝ)
      = (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) := by
  apply coe_modulus_of_valued v
  have hu' : Valued.v (u : (v.adicCompletion K)) = 1 := hu
  rw [Units.val_mul, map_mul, valued_uniformizerUnit_zpow, hu', mul_one]

theorem isLocallyConstant_of_forall_mul {X : Type*} (f : (v.adicCompletion K)ˣ → X)
    (W : Set (v.adicCompletion K)ˣ) (hW : IsOpen W) (h1 : (1 : (v.adicCompletion K)ˣ) ∈ W)
    (h : ∀ y, ∀ u ∈ W, f (y * u) = f y) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hopen : IsOpen ((fun u => y * u) '' W) := isOpenMap_mul_left y W hW
  have hmem : y ∈ (fun u => y * u) '' W := ⟨1, h1, mul_one y⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact h y u hu

theorem isAddHaarMeasure_selfDualHaarAt' :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal K v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt K v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end Kv

section RatLoc

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem range_val :
    Set.range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) = ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩

theorem measurableEmbedding_val :
    letI := localBorel ℚ v
    MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  exact MeasurableEmbedding.iff_comap_eq.mpr ⟨Units.val_injective, rfl, by
    rw [range_val]
    exact (measurableSet_singleton 0).compl⟩

theorem locMul_USet :
    letI := localBorel ℚ v
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (USet v) =
      selfDualHaarAt ℚ v {u : v.adicCompletion ℚ | Valued.v u = 1} := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have himg : Units.val '' USet v = {u : v.adicCompletion ℚ | Valued.v u = 1} := by
    ext x
    simp only [Set.mem_image, USet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  have hS : MeasurableSet {u : v.adicCompletion ℚ | Valued.v u = 1} := by
    have := (isClosed_sphere v 0).measurableSet
    rwa [WithZero.exp_zero] at this
  rw [(measurableEmbedding_val v).comap_apply, himg, mulMeasure, withDensity_apply _ hS,
    Measure.restrict_restrict hS]
  have hsub : {u : v.adicCompletion ℚ | Valued.v u = 1} ∩ {0}ᶜ = {u : v.adicCompletion ℚ | Valued.v u = 1} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, and_iff_left_iff_imp]
    intro hx h0
    rw [h0, map_zero] at hx
    exact zero_ne_one hx
  rw [hsub]
  calc ∫⁻ x in {u : v.adicCompletion ℚ | Valued.v u = 1}, ((modulus x : ℝ≥0∞))⁻¹ ∂(selfDualHaarAt ℚ v)
      = ∫⁻ x in {u : v.adicCompletion ℚ | Valued.v u = 1}, 1 ∂(selfDualHaarAt ℚ v) := by
        refine setLIntegral_congr_fun hS fun x hx => ?_
        have hx' : Valued.v x = WithZero.exp 0 := by rw [WithZero.exp_zero]; exact hx
        have hm : modulus x = 1 := by
          rw [← NNReal.coe_inj, coe_modulus_of_valued v hx', zpow_zero, NNReal.coe_one]
        rw [hm, ENNReal.coe_one, inv_one]
    _ = selfDualHaarAt ℚ v {u : v.adicCompletion ℚ | Valued.v u = 1} := by
        rw [setLIntegral_one]

end RatLoc

end DualEulerGlue

namespace DualEulerGlue

section RatHelpers

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem valued_natCast' (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap v (n : 𝓞 ℚ)

theorem absNorm_span_intCast' (z : ℤ) : Ideal.absNorm (Ideal.span {(z : 𝓞 ℚ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) z, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one]

theorem absNorm_span_natCast' (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  simpa using absNorm_span_intCast' (n : ℤ)

theorem intValuation_absNorm' :
    v.intValuation (Ideal.absNorm v.asIdeal : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast'] at hdvd
    have hle' := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  have hr : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-(c : ℤ)) :=
    ⟨_, v.intValuation_if_neg hr⟩
  rw [hc, WithZero.exp_le_exp] at h1 h2
  rw [hc]
  congr 1
  omega

theorem valued_ratPrimeAt' : Valued.v (ratPrimeAt v) = Valued.v (varpi v) := by
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = _
  rw [valued_natCast', intValuation_absNorm']
  exact (AdelicLevel.valued_uniformizerUnit ℚ v).symm

def piOverP : (v.adicCompletion ℚ)ˣ := AdelicLevel.uniformizerUnit ℚ v * (ratPrimeUnit v)⁻¹

theorem valued_piOverP : Valued.v ((piOverP v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  simp only [piOverP, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [show ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v from rfl, valued_ratPrimeAt']
  exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr (varpi_ne_zero v))

theorem valued_piOverP_pow (n : ℕ) :
    Valued.v (((piOverP v ^ n : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
  rw [Units.val_pow_eq_pow_val, map_pow, valued_piOverP, one_pow]

theorem valued_piOverP_pow_inv (n : ℕ) :
    Valued.v ((((piOverP v ^ n)⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, valued_piOverP_pow, inv_one]

theorem coe_iotaGL_diagUnitGL2 (a : (v.adicCompletion ℚ)ˣ) :
    ((iotaGL (diagUnitGL2 a) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a : v.adicCompletion ℚ), 1, 1] := by
  rw [coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnitGL2]

theorem iotaGL_diagUnitGL2_mem {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    iotaGL (diagUnitGL2 u) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hu' : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have hinv : ((iotaGL (diagUnitGL2 u) : LocalGL3 v))⁻¹ = iotaGL (diagUnitGL2 u⁻¹) := by
    rw [← diagHom_apply, ← diagHom_apply, ← map_inv, ← map_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_iotaGL_diagUnitGL2]
    fin_cases i <;> fin_cases j <;> simp [hu]
  · rw [hinv, coe_iotaGL_diagUnitGL2]
    fin_cases i <;> fin_cases j <;> simp [hu, hu']

theorem lowerUnipotent21_mem {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) :
    (lowerUnipotent21 x : LocalGL3 v) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hx' : Valued.v (-x) ≤ 1 := by rwa [Valuation.map_neg]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [lowerUnipotent21_coe]
    fin_cases i <;> fin_cases j <;> simp <;> first | exact hx | exact hx'
  · rw [show (((lowerUnipotent21 x : LocalGL3 v))⁻¹ : LocalGL3 v) = lowerUnipotent21 (-x) from
      inv_eq_of_mul_eq_one_right (by
        apply Units.ext
        rw [Units.val_mul, lowerUnipotent21_coe, lowerUnipotent21_coe, Units.val_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]), lowerUnipotent21_coe]
    fin_cases i <;> fin_cases j <;> simp <;> first | exact hx' | exact hx

theorem hasSum_int_of_hasSum_nat {f : ℤ → ℂ} (hf : ∀ m : ℤ, m < 0 → f m = 0) {L : ℂ}
    (h : HasSum (fun n : ℕ => f n) L) : HasSum f L := by
  refine (Function.Injective.hasSum_iff Nat.cast_injective ?_).mp h
  intro m hm
  refine hf m (lt_of_not_ge fun h0 => hm ?_)
  exact ⟨m.toNat, Int.toNat_of_nonneg h0⟩

end RatHelpers

end DualEulerGlue

namespace DualEulerGlue

section PerPlace

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem perPlace (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (Wd : LocalGL3 v → ℂ) (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) Wd)
    (hlaw : IsGL3PsiWhittakerFn ψv Wd) (h1 : Wd 1 = 1)
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 1) (hP3 : P.natDegree ≤ 3)
    (hPB : ‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖ ≤ 7)
    (htv : ∀ n : ℕ, Wd (iotaTorusLocal v n) =
      (cNormQ v)⁻¹ ^ n * sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n)
    (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχu : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χv u = 1)
    (hχ1 : ∀ y : (v.adicCompletion ℚ)ˣ, ‖((χv y : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 3 < s.re) :
    letI := localBorel ℚ v
    Integrable (fun y => Wd (lowerUnipotent21 y)) (selfDualHaarAt ℚ v) ∧
    (((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
      ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Wd χv s 1 =
      (P.eval (((χv (uniformizerUnit ℚ v) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
    (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))⁻¹ *
        (∫ y, ‖Wd (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v)) - 1 = 0) ∧
    ‖(P.eval (((χv (uniformizerUnit ℚ v) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ - 1‖ ≤
      56 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt' v

  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hN
  set ϖ : (v.adicCompletion ℚ)ˣ := uniformizerUnit ℚ v with hϖ
  set t : ℕ → ℂ := sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) with ht
  set x : ℂ := ((χv ϖ : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) with hx
  set sd := selfDualHaarAt ℚ v with hsd
  set μx : Measure (v.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure sd) with hμx
  set ball : Set (v.adicCompletion ℚ) := {y | Valued.v y ≤ 1} with hball
  set sph : Set (v.adicCompletion ℚ) := {u | Valued.v u = 1} with hsph
  have hN2 : 2 ≤ N := two_le_absNorm v
  have hNpos : 0 < N := absNorm_pos v
  have hNC0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hballeq : ball = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [coe_integers_eq, WithZero.exp_zero]
  have hball_meas : MeasurableSet ball := by
    rw [hballeq, coe_integers_eq]; exact (isClosed_ball v 0).measurableSet
  have hball_fin : sd ball < ⊤ := by
    rw [hballeq, coe_integers_eq]; exact (isCompact_ball_zero v).measure_lt_top
  have hball_pos : 0 < sd ball := by
    rw [hballeq, coe_integers_eq]
    exact (isOpen_ball v 0).measure_pos sd ⟨0, by simp⟩
  have hV0 : sd.real ball ≠ 0 := by
    rw [Measure.real]
    exact (ENNReal.toReal_pos hball_pos.ne' hball_fin.ne).ne'
  have hsph_meas : MeasurableSet sph := by
    have := (isClosed_sphere v 0).measurableSet
    rwa [WithZero.exp_zero] at this
  have hsph_fin : sd sph < ⊤ := by
    refine lt_of_le_of_lt (measure_mono ?_) hball_fin
    intro u hu; exact le_of_eq hu
  have hsph_pos : 0 < sd sph := by
    have hopen : IsOpen sph := by
      have := isOpen_sphere v 0
      rwa [WithZero.exp_zero] at this
    exact hopen.measure_pos sd ⟨1, by simp [hsph]⟩
  have hV1 : sd.real sph ≠ 0 := by
    rw [Measure.real]
    exact (ENNReal.toReal_pos hsph_pos.ne' hsph_fin.ne).ne'
  have hμxU : μx (USet v) = sd sph := locMul_USet v
  have hV1' : (μx (USet v)).toReal = sd.real sph := by rw [hμxU, Measure.real]

  have hψ1e : ∃ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (1 : ℤ) ∧ ψv y ≠ 1 := by
    obtain ⟨y, hy, hne⟩ := hψ1
    refine ⟨(varpi v)⁻¹ * y, ?_, hne⟩
    rw [map_mul, map_inv₀, show Valued.v (varpi v) = WithZero.exp (-1 : ℤ) from valued_uniformizerUnit ℚ v,
      ← WithZero.exp_neg, neg_neg]
    calc WithZero.exp (1 : ℤ) * Valued.v y ≤ WithZero.exp 1 * 1 := mul_le_mul_right hy _
      _ = WithZero.exp 1 := mul_one _
  have hline : ∀ (a : (v.adicCompletion ℚ)ˣ) (y : v.adicCompletion ℚ),
      Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 y) = ball.indicator (fun _ => Wd (iotaGL (diagUnitGL2 a))) y := by
    intro a y
    by_cases hy : Valued.v y ≤ 1
    · rw [Set.indicator_of_mem (show y ∈ ball from hy)]
      exact hK _ _ (lowerUnipotent21_mem v hy)
    · rw [Set.indicator_of_notMem (show y ∉ ball from hy)]
      by_contra hne
      have hmem := LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero v ψv hψ1e
        Wd hlaw hK a y hne
      exact hy ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hmem)

  have hbig : ∀ a : (v.adicCompletion ℚ)ˣ, 1 < Valued.v (a : v.adicCompletion ℚ) → Wd (iotaGL (diagUnitGL2 a)) = 0 :=
    fun a ha => LanglandsTunnell.CubicInduction.eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv Wd
      hK hlaw hψ1 _ ![(a : v.adicCompletion ℚ), 1, 1] (coe_iotaGL_diagUnitGL2 v a) (Or.inl (by simpa using ha))

  have hunit : ∀ (a u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      Wd (iotaGL (diagUnitGL2 (a * u))) = Wd (iotaGL (diagUnitGL2 a)) := by
    intro a u hu
    rw [← diagHom_apply, map_mul, map_mul, diagHom_apply, diagHom_apply]
    exact hK _ _ (iotaGL_diagUnitGL2_mem v hu)
  have hshell : ∀ (n : ℕ) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      Wd (iotaGL (diagUnitGL2 (ϖ ^ n * u))) = (cNormQ v)⁻¹ ^ n * t n := by
    intro n u hu
    have hdec : ϖ ^ n * u = ratPrimeUnit v ^ n * (piOverP v ^ n * u) := by
      rw [piOverP, mul_pow, inv_pow, ← mul_assoc, ← mul_assoc, mul_comm (ratPrimeUnit v ^ n) (uniformizerUnit ℚ v ^ n),
        mul_assoc (uniformizerUnit ℚ v ^ n), mul_inv_cancel, mul_one]
    have hu' : Valued.v (((piOverP v ^ n * u : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_mul, map_mul, valued_piOverP_pow, hu, one_mul]
    rw [hdec, hunit _ _ hu', ← htv n, iotaTorusLocal, diagHom_apply]

  set φ : (v.adicCompletion ℚ)ˣ → ℂ := fun y =>
    Wd (iotaGL (diagUnitGL2 y)) * ((modulus (y : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (2 : ℂ) with hφ
  have htnorm : ∀ n : ℕ, ‖t n‖ ≤ (7 : ℝ) ^ n := by
    intro n
    have h := (LanglandsTunnell.CubicInduction.mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum P hP0 hP3).2.1 n
    refine h.trans (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) (max_le (by norm_num) hPB) n)
  have hmod_unit : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      (modulus (u : v.adicCompletion ℚ) : ℝ) = 1 := by
    intro u hu
    have hu' : Valued.v (u : v.adicCompletion ℚ) = WithZero.exp 0 := by rw [WithZero.exp_zero]; exact hu
    rw [coe_modulus_of_valued v hu', zpow_zero]
  have hφU : ∀ (y u : (v.adicCompletion ℚ)ˣ), u ∈ USet v → φ (y * u) = φ y := by
    intro y u hu
    simp only [hφ]
    rw [hunit y u hu, Units.val_mul, modulus_mul, NNReal.coe_mul, hmod_unit u hu, mul_one]
  have hφlc : IsLocallyConstant φ := isLocallyConstant_of_forall_mul v φ (USet v) (isOpen_USet v) (one_mem_USet v) hφU
  have hνlc : IsLocallyConstant fun y : (v.adicCompletion ℚ)ˣ => ((χv y : ℂˣ) : ℂ) :=
    isLocallyConstant_of_forall_mul v _ (USet v) (isOpen_USet v) (one_mem_USet v) (fun y u hu => by
      rw [map_mul, hχu u hu, mul_one])
  have hcN : cNormQ v = (Ideal.absNorm v.asIdeal : ℂ) := rfl
  have hφ_shell_nat : ∀ (n : ℕ) (u : (v.adicCompletion ℚ)ˣ), u ∈ USet v →
      φ (ϖ ^ (n : ℤ) * u) = t n * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n : ℂ))) := by
    intro n u hu
    simp only [hφ]
    rw [zpow_natCast, hshell n u hu, show ϖ ^ n * u = ϖ ^ (n : ℤ) * u by rw [zpow_natCast],
      modulus_uniformizer_zpow_mul v hu, Complex.ofReal_zpow, Complex.ofReal_natCast, Complex.cpow_two, hcN, inv_pow]
    have h1 : ((Ideal.absNorm v.asIdeal : ℂ) ^ n)⁻¹ = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(n : ℂ)) := by rw [Complex.cpow_neg, Complex.cpow_natCast]
    have h2 : ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(n : ℤ))) ^ 2 = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * (n : ℂ))) := by
      rw [← Complex.cpow_intCast, ← Complex.cpow_nat_mul]; congr 1; push_cast; ring
    rw [h1, h2, mul_comm ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(n : ℂ))) (t n), mul_assoc, ← Complex.cpow_add _ _ hNC0]
    congr 2
    ring
  have hφ_shell_neg : ∀ (n : ℤ), n < 0 → ∀ u : (v.adicCompletion ℚ)ˣ, u ∈ USet v → φ (ϖ ^ n * u) = 0 := by
    intro n hn u hu
    simp only [hφ]
    have hv : 1 < Valued.v (((ϖ ^ n * u : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) := by
      have hu' : Valued.v (u : v.adicCompletion ℚ) = 1 := hu
      rw [Units.val_mul, map_mul, hϖ, valued_uniformizerUnit_zpow, hu', mul_one, ← WithZero.exp_zero,
        WithZero.exp_lt_exp]
      omega
    rw [hbig _ hv, zero_mul]
  have hφ_bound : ∀ y : (v.adicCompletion ℚ)ˣ, ‖φ y‖ ≤ 1 * max 1 ((modulus (y : v.adicCompletion ℚ)) ^ 0)⁻¹ := by
    intro y
    rw [pow_zero, inv_one, max_self, NNReal.coe_one, one_mul]
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v y

    set u : (v.adicCompletion ℚ)ˣ := ϖ ^ m * y with hu
    have huU : u ∈ USet v := by
      show Valued.v ((ϖ ^ m * y : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1
      rw [Units.val_mul, map_mul, hϖ, valued_uniformizerUnit_zpow, hm, ← WithZero.exp_add, neg_add_cancel,
        WithZero.exp_zero]
    have hy : y = ϖ ^ (-m) * u := by rw [hu, ← mul_assoc, _root_.zpow_neg, inv_mul_cancel, one_mul]
    rcases lt_or_ge 0 m with hm0 | hm0
    · rw [hy, hφ_shell_neg (-m) (by omega) u huU, norm_zero]; exact zero_le_one
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, -m = (n : ℤ) := ⟨(-m).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
      rw [hy, hn, hφ_shell_nat n u huU, norm_mul,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))]

      have h7 : ‖t n‖ ≤ (7 : ℝ) ^ n := htnorm n
      have hre : (-(3 * (n : ℂ))).re = -(3 * (n : ℝ)) := by simp
      rw [hre, Real.rpow_neg (Nat.cast_nonneg _), ← hN, show (3 * (n : ℝ)) = ((3 * n : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, ← div_eq_mul_inv, div_le_one (pow_pos hNpos _), pow_mul]
      refine h7.trans (pow_le_pow_left₀ (by norm_num) ?_ n)
      calc (7 : ℝ) ≤ 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN2 3
  have hφ_big : ∀ y : (v.adicCompletion ℚ)ˣ, (1 : ℝ) < modulus (y : v.adicCompletion ℚ) → φ y = 0 := by
    intro y hy
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v y
    have hmod : (modulus (y : v.adicCompletion ℚ) : ℝ) = N ^ m := coe_modulus_of_valued v hm
    have hm0 : 0 < m := by
      by_contra h
      have : (N : ℝ) ^ m ≤ 1 := zpow_le_one_of_nonpos₀ (by linarith) (by omega)
      have hy' : (1 : ℝ) < (modulus (y : v.adicCompletion ℚ) : ℝ) := by exact_mod_cast hy
      linarith
    simp only [hφ]
    rw [hbig y (by rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp]; exact hm0), zero_mul]
  have hz : ((0 : ℕ) : ℝ) < (s - 3).re := by simp; linarith
  obtain ⟨hint, -, hsum⟩ :=
    LanglandsTunnell.TateLocal.integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le ℚ v sd φ hφlc
      1 0 hφ_bound 1 hφ_big χv hνlc 1 (fun u hu => (hχ1 u).le) (hχ1 _) (s - 3) hz

  have hshellInt : ∀ n : ℤ, (∫ u in USet v, φ (ϖ ^ n * u) * ((χv u : ℂˣ) : ℂ) ∂μx) =
      if n < 0 then 0 else (μx (USet v)).toReal * (t n.toNat * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n.toNat : ℂ)))) := by
    intro n
    split_ifs with hn
    · refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      rw [hφ_shell_neg n hn u hu, zero_mul]
    · have hn' : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
      have hmeasU : MeasurableSet (USet v) := hsph_meas.preimage (comap_measurable Units.val)
      calc (∫ u in USet v, φ (ϖ ^ n * u) * ((χv u : ℂˣ) : ℂ) ∂μx)
          = ∫ u in USet v, t n.toNat * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n.toNat : ℂ))) ∂μx := by
            refine setIntegral_congr_fun hmeasU fun u hu => ?_
            rw [show χv u = 1 from hχu u hu, Units.val_one, mul_one]
            conv_lhs => rw [hn']
            exact hφ_shell_nat n.toNat u hu
        _ = (μx (USet v)).toReal * (t n.toNat * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n.toNat : ℂ)))) := by
            rw [setIntegral_const, Measure.real, Complex.real_smul]

  have hxnorm : ‖x‖ = N ^ (-s.re) := by
    rw [hx, norm_mul, hχ1, one_mul,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))]
    simp [hN]
  have hxle : ‖x‖ ≤ 1 / 8 := by
    rw [hxnorm, Real.rpow_neg hNpos.le, one_div]
    apply inv_anti₀ (by norm_num)
    calc (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
      _ ≤ N ^ (3 : ℝ) := Real.rpow_le_rpow (by norm_num) hN2 (by norm_num)
      _ ≤ N ^ s.re := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
  have hgen := LanglandsTunnell.CubicInduction.mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum P hP0 hP3
  have hxcond : ‖x‖ * max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖) < 1 := by
    calc ‖x‖ * max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖) ≤ (1 / 8) * 7 :=
          mul_le_mul hxle (max_le (by norm_num) hPB) (le_trans zero_le_one (le_max_left _ _)) (by norm_num)
      _ < 1 := by norm_num
  obtain ⟨hPx, hHS⟩ := hgen.2.2 x hxcond

  have hterm : ∀ n : ℕ,
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-(((n : ℤ) : ℂ) * (s - 3))) * ((χv ϖ : ℂˣ) : ℂ) ^ ((n : ℤ)) *
          ((μx (USet v)).toReal * (t n * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n : ℂ))))) =
        (μx (USet v)).toReal * (t n * x ^ n) := by
    intro n
    have hexp : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(((n : ℤ) : ℂ) * (s - 3))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n : ℂ))) =
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n := by
      rw [← Complex.cpow_add _ _ hNC0, ← Complex.cpow_nat_mul]
      congr 1
      push_cast
      ring
    calc (Ideal.absNorm v.asIdeal : ℂ) ^ (-(((n : ℤ) : ℂ) * (s - 3))) * ((χv ϖ : ℂˣ) : ℂ) ^ ((n : ℤ)) *
          ((μx (USet v)).toReal * (t n * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n : ℂ)))))
        = (μx (USet v)).toReal * (t n * (((χv ϖ : ℂˣ) : ℂ) ^ n *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(((n : ℤ) : ℂ) * (s - 3))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (n : ℂ)))))) := by
          rw [zpow_natCast]; ring
      _ = (μx (USet v)).toReal * (t n * x ^ n) := by rw [hexp, hx, mul_pow]
  have hHSZ : HasSum (fun n : ℤ =>
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * (s - 3))) * ((χv ϖ : ℂˣ) : ℂ) ^ n *
        ∫ u in USet v, φ (ϖ ^ n * u) * ((χv u : ℂˣ) : ℂ) ∂μx) ((μx (USet v)).toReal * (P.eval x)⁻¹) := by
    refine hasSum_int_of_hasSum_nat (fun m hm => by rw [hshellInt m, if_pos hm, mul_zero]) ?_
    have := hHS.mul_left ((μx (USet v)).toReal : ℂ)
    refine this.congr_fun fun n => ?_
    rw [hshellInt n, if_neg (by omega), Int.toNat_natCast, hterm n]
  have hIval : (∫ y, φ y * ((χv y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 3) ∂μx) =
      (μx (USet v)).toReal * (P.eval x)⁻¹ := hsum.unique hHSZ

  have hinner : ∀ a : (v.adicCompletion ℚ)ˣ,
      (∫ y : v.adicCompletion ℚ, Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 y * 1) ∂sd) =
        sd.real ball * Wd (iotaGL (diagUnitGL2 a)) := by
    intro a
    simp only [mul_one]
    rw [show (fun y => Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 y)) =
        ball.indicator (fun _ => Wd (iotaGL (diagUnitGL2 a))) from funext (hline a),
      integral_indicator_const _ hball_meas, Measure.real, Complex.real_smul]
  have hintegrand : ∀ a : (v.adicCompletion ℚ)ˣ,
      (∫ y : v.adicCompletion ℚ, Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 y * 1) ∂sd) * ((χv a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
        (sd.real ball : ℂ) * (φ a * ((χv a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 3)) := by
    intro a
    rw [hinner a]
    simp only [hφ]
    have hm0 : ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < modulus (a : v.adicCompletion ℚ) := by
        obtain ⟨m, hm⟩ := exists_valued_eq_exp v a
        rw [show (0 : ℝ) < modulus (a : v.adicCompletion ℚ) ↔ (0 : ℝ) < (modulus (a : v.adicCompletion ℚ) : ℝ)
          from Iff.rfl, coe_modulus_of_valued v hm]
        exact zpow_pos hNpos m
      exact_mod_cast this.ne'
    rw [show ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (2 : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 3)
        by rw [← Complex.cpow_add _ _ hm0]; congr 1; ring]
    ring
  have hZ : localZeta31 v μx sd Wd χv s 1 = (sd.real ball : ℂ) * ((μx (USet v)).toReal * (P.eval x)⁻¹) := by
    rw [localZeta31, show (fun a : (v.adicCompletion ℚ)ˣ => (∫ y : v.adicCompletion ℚ,
        Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 y * 1) ∂sd) * ((χv a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) = fun a => (sd.real ball : ℂ) *
        (φ a * ((χv a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 3)) from funext hintegrand,
      integral_const_mul, hIval]

  have hlineInt : (fun y => Wd (lowerUnipotent21 y)) = ball.indicator (fun _ => (1 : ℂ)) := by
    funext y
    have := hline 1 y
    rw [← diagHom_apply, map_one, map_one, one_mul, h1] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlineInt]
    exact (integrable_indicator_iff hball_meas).mpr (integrableOn_const hball_fin.ne)
  · rw [hballeq] at hZ hV0
    rw [hZ, hV1']
    have hA : ((sd.real sph : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV1
    have hB : ((sd.real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hV0
    rw [mul_assoc ((sd.real sph : ℝ) : ℂ)⁻¹, inv_mul_cancel_left₀ hB, inv_mul_cancel_left₀ hA]
  · have hnorm : (fun y => ‖Wd (lowerUnipotent21 y)‖) = ball.indicator (fun _ => (1 : ℝ)) := by
      funext y
      rw [show Wd (lowerUnipotent21 y) = ball.indicator (fun _ => (1 : ℂ)) y from congrFun hlineInt y]
      by_cases hy : y ∈ ball <;> simp [hy]
    rw [hnorm, integral_indicator_const _ hball_meas, smul_eq_mul, mul_one, ← hballeq, inv_mul_cancel₀ hV0, sub_self]
  ·
    have hsplit := (hHS.summable).hasSum_iff.mpr rfl
    have h0 : t 0 * x ^ 0 = 1 := by simp [ht, sphericalTorusValue]
    have htail : HasSum (fun n : ℕ => t (n + 1) * x ^ (n + 1)) ((P.eval x)⁻¹ - 1) := by
      have := (hasSum_nat_add_iff' 1).mpr hHS
      simp [h0] at this
      exact this
    have hgeo : HasSum (fun n : ℕ => (7 * ‖x‖) ^ (n + 1)) (7 * ‖x‖ / (1 - 7 * ‖x‖)) := by
      have hr : 7 * ‖x‖ < 1 := by linarith [hxle, norm_nonneg x]
      have hr0 : 0 ≤ 7 * ‖x‖ := by positivity
      have := (hasSum_geometric_of_lt_one hr0 hr).mul_left (7 * ‖x‖)
      rw [← div_eq_mul_inv] at this
      refine this.congr_fun fun n => ?_
      ring
    have hle : ‖(P.eval x)⁻¹ - 1‖ ≤ 7 * ‖x‖ / (1 - 7 * ‖x‖) := by
      refine htail.norm_le_of_bounded hgeo fun n => ?_
      rw [norm_mul, norm_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right (htnorm (n + 1)) (pow_nonneg (norm_nonneg _) _)
    refine hle.trans ?_
    rw [hxnorm, hN]
    have hr : N ^ (-s.re) ≤ 1 / 8 := hxnorm ▸ hxle
    have hr0 : 0 ≤ N ^ (-s.re) := Real.rpow_nonneg hNpos.le _
    rw [div_le_iff₀ (by linarith)]
    nlinarith

end PerPlace

end DualEulerGlue

open DualEulerGlue Polynomial in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w → w ∈ S)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hsph : ∀ v, v ∉ S →
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v))
    (h1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (htv : ∀ v, v ∉ S → HasSphericalTorusValuesAt (inducedCoeff K μ) v (Wloc v))
    (hlaw : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v))
    (hψ0 : ∀ v, v ∉ S → ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1)
    (hψ1 : ∀ v, v ∉ S → ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hχU : ∀ v, v ∉ S → TateGlobal.IsUnramifiedCharAt χ v)
    (σ₀ : ℝ) (hσ₀ : 3 ≤ σ₀) :
    (∀ v, v ∉ S →
      letI := localBorel ℚ v
      Integrable (fun y => dualWhittakerFn3 (Wloc v) (lowerUnipotent21 y)) (selfDualHaarAt ℚ v)) ∧
    (∀ v, v ∉ S → ∀ s : ℂ, σ₀ < s.re →
      letI := localBorel ℚ v
      ((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
        ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (selfDualHaarAt ℚ v) (dualWhittakerFn3 (Wloc v)) (TateGlobal.localChar χ v) s 1 =
        ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval
            (((TateGlobal.localChar χ v (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
    (Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖dualWhittakerFn3 (Wloc v.1) (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1) ∧
    (∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          letI := localBorel ℚ v.1
          ((selfDualHaarAt ℚ v.1).real {u : v.1.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
          ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZeta31 v.1 (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v.1)))
              (selfDualHaarAt ℚ v.1) (dualWhittakerFn3 (Wloc v.1)) (TateGlobal.localChar χ v.1) s 1)
        (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
          ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
              (((TateGlobal.localChar χ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
                (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))⁻¹)) := by

  have key : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ s : ℂ, 3 < s.re →
      letI := localBorel ℚ v
      Integrable (fun y => dualWhittakerFn3 (Wloc v) (lowerUnipotent21 y)) (selfDualHaarAt ℚ v) ∧
      (((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
        ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (selfDualHaarAt ℚ v) (dualWhittakerFn3 (Wloc v)) (TateGlobal.localChar χ v) s 1 =
        ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval
            (((TateGlobal.localChar χ v (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
      (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))⁻¹ *
          (∫ y, ‖dualWhittakerFn3 (Wloc v) (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v)) - 1 = 0) ∧
      ‖((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval
            (((TateGlobal.localChar χ v (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ - 1‖ ≤ 56 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
    intro v hv s hs
    have hnb : ¬ IsBadPlace K μ v := fun h => hv (hSbad v h)
    obtain ⟨he₃, -, hd₁, hd₂, hd₃, hb₁, hb₂, hb₃⟩ :=
      LanglandsTunnell.CubicInduction.inducedE_inducedCoeff_inv_eq_of_not_isBadPlace K hdeg μ hμ v hnb
    obtain ⟨hKW, -, -, hcen⟩ := hsph v hv
    obtain ⟨htv₁, htv₂⟩ := htv v hv
    obtain ⟨hKd, hlawd, h1d, -, htvd⟩ :=
      LanglandsTunnell.CubicInduction.dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues v (psiLoc ψ v) (Wloc v)
        hKW (hlaw v hv) (inducedE1 ℚ (inducedCoeff K μ) v) (inducedE2 ℚ (inducedCoeff K μ) v)
        (inducedE3 ℚ (inducedCoeff K μ) v) he₃ hcen (h1 v hv) htv₁ htv₂

    set Pc : Polynomial ℂ := C 1 - C (inducedE1 ℚ (inducedCoeff K μ⁻¹) v) * X + C (inducedE2 ℚ (inducedCoeff K μ⁻¹) v) * X ^ 2 -
      C (inducedE3 ℚ (inducedCoeff K μ⁻¹) v) * X ^ 3 with hPc
    have hc0 : Pc.coeff 0 = 1 := by simp [hPc, coeff_one, coeff_X, coeff_C, coeff_X_pow]
    have hc1 : Pc.coeff 1 = -inducedE1 ℚ (inducedCoeff K μ⁻¹) v := by simp [hPc, coeff_one, coeff_X, coeff_C, coeff_X_pow]
    have hc2 : Pc.coeff 2 = inducedE2 ℚ (inducedCoeff K μ⁻¹) v := by simp [hPc, coeff_one, coeff_X, coeff_C, coeff_X_pow]
    have hc3 : Pc.coeff 3 = -inducedE3 ℚ (inducedCoeff K μ⁻¹) v := by simp [hPc, coeff_one, coeff_X, coeff_C, coeff_X_pow]
    have hdeg3 : Pc.natDegree ≤ 3 := by
      rw [hPc]
      refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
        (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))) ((natDegree_C_mul_le _ _).trans (by simp))))
        ((natDegree_C_mul_le _ _).trans (by simp)))
    have hPB : ‖Pc.coeff 1‖ + ‖Pc.coeff 2‖ + ‖Pc.coeff 3‖ ≤ 7 := by
      rw [hc1, hc2, hc3, norm_neg, norm_neg]; linarith
    have heval : ∀ z : ℂ, Pc.eval z = (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval z := by
      intro z
      rw [LanglandsTunnell.RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three K hdeg.le]
      simp only [hPc, eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    have htv' : ∀ n : ℕ, dualWhittakerFn3 (Wloc v) (iotaTorusLocal v n) =
        (cNormQ v)⁻¹ ^ n * sphericalTorusValue (-Pc.coeff 1) (Pc.coeff 2) (-Pc.coeff 3) n := by
      intro n
      rw [htvd n, hc1, hc2, hc3, neg_neg, neg_neg, hd₁, hd₂, hd₃]
    have hψ1' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ (psiLoc ψ v)⁻¹ ((varpi v)⁻¹ * x) ≠ 1 := by
      obtain ⟨x, hx, hne⟩ := hψ1 v hv
      exact ⟨x, hx, by rwa [AddChar.inv_apply', inv_ne_one]⟩
    have hχu : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → TateGlobal.localChar χ v u = 1 := by
      intro u hu
      refine hχU v hv u ?_ ?_
      · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (le_of_eq hu)
      · refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (le_of_eq ?_)
        rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    have hχ1 : ∀ y : (v.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar χ v y : ℂˣ) : ℂ)‖ = 1 := fun y => hχ.2.2 _
    have h := perPlace v (psiLoc ψ v)⁻¹ hψ1' (dualWhittakerFn3 (Wloc v)) hKd hlawd h1d Pc hc0 hdeg3 hPB htv'
      (TateGlobal.localChar χ v) hχu hχ1 s hs
    rw [heval] at h
    exact h
  refine ⟨fun v hv => (key v hv 4 (by norm_num)).1, fun v hv s hs => (key v hv s (lt_of_le_of_lt hσ₀ hs)).2.1, ?_, ?_⟩
  · have h0 : (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
        letI := localBorel ℚ v.1
        ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
            * (∫ y, ‖dualWhittakerFn3 (Wloc v.1) (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1) =
        fun _ => 0 := funext fun v => (key v.1 v.2 4 (by norm_num)).2.2.1
    rw [h0]
    exact summable_zero
  · intro s hs
    have hs3 : 3 < s.re := lt_of_le_of_lt hσ₀ hs
    set g : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} → ℂ := fun v =>
      ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
          (((TateGlobal.localChar χ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
            (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))⁻¹ with hg
    have hfg : (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          letI := localBorel ℚ v.1
          ((selfDualHaarAt ℚ v.1).real {u : v.1.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
          ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZeta31 v.1 (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v.1)))
              (selfDualHaarAt ℚ v.1) (dualWhittakerFn3 (Wloc v.1)) (TateGlobal.localChar χ v.1) s 1) = g :=
      funext fun v => (key v.1 v.2 s hs3).2.1
    rw [hfg]
    have hmul : Multipliable g := by
      have hfun : g = fun v => 1 + (g v - 1) := by funext v; ring
      rw [hfun]
      refine Complex.multipliable_one_add_of_summable (Summable.of_norm ?_)
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => (key v.1 v.2 s hs3).2.2.2) ?_
      exact ((NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ (by linarith : (1 : ℝ) < s.re)).mul_left
        56).subtype _
    exact hmul.hasProd

end
end S_LanglandsTunnell_CubicInduction_hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le (solution)
