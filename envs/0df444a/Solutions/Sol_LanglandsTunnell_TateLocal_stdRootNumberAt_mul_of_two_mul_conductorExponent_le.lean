-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_two_mul_conductorExponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/47567e75-aab5-5fc8-a49f-5772a95e422a

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_two_mul_conductorExponent_le
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

noncomputable section

namespace GaussSumStability

section

open MeasureTheory LanglandsTunnell.TateLocal

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem lt_of_two_mul_le {a b : ℕ} (ha : 2 ≤ a) (hab : 2 * b ≤ a) : b < a := by omega

private theorem le_sub_index {a b : ℕ} (ha : 2 ≤ a) (hab : 2 * b ≤ a) : b ≤ a - ((a - 1) / 2 + 1) := by
  omega

private theorem index_le_pred {a : ℕ} (ha : 2 ≤ a) : (a - 1) / 2 + 1 ≤ a - 1 := by omega

private theorem sub_index_le_index (a : ℕ) : a - ((a - 1) / 2 + 1) ≤ (a - 1) / 2 + 1 := by omega

private theorem apply_eq_one_of_le {θ : (v.adicCompletion K)ˣ →* ℂˣ} {b k : ℕ}
    (hθ : HasConductorExponentAt K v θ b) (hbk : b ≤ k) {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ higherUnitsAt K v k) : θ u = 1 :=
  hθ.1 u (higherUnitsAt_antitone K v hbk hu)

private theorem mul_hasConductorExponentAt {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ}
    (hχ : HasConductorExponentAt K v χ a) (hθ : HasConductorExponentAt K v θ b) (ha : 2 ≤ a)
    (hab : 2 * b ≤ a) : HasConductorExponentAt K v (θ * χ) a := by
  have hba : b < a := lt_of_two_mul_le ha hab
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.mul_apply, hχ.1 u hu, apply_eq_one_of_le hθ hba.le hu, mul_one]
  · obtain ⟨u, hu, hne⟩ := hχ.2 (max m b) (max_lt hm hba)
    refine ⟨u, higherUnitsAt_antitone K v (le_max_left m b) hu, ?_⟩
    rw [MonoidHom.mul_apply, apply_eq_one_of_le hθ (le_max_right m b) hu, one_mul]
    exact hne

private theorem not_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) : ¬ HasConductorExponentAt K v χ 0 := fun h0 => by
  have := hasConductorExponentAt_unique K v hχ h0
  omega

private def gaussUnit (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) : ℂ :=
  letI := localBorel K v
  ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
    psiLocal K v
        (((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) * u)
      * charExt χ⁻¹ u ∂(selfDualHaarAt K v)

private def normFactor (a : ℕ) : ℂ :=
  ((((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ) : ℝ) : ℂ)) ^ (1 - (1 / 2 : ℂ))

private theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have hne : v.asIdeal ≠ ⊥ := v.ne_bot
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private theorem convergence_bound {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1 := by
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast (one_lt_absNorm (v := v))
  have hinv : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  rw [norm_mul, hinv, one_mul]
  have hre : (-(1 - (1 / 2 : ℂ))).re = -(1 / 2 : ℝ) := by norm_num
  rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt (one_lt_absNorm (v := v))), hre]
  have := Real.rpow_lt_one_of_one_lt_of_neg hN (by norm_num : (-(1 / 2 : ℝ)) < 0)
  exact_mod_cast this

private theorem volume_ne_zero (a : ℕ) (ha : 1 ≤ a) :
    letI := localBorel K v
    ((((selfDualHaarAt K v).real
        (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ) : ℂ)) ≠ 0 := by
  letI := localBorel K v
  rw [selfDualHaarAt_real_image_higherUnitsAt K v a ha]
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (one_lt_absNorm (v := v)))
  exact_mod_cast (mul_pos (zpow_pos hN _) (Real.rpow_pos_of_pos hN _)).ne'

private theorem stdRootNumberAt_eq_gaussUnit {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    stdRootNumberAt K v χ
      = (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ) * normFactor (K := K) (v := v) a
          * gaussUnit χ a := by
  letI := localBorel K v
  have hram := not_hasConductorExponentAt_zero ha hχ
  have hfwd := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt K v χ a ha hχ (1 / 2)
  have hdual := localZeta_tateFourier_stdTestFunAt K v χ a ha hχ (1 / 2) (convergence_bound hu)
  have hvol := volume_ne_zero (v := v) a ha
  rw [stdRootNumberAt_def]
  change localEpsilonAt K v (selfDualHaarAt K v) (psiLocal K v) (stdTestFunAt K v χ) χ (1 / 2) = _
  try dsimp only at hfwd hdual hvol
  rw [localEpsilonAt_of_not_hasConductorExponentAt_zero K v _ _ _ hram, localGammaAt, hdual, hfwd]
  simp only [normFactor, gaussUnit]
  field_simp

private theorem psiLocal_level_spec :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v)) → psiLocal K v x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v) + 1) ∧
        psiLocal K v x ≠ 1 :=
  forall_eq_one_and_exists_ne_one_of_addCharLevel K v (psiLocal K v)
    ⟨0, fun x hx => psiLocal_eq_one_of_mem_integers K v x (by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; simpa using hx)⟩
    (psiLocal_ne_one K v)

private theorem valued_pin {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 2 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (c : (v.adicCompletion K)ˣ)
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1))) :
    Valued.v (c : v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ) := by
  obtain ⟨hlev, x, hx, hψx⟩ := psiLocal_level_spec (K := K) (v := v)
  set n : ℤ := addCharLevel (psiLocal K v) with hn

  have hc0 : Valued.v (c : v.adicCompletion K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact c.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (c : v.adicCompletion K) = WithZero.exp k :=
    ⟨WithZero.log (Valued.v (c : v.adicCompletion K)), (WithZero.exp_log hc0).symm⟩
  rw [hk]
  congr 1

  have hlow : n + a ≤ k := by
    obtain ⟨u₀, hu₀, hne⟩ := hχ.2 (a - 1) (by omega)
    have hu₀m : u₀ ∈ higherUnitsAt K v ((a - 1) / 2 + 1) :=
      higherUnitsAt_antitone K v (index_le_pred ha) hu₀
    have hψne : psiLocal K v ((c : v.adicCompletion K) * ((u₀ : v.adicCompletion K) - 1)) ≠ 1 := by
      rw [← hc u₀ hu₀m]; exact fun h => hne (Units.val_eq_one.mp h)
    have hball : Valued.v ((u₀ : v.adicCompletion K) - 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ)) := by
      rcases ((mem_higherUnitsAt_iff K v).mp hu₀).2 with h0 | h
      · omega
      · exact h
    have hnot : ¬ Valued.v ((c : v.adicCompletion K) * ((u₀ : v.adicCompletion K) - 1)) ≤ WithZero.exp n :=
      fun h => hψne (hlev _ h)
    rw [Valuation.map_mul, hk] at hnot
    by_contra hcon
    apply hnot
    calc WithZero.exp k * Valued.v ((u₀ : v.adicCompletion K) - 1)
        ≤ WithZero.exp k * WithZero.exp (-((a - 1 : ℕ) : ℤ)) := by gcongr
      _ = WithZero.exp (k - ((a - 1 : ℕ) : ℤ)) := by rw [← WithZero.exp_add]; congr 1
      _ ≤ WithZero.exp n := WithZero.exp_le_exp.mpr (by push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; omega)

  have hupp : k ≤ n + a := by
    by_contra hcon
    push Not at hcon
    set y : v.adicCompletion K := x / (c : v.adicCompletion K) with hy
    have hyv : Valued.v y ≤ WithZero.exp (-(a : ℤ)) := by
      rw [hy, Valuation.map_div, hk, div_eq_mul_inv, ← WithZero.exp_neg]
      calc Valued.v x * WithZero.exp (-k) ≤ WithZero.exp (n + 1) * WithZero.exp (-k) := by gcongr
        _ = WithZero.exp (n + 1 + -k) := by rw [← WithZero.exp_add]
        _ ≤ WithZero.exp (-(a : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    have hylt : Valued.v y < Valued.v (1 : v.adicCompletion K) := by
      rw [Valuation.map_one]
      exact lt_of_le_of_lt hyv (by
        rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega))
    have hval : Valued.v (1 + y) = 1 := by
      rw [Valuation.map_add_eq_of_lt_left _ hylt, Valuation.map_one]
    have hne0 : (1 + y) ≠ 0 := fun h => by simp [h] at hval
    set u : (v.adicCompletion K)ˣ := Units.mk0 (1 + y) hne0 with hu
    have hua : u ∈ higherUnitsAt K v a := by
      refine (mem_higherUnitsAt_iff K v).mpr ⟨by simpa [hu] using hval, Or.inr ?_⟩
      simpa [hu] using hyv
    have hum : u ∈ higherUnitsAt K v ((a - 1) / 2 + 1) :=
      higherUnitsAt_antitone K v (by omega) hua
    have h1 : (χ u : ℂ) = 1 := by rw [hχ.1 u hua]; simp
    have h2 := hc u hum
    rw [h1] at h2
    apply hψx
    have hcy : (c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1) = x := by
      simp only [hu, Units.val_mk0, add_sub_cancel_left, hy]
      exact mul_div_cancel₀ x c.ne_zero
    rw [hcy] at h2
    exact h2.symm
  omega

section Mass

private def unitSet (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Set (v.adicCompletion K) :=
  {u | Valued.v u = 1}

private def ball (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Set (v.adicCompletion K) :=
  {x | Valued.v x ≤ WithZero.exp (-(m : ℤ))}

private theorem mem_unitSet {u : v.adicCompletion K} : u ∈ unitSet K v ↔ Valued.v u = 1 := Iff.rfl

private theorem mem_ball {m : ℕ} {x : v.adicCompletion K} :
    x ∈ ball K v m ↔ Valued.v x ≤ WithZero.exp (-(m : ℤ)) := Iff.rfl

private theorem mul_mem_unitSet_iff {ε : v.adicCompletion K} (hε : Valued.v ε = 1) {w : v.adicCompletion K} :
    ε * w ∈ unitSet K v ↔ w ∈ unitSet K v := by
  simp [mem_unitSet, Valuation.map_mul, hε]

private theorem charExt_mul_of_ne_zero (η : (v.adicCompletion K)ˣ →* ℂˣ) {x y : v.adicCompletion K} (hx : x ≠ 0)
    (hy : y ≠ 0) : charExt η (x * y) = charExt η x * charExt η y := by
  have hmk : Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy := Units.ext (by simp)
  rw [charExt_of_ne_zero η (mul_ne_zero hx hy), charExt_of_ne_zero η hx, charExt_of_ne_zero η hy, hmk, map_mul,
    Units.val_mul]

private theorem charExt_coe_units (η : (v.adicCompletion K)ˣ →* ℂˣ) (u : (v.adicCompletion K)ˣ) :
    charExt η (u : v.adicCompletion K) = (η u : ℂ) := by
  rw [charExt_of_ne_zero η u.ne_zero, Units.mk0_val]

private theorem charExt_mul_char (η₁ η₂ : (v.adicCompletion K)ˣ →* ℂˣ) {x : v.adicCompletion K} (hx : x ≠ 0) :
    charExt (η₁ * η₂) x = charExt η₁ x * charExt η₂ x := by
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, MonoidHom.mul_apply, Units.val_mul]

private theorem ne_zero_of_mem_unitSet {u : v.adicCompletion K} (hu : u ∈ unitSet K v) : u ≠ 0 := by
  intro h
  rw [mem_unitSet, h, Valuation.map_zero] at hu
  exact zero_ne_one hu

private theorem valued_one_add {m : ℕ} (hm : 1 ≤ m) {t : v.adicCompletion K} (ht : t ∈ ball K v m) :
    Valued.v (1 + t) = 1 := by
  rw [mem_ball] at ht
  have hlt : Valued.v t < Valued.v (1 : v.adicCompletion K) := by
    rw [Valuation.map_one]
    refine lt_of_le_of_lt ht ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  rw [Valuation.map_add_eq_of_lt_left _ hlt, Valuation.map_one]

private theorem one_add_ne_zero {m : ℕ} (hm : 1 ≤ m) {t : v.adicCompletion K} (ht : t ∈ ball K v m) :
    (1 + t : v.adicCompletion K) ≠ 0 := fun h => by
  have := valued_one_add hm ht
  rw [h, Valuation.map_zero] at this
  exact zero_ne_one this

private theorem mk0_one_add_mem {m : ℕ} (hm : 1 ≤ m) {t : v.adicCompletion K} (ht : t ∈ ball K v m) :
    Units.mk0 (1 + t) (one_add_ne_zero hm ht) ∈ higherUnitsAt K v m := by
  refine (mem_higherUnitsAt_iff K v).mpr ⟨?_, Or.inr ?_⟩
  · simpa using valued_one_add hm ht
  · simpa using (mem_ball.mp ht)

private theorem isAddHaar : letI := localBorel K v; (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast Nat.zero_lt_of_lt (one_lt_absNorm (v := v))
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

private theorem isRegular : letI := localBorel K v; (selfDualHaarAt K v).Regular := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  exact Measure.Regular.smul_nnreal _

private def piPow (k : ℤ) : v.adicCompletion K :=
  ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ k

private theorem valued_piPow (k : ℤ) : Valued.v (piPow (K := K) (v := v) k) = WithZero.exp (-k) := by
  rw [piPow, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

private theorem norm_le_norm_iff {x y : v.adicCompletion K} : ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y :=
  Valued.toNormedField.norm_le_iff

private theorem norm_lt_norm_iff {x y : v.adicCompletion K} : ‖x‖ < ‖y‖ ↔ Valued.v x < Valued.v y :=
  Valued.toNormedField.norm_lt_iff

private theorem norm_eq_one_of_valued_eq_one {u : v.adicCompletion K} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  have h1 : ‖u‖ ≤ ‖(1 : v.adicCompletion K)‖ := norm_le_norm_iff.mpr (by rw [hu, Valuation.map_one])
  have h2 : ‖(1 : v.adicCompletion K)‖ ≤ ‖u‖ := norm_le_norm_iff.mpr (by rw [hu, Valuation.map_one])
  rw [norm_one] at h1 h2
  exact le_antisymm h1 h2

private theorem modulus_eq_one_of_valued_eq_one {u : v.adicCompletion K} (hu : Valued.v u = 1) : modulus u = 1 := by
  rw [modulus_adicCompletion_eq_nnnorm K v u, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one]
  exact norm_eq_one_of_valued_eq_one hu

private theorem unitSet_eq : unitSet K v = {x : v.adicCompletion K | ‖x‖ = 1} := by
  ext x
  constructor
  · exact fun hx => norm_eq_one_of_valued_eq_one hx
  · intro hx
    have h1 : Valued.v x ≤ Valued.v (1 : v.adicCompletion K) := norm_le_norm_iff.mp (by rw [norm_one, hx])
    have h2 : Valued.v (1 : v.adicCompletion K) ≤ Valued.v x := norm_le_norm_iff.mp (by rw [norm_one, hx])
    rw [Valuation.map_one] at h1 h2
    exact le_antisymm h1 h2

private theorem ball_eq_le (m : ℕ) :
    ball K v m = {x : v.adicCompletion K | ‖x‖ ≤ ‖piPow (K := K) (v := v) (m : ℤ)‖} := by
  ext x
  rw [Set.mem_setOf_eq, norm_le_norm_iff, valued_piPow]
  exact Iff.rfl

private theorem ball_eq_lt (m : ℕ) :
    ball K v m = {x : v.adicCompletion K | ‖x‖ < ‖piPow (K := K) (v := v) ((m : ℤ) - 1)‖} := by
  ext x
  rw [Set.mem_setOf_eq, norm_lt_norm_iff, valued_piPow, neg_sub, mem_ball]
  by_cases hx : x = 0
  · subst hx
    simp only [Valuation.map_zero, zero_le', true_iff]
    exact zero_lt_iff.mpr WithZero.exp_ne_zero
  · have hx0 : Valued.v x ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hx
    rw [← WithZero.exp_log hx0, WithZero.exp_le_exp, WithZero.exp_lt_exp]
    omega

private theorem isClosed_unitSet : IsClosed (unitSet K v) := by
  rw [unitSet_eq]
  exact isClosed_eq continuous_norm continuous_const

private theorem isClosed_ball (m : ℕ) : IsClosed (ball K v m) := by
  rw [ball_eq_le]
  exact isClosed_le continuous_norm continuous_const

private theorem isOpen_ball (m : ℕ) : IsOpen (ball K v m) := by
  rw [ball_eq_lt]
  exact isOpen_lt continuous_norm continuous_const

private theorem isCompact_unitSet : IsCompact (unitSet K v) := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitSet ?_
  refine (Metric.isBounded_closedBall (x := (0 : v.adicCompletion K)) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff]
  exact (norm_eq_one_of_valued_eq_one hx).le

private theorem isCompact_ball (m : ℕ) : IsCompact (ball K v m) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_ball m) ?_
  refine (Metric.isBounded_closedBall (x := (0 : v.adicCompletion K))
    (r := ‖piPow (K := K) (v := v) (m : ℤ)‖)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff]
  rw [ball_eq_le] at hx
  exact hx

private theorem measurableSet_unitSet : letI := localBorel K v; MeasurableSet (unitSet K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  exact isClosed_unitSet.measurableSet

private theorem measurableSet_ball (m : ℕ) : letI := localBorel K v; MeasurableSet (ball K v m) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  exact (isClosed_ball m).measurableSet

private theorem closedBall_mem_nhds (w : v.adicCompletion K) (m : ℕ) :
    {y : v.adicCompletion K | Valued.v (y - w) ≤ WithZero.exp (-(m : ℤ))} ∈ nhds w := by
  have hopen : IsOpen ((fun y : v.adicCompletion K => y - w) ⁻¹' ball K v m) :=
    (isOpen_ball m).preimage (continuous_id.sub continuous_const)
  refine hopen.mem_nhds ?_
  show w - w ∈ ball K v m
  rw [mem_ball, sub_self, Valuation.map_zero]
  exact zero_le'

private theorem charExt_eq_of_close {η : (v.adicCompletion K)ˣ →* ℂˣ} {k : ℕ}
    (hη : ∀ u ∈ higherUnitsAt K v k, η u = 1)
    {w : v.adicCompletion K} (hw : w ∈ unitSet K v) {y : v.adicCompletion K}
    (hy : Valued.v (y - w) ≤ WithZero.exp (-((max k 1 : ℕ) : ℤ))) : charExt η y = charExt η w := by
  have hw0 : w ≠ 0 := ne_zero_of_mem_unitSet hw
  set t : v.adicCompletion K := w⁻¹ * (y - w) with ht_def
  have htv : Valued.v t ≤ WithZero.exp (-((max k 1 : ℕ) : ℤ)) := by
    rw [ht_def, Valuation.map_mul, map_inv₀, (mem_unitSet.mp hw), inv_one, one_mul]
    exact hy
  have ht : t ∈ ball K v (max k 1) := mem_ball.mpr htv
  have hk1 : 1 ≤ max k 1 := le_max_right k 1
  have hy_eq : y = w * (1 + t) := by
    rw [ht_def, mul_add, mul_one, mul_inv_cancel_left₀ hw0, add_sub_cancel]
  have hunit : (η (Units.mk0 (1 + t) (one_add_ne_zero hk1 ht)) : ℂ) = 1 := by
    have hmem := higherUnitsAt_antitone K v (le_max_left k 1) (mk0_one_add_mem hk1 ht)
    rw [hη _ hmem, Units.val_one]
  rw [hy_eq, charExt_mul_of_ne_zero η hw0 (one_add_ne_zero hk1 ht), charExt_of_ne_zero η (one_add_ne_zero hk1 ht),
    hunit, mul_one]

private theorem continuousOn_charExt {η : (v.adicCompletion K)ˣ →* ℂˣ} {k : ℕ}
    (hη : ∀ u ∈ higherUnitsAt K v k, η u = 1) :
    ContinuousOn (charExt η) (unitSet K v) := by
  intro w hw
  have hconst : charExt η =ᶠ[nhds w] fun _ => charExt η w :=
    Filter.eventually_of_mem (closedBall_mem_nhds w (max k 1)) fun y hy => charExt_eq_of_close hη hw hy
  exact (continuousWithinAt_const.congr_of_eventuallyEq (Filter.EventuallyEq.filter_mono hconst nhdsWithin_le_nhds)
    (by simp))

private theorem continuousOn_psi_mul (c : v.adicCompletion K) :
    ContinuousOn (fun w : v.adicCompletion K => psiLocal K v (c * w)) (unitSet K v) :=
  ((continuous_psiLocal K v).comp (continuous_const.mul continuous_id)).continuousOn

private theorem integrableOn_unitSet {g : v.adicCompletion K → ℂ} (hg : ContinuousOn g (unitSet K v)) :
    letI := localBorel K v; IntegrableOn g (unitSet K v) (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaar
  haveI : IsFiniteMeasure ((selfDualHaarAt K v).restrict (unitSet K v)) :=
    isFiniteMeasure_restrict.mpr (isCompact_unitSet (K := K) (v := v)).measure_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_unitSet (K := K) (v := v)).exists_bound_of_continuousOn hg
  refine Integrable.of_bound (hg.aestronglyMeasurable measurableSet_unitSet) C ?_
  exact (ae_restrict_mem measurableSet_unitSet).mono fun x hx => hC x hx

private theorem inv_apply_eq_one {η : (v.adicCompletion K)ˣ →* ℂˣ} {k : ℕ} (hη : HasConductorExponentAt K v η k) :
    ∀ u ∈ higherUnitsAt K v k, η⁻¹ u = 1 := fun u hu => by
  rw [MonoidHom.inv_apply, hη.1 u hu, inv_one]

private theorem integral_unit_mul {ε : v.adicCompletion K} (hε : Valued.v ε = 1) (f : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ x, f (ε * x) ∂(selfDualHaarAt K v) = ∫ x, f x ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaar
  haveI : (selfDualHaarAt K v).Regular := isRegular
  have hε0 : ε ≠ 0 := ne_zero_of_mem_unitSet (mem_unitSet.mpr hε)
  have h := tateFourier_comp_mul_left (v.adicCompletion K) (psiLocal K v) (selfDualHaarAt K v) f ε hε0 0
  simp only [tateFourier, mul_zero, AddChar.map_zero_eq_one, mul_one, modulus_eq_one_of_valued_eq_one hε,
    NNReal.coe_one, Complex.ofReal_one, inv_one, one_mul] at h
  exact h

private theorem setIntegral_unit_mul {ε : v.adicCompletion K} (hε : Valued.v ε = 1) (g : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ w in unitSet K v, g (ε * w) ∂(selfDualHaarAt K v) = ∫ w in unitSet K v, g w ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  rw [← integral_indicator measurableSet_unitSet, ← integral_indicator measurableSet_unitSet]
  have hind : (unitSet K v).indicator (fun w => g (ε * w)) = fun w => (unitSet K v).indicator g (ε * w) := by
    funext w
    by_cases hw : w ∈ unitSet K v <;> simp [Set.indicator_apply, mul_mem_unitSet_iff hε, hw]
  rw [hind]
  exact integral_unit_mul hε ((unitSet K v).indicator g)

private theorem integral_ball_psi (m : ℕ) (y : v.adicCompletion K) :
    letI := localBorel K v
    ∫ t in ball K v m, psiLocal K v (t * y) ∂(selfDualHaarAt K v)
      = (((selfDualHaarAt K v).real (ball K v m) : ℝ) : ℂ)
          * (if Valued.v y ≤ WithZero.exp (addCharLevel (psiLocal K v) + m) then 1 else 0) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaar
  obtain ⟨hlev, x, hx, hψx⟩ := psiLocal_level_spec (K := K) (v := v)

  have hL : tateFourier (psiLocal K v) (selfDualHaarAt K v) ((ball K v m).indicator fun _ => (1 : ℂ)) y
      = ∫ t in ball K v m, psiLocal K v (t * y) ∂(selfDualHaarAt K v) := by
    rw [← integral_indicator (measurableSet_ball m)]
    unfold tateFourier
    congr 1
    funext t
    by_cases ht : t ∈ ball K v m <;> simp [Set.indicator_apply, ht]
  have h := tateFourier_indicator_setOf_valued_sub_le K v (selfDualHaarAt K v) (psiLocal K v)
    (addCharLevel (psiLocal K v)) hlev ⟨x, hx, hψx⟩ 0 (m : ℤ) y
  simp only [sub_zero, zero_mul, AddChar.map_zero_eq_one, one_mul] at h
  change tateFourier (psiLocal K v) (selfDualHaarAt K v) ((ball K v m).indicator fun _ => (1 : ℂ)) y
    = (((selfDualHaarAt K v).real (ball K v m) : ℝ) : ℂ)
        * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (addCharLevel (psiLocal K v) + m)}.indicator
            (fun _ => (1 : ℂ)) y at h
  rw [← hL, h]
  by_cases hy : Valued.v y ≤ WithZero.exp (addCharLevel (psiLocal K v) + m) <;> simp [Set.indicator_apply, hy]

private theorem ballVol_ne_zero (m : ℕ) : letI := localBorel K v; (selfDualHaarAt K v).real (ball K v m) ≠ 0 := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaar
  have hpos : 0 < selfDualHaarAt K v (ball K v m) :=
    (isOpen_ball m).measure_pos _ ⟨0, by simp [mem_ball]⟩
  have hfin : selfDualHaarAt K v (ball K v m) ≠ ⊤ := (isCompact_ball m).measure_lt_top.ne
  rw [measureReal_def]
  exact (ENNReal.toReal_pos hpos.ne' hfin).ne'

private theorem le_index {a b : ℕ} (hab : 2 * b ≤ a) : b ≤ (a - 1) / 2 + 1 := by omega

private theorem one_le_index (a : ℕ) : 1 ≤ (a - 1) / 2 + 1 := Nat.le_add_left 1 _

private theorem index_le {a : ℕ} (ha : 2 ≤ a) : (a - 1) / 2 + 1 ≤ a := by omega

private def hInt (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : v.adicCompletion K) : ℂ :=
  letI := localBorel K v
  ∫ w in unitSet K v, psiLocal K v (c * w) * charExt η⁻¹ w ∂(selfDualHaarAt K v)

private def phi (χ θ : (v.adicCompletion K)ˣ →* ℂˣ) (c : v.adicCompletion K) (w : v.adicCompletion K) : ℂ :=
  psiLocal K v (c * w) * charExt χ⁻¹ w * (charExt θ⁻¹ w - 1)

private theorem continuousOn_phi {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (hχ : HasConductorExponentAt K v χ a)
    (hθ : HasConductorExponentAt K v θ b) (c : v.adicCompletion K) : ContinuousOn (phi χ θ c) (unitSet K v) :=
  ((continuousOn_psi_mul c).mul (continuousOn_charExt (inv_apply_eq_one hχ))).mul
    ((continuousOn_charExt (inv_apply_eq_one hθ)).sub continuousOn_const)

private theorem phi_one_add_mul {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (hθ : HasConductorExponentAt K v θ b)
    (hab : 2 * b ≤ a) {c : (v.adicCompletion K)ˣ}
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1)))
    {t : v.adicCompletion K} (ht : t ∈ ball K v ((a - 1) / 2 + 1)) {w : v.adicCompletion K} (hw : w ∈ unitSet K v) :
    phi χ θ (c : v.adicCompletion K) ((1 + t) * w)
      = phi χ θ (c : v.adicCompletion K) w * psiLocal K v (t * ((c : v.adicCompletion K) * (w - 1))) := by
  have hm1 := one_le_index a
  have hε0 : (1 + t : v.adicCompletion K) ≠ 0 := one_add_ne_zero hm1 ht
  have hw0 : w ≠ 0 := ne_zero_of_mem_unitSet hw
  have hmem := mk0_one_add_mem hm1 ht

  have hχε : charExt χ⁻¹ (1 + t) = (psiLocal K v ((c : v.adicCompletion K) * t))⁻¹ := by
    rw [charExt_of_ne_zero _ hε0, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hc _ hmem, Units.val_mk0,
      add_sub_cancel_left]
  have hθε : charExt θ⁻¹ (1 + t) = 1 := by
    rw [charExt_of_ne_zero _ hε0, inv_apply_eq_one hθ _ (higherUnitsAt_antitone K v (le_index hab) hmem),
      Units.val_one]

  have h1 : (c : v.adicCompletion K) * ((1 + t) * w)
      = (c : v.adicCompletion K) * w + t * ((c : v.adicCompletion K) * w) := by
    ring
  have h2 : t * ((c : v.adicCompletion K) * (w - 1))
      = t * ((c : v.adicCompletion K) * w) + -((c : v.adicCompletion K) * t) := by
    ring
  simp only [phi, charExt_mul_of_ne_zero _ hε0 hw0, hχε, hθε, one_mul, h1, h2, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv]
  ring

private theorem setIntegral_phi_eq {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (hθ : HasConductorExponentAt K v θ b)
    (hab : 2 * b ≤ a) {c : (v.adicCompletion K)ˣ}
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1)))
    {t : v.adicCompletion K} (ht : t ∈ ball K v ((a - 1) / 2 + 1)) :
    letI := localBorel K v
    ∫ w in unitSet K v, phi χ θ (c : v.adicCompletion K) w ∂(selfDualHaarAt K v)
      = ∫ w in unitSet K v,
          phi χ θ (c : v.adicCompletion K) w * psiLocal K v (t * ((c : v.adicCompletion K) * (w - 1)))
            ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  rw [← setIntegral_unit_mul (valued_one_add (one_le_index a) ht) (phi χ θ (c : v.adicCompletion K))]
  exact setIntegral_congr_fun measurableSet_unitSet fun w hw => phi_one_add_mul hθ hab hc ht hw

private theorem phi_mul_indicator_eq_zero {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (ha : 2 ≤ a)
    (hθ : HasConductorExponentAt K v θ b) (hab : 2 * b ≤ a) {c : (v.adicCompletion K)ˣ}
    (hvc : Valued.v (c : v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ)) (r : ℂ)
    {w : v.adicCompletion K} (hw : w ∈ unitSet K v) :
    phi χ θ (c : v.adicCompletion K) w
        * (r * (if Valued.v ((c : v.adicCompletion K) * (w - 1))
            ≤ WithZero.exp (addCharLevel (psiLocal K v) + ((a - 1) / 2 + 1 : ℕ)) then 1 else 0)) = 0 := by
  split_ifs with h
  ·
    have hw0 : w ≠ 0 := ne_zero_of_mem_unitSet hw
    rw [Valuation.map_mul, hvc] at h
    have hball : Valued.v (w - 1) ≤ WithZero.exp (-((a - ((a - 1) / 2 + 1) : ℕ) : ℤ)) := by
      have hma := index_le ha
      calc Valued.v (w - 1)
          = WithZero.exp (-(addCharLevel (psiLocal K v) + a : ℤ))
              * (WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ) * Valued.v (w - 1)) := by
            rw [← mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul]
        _ ≤ WithZero.exp (-(addCharLevel (psiLocal K v) + a : ℤ))
              * WithZero.exp (addCharLevel (psiLocal K v) + ((a - 1) / 2 + 1 : ℕ)) := by gcongr
        _ = WithZero.exp (-((a - ((a - 1) / 2 + 1) : ℕ) : ℤ)) := by
            rw [← WithZero.exp_add]
            congr 1
            push_cast [Nat.cast_sub hma]
            ring
    have hmemk : Units.mk0 w hw0 ∈ higherUnitsAt K v (a - ((a - 1) / 2 + 1)) :=
      (mem_higherUnitsAt_iff K v).mpr ⟨by simpa using mem_unitSet.mp hw, Or.inr (by simpa using hball)⟩
    have hmemb : Units.mk0 w hw0 ∈ higherUnitsAt K v b := higherUnitsAt_antitone K v (le_sub_index ha hab) hmemk
    have hθw : charExt θ⁻¹ w = 1 := by
      rw [charExt_of_ne_zero _ hw0, inv_apply_eq_one hθ _ hmemb, Units.val_one]
    simp [phi, hθw]
  · simp

private def kernel (χ θ : (v.adicCompletion K)ˣ →* ℂˣ) (c : v.adicCompletion K) (t w : v.adicCompletion K) : ℂ :=
  phi χ θ c w * psiLocal K v (t * (c * (w - 1)))

private theorem setIntegral_phi_eq_zero {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (ha : 2 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hθ : HasConductorExponentAt K v θ b) (hab : 2 * b ≤ a)
    {c : (v.adicCompletion K)ˣ}
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1)))
    (hvc : Valued.v (c : v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ)) :
    letI := localBorel K v
    ∫ w in unitSet K v, phi χ θ (c : v.adicCompletion K) w ∂(selfDualHaarAt K v) = 0 := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaar

  have hKcont : ContinuousOn (Function.uncurry (kernel χ θ (c : v.adicCompletion K)))
      (ball K v ((a - 1) / 2 + 1) ×ˢ unitSet K v) := by
    have hΦc : ContinuousOn (fun p : v.adicCompletion K × v.adicCompletion K => phi χ θ (c : v.adicCompletion K) p.2)
        (ball K v ((a - 1) / 2 + 1) ×ˢ unitSet K v) :=
      (continuousOn_phi hχ hθ _).comp continuousOn_snd fun p hp => hp.2
    have hψc : Continuous fun p : v.adicCompletion K × v.adicCompletion K =>
        psiLocal K v (p.1 * ((c : v.adicCompletion K) * (p.2 - 1))) :=
      (continuous_psiLocal K v).comp (continuous_fst.mul (continuous_const.mul (continuous_snd.sub continuous_const)))
    exact hΦc.mul hψc.continuousOn
  have hrect : MeasurableSet (ball K v ((a - 1) / 2 + 1) ×ˢ unitSet K v) :=
    (measurableSet_ball _).prod measurableSet_unitSet
  have hcpt : IsCompact (ball K v ((a - 1) / 2 + 1) ×ˢ unitSet K v) := (isCompact_ball _).prod isCompact_unitSet
  have hint : Integrable (Function.uncurry (kernel χ θ (c : v.adicCompletion K)))
      (((selfDualHaarAt K v).restrict (ball K v ((a - 1) / 2 + 1))).prod
        ((selfDualHaarAt K v).restrict (unitSet K v))) := by
    rw [Measure.prod_restrict]
    haveI : IsFiniteMeasure (((selfDualHaarAt K v).prod (selfDualHaarAt K v)).restrict
        (ball K v ((a - 1) / 2 + 1) ×ˢ unitSet K v)) :=
      isFiniteMeasure_restrict.mpr (hcpt.measure_lt_top (μ := (selfDualHaarAt K v).prod (selfDualHaarAt K v))).ne
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hKcont
    refine Integrable.of_bound (hKcont.aestronglyMeasurable hrect) C ?_
    exact (ae_restrict_mem hrect).mono fun p hp => hC p hp

  have hkey : (((selfDualHaarAt K v).real (ball K v ((a - 1) / 2 + 1)) : ℝ) : ℂ)
      * ∫ w in unitSet K v, phi χ θ (c : v.adicCompletion K) w ∂(selfDualHaarAt K v) = 0 := by
    calc (((selfDualHaarAt K v).real (ball K v ((a - 1) / 2 + 1)) : ℝ) : ℂ)
          * ∫ w in unitSet K v, phi χ θ (c : v.adicCompletion K) w ∂(selfDualHaarAt K v)
        = ∫ _t in ball K v ((a - 1) / 2 + 1),
            (∫ w in unitSet K v, phi χ θ (c : v.adicCompletion K) w ∂(selfDualHaarAt K v)) ∂(selfDualHaarAt K v) := by
          rw [setIntegral_const, Complex.real_smul]
      _ = ∫ t in ball K v ((a - 1) / 2 + 1),
            (∫ w in unitSet K v, kernel χ θ (c : v.adicCompletion K) t w ∂(selfDualHaarAt K v))
              ∂(selfDualHaarAt K v) :=
          setIntegral_congr_fun (measurableSet_ball _) fun t ht => by
            simp only [kernel]
            exact setIntegral_phi_eq hθ hab hc ht
      _ = ∫ w in unitSet K v,
            (∫ t in ball K v ((a - 1) / 2 + 1), kernel χ θ (c : v.adicCompletion K) t w ∂(selfDualHaarAt K v))
              ∂(selfDualHaarAt K v) := integral_integral_swap hint
      _ = ∫ w in unitSet K v,
            phi χ θ (c : v.adicCompletion K) w * ((((selfDualHaarAt K v).real (ball K v ((a - 1) / 2 + 1)) : ℝ) : ℂ)
              * (if Valued.v ((c : v.adicCompletion K) * (w - 1))
                  ≤ WithZero.exp (addCharLevel (psiLocal K v) + ((a - 1) / 2 + 1 : ℕ)) then 1 else 0))
              ∂(selfDualHaarAt K v) := by
          refine setIntegral_congr_fun measurableSet_unitSet fun w _ => ?_
          simp only [kernel]
          rw [integral_const_mul, integral_ball_psi]
      _ = 0 := setIntegral_eq_zero_of_forall_eq_zero fun w hw => phi_mul_indicator_eq_zero ha hθ hab hvc _ hw
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd (Complex.ofReal_eq_zero.mp h) (ballVol_ne_zero _)
  · exact h

private theorem hInt_mul {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (ha : 2 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hθ : HasConductorExponentAt K v θ b) (hab : 2 * b ≤ a)
    {c : (v.adicCompletion K)ˣ}
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1)))
    (hvc : Valued.v (c : v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ)) :
    hInt (θ * χ) (c : v.adicCompletion K) = hInt χ (c : v.adicCompletion K) := by
  letI := localBorel K v
  have hθχ := mul_hasConductorExponentAt hχ hθ ha hab
  have h₁ : IntegrableOn (fun w => psiLocal K v ((c : v.adicCompletion K) * w) * charExt (θ * χ)⁻¹ w) (unitSet K v)
      (selfDualHaarAt K v) :=
    integrableOn_unitSet ((continuousOn_psi_mul (c : v.adicCompletion K)).mul
      (continuousOn_charExt (inv_apply_eq_one hθχ)))
  have h₂ : IntegrableOn (fun w => psiLocal K v ((c : v.adicCompletion K) * w) * charExt χ⁻¹ w) (unitSet K v)
      (selfDualHaarAt K v) :=
    integrableOn_unitSet ((continuousOn_psi_mul (c : v.adicCompletion K)).mul
      (continuousOn_charExt (inv_apply_eq_one hχ)))
  rw [← sub_eq_zero]
  change (∫ w in unitSet K v, psiLocal K v ((c : v.adicCompletion K) * w) * charExt (θ * χ)⁻¹ w ∂(selfDualHaarAt K v))
    - (∫ w in unitSet K v, psiLocal K v ((c : v.adicCompletion K) * w) * charExt χ⁻¹ w ∂(selfDualHaarAt K v)) = 0
  rw [← integral_sub h₁ h₂, ← setIntegral_phi_eq_zero ha hχ hθ hab hc hvc]
  refine setIntegral_congr_fun measurableSet_unitSet fun w hw => ?_
  have hw0 : w ≠ 0 := ne_zero_of_mem_unitSet hw
  have hsplit : charExt (θ * χ)⁻¹ w = charExt χ⁻¹ w * charExt θ⁻¹ w := by
    rw [charExt_of_ne_zero _ hw0, charExt_of_ne_zero _ hw0, charExt_of_ne_zero _ hw0, MonoidHom.inv_apply,
      MonoidHom.inv_apply, MonoidHom.inv_apply, MonoidHom.mul_apply, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_mul]
    ring
  simp only [phi, hsplit]
  ring

private def pinUnit (a : ℕ) (c : (v.adicCompletion K)ˣ) : (v.adicCompletion K)ˣ :=
  (uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)))⁻¹ * c

private theorem valued_pinUnit {a : ℕ} {c : (v.adicCompletion K)ˣ}
    (hvc : Valued.v (c : v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ)) :
    Valued.v ((pinUnit a c : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  rw [pinUnit, Units.val_mul, Valuation.map_mul, hvc, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val,
    map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
  exact inv_mul_cancel₀ WithZero.exp_ne_zero

private theorem gaussUnit_eq_hInt (η : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} {c : (v.adicCompletion K)ˣ}
    (hvc : Valued.v (c : v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ)) :
    gaussUnit η a = (η (pinUnit a c) : ℂ)⁻¹ * hInt η (c : v.adicCompletion K) := by
  letI := localBorel K v
  have hz : ((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K)
      * ((pinUnit a c : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (c : v.adicCompletion K) := by
    rw [← Units.val_mul, pinUnit, mul_inv_cancel_left]
  have hηu : charExt η⁻¹ ((pinUnit a c : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (η (pinUnit a c) : ℂ)⁻¹ := by
    rw [charExt_coe_units, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  change (∫ u in unitSet K v, psiLocal K v (_ * u) * charExt η⁻¹ u ∂(selfDualHaarAt K v)) = _
  rw [← setIntegral_unit_mul (valued_pinUnit hvc), hInt, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_unitSet fun w hw => ?_
  show psiLocal K v (_ * (((pinUnit a c : (v.adicCompletion K)ˣ) : v.adicCompletion K) * w))
      * charExt η⁻¹ (((pinUnit a c : (v.adicCompletion K)ˣ) : v.adicCompletion K) * w) = _
  rw [← mul_assoc, hz, charExt_mul_of_ne_zero _ (pinUnit a c).ne_zero (ne_zero_of_mem_unitSet hw), hηu]
  ring

private theorem gaussUnit_mul {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (ha : 2 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hθ : HasConductorExponentAt K v θ b) (hab : 2 * b ≤ a)
    {c : (v.adicCompletion K)ˣ}
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1)))
    (hvc : Valued.v (c : v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ)) :
    gaussUnit (θ * χ) a = (θ (pinUnit a c) : ℂ)⁻¹ * gaussUnit χ a := by
  rw [gaussUnit_eq_hInt (θ * χ) hvc, gaussUnit_eq_hInt χ hvc, hInt_mul ha hχ hθ hab hc hvc, MonoidHom.mul_apply,
    Units.val_mul, mul_inv]
  ring

end Mass

private theorem main {χ θ : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ} (hχ : HasConductorExponentAt K v χ a)
    (hθ : HasConductorExponentAt K v θ b) (ha : 2 ≤ a) (hab : 2 * b ≤ a)
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) (huθ : ‖(θ (uniformizerUnit K v) : ℂ)‖ = 1)
    (c : (v.adicCompletion K)ˣ)
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1))) :
    stdRootNumberAt K v (θ * χ) = (θ c : ℂ)⁻¹ * stdRootNumberAt K v χ := by
  have h1 : HasConductorExponentAt K v (θ * χ) a := mul_hasConductorExponentAt hχ hθ ha hab
  have hu1 : ‖((θ * χ) (uniformizerUnit K v) : ℂ)‖ = 1 := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, huθ, hu, one_mul]
  have hvc := valued_pin ha hχ c hc
  rw [stdRootNumberAt_eq_gaussUnit (by omega) h1 hu1, stdRootNumberAt_eq_gaussUnit (by omega) hχ hu,
    gaussUnit_mul ha hχ hθ hab hc hvc]
  have hpin : (θ (pinUnit a c) : ℂ)
      = (θ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ) * (θ c : ℂ) := by
    rw [pinUnit, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      zpow_neg, inv_inv]
  have hX : (θ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ) ≠ 0 :=
    zpow_ne_zero _ (Units.ne_zero _)
  rw [hpin, MonoidHom.mul_apply, Units.val_mul, mul_zpow, mul_inv]
  linear_combination
    ((θ c : ℂ)⁻¹ * ((χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ)
      * normFactor (K := K) (v := v) a * gaussUnit χ a)) * mul_inv_cancel₀ hX

end

end GaussSumStability

open LanglandsTunnell.TateLocal in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ θ : (v.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ)
    (hχ : HasConductorExponentAt K v χ a) (hθ : HasConductorExponentAt K v θ b)
    (ha : 2 ≤ a) (hab : 2 * b ≤ a)
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) (huθ : ‖(θ (uniformizerUnit K v) : ℂ)‖ = 1)
    (c : (v.adicCompletion K)ˣ)
    (hc : ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1))) :
    stdRootNumberAt K v (θ * χ) = (θ c : ℂ)⁻¹ * stdRootNumberAt K v χ :=
  GaussSumStability.main hχ hθ ha hab hu huθ c hc

end

end S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_two_mul_conductorExponent_le
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_two_mul_conductorExponent_le (solution)
