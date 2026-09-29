-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_iotaGL_eq_of_forall_torusShell_localLevelOne_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b434febe-ffab-5fc1-aa84-3d5d938c5fda

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_iotaGL_eq_of_forall_torusShell_localLevelOne_pow_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped Topology

namespace KcTorusPolyLevel

noncomputable section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

theorem idealBound_pow (b : ℕ) :
    AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ b) v = WithZero.exp (-(b : ℤ)) := by
  classical
  have hne : v.asIdeal ^ b ≠ ⊥ := pow_ne_zero _ v.ne_bot
  rw [AdelicLevel.idealBound_of_ne_bot hne, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) v.associates_irreducible,
    Associates.count_self v.associates_irreducible, mul_one]

theorem localLevelOne_pow_le (b : ℕ) :
    AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b) ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  intro k hk
  rw [AdelicDock.mem_localLevelOne_iff] at hk ⊢
  have key : ∀ m : Mat, AdelicDock.IsLocalLevelOne (𝓞 K) K v (v.asIdeal ^ b) m →
      AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
    intro m hm
    refine ⟨hm.integral, ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]
      exact hm.lowerLeft.trans (AdelicLevel.idealBound_le_one _ _)
    · rw [AdelicLevel.idealBound_top]
      exact hm.lowerRight.trans (AdelicLevel.idealBound_le_one _ _)
  exact ⟨key _ hk.1, key _ hk.2⟩

theorem mem_localLevelOne_pow_of_cong (b : ℕ) (k : G₂) (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    k ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b) := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk ⊢
  obtain ⟨hk1, hk2⟩ := hk
  have hint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk1.integral i j)
  have hiint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk2.integral i j)

  have hc' : ∀ i j : Fin 2, Valued.v ((((k⁻¹ : G₂) : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ)) := by
    intro i j
    have hexp : ((k⁻¹ : G₂) : Mat) - 1 = -(((k⁻¹ : G₂) : Mat) * ((k : Mat) - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      abel
    rw [hexp]
    simp only [Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply, Fin.sum_univ_two]
    have hterm : ∀ l, Valued.v (((k⁻¹ : G₂) : Mat) i l * ((k : Mat) - 1) l j) ≤ WithZero.exp (-(b : ℤ)) := by
      intro l
      rw [map_mul]
      calc Valued.v (((k⁻¹ : G₂) : Mat) i l) * Valued.v (((k : Mat) - 1) l j)
          ≤ 1 * WithZero.exp (-(b : ℤ)) := by
            gcongr
            · exact hiint i l
            · exact hc l j
        _ = WithZero.exp (-(b : ℤ)) := one_mul _
    exact (Valuation.map_add _ _ _).trans (max_le (hterm 0) (hterm 1))
  have key : ∀ m : Mat, (∀ i j, m i j ∈ (O)) → (∀ i j : Fin 2, Valued.v ((m - 1) i j) ≤ WithZero.exp (-(b : ℤ))) →
      AdelicDock.IsLocalLevelOne (𝓞 K) K v (v.asIdeal ^ b) m := by
    intro m hm hmc
    refine ⟨hm, ?_, ?_⟩
    · rw [idealBound_pow]
      have := hmc 1 0
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
    · rw [idealBound_pow]
      have := hmc 1 1
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
  exact ⟨key _ hk1.integral hc, key _ hk2.integral hc'⟩

theorem continuous_iotaGL : Continuous (iotaGL : G₂ → G₃) := by
  have hemb : ∀ (f : G₂ → Mat), Continuous f → Continuous fun h => (embedMat2 (f h) : Matrix (Fin 3) (Fin 3) F) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [embedMat2] <;> first
        | exact hf.matrix_elem _ _
        | exact continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hemb _ Units.continuous_val
  · change Continuous fun h : G₂ => (embedMat2 ((h⁻¹ : G₂) : Mat) : Matrix (Fin 3) (Fin 3) F)
    exact hemb _ Units.continuous_coe_inv

variable {K v}

theorem smooth_A {W₃ : G₃ → ℂ}
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) (g₃ : G₃) :
    ∃ U : Subgroup G₂, IsOpen (U : Set G₂) ∧ ∀ k ∈ U, ∀ g : G₂, W₃ (iotaGL (g * k) * g₃) = W₃ (iotaGL g * g₃) := by
  obtain ⟨Uv, hUv, hinv⟩ := hW₃sm

  let φ : G₂ →* G₃ := (MulAut.conj g₃⁻¹).toMonoidHom.comp iotaGL
  refine ⟨Uv.comap φ, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun h : G₂ => g₃⁻¹ * iotaGL h * g₃⁻¹⁻¹
      exact (continuous_const.mul (continuous_iotaGL K v)).mul continuous_const
    exact hUv.preimage hφ
  · intro k hk g
    have hk' : g₃⁻¹ * iotaGL k * g₃ ∈ Uv := by
      have := hk
      rw [Subgroup.mem_comap] at this
      simpa [φ] using this
    have : iotaGL (g * k) * g₃ = iotaGL g * g₃ * (g₃⁻¹ * iotaGL k * g₃) := by
      rw [map_mul]; group
    rw [this, hinv _ hk']

theorem iotaGL_unipotent (x : F) : iotaGL (unipotent x : G₂) = (upperUnipotent3 x 0 0 : G₃) := by
  have : (unipotent x : G₂) = AutomorphicForm.unipotentGL2 x := by
    refine Units.ext ?_
    simp [unipotent, unipotentGL2_coe]
  rw [this, iotaGL_unipotentGL2]

theorem prod_unipotent {θ : AddChar F ℂ} {W₃ : G₃ → ℂ} (hW₃law : IsGL3PsiWhittakerFn θ⁻¹ W₃) (g₃ : G₃)
    {w₂ : G₂ → ℂ} (hw₂law : ∀ (x : F) (g : G₂), w₂ (unipotent x * g) = θ x * w₂ g) (x : F) (g : G₂) :
    W₃ (iotaGL (unipotent x * g) * g₃) * w₂ (unipotent x * g) = W₃ (iotaGL g * g₃) * w₂ g := by
  rw [map_mul, iotaGL_unipotent, mul_assoc, hW₃law x 0 0, hw₂law, add_zero, AddChar.inv_apply]
  have h1 : θ (-x) * θ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc θ (-x) * W₃ (iotaGL g * g₃) * (θ x * w₂ g) = (θ (-x) * θ x) * (W₃ (iotaGL g * g₃) * w₂ g) := by ring
    _ = W₃ (iotaGL g * g₃) * w₂ g := by rw [h1, one_mul]

end

end KcTorusPolyLevel

open KcTorusPolyLevel in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ) (θ : AddChar (v.adicCompletion K) ℂ)
    (W₃ : GL (Fin 3) (v.adicCompletion K) → ℂ) (hW₃law : IsGL3PsiWhittakerFn θ⁻¹ W₃)
    (hW₃sm : ∃ Uv : Subgroup (GL (Fin 3) (v.adicCompletion K)), IsOpen (Uv : Set (GL (Fin 3) (v.adicCompletion K))) ∧
      ∀ k ∈ Uv, ∀ g : GL (Fin 3) (v.adicCompletion K), W₃ (g * k) = W₃ g)
    (g₃ : GL (Fin 3) (v.adicCompletion K))
    (w₂ : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hw₂law : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)), w₂ (unipotent x * g) = θ x * w₂ g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b), ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₂ (g * k) = w₂ g) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  W₃ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →
      ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
          (W₃ (iotaGL g * g₃) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
            (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
            s (fun g => W₃ (iotaGL g * g₃)) w₂ =
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  intro μ₂ _ μN₂ _ ν _ hβ
  have hopen := (AdelicDock.isCompact_and_isOpen_localLevelOne K v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).2
  exact LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
    K v hπ hϖ b (AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b)) hopen (localLevelOne_pow_le K v b)
    (fun k hk hc => mem_localLevelOne_pow_of_cong K v b k hk hc)
    (fun g => W₃ (iotaGL g * g₃)) w₂ (smooth_A hW₃sm g₃) hw₂K (prod_unipotent hW₃law g₃ hw₂law)
    μ₂ μN₂ ν hβ

end S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_iotaGL_eq_of_forall_torusShell_localLevelOne_pow_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_iotaGL_eq_of_forall_torusShell_localLevelOne_pow_eq_zero (solution)
