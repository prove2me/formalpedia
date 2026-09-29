-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5bc8e210-a532-50b7-ac5a-270852a06d1a

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
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
import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsLocalIntegrand_of_gauge
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_integrable_setIntegral_localLevelOne_of_torusShell
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_flatSection_mul_whittaker_iotaGL_diagUnits2_longWeyl3_of_gauge
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped Topology ENNReal NNReal Matrix

namespace KcParentC686

noncomputable section

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem embedMat2_transpose (M : Matrix (Fin 2) (Fin 2) A) : embedMat2 Mᵀ = (embedMat2 M)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem transposeInv3_iotaGL (h : GL (Fin 2) A) :
    transposeInv3 (iotaGL h) = iotaGL (transposeInvN (Fin 2) h) := by
  refine Units.ext ?_
  rw [transposeInv3_coe, ← map_inv, coe_iotaGL, coe_iotaGL, coe_transposeInvN, embedMat2_transpose]

theorem det_transposeInvN (h : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) h) = (Matrix.GeneralLinearGroup.det h)⁻¹ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose,
    ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem transposeInv3_upperUnipotent3 (x : A) :
    transposeInv3 (upperUnipotent3 x 0 0 : GL (Fin 3) A) = lowerUnipotent21 (-x) := by
  have h := transposeInv3_lowerUnipotent21 (A := A) (-x)
  rw [neg_neg] at h
  rw [← h, transposeInv3_transposeInv3]

theorem longWeyl3_mul_lowerUnipotent21 (x : A) :
    (longWeyl3 : GL (Fin 3) A) * lowerUnipotent21 x = upperUnipotent3 0 x 0 * longWeyl3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, longWeyl3_coe, lowerUnipotent21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

variable {L : Type*} [Field L]

theorem unipotent_eq_unipotentGL2 (x : L) : UnramifiedWhittaker.unipotent x = (unipotentGL2 x : GL (Fin 2) L) := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem coe_inv_unipotentGL2 (x : L) :
    (((unipotentGL2 x : GL (Fin 2) L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -x; 0, 1] := rfl

theorem weyl_mul_transposeInvN_unipotentGL2 {w₀p : GL (Fin 2) L}
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0]) (x : L) :
    w₀p * transposeInvN (Fin 2) (unipotentGL2 x) = unipotentGL2 (-x) * w₀p := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, coe_inv_unipotentGL2, hw₀p, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def tau : GL (Fin 2) A ≃* GL (Fin 2) A where
  toFun := transposeInvN (Fin 2)
  invFun := transposeInvN (Fin 2)
  left_inv := transposeInvN_transposeInvN (Fin 2)
  right_inv := transposeInvN_transposeInvN (Fin 2)
  map_mul' := transposeInvN_mul (Fin 2)

theorem tau_apply (g : GL (Fin 2) A) : tau g = transposeInvN (Fin 2) g := rfl

end Algebra

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G₂ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G₂ := locallyCompactSpace_localGL K v

theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : G₂ → G₂) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : G₂ => (((g⁻¹ : G₂) : Mat))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : G₂ => ((g : G₂) : Mat)ᵀ
    exact Units.continuous_val.matrix_transpose

def tauHomeo : G₂ ≃ₜ G₂ where
  toEquiv := (tau : G₂ ≃* G₂).toEquiv
  continuous_toFun := continuous_transposeInvN K v
  continuous_invFun := continuous_transposeInvN K v

theorem map_transposeInvN_eq (μ : Measure G₂) [μ.IsHaarMeasure] : Measure.map (transposeInvN (Fin 2)) μ = μ := by
  have hcont := continuous_transposeInvN K v
  haveI : (Measure.map (transposeInvN (Fin 2)) μ).IsHaarMeasure :=
    (tau : G₂ ≃* G₂).isHaarMeasure_map μ hcont hcont
  set c := Measure.haarScalarFactor (Measure.map (transposeInvN (Fin 2)) μ) μ with hc
  have h1 : Measure.map (transposeInvN (Fin 2)) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ _

  have h2 : μ = (c * c) • μ := by
    have hmm : Measure.map (transposeInvN (Fin 2)) (Measure.map (transposeInvN (Fin 2)) μ) = μ := by
      rw [Measure.map_map hcont.measurable hcont.measurable]
      have : (transposeInvN (Fin 2) ∘ transposeInvN (Fin 2) : G₂ → G₂) = id :=
        funext (transposeInvN_transposeInvN (Fin 2))
      rw [this, Measure.map_id]
    calc μ = Measure.map (transposeInvN (Fin 2)) (Measure.map (transposeInvN (Fin 2)) μ) := hmm.symm
      _ = Measure.map (transposeInvN (Fin 2)) (c • μ) := by rw [h1]
      _ = c • Measure.map (transposeInvN (Fin 2)) μ := by rw [Measure.map_smul]
      _ = (c * c) • μ := by rw [h1, smul_smul]

  obtain ⟨K₀, hK₀c, hK₀i⟩ : ∃ S : Set G₂, IsCompact S ∧ (interior S).Nonempty :=
    ⟨localIntegralSet K v, isCompact_localIntegralSet K v,
      ⟨1, by rw [(isOpen_localIntegralSet K v).interior_eq]; exact one_mem_localIntegralSet K v⟩⟩
  have hpos : 0 < μ K₀ := hK₀i.mono interior_subset |>.elim (fun x hx => lt_of_lt_of_le (isOpen_interior.measure_pos μ hK₀i) (measure_mono interior_subset))
  have hfin : μ K₀ < ⊤ := hK₀c.measure_lt_top
  have hcc : (c * c : ℝ≥0) = 1 := by
    have h3 := congr_arg (fun m : Measure G₂ => m K₀) h2
    simp only [Measure.smul_apply] at h3
    rw [ENNReal.smul_def, smul_eq_mul] at h3
    have h4 : (1 : ℝ≥0∞) = ((c * c : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h3
    exact_mod_cast h4.symm
  have hc1 : c = 1 := by
    have h5 : ((c : ℝ) * c) = 1 := by exact_mod_cast hcc
    have h6 : (c : ℝ) = 1 := by
      have hn : (0 : ℝ) ≤ c := c.2
      nlinarith [h5, hn]
    exact_mod_cast h6
  rw [h1, hc1, one_smul]

abbrev kzero : Subgroup G₂ := AdelicDock.localLevelOne (𝓞 K) K v ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G₂) :
    k ∈ kzero K v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G₂) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral K v h1, isLocalLevelOne_top_of_integral K v h2⟩

theorem transposeInvN_mem_kzero {k : G₂} (hk : k ∈ kzero K v) : transposeInvN (Fin 2) k ∈ kzero K v := by
  rw [mem_kzero_iff] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_transposeInvN, Matrix.transpose_apply]; exact hk.2 j i
  · rw [coe_inv_transposeInvN, Matrix.transpose_apply]; exact hk.1 j i

theorem valuation_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = 1 := by
  rw [mem_kzero_iff] at hk
  have hint : ∀ (m : Mat), (∀ i j, m i j ∈ (O)) → Valued.v m.det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    have h := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm i j)
    calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
        ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
      _ ≤ 1 := by
          refine max_le ?_ ?_
          · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
          · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)
  have h1 := hint _ hk.1
  have h2 := hint _ hk.2
  have hprod : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

theorem modulus_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    (modulus ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) = 1 := by
  rw [coe_modulus_eq_norm, NumberField.FinitePlace.norm_def, valuation_det_of_mem_kzero K v hk, map_one, NNReal.coe_one]

variable (b : ℕ)

abbrev kone : Subgroup G₂ := AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b)

theorem idealBound_pow :
    AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ b) v = WithZero.exp (-(b : ℤ)) := by
  classical
  have hne : v.asIdeal ^ b ≠ ⊥ := pow_ne_zero _ v.ne_bot
  rw [AdelicLevel.idealBound_of_ne_bot hne, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) v.associates_irreducible,
    Associates.count_self v.associates_irreducible, mul_one]

theorem kone_le : kone K v b ≤ kzero K v := by
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

theorem isOpen_kone : IsOpen ((kone K v b : Subgroup G₂) : Set G₂) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne K v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).2

theorem isCompact_kone : IsCompact ((kone K v b : Subgroup G₂) : Set G₂) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne K v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).1

theorem cong_inv {k : G₂} (hk : k ∈ kzero K v)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    ∀ i j : Fin 2, Valued.v ((((k⁻¹ : G₂) : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ)) := by
  rw [mem_kzero_iff] at hk
  have hiint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk.2 i j)
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

theorem mem_kone_of_cong (k : G₂) (hk : k ∈ kzero K v)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    k ∈ kone K v b := by
  have hc' := cong_inv K v b hk hc
  rw [AdelicDock.mem_localLevelOne_iff] at hk ⊢
  obtain ⟨hk1, hk2⟩ := hk
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

def koneT : Subgroup G₂ := (kone K v b).comap ((tau : G₂ ≃* G₂).toMonoidHom)

theorem mem_koneT_iff (k : G₂) : k ∈ koneT K v b ↔ transposeInvN (Fin 2) k ∈ kone K v b := Iff.rfl

theorem isOpen_koneT : IsOpen ((koneT K v b : Subgroup G₂) : Set G₂) :=
  (isOpen_kone K v b).preimage (continuous_transposeInvN K v)

theorem koneT_le : koneT K v b ≤ kzero K v := by
  intro k hk
  rw [mem_koneT_iff] at hk
  have h := transposeInvN_mem_kzero K v (kone_le K v b hk)
  rwa [transposeInvN_transposeInvN] at h

theorem mem_koneT_of_cong (k : G₂) (hk : k ∈ kzero K v)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    k ∈ koneT K v b := by
  rw [mem_koneT_iff]
  refine mem_kone_of_cong K v b _ (transposeInvN_mem_kzero K v hk) fun i j => ?_
  rw [coe_transposeInvN]
  have : ((((k⁻¹ : G₂) : Mat))ᵀ - 1) i j = ((((k⁻¹ : G₂) : Mat)) - 1) j i := by
    simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [this]
  exact cong_inv K v b hk hc j i

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

variable {K v b}

section Pair

variable {θ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ} {W₃ : GL (Fin 3) (HeightOneSpectrum.adicCompletion K v) → ℂ}
  (g₃ : GL (Fin 3) (HeightOneSpectrum.adicCompletion K v)) {w₂ : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ}
  {w₀p : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)}

theorem smooth_A
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) :
    ∃ U : Subgroup G₂, IsOpen (U : Set G₂) ∧ ∀ k ∈ U, ∀ g : G₂,
      (fun g : G₂ => W₃ (iotaGL g * g₃)) (g * k) = (fun g : G₂ => W₃ (iotaGL g * g₃)) g := by
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
    simp only
    rw [this, hinv _ hk']

theorem smooth_translate
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) :
    ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃,
      (fun x : G₃ => W₃ (x * g₃)) (g * k) = (fun x : G₃ => W₃ (x * g₃)) g := by
  obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
  let φ : G₃ →* G₃ := (MulAut.conj g₃⁻¹).toMonoidHom
  refine ⟨Uv.comap φ, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun h : G₃ => g₃⁻¹ * h * g₃⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    exact hUv.preimage hφ
  · intro k hk g
    have hk' : g₃⁻¹ * k * g₃ ∈ Uv := by
      have := hk
      rw [Subgroup.mem_comap] at this
      simpa [φ] using this
    have : g * k * g₃ = g * g₃ * (g₃⁻¹ * k * g₃) := by group
    simp only
    rw [this, hinv _ hk']

theorem Afun_apply (g : G₂) :
    dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g) = W₃ (longWeyl3 * transposeInv3 (iotaGL g) * g₃) := rfl

theorem smooth_Afun
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) :
    ∃ U : Subgroup G₂, IsOpen (U : Set G₂) ∧ ∀ k ∈ U, ∀ g : G₂,
      (fun g : G₂ => dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g)) (g * k) =
        (fun g : G₂ => dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g)) g := by
  obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
  let φ : G₂ →* G₃ := (MulAut.conj g₃⁻¹).toMonoidHom.comp (iotaGL.comp (tau : G₂ ≃* G₂).toMonoidHom)
  refine ⟨Uv.comap φ, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun h : G₂ => g₃⁻¹ * iotaGL (transposeInvN (Fin 2) h) * g₃⁻¹⁻¹
      exact (continuous_const.mul ((continuous_iotaGL K v).comp (continuous_transposeInvN K v))).mul continuous_const
    exact hUv.preimage hφ
  · intro k hk g
    have hk' : g₃⁻¹ * iotaGL (transposeInvN (Fin 2) k) * g₃ ∈ Uv := by
      have := hk
      rw [Subgroup.mem_comap] at this
      simpa [φ, tau_apply] using this
    simp only
    rw [Afun_apply, Afun_apply, map_mul, transposeInv3_mul, transposeInv3_iotaGL k]
    have : longWeyl3 * (transposeInv3 (iotaGL g) * iotaGL (transposeInvN (Fin 2) k)) * g₃ =
        longWeyl3 * transposeInv3 (iotaGL g) * g₃ * (g₃⁻¹ * iotaGL (transposeInvN (Fin 2) k) * g₃) := by group
    rw [this, hinv _ hk']

theorem Bfun_mul (hw₂K : ∀ k ∈ kone K v b, ∀ g : G₂, w₂ (g * k) = w₂ g) :
    ∀ k ∈ koneT K v b, ∀ g : G₂,
      (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
          w₂ (w₀p * transposeInvN (Fin 2) g)) (g * k) =
        (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
          w₂ (w₀p * transposeInvN (Fin 2) g)) g := by
  intro k hk g
  have hkK : k ∈ kzero K v := koneT_le K v b hk
  rw [mem_koneT_iff] at hk
  simp only
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, modulus_det_of_mem_kzero K v hkK, mul_one,
    transposeInvN_mul, ← mul_assoc, hw₂K _ hk]

theorem iotaGL_unipotent (x : F) : iotaGL (unipotent x : G₂) = (upperUnipotent3 x 0 0 : G₃) := by
  rw [unipotent_eq_unipotentGL2, iotaGL_unipotentGL2]

theorem prod_unipotent_primal (hW₃law : IsGL3PsiWhittakerFn θ⁻¹ W₃)
    (hw₂law : ∀ (x : F) (g : G₂), w₂ (unipotent x * g) = θ x * w₂ g) (x : F) (g : G₂) :
    (fun g : G₂ => W₃ (iotaGL g * g₃)) (unipotent x * g) * w₂ (unipotent x * g) =
      (fun g : G₂ => W₃ (iotaGL g * g₃)) g * w₂ g := by
  simp only
  rw [map_mul, iotaGL_unipotent, mul_assoc, hW₃law x 0 0, hw₂law, add_zero, AddChar.inv_apply]
  have h1 : θ (-x) * θ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc θ (-x) * W₃ (iotaGL g * g₃) * (θ x * w₂ g) = (θ (-x) * θ x) * (W₃ (iotaGL g * g₃) * w₂ g) := by ring
    _ = W₃ (iotaGL g * g₃) * w₂ g := by rw [h1, one_mul]

theorem prod_unipotent_dual (hW₃law : IsGL3PsiWhittakerFn θ⁻¹ W₃)
    (hw₂law : ∀ (x : F) (g : G₂), w₂ (unipotent x * g) = θ x * w₂ g)
    (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (x : F) (g : G₂) :
    (fun g : G₂ => dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g)) (unipotent x * g) *
        (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
          w₂ (w₀p * transposeInvN (Fin 2) g)) (unipotent x * g) =
      (fun g : G₂ => dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g)) g *
        (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
          w₂ (w₀p * transposeInvN (Fin 2) g)) g := by
  simp only
  have h1 : dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL (unipotent x * g)) =
      θ x * dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g) := by
    rw [Afun_apply, Afun_apply, map_mul, transposeInv3_mul, unipotent_eq_unipotentGL2, iotaGL_unipotentGL2,
      transposeInv3_upperUnipotent3, ← mul_assoc (longWeyl3 : G₃), longWeyl3_mul_lowerUnipotent21, mul_assoc,
      mul_assoc, hW₃law, AddChar.inv_apply, zero_add, neg_neg, ← mul_assoc]
  have h2 : ((modulus ((Matrix.GeneralLinearGroup.det (unipotent x * g) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
        w₂ (w₀p * transposeInvN (Fin 2) (unipotent x * g)) =
      θ (-x) * (((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
        w₂ (w₀p * transposeInvN (Fin 2) g)) := by
    have hw₂law' : ∀ (y : F) (h : G₂), w₂ ((unipotentGL2 y : G₂) * h) = θ y * w₂ h := by
      intro y h; rw [← unipotent_eq_unipotentGL2]; exact hw₂law y h
    have hdet : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G₂) = 1 := by
      refine Units.ext ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
      simp
    rw [map_mul, unipotent_eq_unipotentGL2, transposeInvN_mul, ← mul_assoc, weyl_mul_transposeInvN_unipotentGL2 hw₀p,
      mul_assoc, hw₂law', hdet, one_mul]
    ring
  rw [h1, h2]
  have h3 : θ x * θ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc θ x * dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g) *
        (θ (-x) * (((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
          w₂ (w₀p * transposeInvN (Fin 2) g)))
      = (θ x * θ (-x)) * (dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
            w₂ (w₀p * transposeInvN (Fin 2) g))) := by ring
    _ = _ := by rw [h3, one_mul]

theorem setIntegral_koneT_eq (μ₂ : Measure G₂) [μ₂.IsHaarMeasure] (G : G₂ → ℂ) (hG : Continuous G) :
    ∫ k in ((koneT K v b : Subgroup G₂) : Set G₂), G k ∂μ₂ =
      ∫ k in ((kone K v b : Subgroup G₂) : Set G₂), G (transposeInvN (Fin 2) k) ∂μ₂ := by
  have hτ := continuous_transposeInvN K v
  conv_lhs => rw [← map_transposeInvN_eq K v μ₂]
  rw [setIntegral_map (isOpen_koneT K v b).measurableSet hG.aestronglyMeasurable hτ.aemeasurable]
  have hset : (transposeInvN (Fin 2)) ⁻¹' ((koneT K v b : Subgroup G₂) : Set G₂) = ((kone K v b : Subgroup G₂) : Set G₂) := by
    ext k
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_koneT_iff, transposeInvN_transposeInvN]
  rw [hset]

theorem continuous_of_rightInvariant {X : Type*} [TopologicalSpace X] {U : Subgroup G₂}
    (hU : IsOpen (U : Set G₂)) {f : G₂ → X} (hf : ∀ k ∈ U, ∀ g : G₂, f (g * k) = f g) : Continuous f := by
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hopen : IsOpen ((fun h => x * h) '' (U : Set G₂)) := isOpenMap_mul_left x _ hU
    have hmem : x ∈ (fun h => x * h) '' (U : Set G₂) := ⟨1, U.one_mem, mul_one x⟩
    filter_upwards [hopen.mem_nhds hmem] with y hy
    obtain ⟨h, hh, rfl⟩ := hy
    exact hf h hh x
  exact hlc.continuous

theorem isLocallyConstant_translFamily
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) :
    IsLocallyConstant (fun k : G₂ => fun x : G₃ => W₃ (x * iotaGL k * g₃)) := by
  obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
  let φ : G₂ →* G₃ := (MulAut.conj g₃⁻¹).toMonoidHom.comp iotaGL
  have hφ : Continuous φ := by
    change Continuous fun h : G₂ => g₃⁻¹ * iotaGL h * g₃⁻¹⁻¹
    exact (continuous_const.mul (continuous_iotaGL K v)).mul continuous_const
  have hO : IsOpen ((Uv.comap φ : Subgroup G₂) : Set G₂) := hUv.preimage hφ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro k
  have hopen : IsOpen ((fun h => k * h) '' ((Uv.comap φ : Subgroup G₂) : Set G₂)) := isOpenMap_mul_left k _ hO
  have hmem : k ∈ (fun h => k * h) '' ((Uv.comap φ : Subgroup G₂) : Set G₂) := ⟨1, (Uv.comap φ).one_mem, mul_one k⟩
  filter_upwards [hopen.mem_nhds hmem] with k' hk'
  obtain ⟨o, ho, rfl⟩ := hk'
  have ho' : g₃⁻¹ * iotaGL o * g₃ ∈ Uv := by
    have := ho
    rw [SetLike.mem_coe, Subgroup.mem_comap] at this
    simpa [φ] using this
  funext x
  have : x * iotaGL (k * o) * g₃ = x * iotaGL k * g₃ * (g₃⁻¹ * iotaGL o * g₃) := by
    rw [map_mul]; group
  rw [this, hinv _ ho']

theorem exists_avg_eq_sum (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) :
    ∃ (T : Finset (G₃ → ℂ)) (c : (G₃ → ℂ) → ℝ),
      (∀ f ∈ T, ∃ k ∈ kone K v b, f = fun x : G₃ => W₃ (x * iotaGL k * g₃)) ∧
      (∀ f, 0 ≤ c f) ∧
      (∑ f ∈ T, c f = μ₂.real ((kone K v b : Subgroup G₂) : Set G₂)) ∧
      ∀ x : G₃, ∫ k in ((kone K v b : Subgroup G₂) : Set G₂), W₃ (x * iotaGL k * g₃) ∂μ₂ =
        ∑ f ∈ T, (c f : ℂ) * f x := by
  set Φ : G₂ → (G₃ → ℂ) := fun k x => W₃ (x * iotaGL k * g₃) with hΦ
  have hlc : IsLocallyConstant Φ := isLocallyConstant_translFamily g₃ hW₃sm
  set Kb : Set G₂ := ((kone K v b : Subgroup G₂) : Set G₂) with hKb
  have hKc : IsCompact Kb := isCompact_kone K v b
  have hKm : MeasurableSet Kb := (isOpen_kone K v b).measurableSet

  haveI : CompactSpace Kb := isCompact_iff_compactSpace.mp hKc
  have hfin : (Φ '' Kb).Finite := by
    have h1 : IsLocallyConstant (Φ ∘ ((↑) : Kb → G₂)) := hlc.comp_continuous continuous_subtype_val
    have := h1.range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  set T : Finset (G₃ → ℂ) := hfin.toFinset with hT

  set piece : (G₃ → ℂ) → Set G₂ := fun f => Kb ∩ Φ ⁻¹' {f} with hpiece
  have hpm : ∀ f, MeasurableSet (piece f) := fun f => hKm.inter (hlc.isOpen_fiber f).measurableSet
  have hpsub : ∀ f, piece f ⊆ Kb := fun f => Set.inter_subset_left
  have hpfin : ∀ f, μ₂ (piece f) < ⊤ := fun f => lt_of_le_of_lt (measure_mono (hpsub f)) hKc.measure_lt_top
  have hpdisj : (T : Set (G₃ → ℂ)).Pairwise (Function.onFun Disjoint piece) := by
    intro f _ f' _ hff'
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨_, hx⟩ ⟨_, hx'⟩
    exact hff' ((Set.mem_singleton_iff.mp hx).symm.trans (Set.mem_singleton_iff.mp hx'))
  have hcover : Kb = ⋃ f ∈ T, piece f := by
    ext k
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hk
      exact ⟨Φ k, hfin.mem_toFinset.mpr ⟨k, hk, rfl⟩, hk, rfl⟩
    · rintro ⟨f, _, hk, _⟩
      exact hk
  refine ⟨T, fun f => μ₂.real (piece f), ?_, fun f => measureReal_nonneg, ?_, ?_⟩
  · intro f hf
    obtain ⟨k, hk, rfl⟩ := hfin.mem_toFinset.mp hf
    exact ⟨k, hk, rfl⟩
  · rw [← measureReal_biUnion_finset (fun f hf f' hf' hff' => hpdisj hf hf' hff') (fun f _ => hpm f)
      (fun f _ => (hpfin f).ne), ← hcover]
  · intro x
    have h1 : ∫ k in Kb, W₃ (x * iotaGL k * g₃) ∂μ₂ = ∫ k in Kb, Φ k x ∂μ₂ := rfl
    rw [h1]
    conv_lhs => rw [hcover]
    rw [integral_biUnion_finset _ (fun f _ => hpm f) hpdisj]
    · refine Finset.sum_congr rfl fun f hf => ?_
      have hcongr : Set.EqOn (fun k => Φ k x) (fun _ => f x) (piece f) := by
        rintro k ⟨_, hk⟩
        show Φ k x = f x
        rw [show Φ k = f from hk]
      rw [setIntegral_congr_fun (hpm f) hcongr, setIntegral_const, Complex.real_smul, measureReal_def]
      rfl
    · intro f hf
      have hcongr : Set.EqOn (fun _ => f x) (fun k => Φ k x) (piece f) := by
        rintro k ⟨_, hk⟩
        show f x = Φ k x
        rw [show Φ k = f from hk]
      exact (integrableOn_const (hpfin f).ne).congr_fun hcongr (hpm f)

theorem law_of_mem_gl3CyclicSubspace {θ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ}
    (hW₃law : IsGL3PsiWhittakerFn θ W₃) {W : G₃ → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    IsGL3PsiWhittakerFn θ W := by
  have hle : gl3CyclicSubspace W₃ ≤ gl3PsiWhittakerFnSpace (HeightOneSpectrum.adicCompletion K v) ℂ θ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace θ h ((mem_gl3PsiWhittakerFnSpace_iff θ _).mpr hW₃law)
  exact (mem_gl3PsiWhittakerFnSpace_iff θ _).mp (hle hW)

theorem central_of_mem_gl3CyclicSubspace {ω : (HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ}
    (hω : ∀ (z : (HeightOneSpectrum.adicCompletion K v)ˣ) (g : G₃),
      W₃ (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W₃ g)
    {W : G₃ → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∀ (z : (HeightOneSpectrum.adicCompletion K v)ˣ) (g : G₃),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g := by
  refine Submodule.span_induction (p := fun W _ => ∀ (z : (HeightOneSpectrum.adicCompletion K v)ˣ) (g : G₃),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ z g
    simp only [gl3AmbientRightTranslate_apply]
    rw [mul_assoc, hω]
  · intro z g; simp
  · intro f g _ _ hf hg z x
    simp only [Pi.add_apply]
    rw [hf, hg]; ring
  · intro a f _ hf z x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]; ring

theorem smooth_of_mem_gl3CyclicSubspace
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g)
    {W : G₃ → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W (g * k) = W g := by
  refine Submodule.span_induction (p := fun W _ =>
      ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W (g * k) = W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩
    obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
    let φ : G₃ →* G₃ := (MulAut.conj h⁻¹).toMonoidHom
    refine ⟨Uv.comap φ, ?_, ?_⟩
    · have hφ : Continuous φ := by
        change Continuous fun x : G₃ => h⁻¹ * x * h⁻¹⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const
      exact hUv.preimage hφ
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ Uv := by
        have := hk
        rw [Subgroup.mem_comap] at this
        simpa [φ] using this
      simp only [gl3AmbientRightTranslate_apply]
      have : g * k * h = g * h * (h⁻¹ * k * h) := by group
      rw [this, hinv _ hk']
  · obtain ⟨Uv, hUv, _⟩ := hW₃sm
    exact ⟨Uv, hUv, fun k _ g => rfl⟩
  · rintro f g _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk x => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · simp only [Pi.add_apply]
      rw [h₁ k (Subgroup.mem_inf.mp hk).1, h₂ k (Subgroup.mem_inf.mp hk).2]
  · rintro a f _ ⟨U, hU, h⟩
    exact ⟨U, hU, fun k hk x => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h k hk]⟩

theorem avg_mem_gl3CyclicSubspace (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) :
    (fun x : G₃ => ∫ k in ((kone K v b : Subgroup G₂) : Set G₂), W₃ (x * iotaGL k * g₃) ∂μ₂) ∈
      gl3CyclicSubspace W₃ := by
  obtain ⟨T, c, hT, -, -, havg⟩ := exists_avg_eq_sum (b := b) g₃ μ₂ hW₃sm
  have hfun : (fun x : G₃ => ∫ k in ((kone K v b : Subgroup G₂) : Set G₂), W₃ (x * iotaGL k * g₃) ∂μ₂) =
      ∑ f ∈ T, (c f : ℂ) • f := by
    funext x; rw [havg x, Finset.sum_apply]; rfl
  rw [hfun]
  refine Submodule.sum_smul_mem _ _ fun f hf => ?_
  obtain ⟨k, _, rfl⟩ := hT f hf
  refine Submodule.subset_span ⟨iotaGL k * g₃, ?_⟩
  funext x
  simp [gl3AmbientRightTranslate_apply, mul_assoc]

end Pair

end

end KcParentC686
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2.KcParentC686"

namespace KcParentC686Q

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance borelSpace_units_adic : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_units

scoped instance isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance isHaarMeasure_mulHaar :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

theorem modulus_eq_one_of_valuation_eq_one {x : p.adicCompletion ℚ} (hx : Valued.v x = 1) :
    (modulus x : ℝ) = 1 := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm, NumberField.FinitePlace.norm_def, hx, map_one,
    NNReal.coe_one]

theorem scalar_eq_diagonal2 (t : (p.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) t = diagonal2 p (fun _ => t) := by
  refine Units.ext ?_
  rw [diagonal2_coe]
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem scalar_mul_comm (t : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) t * g := by
  refine Units.ext ?_
  simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, Matrix.scalar_apply]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem torusChar2_scalar (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (t : (p.adicCompletion ℚ)ˣ) :
    torusChar2 p χ (fun _ => t) = ((χ 0 t : ℂˣ) : ℂ) * ((χ 1 t : ℂˣ) : ℂ) := by
  simp [torusChar2, Fin.prod_univ_two]

theorem halfModulus2_scalar (t : (p.adicCompletion ℚ)ˣ) : halfModulus2 p (fun _ => t) = 1 := by
  have h : ‖(t : p.adicCompletion ℚ)‖ ≠ 0 := norm_ne_zero_iff.mpr t.ne_zero
  simp [halfModulus2, h]

theorem central_of_hPS (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hPS : ∃ Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        Φ (fun g => w (g * h)) = fun g => Φ w (g * h)) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w = 0 → w = 0) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w ∈ principalSeries2 p χ)) :
    ∀ (t : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = (((χ 0 * χ 1) t : ℂˣ) : ℂ) * w₂base g := by
  obtain ⟨Φ, hΦeq, hΦinj, hΦPS⟩ := hPS
  intro t g
  set V := Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
    fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) with hV
  set z := Matrix.GeneralLinearGroup.scalar (Fin 2) t with hz
  set c : ℂ := ((χ 0 t : ℂˣ) : ℂ) * ((χ 1 t : ℂˣ) : ℂ) with hc
  have hbase : w₂base ∈ V := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext g'; simp
  have hzmem : (fun g' => w₂base (g' * z)) ∈ V := Submodule.subset_span ⟨z, rfl⟩

  have hPSlaw := (mem_principalSeries2_iff.mp (hΦPS w₂base hbase)).2.2
  have h1 : Φ (fun g' => w₂base (g' * z)) = c • Φ w₂base := by
    rw [hΦeq w₂base hbase z]
    funext g'
    rw [Pi.smul_apply, smul_eq_mul, scalar_mul_comm, scalar_eq_diagonal2, hPSlaw, torusChar2_scalar,
      halfModulus2_scalar, mul_one]
  have h2 : Φ ((fun g' => w₂base (g' * z)) - c • w₂base) = 0 := by
    rw [map_sub, map_smul, h1, sub_self]
  have h3 := hΦinj _ (V.sub_mem hzmem (V.smul_mem c hbase)) h2
  have h4 := congrFun h3 g
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at h4
  rw [h4, hc, MonoidHom.mul_apply, Units.val_mul]

theorem continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 p → LocalGL3 p) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : LocalGL3 p => (((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : LocalGL3 p => ((g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))ᵀ
    exact Units.continuous_val.matrix_transpose

def tau3 : LocalGL3 p →* LocalGL3 p where
  toFun := transposeInv3
  map_one' := by
    refine Units.ext ?_
    rw [KcParentC686.transposeInv3_coe, inv_one, Units.val_one, Matrix.transpose_one]
  map_mul' := KcParentC686.transposeInv3_mul

theorem smooth_dualWhittakerFn3 {W : LocalGL3 p → ℂ}
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) :
    ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, dualWhittakerFn3 W (g * k) = dualWhittakerFn3 W g := by
  obtain ⟨Uv, hUv, hinv⟩ := hWsm
  refine ⟨Uv.comap (tau3 p), hUv.preimage (continuous_transposeInv3 p), fun k hk g => ?_⟩
  change W (longWeyl3 * transposeInv3 (g * k)) = W (longWeyl3 * transposeInv3 g)
  rw [KcParentC686.transposeInv3_mul, ← mul_assoc]
  exact hinv (transposeInv3 k) hk _

theorem exists_forall_dominant (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (χu : ℂ → Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχu0 : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((χu u 0 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ u))
    (hχu1 : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((χu u 1 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-u)))
    {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    ∃ u₁ : ℝ, ∀ u : ℂ, u₁ < u.re →
      ‖((χu u 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χu u 1 ϖ : ℂˣ) : ℂ)‖ := by
  set m : ℝ := ((modulus (ϖ : p.adicCompletion ℚ) : ℝ)) with hm
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast modulus_pos ϖ.ne_zero
  have hm1 : m < 1 := by
    rw [hm, modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm, NumberField.FinitePlace.norm_def, ← NNReal.coe_one,
      NNReal.coe_lt_coe, WithZeroMulInt.toNNReal_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p),
      hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  set A : ℝ := ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ with hA
  set B : ℝ := ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ with hB
  have hA0 : 0 < A := norm_pos_iff.mpr (Units.ne_zero _)
  have hB0 : 0 < B := norm_pos_iff.mpr (Units.ne_zero _)
  set M : ℝ := m⁻¹ with hM
  have hM1 : 1 < M := by rw [hM]; exact one_lt_inv_iff₀.mpr ⟨hm0, hm1⟩
  have hM0 : 0 < M := by linarith
  refine ⟨Real.logb M (A / B) / 2, fun u hu => ?_⟩
  rw [hχu0, hχu1, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hm0, Complex.norm_cpow_eq_rpow_re_of_pos hm0,
    ← hA, ← hB, Complex.neg_re]
  have h2 : Real.logb M (A / B) < 2 * u.re := by linarith
  have h3 : A / B < M ^ (2 * u.re) := by
    have := Real.rpow_lt_rpow_of_exponent_lt hM1 h2
    rwa [Real.rpow_logb hM0 hM1.ne' (div_pos hA0 hB0)] at this
  have hmM : m = M⁻¹ := by rw [hM, inv_inv]
  rw [hmM, Real.inv_rpow hM0.le, Real.inv_rpow hM0.le, Real.rpow_neg hM0.le, inv_inv]
  have hMx : 0 < M ^ u.re := Real.rpow_pos_of_pos hM0 _
  rw [div_lt_iff₀ hB0] at h3
  have : M ^ (2 * u.re) = M ^ u.re * M ^ u.re := by rw [two_mul, Real.rpow_add hM0]
  rw [this] at h3
  calc A * (M ^ u.re)⁻¹ = A / M ^ u.re := by rw [div_eq_mul_inv]
    _ < B * M ^ u.re := by
        rw [div_lt_iff₀ hMx]
        calc A < M ^ u.re * M ^ u.re * B := h3
          _ = B * M ^ u.re * M ^ u.re := by ring

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2.KcParentC686"

end KcParentC686Q
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2.KcParentC686 P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2.KcParentC686Q"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

set_option maxHeartbeats 6400000 in
open KcParentC686 KcParentC686Q in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (C : Fin 2 → ℂ) (k : Fin 2 → ℤ)
    (h31 : ∀ i : Fin 2,
      ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base (χ i) g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (χ i) s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) ((χ i))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base (χ i) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C i * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k i : ℂ) * s))))
    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hPS : ∃ Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        Φ (fun g => w (g * h)) = fun g => Φ w (g * h)) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w = 0 → w = 0) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w ∈ principalSeries2 p χ))
    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))
    (hβ : ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              ((C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
                (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by
  intro μ₂ _ μN₂ _
  classical

  set qC : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hqC
  have hq0 : qC ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm p
    rw [hqC]; exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)

  have hw₂K' : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g := fun k hk g =>
    LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
      p N w₂base hw₂K b hNb k g hk
  have hw₂K'' : ∀ (k g : GL (Fin 2) (p.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) → w₂base (g * k) = w₂base g := fun k g hk => hw₂K' k hk g
  have hkone : IsOpen ((kone ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    isOpen_kone ℚ p b
  have hw₂sm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g := ⟨_, hkone, hw₂K'⟩

  have hZ := central_of_hPS p χ w₂base hPS

  have hχb : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, χ i u = 1 := by
    obtain ⟨Φ, hΦeq, hΦinj, hΦPS⟩ := hPS
    have hbase : w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
      refine Submodule.subset_span ⟨1, ?_⟩
      funext g'; simp
    refine LanglandsTunnell.CubicInduction.forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
      p χ b (Φ w₂base) (hΦPS w₂base hbase) ?_ ?_
    · intro h0
      exact hw₂ne (hΦinj w₂base hbase h0)
    · intro k' hk' g'
      have h1 : (fun g => w₂base (g * k')) = w₂base := funext fun g => hw₂K' k' hk' g
      have h2 := hΦeq w₂base hbase k'
      rw [h1] at h2
      exact (congrFun h2 g').symm

  have hw₂law' : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g := fun x g => by
    rw [← unipotent_eq_unipotentGL2]; exact hw₂law x g
  obtain ⟨fu, χu, E, u₁, hχu0, hχu1, hfuPS, hfuK, hEK, hElaw', hEfin, hJ', hEsum⟩ :=
    LanglandsTunnell.CubicInduction.exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2
      p χ cχ hcχ (kone ℚ p b) (isOpen_kone ℚ p b) (kone_le ℚ p b) w₂base hw₂law' hw₂K' hPS w₀p hw₀p
      (selfDualHaarAt ℚ p)
  have hElaw : ∀ (i : ℤ) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      E i (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * E i g := fun i x g => by
    rw [unipotent_eq_unipotentGL2]; exact hElaw' i x g
  have hJ : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      ∫ y, fu u (w₀p * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y ∂(selfDualHaarAt ℚ p) =
        ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g := fun u hu g => (hJ' u hu g).2

  have hmod1 : ∀ (n : ℕ), ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p n,
      ((modulus (h : p.adicCompletion ℚ) : ℝ) : ℂ) = 1 := by
    intro n h hh
    have hv : Valued.v (h : p.adicCompletion ℚ) = 1 :=
      ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff (K := ℚ) (v := p)).mp hh).1
    rw [modulus_eq_one_of_valuation_eq_one p hv]; simp
  have hcχu : ∀ (u : ℂ) (i : Fin 2), ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χu u i h = 1 := by
    intro u
    refine Fin.forall_fin_two.mpr ⟨fun h hh => Units.val_injective ?_, fun h hh => Units.val_injective ?_⟩
    · rw [hχu0 u h, hmod1 _ h hh, Complex.one_cpow, mul_one, Units.val_one, hcχ 0 h hh, Units.val_one]
    · rw [hχu1 u h, hmod1 _ h hh, Complex.one_cpow, mul_one, Units.val_one, hcχ 1 h hh, Units.val_one]

  set ϖu : (p.adicCompletion ℚ)ˣ := Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
    with hϖu_def
  have hϖu : Valued.v (ϖu : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := hϖ
  obtain ⟨ud, hud⟩ := exists_forall_dominant p χ χu hχu0 hχu1 hϖu

  set w₁ : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun u g =>
    ∫ y, fu u (w₀p * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y ∂(selfDualHaarAt ℚ p)
    with hw₁def
  set E₂ : ℤ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i g =>
    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
      E i (w₀p * transposeInvN (Fin 2) g) with hE₂def
  set w₂fam : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun u g =>
    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
      w₁ u (w₀p * transposeInvN (Fin 2) g) with hw₂famdef
  set wc₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
      w₂base (w₀p * transposeInvN (Fin 2) g) with hwc₂def

  have hsupp : ∀ (cf : ℤ → ℂ) (g : GL (Fin 2) (p.adicCompletion ℚ)), (Function.support fun i : ℤ => cf i * E i g).Finite := by
    intro cf g
    refine (hEfin {g} isCompact_singleton).subset ?_
    intro i hi
    rw [Function.mem_support] at hi
    exact ⟨g, rfl, right_ne_zero_of_mul hi⟩
  have hw₂fam : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂fam u g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E₂ i g := by
    intro u hu g
    simp only [hw₂famdef, hw₁def, hE₂def]
    rw [hJ u hu, mul_finsum' _ _ (hsupp _ _)]
    exact finsum_congr fun i => by ring
  have hwc₂ : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), wc₂ g = ∑ᶠ i : ℤ, E₂ i g := by
    intro g
    simp only [hwc₂def, hE₂def]
    rw [hEsum, mul_finsum' _ _ ?_]
    have h__af := (hsupp (fun _ => 1) (w₀p * transposeInvN (Fin 2) g))
    simp at h__af
    exact h__af

  have hE₂fin : ∀ Cset : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact Cset → {i : ℤ | ∃ g ∈ Cset, E₂ i g ≠ 0}.Finite := by
    intro Cset hC
    have hC' : IsCompact ((fun g => w₀p * transposeInvN (Fin 2) g) '' Cset) :=
      hC.image (continuous_const.mul (continuous_transposeInvN ℚ p))
    refine (hEfin _ hC').subset ?_
    rintro i ⟨g, hg, hi⟩
    exact ⟨w₀p * transposeInvN (Fin 2) g, ⟨g, hg, rfl⟩, right_ne_zero_of_mul hi⟩

  intro w₂ hw₂ W₃ hW₃
  refine LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul
    p W₃base hW₃law hW₃sm w₂base hw₂law hw₂sm w₀p hw₀p
    (fun s => (C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
      (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) μ₂ μN₂ (fun g₃ => ?_) w₂ hw₂ W₃ hW₃

  have hA₁sm := smooth_A (K := ℚ) (v := p) g₃ hW₃sm
  have hA₂sm := smooth_Afun (K := ℚ) (v := p) g₃ hW₃sm
  have hA₂c : Continuous (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g)) := by
    obtain ⟨U, hU, hAU⟩ := hA₂sm
    exact continuous_of_rightInvariant hU hAU

  have hTF₁ : ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ p η c → c ≤ b →
      ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((kone ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₃base (iotaGL g * g₃))
                  (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                    ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 := by
    intro k₀ _ η c hη hc
    obtain ⟨T, hT⟩ := hβ g₃ k₀ η c hη hc μ₂
    exact ⟨T, fun n hn => (hT n hn).1⟩
  have hTF₂ : ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ p η c → c ≤ b →
      ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((koneT ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g))
                  (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                    ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 := by
    intro k₀ _ η c hη hc
    obtain ⟨T, hT⟩ := hβ g₃ k₀ η c hη hc μ₂
    refine ⟨T, fun n hn => ?_⟩
    have h0 := (hT n hn).2
    have hcv : ∀ u : (p.adicCompletion ℚ)ˣ,
        (∫ k in ((koneT ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g))
              (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                ^ n.1 * u) * (k₀ * k)) ∂μ₂) =
        ∫ k in ((kone ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL
              (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                ^ n.1 * u) * (k₀ * transposeInvN (Fin 2) k))) ∂μ₂ := by
      intro u
      exact setIntegral_koneT_eq (b := b) μ₂ _ (hA₂c.comp (continuous_const.mul (continuous_const.mul continuous_id)))
    simp_rw [hcv]
    exact h0

  have hcentre₁ := LanglandsTunnell.CubicInduction.exists_forall_integrable_rsLocalIntegrand_of_gauge p
    (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ rfl W₃base hW₃law hW₃sm hWgauge hπ hϖ b w₂base hw₂law hw₂K''
    (χ 0 * χ 1) hZ hw₂gr g₃ μ₂ μN₂
  have hbase_mem : W₃base ∈ gl3CyclicSubspace W₃base := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext h; simp [gl3AmbientRightTranslate]
  have htr_mem : (fun x => W₃base (x * g₃)) ∈ gl3CyclicSubspace W₃base :=
    gl3AmbientRightTranslate_mem_gl3CyclicSubspace W₃base g₃ hbase_mem
  have htr_gauge := (LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
    W₃base hWgauge _ htr_mem).1
  have htr_law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (fun x => W₃base (x * g₃)) := by
    intro x y z g
    simp only
    rw [mul_assoc, hW₃law]
  have htr_sm := smooth_translate (K := ℚ) (v := p) g₃ hW₃sm
  have hcentre₂ := LanglandsTunnell.RankinSelberg.exists_forall_integrable_dual_rsLocalIntegrand_of_gauge p
    (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ rfl (fun x => W₃base (x * g₃)) htr_law htr_sm htr_gauge hπ hϖ b
    w₂base hw₂law hw₂K'' (χ 0 * χ 1) hZ hw₂gr w₀p hw₀p μ₂ μN₂
  obtain ⟨σc₁, hσc₁⟩ := hcentre₁
  obtain ⟨σc₂, hσc₂⟩ := hcentre₂

  have hdual_gauge := (LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
    W₃base hWgauge _ htr_mem).2
  have hdual_sm := smooth_dualWhittakerFn3 p (W := fun x => W₃base (x * g₃)) htr_sm
  have hω₃tr : ∀ (z : (p.adicCompletion ℚ)ˣ) (x : LocalGL3 p),
      (fun x : LocalGL3 p => W₃base (x * g₃)) (Matrix.GeneralLinearGroup.scalar (Fin 3) z * x) =
        ((ω₃ z : ℂˣ) : ℂ) * (fun x : LocalGL3 p => W₃base (x * g₃)) x := by
    intro z x; simp only; rw [mul_assoc, hω₃]

  have hnat_mem : (fun x : LocalGL3 p => ∫ k in ((kone ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))), W₃base (x * iotaGL k * g₃) ∂μ₂) ∈ gl3CyclicSubspace W₃base :=
    avg_mem_gl3CyclicSubspace (K := ℚ) (v := p) (b := b) g₃ μ₂ hW₃sm
  have hnat_law := law_of_mem_gl3CyclicSubspace (K := ℚ) (v := p) hW₃law hnat_mem
  have hnat_sm := smooth_of_mem_gl3CyclicSubspace (K := ℚ) (v := p) hW₃sm hnat_mem
  have hnat_ω := central_of_mem_gl3CyclicSubspace (K := ℚ) (v := p) hω₃ hnat_mem
  have hnat_gauge := (LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
    W₃base hWgauge _ hnat_mem).1
  obtain ⟨uM, huM⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_flatSection_mul_whittaker_iotaGL_diagUnits2_longWeyl3_of_gauge
      p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ _ hnat_law hnat_sm ω₃ hnat_ω hnat_gauge
      χ cχ hcχ fu χu hχu0 hχu1 hfuPS w₀p hw₀p (selfDualHaarAt ℚ p)
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))

  have hFE : ∃ u₀ : ℝ, ∀ u : ℂ, u₀ < u.re →
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₃base (iotaGL g * g₃)) g * w₁ u g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g)) g * w₂fam u g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₃base (iotaGL g * g₃)) (w₁ u) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g)) (w₂fam u) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            ((fun s => (C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
                (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) s *
              (Ideal.absNorm p.asIdeal : ℂ) ^ (((k 0 - k 1 : ℤ) : ℂ) * u)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by
    refine ⟨max ud uM, fun u hu => ?_⟩
    have hdom := hud u (lt_of_le_of_lt (le_max_left _ _) hu)
    have hcM := huM u (lt_of_le_of_lt (le_max_right _ _) hu)

    have hcP :=
      LanglandsTunnell.RankinSelberg.exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
        p (fun x => W₃base (x * g₃)) htr_sm htr_gauge (χu u) cχ (hcχu u) ϖu hϖu hdom (fu u) (hfuPS u)
        ⟨_, isOpen_kone ℚ p b, hfuK u⟩ w₀p hw₀p μ₂

    obtain ⟨χD, hχD0, hχD1, hfD⟩ :=
      LanglandsTunnell.CubicInduction.exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
        p (χu u) (fu u) (hfuPS u) w₀p hw₀p
    have hcχD : ∀ i : Fin 2, ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (![cχ 1, cχ 0] i), χD i h = 1 := by
      refine Fin.forall_fin_two.mpr ⟨fun h hh => Units.val_injective ?_, fun h hh => Units.val_injective ?_⟩
      · rw [hχD0 h, hmod1 _ h hh, mul_one, Units.val_one, hcχu u 1 h hh, Units.val_one, inv_one]
      · rw [hχD1 h, hmod1 _ h hh, mul_one, Units.val_one, hcχu u 0 h hh, Units.val_one, inv_one]
    have hdomD : ‖((χD 0 ϖu : ℂˣ) : ℂ)‖ < ‖((χD 1 ϖu : ℂˣ) : ℂ)‖ := by
      rw [hχD0, hχD1, norm_mul, norm_mul, norm_inv, norm_inv]
      exact mul_lt_mul_of_pos_right (inv_strictAnti₀ (norm_pos_iff.mpr (Units.ne_zero _)) hdom)
        (norm_pos_iff.mpr (by exact_mod_cast (modulus_pos ϖu.ne_zero).ne'))
    have hcD :=
      LanglandsTunnell.RankinSelberg.exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
        p (dualWhittakerFn3 (fun x => W₃base (x * g₃))) hdual_sm hdual_gauge χD ![cχ 1, cχ 0] hcχD ϖu hϖu hdomD
        _ hfD ⟨_, isOpen_koneT ℚ p b, Bfun_mul (b := b) (w₂ := fu u) (w₀p := w₀p) (hfuK u)⟩ w₀p hw₀p μ₂

    have hχub : ∀ i : Fin 2, ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, χu u i h = 1 := by
      have hm : ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, ((modulus (h : p.adicCompletion ℚ) : ℝ) : ℂ) = 1 := by
        intro h hh
        have hv : Valued.v (h : p.adicCompletion ℚ) = 1 := ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff (K := ℚ) (v := p)).mp hh).1
        rw [modulus_eq_one_of_valuation_eq_one p hv]; simp
      have h1 : ∀ i : Fin 2, ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, ((χ i h : ℂˣ) : ℂ) = 1 := by
        intro i h hh; rw [hχb i h hh]; simp
      refine Fin.forall_fin_two.mpr ⟨fun h hh => Units.val_injective ?_, fun h hh => Units.val_injective ?_⟩
      · rw [hχu0 u h, hm h hh, Complex.one_cpow, mul_one, Units.val_one]; exact h1 0 h hh
      · rw [hχu1 u h, hm h hh, Complex.one_cpow, mul_one, Units.val_one]; exact h1 1 h hh

    have h40_0 := LanglandsTunnell.CubicInduction.forall_localZeta31_fe_of_twist_modulus_cpow p W₃base (χ 0) (χu u 0) u
      (hχu0 u) (C 0) (k 0) (h31 0)
    have h40_1 := LanglandsTunnell.CubicInduction.forall_localZeta31_fe_of_twist_modulus_cpow p W₃base (χ 1) (χu u 1) (-u)
      (hχu1 u) (C 1) (k 1) (h31 1)
    set Cu : Fin 2 → ℂ := ![C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * u),
      C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-u))] with hCu
    have h31u : ∀ i : Fin 2, ∀ g : LocalGL3 p,
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base (χu u i) g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (χu u i) s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) ((χu u i))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base (χu u i) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (Cu i * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k i : ℂ) * s))) := by
      refine Fin.forall_fin_two.mpr ⟨fun g => ?_, fun g => ?_⟩
      · simpa [hCu] using h40_0 g
      · simpa [hCu] using h40_1 g

    obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4, h5⟩ :=
      LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_integrable_setIntegral_localLevelOne_of_torusShell
        p hπ hϖ b W₃base hW₃law hW₃sm ω₃ hω₃ hWgauge g₃ (hβ g₃) (χu u) hχub Cu k h31u (fu u) (hfuPS u) (hfuK u)
        w₀p hw₀p μ₂ μN₂ hcP hcD hcM

    have hγ : ∀ s : ℂ,
        (Cu 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) * (Cu 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s))) =
          ((C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) * (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) *
            (Ideal.absNorm p.asIdeal : ℂ) ^ (((k 0 - k 1 : ℤ) : ℂ) * u) := by
      intro s
      have hsplit : (Ideal.absNorm p.asIdeal : ℂ) ^ (((k 0 - k 1 : ℤ) : ℂ) * u) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * u) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-u)) := by
        rw [← Complex.cpow_add _ _ hq0]
        congr 1
        push_cast
        ring
      simp only [hCu, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsplit]
      ring
    refine ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4, fun s => ?_⟩
    rw [h5 s, hγ s]

  have hcentre : ∃ σc : ℝ, ∀ s : ℂ, σc < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₃base (iotaGL g * g₃)) g * w₂base g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g)) g * wc₂ g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := by
    refine ⟨max σc₁ σc₂, fun s hs => ⟨?_, ?_⟩⟩
    · exact hσc₁ s (lt_of_le_of_lt (le_max_left _ _) hs)
    · exact hσc₂ s (lt_of_le_of_lt (le_max_right _ _) hs)

  have hR6 :=
    LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
      ℚ p hπ hϖ b (kone ℚ p b) (koneT ℚ p b) (isOpen_kone ℚ p b) (kone_le ℚ p b)
      (fun k' hk' hc => mem_kone_of_cong ℚ p b k' hk' hc)
      (isOpen_koneT ℚ p b) (koneT_le ℚ p b) (fun k' hk' hc => mem_koneT_of_cong ℚ p b k' hk' hc)
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₃base (iotaGL g * g₃))
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g))
      hA₁sm hA₂sm E E₂ hEK
      (fun i => Bfun_mul (b := b) (w₂ := E i) (w₀p := w₀p) (hEK i))
      (fun i x g => prod_unipotent_primal g₃ hW₃law (hElaw i) x g)
      (fun i x g => prod_unipotent_dual g₃ hW₃law (hElaw i) hw₀p x g)
      hEfin hE₂fin w₁ w₂fam w₂base wc₂ u₁ (fun u hu g => hJ u hu g) hw₂fam hEsum hwc₂
      (fun s => (C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
        (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) (k 0 - k 1)
      μ₂ μN₂ (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) hTF₁ hTF₂ hFE hcentre
  simpa only using hR6

end S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2 (solution)
