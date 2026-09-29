-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/71c71fd3-aefe-57c2-a295-c8c438c23370

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
import Theorems.Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace KcFibreFED

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

theorem transposeInv3_longWeyl3 : transposeInv3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 := by
  refine Units.ext ?_
  change (((longWeyl3 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  change ((longWeyl3 : GL (Fin 3) A).inv)ᵀ = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longWeyl3]

theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl3_inv : (longWeyl3 : GL (Fin 3) A)⁻¹ = longWeyl3 :=
  inv_eq_of_mul_eq_one_right longWeyl3_mul_longWeyl3

theorem weylPrime3_transposeInv3_weylPrime3_transposeInv3 (g : GL (Fin 3) A) :
    weylPrime3 * transposeInv3 (weylPrime3 * transposeInv3 g) = g := by
  rw [transposeInv3_mul, transposeInv3_weylPrime3, transposeInv3_transposeInv3, ← mul_assoc, weylPrime3_mul_self,
    one_mul]

theorem dualWhittakerFn3_dualWhittakerFn3 {R : Type*} (Φ : GL (Fin 3) A → R) :
    dualWhittakerFn3 (dualWhittakerFn3 Φ) = Φ := by
  funext g
  simp only [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_longWeyl3, transposeInv3_transposeInv3,
    ← mul_assoc, longWeyl3_mul_longWeyl3, one_mul]

theorem dualWhittakerFn3_gl3AmbientRightTranslate (g : GL (Fin 3) A) (Φ : GL (Fin 3) A → ℂ) :
    dualWhittakerFn3 (gl3AmbientRightTranslate (R := ℂ) g Φ) =
      gl3AmbientRightTranslate (R := ℂ) (transposeInv3 g) (dualWhittakerFn3 Φ) := by
  funext x
  simp only [dualWhittakerFn3_apply, gl3AmbientRightTranslate_apply, transposeInv3_mul,
    transposeInv3_transposeInv3, mul_assoc]

theorem dualWhittakerFn3_add {R : Type*} [Add R] (Φ₁ Φ₂ : GL (Fin 3) A → R) :
    dualWhittakerFn3 (Φ₁ + Φ₂) = dualWhittakerFn3 Φ₁ + dualWhittakerFn3 Φ₂ := rfl

theorem dualWhittakerFn3_smul (c : ℂ) (Φ : GL (Fin 3) A → ℂ) :
    dualWhittakerFn3 (c • Φ) = c • dualWhittakerFn3 Φ := rfl

theorem dualWhittakerFn3_zero {R : Type*} [Zero R] : dualWhittakerFn3 (0 : GL (Fin 3) A → R) = 0 := rfl

theorem dualWhittakerFn3_mem_gl3CyclicSubspace (V : GL (Fin 3) A → ℂ) {W' : GL (Fin 3) A → ℂ}
    (hW' : W' ∈ gl3CyclicSubspace (dualWhittakerFn3 V)) : dualWhittakerFn3 W' ∈ gl3CyclicSubspace V := by
  refine Submodule.span_induction (p := fun f _ => dualWhittakerFn3 f ∈ gl3CyclicSubspace V) ?_ ?_ ?_ ?_ hW'
  · rintro _ ⟨g, rfl⟩
    rw [dualWhittakerFn3_gl3AmbientRightTranslate, dualWhittakerFn3_dualWhittakerFn3]
    exact Submodule.subset_span ⟨transposeInv3 g, rfl⟩
  · show dualWhittakerFn3 (0 : GL (Fin 3) A → ℂ) ∈ gl3CyclicSubspace V
    rw [dualWhittakerFn3_zero]; exact Submodule.zero_mem _
  · intro f₁ f₂ _ _ h₁ h₂
    show dualWhittakerFn3 (f₁ + f₂) ∈ gl3CyclicSubspace V
    rw [dualWhittakerFn3_add]; exact Submodule.add_mem _ h₁ h₂
  · intro c f _ h
    show dualWhittakerFn3 (c • f) ∈ gl3CyclicSubspace V
    rw [dualWhittakerFn3_smul]; exact Submodule.smul_mem _ c h

theorem coe_transposeInv3_upperUnipotent3 (x y z : A) :
    ((transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
  have hinv : (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  change (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3 (x y z : A) :
    (longWeyl3 : GL (Fin 3) A) * transposeInv3 (upperUnipotent3 x y z) * longWeyl3 =
      upperUnipotent3 (-y) (-x) (x * y - z) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInv3_upperUnipotent3, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem isGL3PsiWhittakerFn_dualWhittakerFn3 {F : Type*} [CommRing F] {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) : IsGL3PsiWhittakerFn ψ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul]
  have h : (longWeyl3 : GL (Fin 3) F) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
      upperUnipotent3 (-y) (-x) (x * y - z) * (longWeyl3 * transposeInv3 g) := by
    rw [← longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3]
    have : (longWeyl3 : GL (Fin 3) F) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
        longWeyl3 * transposeInv3 (upperUnipotent3 x y z) * longWeyl3⁻¹ * (longWeyl3 * transposeInv3 g) := by
      group
    rw [this, longWeyl3_inv]
  rw [h, hW, AddChar.inv_apply]
  congr 2
  ring

end Algebra

section Smooth

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

def IsSmooth3 (W : GL (Fin 3) F → ℂ) : Prop :=
  ∃ U : Subgroup (GL (Fin 3) F), IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g : GL (Fin 3) F, W (g * k) = W g

theorem isSmooth3_zero : IsSmooth3 (0 : GL (Fin 3) F → ℂ) :=
  ⟨⊤, by simp, fun _ _ _ => rfl⟩

theorem IsSmooth3.add {W₁ W₂ : GL (Fin 3) F → ℂ} (h₁ : IsSmooth3 W₁) (h₂ : IsSmooth3 W₂) :
    IsSmooth3 (W₁ + W₂) := by
  obtain ⟨U₁, hU₁, hW₁⟩ := h₁
  obtain ⟨U₂, hU₂, hW₂⟩ := h₂
  refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
  · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
  · simp only [Pi.add_apply, hW₁ k (Subgroup.mem_inf.mp hk).1 g, hW₂ k (Subgroup.mem_inf.mp hk).2 g]

theorem IsSmooth3.smul (c : ℂ) {W : GL (Fin 3) F → ℂ} (h : IsSmooth3 W) : IsSmooth3 (c • W) := by
  obtain ⟨U, hU, hW⟩ := h
  exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hW k hk g]⟩

theorem IsSmooth3.translate {W : GL (Fin 3) F → ℂ} (h : IsSmooth3 W) (h₀ : GL (Fin 3) F) :
    IsSmooth3 (fun x => W (x * h₀)) := by
  obtain ⟨U, hU, hW⟩ := h
  refine ⟨U.comap (MulAut.conj h₀⁻¹).toMonoidHom, ?_, fun k hk g => ?_⟩
  · rw [Subgroup.coe_comap]
    refine hU.preimage ?_
    show Continuous fun k : GL (Fin 3) F => h₀⁻¹ * k * h₀⁻¹⁻¹
    exact (continuous_const.mul continuous_id).mul continuous_const
  · have hk' : h₀⁻¹ * k * h₀ ∈ U := by
      have := Subgroup.mem_comap.mp hk
      simpa using this
    show W (g * k * h₀) = W (g * h₀)
    rw [show g * k * h₀ = g * h₀ * (h₀⁻¹ * k * h₀) by group]
    exact hW _ hk' _

theorem isSmooth3_of_mem_gl3CyclicSubspace {W : GL (Fin 3) F → ℂ} (hW : IsSmooth3 W)
    {W' : GL (Fin 3) F → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) : IsSmooth3 W' := by
  refine Submodule.span_induction (p := fun f _ => IsSmooth3 f) ?_ ?_ ?_ ?_ hW'
  · rintro _ ⟨h₀, rfl⟩
    exact hW.translate h₀
  · exact isSmooth3_zero
  · intro f₁ f₂ _ _ h₁ h₂; exact h₁.add h₂
  · intro c f _ h; exact h.smul c

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace {θ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn θ W) {W' : GL (Fin 3) F → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) :
    IsGL3PsiWhittakerFn θ W' := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace F ℂ θ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h₀, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace θ h₀ ((mem_gl3PsiWhittakerFnSpace_iff θ W).mpr hW)
  exact (mem_gl3PsiWhittakerFnSpace_iff θ W').mp (hle hW')

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem gl3CyclicSubspace_le_of_mem {W W' : GL (Fin 3) F → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace W' ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h₀, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h₀ hW'

theorem continuous_transposeInv3 : Continuous (transposeInv3 : GL (Fin 3) F → GL (Fin 3) F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin 3) F => (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : GL (Fin 3) F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ
    exact Units.continuous_val.matrix_transpose

def tau3 : GL (Fin 3) F →* GL (Fin 3) F where
  toFun := transposeInv3
  map_one' := by
    refine Units.ext ?_
    rw [transposeInv3_coe, inv_one, Units.val_one, Matrix.transpose_one]
  map_mul' := transposeInv3_mul

theorem IsSmooth3.dual {W : GL (Fin 3) F → ℂ} (hW : IsSmooth3 W) : IsSmooth3 (dualWhittakerFn3 W) := by
  obtain ⟨Uv, hUv, hinv⟩ := hW
  refine ⟨Uv.comap (tau3 (F := F)), hUv.preimage continuous_transposeInv3, fun k hk g => ?_⟩
  change W (longWeyl3 * transposeInv3 (g * k)) = W (longWeyl3 * transposeInv3 g)
  rw [transposeInv3_mul, ← mul_assoc]
  exact hinv (transposeInv3 k) hk _

end Smooth

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance borelSpace_units_adic : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_units

theorem coe_modulus_eq_norm (x : p.adicCompletion ℚ) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem modulus_units_ne_zero (u : (p.adicCompletion ℚ)ˣ) : (((modulus (u : p.adicCompletion ℚ) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
  rw [coe_modulus_eq_norm]
  exact_mod_cast (norm_pos_iff.mpr u.ne_zero).ne'

theorem val_eq_one_iff_norm_eq_one (x : p.adicCompletion ℚ) : Valued.v x = 1 ↔ ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def]
  have h1 : (1 : ℝ) = ((1 : NNReal) : ℝ) := rfl
  rw [h1, NNReal.coe_inj, WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero p)
    (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p))]

theorem measurableSet_sph :
    MeasurableSet {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
  have h : {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} =
      Units.val ⁻¹' Metric.sphere (0 : p.adicCompletion ℚ) 1 := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_sphere_zero_iff_norm]
    exact val_eq_one_iff_norm_eq_one p _
  rw [h]
  exact ((IsUltrametricDist.isOpen_sphere (0 : p.adicCompletion ℚ) one_ne_zero).preimage
    Units.continuous_val).measurableSet

theorem one_lt_q : 1 < Ideal.absNorm p.asIdeal := by
  refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot, ?_⟩
  exact Ideal.absNorm_eq_one_iff.not.mpr (Ideal.IsPrime.ne_top p.isPrime)

theorem qC_ne_zero : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)

end Place

end KcFibreFED
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell.KcFibreFED"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell.KcFibreFED"

open KcFibreFED

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

set_option maxHeartbeats 8000000 in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (n : ℤ)
    (hψn : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (V : LocalGL3 p → ℂ) (hV : IsGL3PsiWhittakerFn ψ⁻¹ V)
    (hVsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, V (g * k) = V g)
    (χ η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((η a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ))
    (C : ℂ) (k : ℤ) (h : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],

      (∀ h' : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ j : ℤ, j ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          dualWhittakerFn3 V (iotaGL (diagUnitGL2
            (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ j * u) * h')) *
            ((χ u : ℂˣ) : ℂ)⁻¹ ∂τ = 0) →

      (∀ V' ∈ gl3CyclicSubspace V, ∃ (Q₁ Q₂ : Polynomial ℂ) (n₀ : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p τ V' χ (weylPrime3 * transposeInv3 (iotaGL h)) σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p τ V' χ s (weylPrime3 * transposeInv3 (iotaGL h)) *
                Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p τ ν (dualWhittakerFn3 V') χ⁻¹
            (weylPrime3 * transposeInv3 (weylPrime3 * transposeInv3 (iotaGL h))) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p τ ν V' χ (1 - s) (weylPrime3 * transposeInv3 (iotaGL h)) *
                Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℂ) * s) *
                (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)))) →
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ σ₁ : ℝ) (R : Finset ℝ),
        IsLocalZeta31ConvergentAbove p τ ν (dualWhittakerFn3 V) η (iotaGL h) σ₀ ∧
        (∀ S : ℂ, σ₀ < S.re →
          localZeta31 p τ ν (dualWhittakerFn3 V) η S (iotaGL h) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * S) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S))) ∧
        IsLocalZeta30ConvergentAbove p τ V χ (weylPrime3 * transposeInv3 (iotaGL h)) σ₁ ∧
        (∀ S : ℂ, σ₁ < (-S).re → (Ideal.absNorm p.asIdeal : ℝ) ^ S.re ∉ R →
          C * localZeta30 p τ V χ (-S) (weylPrime3 * transposeInv3 (iotaGL h)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * S) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * S) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S)))) := by
  intro τ _ ν _ hT h31
  set qC : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hqCdef
  have hqC0 : qC ≠ 0 := qC_ne_zero p
  set g' : LocalGL3 p := weylPrime3 * transposeInv3 (iotaGL h) with hg'
  have hg'back : weylPrime3 * transposeInv3 g' = iotaGL h := weylPrime3_transposeInv3_weylPrime3_transposeInv3 _

  have hVs : IsSmooth3 V := hVsm
  have hVd : IsGL3PsiWhittakerFn ψ (dualWhittakerFn3 V) := isGL3PsiWhittakerFn_dualWhittakerFn3 hV
  have hVdsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, dualWhittakerFn3 V (g * k) = dualWhittakerFn3 V g := hVs.dual
  have hθ : ∃ x : p.adicCompletion ℚ, ψ x ≠ 1 := by
    obtain ⟨x, _, hx⟩ := hψn'
    exact ⟨x, hx⟩

  have hconv : ∀ W' ∈ gl3CyclicSubspace (dualWhittakerFn3 V), ∃ σ : ℝ,
      IsLocalZeta30ConvergentAbove p τ W' η (iotaGL h) σ := by
    intro W' hW'
    set V'' : LocalGL3 p → ℂ := dualWhittakerFn3 W' with hV''
    have hV''mem : V'' ∈ gl3CyclicSubspace V := dualWhittakerFn3_mem_gl3CyclicSubspace V hW'
    have hV''law : IsGL3PsiWhittakerFn ψ⁻¹ V'' := isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace hV hV''mem
    have hV''s : IsSmooth3 V'' := isSmooth3_of_mem_gl3CyclicSubspace hVs hV''mem
    have hV''sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 p, V'' (g * k) = V'' g := hV''s
    have hle : gl3CyclicSubspace V'' ≤ gl3CyclicSubspace V := gl3CyclicSubspace_le_of_mem hV''mem
    obtain ⟨-, -, -, -, σ₁'', -, -, -, hc30d, -⟩ :=
      LanglandsTunnell.CubicInduction.exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
        p ψ n hψn hψn' V'' hV''law hV''sm χ (fun s => C * qC ^ ((k : ℂ) * s)) g' τ ν
        (fun V' hV' => h31 V' (hle hV'))

    rw [hV'', dualWhittakerFn3_dualWhittakerFn3, hg'back] at hc30d
    refine ⟨σ₁'' - 1, fun s hs => ?_⟩
    have hs' : σ₁'' < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
    refine (hc30d (s + 1) hs').congr (Filter.Eventually.of_forall fun a => ?_)
    show W' (iotaGL (diagUnitGL2 a) * iotaGL h) * ((χ⁻¹ a : ℂˣ) : ℂ) *
        (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (s + 1 - 1) =
      W' (iotaGL (diagUnitGL2 a) * iotaGL h) * ((η a : ℂˣ) : ℂ) *
        (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (s - 1)
    rw [hη a, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, show s + 1 - 1 = (s - 1) + 1 by ring,
      Complex.cpow_add _ _ (modulus_units_ne_zero p a), Complex.cpow_one]
    ring

  have hTη : ∀ h' : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ j : ℤ, j ∉ T →
      ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
        dualWhittakerFn3 V (iotaGL (diagUnitGL2
          (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ j * u) * h')) *
          ((η u : ℂˣ) : ℂ) ∂τ = 0 := by
    intro h'
    obtain ⟨T, hT'⟩ := hT h'
    refine ⟨T, fun j hj => ?_⟩
    rw [← hT' j hj]
    refine setIntegral_congr_fun (measurableSet_sph p) fun u hu => ?_
    have hu1 : ‖(u : p.adicCompletion ℚ)‖ = 1 := (val_eq_one_iff_norm_eq_one p _).mp hu
    show _ * ((η u : ℂˣ) : ℂ) = _ * ((χ u : ℂˣ) : ℂ)⁻¹
    rw [hη u, coe_modulus_eq_norm, hu1, Complex.ofReal_one, mul_one]

  obtain ⟨P₀, m₀, σa, hc31, hZ1⟩ :=
    LanglandsTunnell.RankinSelberg.exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
      p hπ hϖ ψ hθ (dualWhittakerFn3 V) hVd hVdsm η h τ ν hTη hconv
  rw [← hqCdef] at hZ1

  have hVmem : V ∈ gl3CyclicSubspace V := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext x
    simp only [gl3AmbientRightTranslate_apply, mul_one]
  obtain ⟨Q₁, Q₂, n₀, σ₀, σ₁, hQ₂, hc30, he30, hc31d, he31d⟩ := h31 V hVmem

  have hZdual : ∀ s : ℂ, localZetaDual31 p τ ν V χ (1 - s) g' = localZeta31 p τ ν (dualWhittakerFn3 V) η (-s) (iotaGL h) := by
    intro s
    unfold localZetaDual31
    rw [hg'back]
    unfold localZeta31
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show _ * ((χ⁻¹ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (1 - s - 1) =
      _ * ((η a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (-s - 1)
    rw [hη a, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, show (1 : ℂ) - s - 1 = (-s - 1) + 1 by ring,
      Complex.cpow_add _ _ (modulus_units_ne_zero p a), Complex.cpow_one]
    ring

  set d : ℕ := P₀.natDegree with hd
  set Pr : Polynomial ℂ := Polynomial.reflect d P₀ with hPr
  have hrefl : ∀ s : ℂ, P₀.eval (qC ^ s) = Pr.eval (qC ^ (-s)) * qC ^ ((d : ℂ) * s) := by
    intro s
    haveI : Invertible (qC ^ s) := invertibleOfNonzero (by
      intro h0
      rw [Complex.cpow_eq_zero_iff] at h0
      exact hqC0 h0.1)
    have h1 := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (qC ^ s) d P₀ (le_of_eq hd.symm)
    rw [Polynomial.eval₂_id, Polynomial.eval₂_id] at h1
    have hinv : (⅟(qC ^ s) : ℂ) = qC ^ (-s) := by
      rw [invOf_eq_inv, Complex.cpow_neg]
    rw [hinv] at h1
    rw [hPr, ← h1, ← Complex.cpow_nat_mul]

  set σL : ℝ := min (1 - σ₁) (-σa) with hσL
  have hq : 1 < Ideal.absNorm p.asIdeal := one_lt_q p
  have hS : {t : ℝ | (t : ℂ) ∈ {s : ℂ | s.re < σL}}.Infinite := by
    have : {t : ℝ | (t : ℂ) ∈ {s : ℂ | s.re < σL}} = Set.Iio σL := by
      ext t
      simp only [Set.mem_setOf_eq, Complex.ofReal_re, Set.mem_Iio]
    rw [this]
    exact Set.Iio_infinite σL
  have hLid : ∀ s ∈ {s : ℂ | s.re < σL},
      qC ^ ((((d : ℤ) - m₀ : ℤ) : ℂ) * s) * Pr.eval (qC ^ (-s)) * Q₂.eval (qC ^ (-s)) =
        (C • Q₁).eval (qC ^ (-s)) * qC ^ (((n₀ + k : ℤ) : ℂ) * s) := by
    intro s hs
    have hs' : s.re < σL := hs
    have h1 : σ₁ < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      have := lt_of_lt_of_le hs' (min_le_left _ _)
      linarith
    have h2 : σa < (-s).re := by
      rw [Complex.neg_re]
      have := lt_of_lt_of_le hs' (min_le_right _ _)
      linarith
    have hfe := he31d s h1
    rw [hZdual s, hZ1 (-s) h2, neg_neg, hrefl s] at hfe

    rw [Polynomial.eval_smul, smul_eq_mul]
    have hexp1 : qC ^ ((((d : ℤ) - m₀ : ℤ) : ℂ) * s) = qC ^ ((m₀ : ℂ) * (-s)) * qC ^ ((d : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hqC0]
      congr 1
      push_cast
      ring
    have hexp2 : qC ^ (((n₀ + k : ℤ) : ℂ) * s) = qC ^ ((n₀ : ℂ) * s) * qC ^ ((k : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hqC0]
      congr 1
      push_cast
      ring
    rw [hexp1, hexp2]
    linear_combination hfe
  have hLdual : ∀ s ∈ {s : ℂ | σ₀ < s.re},
      (fun s : ℂ => C * localZeta30 p τ V χ s g') s * Q₂.eval (qC ^ (-s)) =
        (C • Q₁).eval (qC ^ (-s)) * qC ^ (((n₀ + k : ℤ) : ℂ) * s) *
          (fun s : ℂ => (qC ^ ((k : ℂ) * s))⁻¹) s := by
    intro s hs
    have h1 := he30 s hs
    rw [Polynomial.eval_smul, smul_eq_mul]
    have hexp2 : qC ^ (((n₀ + k : ℤ) : ℂ) * s) = qC ^ ((n₀ : ℂ) * s) * qC ^ ((k : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hqC0]
      congr 1
      push_cast
      ring
    have hk0 : qC ^ ((k : ℂ) * s) ≠ 0 := fun h0 => hqC0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1
    rw [hexp2]
    show C * localZeta30 p τ V χ s g' * Q₂.eval (qC ^ (-s)) =
      C * Q₁.eval (qC ^ (-s)) * (qC ^ ((n₀ : ℂ) * s) * qC ^ ((k : ℂ) * s)) * (qC ^ ((k : ℂ) * s))⁻¹
    rw [mul_assoc (C * Q₁.eval (qC ^ (-s))), mul_assoc (qC ^ ((n₀ : ℂ) * s)), mul_inv_cancel₀ hk0, mul_one,
      mul_assoc C, h1]
    ring
  obtain ⟨-, R, hR⟩ :=
    Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
      (Ideal.absNorm p.asIdeal) hq Pr (C • Q₁) Q₂ hQ₂ ((d : ℤ) - m₀) (n₀ + k)
      (fun s : ℂ => (qC ^ ((k : ℂ) * s))⁻¹) (fun s : ℂ => C * localZeta30 p τ V χ s g')
      {s : ℂ | s.re < σL} {s : ℂ | σ₀ < s.re} hS hLid hLdual

  refine ⟨P₀, m₀, σa, σ₀, R, hc31, hZ1, hc30, fun S hS hSR => ?_⟩
  have hR' := hR (-S) hS (by rw [Complex.neg_re, neg_neg]; exact hSR)

  rw [hR']
  have hexp1 : qC ^ ((((d : ℤ) - m₀ : ℤ) : ℂ) * (-S)) = qC ^ ((m₀ : ℂ) * S) * qC ^ ((d : ℂ) * (-S)) := by
    rw [← Complex.cpow_add _ _ hqC0]
    congr 1
    push_cast
    ring
  have hexp3 : (qC ^ ((k : ℂ) * (-S)))⁻¹ = qC ^ ((k : ℂ) * S) := by
    rw [← Complex.cpow_neg]
    congr 1
    ring
  rw [neg_neg, hexp1, hexp3, hrefl (-S), neg_neg]
  ring

end S_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell (solution)
