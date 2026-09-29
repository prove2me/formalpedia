-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b7ea50ab-7719-5ead-968e-6d752359b21d

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
import Theorems.Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal

open scoped ENNReal Topology

namespace FlatClearedGL2

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) := locallyCompactSpace_localGL ℚ p

abbrev kzero : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem isLocalLevelOne_top_of_integral {m : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (h : ∀ i j, m i j ∈ (HeightOneSpectrum.adicCompletionIntegers ℚ p)) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : (HeightOneSpectrum.adicCompletion ℚ p))) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) :
    k ∈ kzero p ↔ (∀ i j, (k : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) i j ∈ (HeightOneSpectrum.adicCompletionIntegers ℚ p)) ∧ ∀ i j, ((k⁻¹ : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) i j ∈ (HeightOneSpectrum.adicCompletionIntegers ℚ p) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral p h1, isLocalLevelOne_top_of_integral p h2⟩

theorem coe_kzero_eq_localIntegralSet : ((kzero p : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) = localIntegralSet ℚ p := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero p : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet ℚ p

theorem isCompact_kzero : IsCompact ((kzero p : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet ℚ p

theorem valuation_det_of_mem_kzero {k : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hk : k ∈ kzero p) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) = 1 := by
  rw [mem_kzero_iff] at hk
  have hint : ∀ (m : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))), (∀ i j, m i j ∈ (HeightOneSpectrum.adicCompletionIntegers ℚ p)) → Valued.v m.det ≤ 1 := by
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
  have hprod : Valued.v ((k : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))).det) * Valued.v (((k⁻¹ : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))).det) * Valued.v (((k⁻¹ : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))).det) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

variable (ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p)
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) (HeightOneSpectrum.adicCompletion ℚ p) ϖ ≠ 0)

def rep (dn : ℤ × ℤ) : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ dn.1

theorem val_det_scalarPi :
    ((Matrix.GeneralLinearGroup.det (scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p))
      = algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ * algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [scalarPi, Matrix.det_fin_two]

theorem val_det_diagZ (d : ℤ) :
    ((Matrix.GeneralLinearGroup.det (diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ d) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p))
      = algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ ^ d := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [diagZ, Matrix.det_fin_two]

theorem val_det_rep (dn : ℤ × ℤ) :
    ((Matrix.GeneralLinearGroup.det (rep p ϖ hπ dn) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p))
      = algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ ^ (dn.1 + 2 * dn.2) := by
  rw [rep, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, val_det_scalarPi, val_det_diagZ,
    ← pow_two, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hπ]
  congr 1
  push_cast
  ring

theorem norm_uniformizer (hϖ : Valued.v (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) = WithZero.exp (-1 : ℤ)) :
    ‖algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [this]
  simp

theorem norm_eq_one_of_valuation_eq_one {x : (HeightOneSpectrum.adicCompletion ℚ p)} (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

theorem coe_modulus_eq_norm (x : (HeightOneSpectrum.adicCompletion ℚ p)) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem modulus_det_rep (hϖ : Valued.v (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) = WithZero.exp (-1 : ℤ)) (dn : ℤ × ℤ) :
    ((modulus ((Matrix.GeneralLinearGroup.det (rep p ϖ hπ dn) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ)
        : ℂ) = (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(dn.1 + 2 * dn.2) : ℤ) : ℂ)) := by
  rw [coe_modulus_eq_norm, val_det_rep, norm_zpow, norm_uniformizer p ϖ hϖ, inv_zpow', Complex.ofReal_zpow,
    ← Complex.cpow_intCast]
  push_cast
  rfl

theorem modulus_det_mul_of_mem_kzero (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) {k : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hk : k ∈ kzero p) :
    (modulus ((Matrix.GeneralLinearGroup.det (a * k) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ) =
      (modulus ((Matrix.GeneralLinearGroup.det a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ) := by
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, coe_modulus_eq_norm p ((Matrix.GeneralLinearGroup.det k : _ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)),
    norm_eq_one_of_valuation_eq_one p (valuation_det_of_mem_kzero p hk), mul_one]

section Integrand

variable (A B : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)))

def fS (s : ℂ) (g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : ℂ :=
  (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ) : ℂ) ^ (s - 1 / 2)

def Sshell (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : ℂ := ∫ k in (kzero p : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))), A (a * k) * B (a * k) ∂μ₂

abbrev qC : ℂ := (Ideal.absNorm p.asIdeal : ℂ)

theorem one_lt_q : 1 < Ideal.absNorm p.asIdeal := by
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
  omega

theorem qC_ne_zero : qC p ≠ 0 := by
  have := one_lt_q p
  exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)

theorem log_qC_im : (Complex.log (qC p)).im = 0 := by
  rw [qC, show ((Ideal.absNorm p.asIdeal : ℂ)) = ((Ideal.absNorm p.asIdeal : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_log (by positivity), Complex.ofReal_im]

theorem qC_cpow_cpow (y z : ℂ) (hy : y.im = 0) : ((qC p) ^ y) ^ z = (qC p) ^ (y * z) := by
  rw [Complex.cpow_mul]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos.le]

variable {A B}

theorem continuous_modulus_det :
    Continuous fun g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ) : ℂ) := by
  have h : (fun g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ) : ℂ))
      = fun g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) => ((‖(g : (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [h]
  exact Complex.continuous_ofReal.comp ((Units.continuous_val.matrix_det).norm)

theorem measurable_fS (hAc : Continuous A) (hBc : Continuous B) (s : ℂ) : Measurable (fS p A B s) := by
  unfold fS
  exact (hAc.measurable.mul hBc.measurable).mul ((continuous_modulus_det p).measurable.pow_const _)

theorem exists_eq_unipotent {x : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hx : x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range) :
    ∃ y : (HeightOneSpectrum.adicCompletion ℚ p), x = unipotent y := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨Multiplicative.toAdd z, Units.ext ?_⟩
  simp [unipotentGL2Hom, unipotent, unipotentGL2_coe]

theorem det_unipotent (y : (HeightOneSpectrum.adicCompletion ℚ p)) : Matrix.GeneralLinearGroup.det (unipotent y : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [unipotent, Matrix.det_fin_two]

theorem fS_unip (hAB : ∀ (x : (HeightOneSpectrum.adicCompletion ℚ p)) (g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))), A (unipotent x * g) * B (unipotent x * g) = A g * B g) (s : ℂ) :
    ∀ x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range, ∀ g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
      fS p A B s (x * g) = fS p A B s g := by
  intro x hx g
  obtain ⟨y, rfl⟩ := exists_eq_unipotent p hx
  rw [fS, fS, hAB, map_mul, det_unipotent, one_mul]

theorem setIntegral_fS_mul (s : ℂ) (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) :
    ∫ k in (kzero p : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))), fS p A B s (a * k) ∂μ₂ =
      ((modulus ((Matrix.GeneralLinearGroup.det a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ) : ℂ) ^ (s - 1 / 2) *
        Sshell p A B μ₂ a := by
  rw [Sshell, ← integral_const_mul]
  refine setIntegral_congr_fun (isOpen_kzero p).measurableSet fun k hk => ?_
  rw [fS, modulus_det_mul_of_mem_kzero p a hk, mul_comm]

theorem modulus_rep_cpow (hϖ : Valued.v (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) = WithZero.exp (-1 : ℤ)) (s : ℂ) (dn : ℤ × ℤ) :
    ((modulus ((Matrix.GeneralLinearGroup.det (rep p ϖ hπ dn) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (HeightOneSpectrum.adicCompletion ℚ p)) : ℝ) : ℂ)
        ^ (s - 1 / 2) =
      (qC p) ^ (((dn.1 + 2 * dn.2 : ℤ) : ℂ) / 2) * ((qC p) ^ (-s)) ^ (dn.1 + 2 * dn.2) := by
  rw [modulus_det_rep p ϖ hπ hϖ, qC_cpow_cpow, ← Complex.cpow_int_mul, ← Complex.cpow_add _ _ (qC_ne_zero p)]
  · congr 1
    push_cast
    ring
  · push_cast; simp

end Integrand

section Family

variable (F : ℤ → GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (B : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (hF : ∀ i : ℤ, IsLocallyConstant (F i)) (hB : IsLocallyConstant B)
  (hFfin : ∀ C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)), IsCompact C → {i : ℤ | ∃ g ∈ C, F i g ≠ 0}.Finite)

def Ifin {C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hC : IsCompact C) : Finset ℤ := (hFfin C hC).toFinset

theorem eq_zero_of_not_mem_Ifin {C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hC : IsCompact C) {i : ℤ} (hi : i ∉ Ifin p F hFfin hC)
    {g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hg : g ∈ C) : F i g = 0 := by
  by_contra h
  exact hi ((Set.Finite.mem_toFinset _).mpr ⟨g, hg, h⟩)

theorem finsum_eq_sum_of_mem (Y : ℤ → ℂ) {C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hC : IsCompact C) {g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))} (hg : g ∈ C) :
    ∑ᶠ i : ℤ, Y i * F i g = ∑ i ∈ Ifin p F hFfin hC, Y i * F i g := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Function.mem_support] at hi
  by_contra h
  exact hi (by rw [eq_zero_of_not_mem_Ifin p F hFfin hC h hg, mul_zero])

include hF in
theorem isLocallyConstant_sum (Y : ℤ → ℂ) (T : Finset ℤ) :
    IsLocallyConstant fun g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) => ∑ i ∈ T, Y i * F i g := by
  classical
  induction T using Finset.induction_on with
  | empty => (simp; exact IsLocallyConstant.const (0 : ℂ))
  | insert a T ha ih =>
    have h1 : IsLocallyConstant fun g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) => Y a * F a g := (IsLocallyConstant.const (Y a)).mul (hF a)
    have := h1.add ih
    simp [Finset.sum_insert ha] at this ⊢
    exact this

include hF hFfin in

theorem isLocallyConstant_finsum (Y : ℤ → ℂ) : IsLocallyConstant fun g : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) => ∑ᶠ i : ℤ, Y i * F i g := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
  have hg : g ∈ C := mem_of_mem_nhds hCg
  have hlc := (IsLocallyConstant.iff_eventually_eq _).mp (isLocallyConstant_sum p F hF Y (Ifin p F hFfin hC)) g
  filter_upwards [hCg, hlc] with g' hg' hg'eq
  rw [finsum_eq_sum_of_mem p F hFfin Y hC hg', finsum_eq_sum_of_mem p F hFfin Y hC hg, hg'eq]

variable (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) [μ₂.IsHaarMeasure]

def βI (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) (i : ℤ) : ℂ := ∫ k in (kzero p : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))), F i (a * k) * B (a * k) ∂μ₂

theorem isCompact_shell (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : IsCompact ((fun k : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) => a * k) '' (kzero p : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)))) :=
  (isCompact_kzero p).image (continuous_const.mul continuous_id)

include hF hB in
theorem integrableOn_FB (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) (i : ℤ) :
    IntegrableOn (fun k : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) => F i (a * k) * B (a * k)) (kzero p : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) μ₂ :=
  (((hF i).continuous.comp (continuous_const.mul continuous_id)).mul
    (hB.continuous.comp (continuous_const.mul continuous_id))).continuousOn.integrableOn_compact (isCompact_kzero p)

theorem βI_eq_zero_of_not_mem (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) {i : ℤ} (hi : i ∉ Ifin p F hFfin (isCompact_shell p a)) :
    βI p F B μ₂ a i = 0 := by
  rw [βI]
  refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
  rw [eq_zero_of_not_mem_Ifin p F hFfin (isCompact_shell p a) hi ⟨k, hk, rfl⟩, zero_mul]

include hF hB in

theorem Sshell_family (Y : ℤ → ℂ) (a : (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) (J : Finset ℤ) (hJ : Ifin p F hFfin (isCompact_shell p a) ⊆ J) :
    Sshell p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B μ₂ a = ∑ i ∈ J, Y i * βI p F B μ₂ a i := by
  have hI := isCompact_shell p a
  rw [Sshell]
  have h1 : ∫ k in (kzero p : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))), (∑ᶠ i : ℤ, Y i * F i (a * k)) * B (a * k) ∂μ₂ =
      ∫ k in (kzero p : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))), ∑ i ∈ Ifin p F hFfin hI, Y i * (F i (a * k) * B (a * k)) ∂μ₂ := by
    refine setIntegral_congr_fun (isOpen_kzero p).measurableSet fun k hk => ?_
    show (∑ᶠ i : ℤ, Y i * F i (a * k)) * B (a * k) = ∑ i ∈ Ifin p F hFfin hI, Y i * (F i (a * k) * B (a * k))
    rw [finsum_eq_sum_of_mem p F hFfin Y hI ⟨k, hk, rfl⟩, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, integral_finset_sum _ fun i _ => (integrableOn_FB p F B hF hB μ₂ a i).const_mul (Y i)]
  rw [← Finset.sum_subset hJ fun i _ hi => by rw [βI_eq_zero_of_not_mem p F B hFfin μ₂ a hi, mul_zero]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, βI]

end Family

section LaurentAlgebra

theorem laurent_eq_zero_of_infinite {ι : Type*} (T : Finset ι) (a : ι → ℂ) (k : ι → ℤ) (S : Set ℂ)
    (hS : S.Infinite) (h0 : ∀ z ∈ S, z ≠ 0) (h : ∀ z ∈ S, ∑ t ∈ T, a t * z ^ (k t) = 0) :
    ∀ z : ℂ, z ≠ 0 → ∑ t ∈ T, a t * z ^ (k t) = 0 := by
  classical
  set K : ℕ := T.sup fun t => (k t).natAbs with hK
  have hKt : ∀ t ∈ T, 0 ≤ k t + K := by
    intro t ht
    have : (k t).natAbs ≤ K := Finset.le_sup (f := fun t => (k t).natAbs) ht
    omega
  set Q : Polynomial ℂ := ∑ t ∈ T, Polynomial.C (a t) * Polynomial.X ^ (k t + K).toNat with hQ
  have hQeval : ∀ z : ℂ, z ≠ 0 → Q.eval z = (∑ t ∈ T, a t * z ^ (k t)) * z ^ (K : ℤ) := by
    intro z hz
    rw [hQ, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_assoc]
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg (hKt t ht), zpow_add₀ hz]
  have hroots : Set.Infinite {z : ℂ | Q.IsRoot z} := by
    refine hS.mono fun z hz => ?_
    show Q.IsRoot z
    rw [Polynomial.IsRoot.def, hQeval z (h0 z hz), h z hz, zero_mul]
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q hroots
  intro z hz
  have h1 : (∑ t ∈ T, a t * z ^ (k t)) * z ^ (K : ℤ) = 0 := by rw [← hQeval z hz, hQ0, Polynomial.eval_zero]
  rcases mul_eq_zero.mp h1 with h1 | h1
  · exact h1
  · exact absurd h1 (zpow_ne_zero _ hz)

theorem infinite_image_cpow_neg (N : ℕ) (hN : 1 < N) (Sr : Set ℝ) (hSr : Sr.Infinite) :
    Set.Infinite ((fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Sr) ∧
      ∀ z ∈ (fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Sr, z ≠ 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  refine ⟨hSr.image fun t₁ _ t₂ _ ht => ?_, ?_⟩
  · have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((N : ℝ) ^ (-(t₁ : ℝ)) : ℝ) = (N : ℝ) ^ (-(t₂ : ℝ)) := by
      have := congrArg Complex.re ht
      rwa [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast, show (-((t₁ : ℝ) : ℂ)) = ((-(t₁ : ℝ) : ℝ) : ℂ) by push_cast; ring,
        show (-((t₂ : ℝ) : ℂ)) = ((-(t₂ : ℝ) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity),
        Complex.ofReal_re, Complex.ofReal_re] at this
    have h2 : -(t₁ : ℝ) = -(t₂ : ℝ) := by
      rcases lt_trichotomy (-(t₁ : ℝ)) (-(t₂ : ℝ)) with hlt | heq | hgt
      · exact absurd h1 (ne_of_lt ((Real.rpow_lt_rpow_left_iff hN1).mpr hlt))
      · exact heq
      · exact absurd h1 (ne_of_gt ((Real.rpow_lt_rpow_left_iff hN1).mpr hgt))
    exact neg_injective h2
  · rintro z ⟨t, -, rfl⟩
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)

theorem cpow_neg_int_mul (N : ℕ) (i : ℤ) (u : ℂ) :
    (N : ℂ) ^ (-(i : ℂ) * u) = ((N : ℂ) ^ (-u)) ^ i := by
  rw [← Complex.cpow_int_mul]
  congr 1
  ring

def piCoeff (P : Polynomial ℂ) (m₀ : ℤ) (m : ℤ) : ℂ :=
  if 0 ≤ m + m₀ then P.coeff (m + m₀).toNat else 0

theorem piCoeff_eq_zero_of_lt (P : Polynomial ℂ) (m₀ : ℤ) {m : ℤ} (hm : (P.natDegree : ℤ) - m₀ < m) :
    piCoeff P m₀ m = 0 := by
  unfold piCoeff
  split_ifs with h
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  · rfl

theorem hasSum_piCoeff (N : ℕ) (hN : 1 < N) (P : Polynomial ℂ) (m₀ : ℤ) (s : ℂ) :
    HasSum (fun m : ℤ => piCoeff P m₀ m * ((N : ℂ) ^ (-s)) ^ m)
      ((N : ℂ) ^ ((m₀ : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hX : (N : ℂ) ^ (-s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)
  set f : ℕ → ℤ := fun j => (j : ℤ) - m₀ with hf
  have hfinj : Function.Injective f := fun a b h => by simp only [hf] at h; omega
  set T : Finset ℤ := (Finset.range (P.natDegree + 1)).image f with hT
  have hzero : ∀ m ∉ T, piCoeff P m₀ m * ((N : ℂ) ^ (-s)) ^ m = 0 := by
    intro m hm
    unfold piCoeff
    split_ifs with h
    · have : P.coeff (m + m₀).toNat = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        by_contra hlt
        push Not at hlt
        apply hm
        rw [hT, Finset.mem_image]
        refine ⟨(m + m₀).toNat, Finset.mem_range.mpr (by omega), ?_⟩
        simp only [hf]
        rw [Int.toNat_of_nonneg h]
        ring
      rw [this, zero_mul]
    · rw [zero_mul]
  have hfin : HasSum (fun m : ℤ => piCoeff P m₀ m * ((N : ℂ) ^ (-s)) ^ m)
      (∑ m ∈ T, piCoeff P m₀ m * ((N : ℂ) ^ (-s)) ^ m) := hasSum_sum_of_ne_finset_zero hzero
  have hval : ∑ m ∈ T, piCoeff P m₀ m * ((N : ℂ) ^ (-s)) ^ m =
      (N : ℂ) ^ ((m₀ : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) := by
    rw [hT, Finset.sum_image fun a _ b _ h => hfinj h]
    have hm : (N : ℂ) ^ ((m₀ : ℂ) * s) = ((N : ℂ) ^ (-s)) ^ (-m₀) := by
      rw [← Complex.cpow_int_mul]; congr 1; push_cast; ring
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpi : piCoeff P m₀ (f j) = P.coeff j := by
      unfold piCoeff
      simp only [hf, sub_add_cancel, Int.toNat_natCast]
      rw [if_pos (by positivity)]
    rw [hpi, hm, show f j = (j : ℤ) + (-m₀) by simp [hf, sub_eq_add_neg], zpow_add₀ hX, zpow_natCast]
    ring
  rwa [hval] at hfin

end LaurentAlgebra

section Coeff

variable (ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p)
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) (HeightOneSpectrum.adicCompletion ℚ p) ϖ ≠ 0)
  (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) (HeightOneSpectrum.adicCompletion ℚ p) ϖ) =
    WithZero.exp (-1 : ℤ))
  (F : ℤ → GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (B : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (hF : ∀ i : ℤ, IsLocallyConstant (F i)) (hB : IsLocallyConstant B)
  (hFB : ∀ (i : ℤ) (x : HeightOneSpectrum.adicCompletion ℚ p) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    F i (unipotent x * g) * B (unipotent x * g) = F i g * B g)
  (hFfin : ∀ C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)), IsCompact C → {i : ℤ | ∃ g ∈ C, F i g ≠ 0}.Finite)
  (L : ℕ)
  (hcutL : ∀ (i : ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ × ℤ,
    (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
      F i (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
        diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n.1 * k) = 0)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) [μ₂.IsHaarMeasure]
  (μN₂ : Measure ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range) [μN₂.IsHaarMeasure]

def wgt (dn : ℤ × ℤ) : ℝ :=
  ((μN₂ {x : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range |
      (scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ^ dn.2 *
          diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ dn.1)⁻¹ *
        (x : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) *
        (scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ^ dn.2 *
          diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ dn.1) ∈
      AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤})⁻¹).toReal

theorem wgt_nonneg (dn : ℤ × ℤ) : 0 ≤ wgt p ϖ hπ μN₂ dn := ENNReal.toReal_nonneg

def Nr (m : ℤ) : Finset ℤ := Finset.Icc (-(L : ℤ)) (m + 3 * L)

def Jm (m : ℤ) : Finset ℤ :=
  (Nr L m).biUnion fun n => Ifin p F hFfin (isCompact_shell p (rep p ϖ hπ (m - 2 * n, n)))

def cI (m i : ℤ) : ℂ :=
  (qC p) ^ (((m : ℤ) : ℂ) / 2) *
    ∑ n ∈ Nr L m, ((wgt p ϖ hπ μN₂ (m - 2 * n, n) : ℝ) : ℂ) * βI p F B μ₂ (rep p ϖ hπ (m - 2 * n, n)) i

def eY (Y : ℤ → ℂ) (m : ℤ) : ℂ := ∑ i ∈ Jm p ϖ hπ F hFfin L m, Y i * cI p ϖ hπ F B L μ₂ μN₂ m i

def Tterm (A : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ) (s : ℂ) (dn : ℤ × ℤ) : ℂ :=
  ((wgt p ϖ hπ μN₂ dn : ℝ) : ℂ) *
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) :
        Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))),
      fS p A B s (scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ^ dn.2 *
        diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ dn.1 * k) ∂μ₂

def fibreEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun mn := (mn.1 - 2 * mn.2, mn.2)
  invFun dn := (dn.1 + 2 * dn.2, dn.2)
  left_inv mn := by ext <;> simp
  right_inv dn := by ext <;> simp

include hϖ in
theorem modulus_rep_fibre (s : ℂ) (m n : ℤ) :
    ((modulus ((Matrix.GeneralLinearGroup.det (rep p ϖ hπ (m - 2 * n, n)) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ p) : ℝ) : ℂ) ^ (s - 1 / 2) =
      (qC p) ^ (((m : ℤ) : ℂ) / 2) * ((qC p) ^ (-s)) ^ m := by
  have h : ((m - 2 * n, n) : ℤ × ℤ).1 + 2 * ((m - 2 * n, n) : ℤ × ℤ).2 = m := by
    show m - 2 * n + 2 * n = m
    ring
  rw [modulus_rep_cpow p ϖ hπ hϖ s (m - 2 * n, n), h]

include hcutL in

theorem βI_eq_zero_of_cut {dn : ℤ × ℤ} (hdn : dn.1 < -(L : ℤ) ∨ dn.2 < -(L : ℤ)) (i : ℤ) :
    βI p F B μ₂ (rep p ϖ hπ dn) i = 0 := by
  rw [βI]
  refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
  have := hcutL i k hk dn hdn
  rw [rep, this, zero_mul]

include hF hB hFfin hcutL in
theorem Sshell_eq_zero_of_cut (Y : ℤ → ℂ) {dn : ℤ × ℤ} (hdn : dn.1 < -(L : ℤ) ∨ dn.2 < -(L : ℤ)) :
    Sshell p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B μ₂ (rep p ϖ hπ dn) = 0 := by
  rw [Sshell_family p F B hF hB hFfin μ₂ Y (rep p ϖ hπ dn) _ (Finset.Subset.refl _)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [βI_eq_zero_of_cut p ϖ hπ F B L hcutL μ₂ hdn, mul_zero]

include hF hB hFfin hcutL in

theorem Tterm_eq_zero_of_not_mem (Y : ℤ → ℂ) (s : ℂ) (m : ℤ) {n : ℤ} (hn : n ∉ Nr L m) :
    Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) s (m - 2 * n, n) = 0 := by
  have hcond : (m - 2 * n < -(L : ℤ)) ∨ n < -(L : ℤ) := by
    simp only [Nr, Finset.mem_Icc, not_and_or, not_le] at hn
    omega
  rw [Tterm]
  have : ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) :
        Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))),
      fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s (scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ^ ((m - 2 * n, n) : ℤ × ℤ).2 *
        diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ((m - 2 * n, n) : ℤ × ℤ).1 * k) ∂μ₂ =
      ∫ k in ((kzero p : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : Set _),
        fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s (rep p ϖ hπ (m - 2 * n, n) * k) ∂μ₂ := rfl
  rw [this, setIntegral_fS_mul, Sshell_eq_zero_of_cut p ϖ hπ F B hF hB hFfin L hcutL μ₂ Y hcond, mul_zero, mul_zero]

include hcutL in

theorem cI_eq_zero_of_lt {m : ℤ} (hm : m < -(3 * L : ℤ)) (i : ℤ) : cI p ϖ hπ F B L μ₂ μN₂ m i = 0 := by
  rw [cI]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun n hn => ?_)
  have hcond : (((m - 2 * n, n) : ℤ × ℤ).1 < -(L : ℤ)) ∨ ((m - 2 * n, n) : ℤ × ℤ).2 < -(L : ℤ) := by
    simp only [Nr, Finset.mem_Icc] at hn
    left
    show m - 2 * n < -(L : ℤ)
    omega
  rw [βI_eq_zero_of_cut p ϖ hπ F B L hcutL μ₂ hcond, mul_zero]

include hcutL in
theorem eY_eq_zero_of_lt (Y : ℤ → ℂ) {m : ℤ} (hm : m < -(3 * L : ℤ)) : eY p ϖ hπ F B hFfin L μ₂ μN₂ Y m = 0 := by
  rw [eY]
  exact Finset.sum_eq_zero fun i _ => by rw [cI_eq_zero_of_lt p ϖ hπ F B L hcutL μ₂ μN₂ hm, mul_zero]

include hϖ hF hB in

theorem sum_Tterm_fibre (Y : ℤ → ℂ) (s : ℂ) (m : ℤ) :
    ∑ n ∈ Nr L m, Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) s (m - 2 * n, n) =
      eY p ϖ hπ F B hFfin L μ₂ μN₂ Y m * ((qC p) ^ (-s)) ^ m := by
  have hterm : ∀ n ∈ Nr L m,
      Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) s (m - 2 * n, n) =
        ∑ i ∈ Jm p ϖ hπ F hFfin L m,
          ((wgt p ϖ hπ μN₂ (m - 2 * n, n) : ℝ) : ℂ) * ((qC p) ^ (((m : ℤ) : ℂ) / 2) * ((qC p) ^ (-s)) ^ m) *
            (Y i * βI p F B μ₂ (rep p ϖ hπ (m - 2 * n, n)) i) := by
    intro n hn
    rw [Tterm]
    have : ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) :
          Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))),
        fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s (scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ^ ((m - 2 * n, n) : ℤ × ℤ).2 *
          diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ((m - 2 * n, n) : ℤ × ℤ).1 * k) ∂μ₂ =
        ∫ k in ((kzero p : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) : Set _),
          fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s (rep p ϖ hπ (m - 2 * n, n) * k) ∂μ₂ := rfl
    rw [this, setIntegral_fS_mul, modulus_rep_fibre p ϖ hπ hϖ s m n,
      Sshell_family p F B hF hB hFfin μ₂ Y (rep p ϖ hπ (m - 2 * n, n)) (Jm p ϖ hπ F hFfin L m)
        (Finset.subset_biUnion_of_mem (fun n => Ifin p F hFfin (isCompact_shell p (rep p ϖ hπ (m - 2 * n, n)))) hn),
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, eY, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cI, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

include hFB hFfin in

theorem finsum_mul_unip (Y : ℤ → ℂ) (x : HeightOneSpectrum.adicCompletion ℚ p)
    (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :
    (fun g => ∑ᶠ i : ℤ, Y i * F i g) (unipotent x * g) * B (unipotent x * g) =
      (fun g => ∑ᶠ i : ℤ, Y i * F i g) g * B g := by
  have hsupp : ∀ h : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p),
      (Function.support fun i : ℤ => Y i * F i h).Finite := by
    intro h
    refine (hFfin {h} isCompact_singleton).subset fun i hi => ?_
    rw [Function.mem_support] at hi
    exact ⟨h, Set.mem_singleton h, fun h0 => hi (by rw [h0, mul_zero])⟩
  show (∑ᶠ i : ℤ, Y i * F i (unipotent x * g)) * B (unipotent x * g) = (∑ᶠ i : ℤ, Y i * F i g) * B g
  rw [finsum_mul' _ _ (hsupp _), finsum_mul' _ _ (hsupp _)]
  refine finsum_congr fun i => ?_
  rw [mul_assoc, hFB, mul_assoc]

include hϖ hF hB hFB hFfin hcutL in

theorem hasSum_eY (Y : ℤ → ℂ) (s : ℂ)
    (hint : Integrable (fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s)
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) :
    HasSum (fun m : ℤ => eY p ϖ hπ F B hFfin L μ₂ μN₂ Y m * ((qC p) ^ (-s)) ^ m)
      (∫ g, fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) := by
  have hAc : Continuous (fun g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) => ∑ᶠ i : ℤ, Y i * F i g) :=
    (isLocallyConstant_finsum p F hF hFfin Y).continuous
  obtain ⟨-, -, hHS⟩ :=
    AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 ℚ p ϖ hπ hϖ μ₂ μN₂
      (fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s) (measurable_fS p hAc hB.continuous s)
      (fS_unip p (finsum_mul_unip p F B hFB hFfin Y) s) hint
  have hHS' : HasSum (fun dn : ℤ × ℤ => Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) s dn) _ := hHS
  have hre := ((fibreEquiv).hasSum_iff).mpr hHS'
  have hfib : ∀ m : ℤ, HasSum (fun n : ℤ => (fun mn : ℤ × ℤ =>
      Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) s (fibreEquiv mn)) (m, n))
      (eY p ϖ hπ F B hFfin L μ₂ μN₂ Y m * ((qC p) ^ (-s)) ^ m) := by
    intro m
    rw [← sum_Tterm_fibre p ϖ hπ hϖ F B hF hB hFfin L μ₂ μN₂ Y s m]
    exact hasSum_sum_of_ne_finset_zero fun n hn => Tterm_eq_zero_of_not_mem p ϖ hπ F B hF hB hFfin L hcutL μ₂ μN₂ Y s m hn
  exact hre.prod_fiberwise hfib

include hϖ hF hB hFB hFfin hcutL in

theorem summable_norm_eY (Y : ℤ → ℂ) (t : ℝ)
    (hint : Integrable (fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B (t : ℂ))
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) :
    Summable fun m : ℤ => ‖eY p ϖ hπ F B hFfin L μ₂ μN₂ Y m‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t)) ^ m := by
  have hAc : Continuous (fun g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) => ∑ᶠ i : ℤ, Y i * F i g) :=
    (isLocallyConstant_finsum p F hF hFfin Y).continuous
  obtain ⟨-, hSum, -⟩ :=
    AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 ℚ p ϖ hπ hϖ μ₂ μN₂
      (fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B (t : ℂ)) (measurable_fS p hAc hB.continuous _)
      (fS_unip p (finsum_mul_unip p F B hFB hFfin Y) _) hint
  set maj : ℤ × ℤ → ℝ := fun dn => wgt p ϖ hπ μN₂ dn *
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) :
        Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))),
      ‖fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B (t : ℂ) (scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ ^ dn.2 *
        diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion ℚ p) ϖ) hπ dn.1 * k)‖ ∂μ₂ with hmaj
  have hSum' : Summable maj := hSum
  have hre : Summable (maj ∘ fibreEquiv) := (fibreEquiv.summable_iff).mpr hSum'
  have hfib : Summable fun m : ℤ => ∑' n : ℤ, (maj ∘ fibreEquiv) (m, n) := hre.prod
  have hmaj0 : ∀ dn, 0 ≤ maj dn := fun dn =>
    mul_nonneg (wgt_nonneg p ϖ hπ μN₂ dn) (integral_nonneg fun _ => norm_nonneg _)
  have hq : 1 < Ideal.absNorm p.asIdeal := one_lt_q p
  have hX : ‖(qC p) ^ (-(t : ℂ))‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t) := by
    rw [qC, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (zpow_nonneg (by positivity) _)) (fun m => ?_) hfib

  have hnorm : ‖eY p ϖ hπ F B hFfin L μ₂ μN₂ Y m‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t)) ^ m =
      ‖∑ n ∈ Nr L m, Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) (t : ℂ) (m - 2 * n, n)‖ := by
    rw [sum_Tterm_fibre p ϖ hπ hϖ F B hF hB hFfin L μ₂ μN₂ Y (t : ℂ) m, norm_mul, norm_zpow, hX]
  rw [hnorm]
  refine (norm_sum_le _ _).trans ?_
  have hle : ∀ n ∈ Nr L m, ‖Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) (t : ℂ) (m - 2 * n, n)‖ ≤
      (maj ∘ fibreEquiv) (m, n) := by
    intro n _
    show ‖Tterm p ϖ hπ B μ₂ μN₂ (fun g => ∑ᶠ i : ℤ, Y i * F i g) (t : ℂ) (m - 2 * n, n)‖ ≤ maj (m - 2 * n, n)
    rw [Tterm, hmaj, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wgt_nonneg p ϖ hπ μN₂ _)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (wgt_nonneg p ϖ hπ μN₂ _)
  refine (Finset.sum_le_sum hle).trans ?_
  exact (hre.prod_factor m).sum_le_tsum (Nr L m) fun n _ => hmaj0 _

end Coeff

section Cleared

variable (ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p)
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) (HeightOneSpectrum.adicCompletion ℚ p) ϖ ≠ 0)
  (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) (HeightOneSpectrum.adicCompletion ℚ p) ϖ) =
    WithZero.exp (-1 : ℤ))
  (F : ℤ → GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (B : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (hF : ∀ i : ℤ, IsLocallyConstant (F i)) (hB : IsLocallyConstant B)
  (hFB : ∀ (i : ℤ) (x : HeightOneSpectrum.adicCompletion ℚ p) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    F i (unipotent x * g) * B (unipotent x * g) = F i g * B g)
  (hFfin : ∀ C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)), IsCompact C → {i : ℤ | ∃ g ∈ C, F i g ≠ 0}.Finite)
  (L : ℕ)
  (hcutL : ∀ (i : ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ × ℤ,
    (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
      F i (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
        diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n.1 * k) = 0)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) [μ₂.IsHaarMeasure]
  (μN₂ : Measure ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range) [μN₂.IsHaarMeasure]
  (SQ : Finset (ℤ × ℤ)) (q : ℤ × ℤ → ℂ)

def shiftBound : ℕ := ∑ ab ∈ SQ, (ab.1).natAbs

theorem natAbs_le_shiftBound {ab : ℤ × ℤ} (h : ab ∈ SQ) : (ab.1).natAbs ≤ shiftBound SQ :=
  Finset.single_le_sum (f := fun ab : ℤ × ℤ => (ab.1).natAbs) (fun _ _ => Nat.zero_le _) h

def eYQ (Y : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑ ab ∈ SQ, q ab * Y ab.2 * eY p ϖ hπ F B hFfin L μ₂ μN₂ Y (m - ab.1)

include hcutL in
theorem eYQ_eq_zero_of_lt (Y : ℤ → ℂ) {m : ℤ} (hm : m < -(3 * L : ℤ) - (shiftBound SQ : ℤ)) :
    eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q Y m = 0 := by
  unfold eYQ
  refine Finset.sum_eq_zero fun ab hab => ?_
  have hb : (ab.1).natAbs ≤ shiftBound SQ := natAbs_le_shiftBound SQ hab
  have hlt : m - ab.1 < -(3 * L : ℤ) := by
    have h1 : -((ab.1).natAbs : ℤ) ≤ ab.1 := by
      have := Int.le_natAbs (a := -ab.1); simp only [Int.natAbs_neg] at this; omega
    omega
  rw [eY_eq_zero_of_lt p ϖ hπ F B hFfin L hcutL μ₂ μN₂ Y hlt, mul_zero]

include hϖ hF hB hFB hFfin hcutL in

theorem hasSum_eYQ (Y : ℤ → ℂ) (s : ℂ)
    (hint : Integrable (fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s)
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) :
    HasSum (fun m : ℤ => eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q Y m * ((qC p) ^ (-s)) ^ m)
      ((∫ g, fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) *
        ∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * s) * Y ab.2) := by
  have h := hasSum_eY p ϖ hπ hϖ F B hF hB hFB hFfin L hcutL μ₂ μN₂ Y s hint
  have hX : (qC p) ^ (-s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (qC_ne_zero p))
  set I : ℂ := ∫ g, fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂)) with hI
  have hab : ∀ ab ∈ SQ, HasSum (fun m : ℤ => q ab * Y ab.2 *
        eY p ϖ hπ F B hFfin L μ₂ μN₂ Y (m - ab.1) * ((qC p) ^ (-s)) ^ m)
      (I * (q ab * (qC p) ^ (-(ab.1 : ℂ) * s) * Y ab.2)) := by
    intro ab _
    have h1 := h.mul_left (q ab * Y ab.2 * ((qC p) ^ (-s)) ^ ab.1)
    have h2 := (Equiv.subRight ab.1).hasSum_iff.mpr h1
    have hval : q ab * Y ab.2 * ((qC p) ^ (-s)) ^ ab.1 * I = I * (q ab * (qC p) ^ (-(ab.1 : ℂ) * s) * Y ab.2) := by
      rw [cpow_neg_int_mul (Ideal.absNorm p.asIdeal) ab.1 s]
      show q ab * Y ab.2 * ((qC p) ^ (-s)) ^ ab.1 * I = I * (q ab * ((qC p) ^ (-s)) ^ ab.1 * Y ab.2)
      ring
    rw [← hval]
    convert h2 using 1 <;> try with_reducible_and_instances rfl
    funext m
    simp only [Function.comp, Equiv.subRight_apply]
    have hz : ((qC p) ^ (-s)) ^ m = ((qC p) ^ (-s)) ^ ab.1 * ((qC p) ^ (-s)) ^ (m - ab.1) := by
      rw [← zpow_add₀ hX]; congr 1; ring
    rw [hz]; ring
  have hsum := hasSum_sum hab
  rw [← Finset.mul_sum] at hsum
  convert hsum using 1
  funext m
  rw [eYQ, Finset.sum_mul]

include hϖ hF hB hFB hFfin hcutL in

theorem summable_norm_eYQ (Y : ℤ → ℂ) (t : ℝ)
    (hint : Integrable (fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B (t : ℂ))
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) :
    Summable fun m : ℤ => ‖eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q Y m‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t)) ^ m := by
  have h := summable_norm_eY p ϖ hπ hϖ F B hF hB hFB hFfin L hcutL μ₂ μN₂ Y t hint
  set r : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by exact_mod_cast (lt_trans zero_lt_one (one_lt_q p))) _
  have hab : ∀ ab ∈ SQ, Summable fun m : ℤ =>
      ‖q ab * Y ab.2‖ * r ^ ab.1 * (‖eY p ϖ hπ F B hFfin L μ₂ μN₂ Y (m - ab.1)‖ * r ^ (m - ab.1)) := by
    intro ab _
    exact ((Equiv.subRight ab.1).summable_iff.mpr h).mul_left _
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (zpow_nonneg hr0.le _)) (fun m => ?_)
    (summable_sum hab)
  rw [eYQ]
  calc ‖∑ ab ∈ SQ, q ab * Y ab.2 * eY p ϖ hπ F B hFfin L μ₂ μN₂ Y (m - ab.1)‖ * r ^ m
      ≤ (∑ ab ∈ SQ, ‖q ab * Y ab.2 * eY p ϖ hπ F B hFfin L μ₂ μN₂ Y (m - ab.1)‖) * r ^ m :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (zpow_nonneg hr0.le _)
    _ = ∑ ab ∈ SQ, ‖q ab * Y ab.2‖ * r ^ ab.1 * (‖eY p ϖ hπ F B hFfin L μ₂ μN₂ Y (m - ab.1)‖ * r ^ (m - ab.1)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [norm_mul]
        have hz : r ^ m = r ^ ab.1 * r ^ (m - ab.1) := by rw [← zpow_add₀ hr0.ne']; congr 1; ring
        rw [hz]; ring

theorem cI_eq_zero_of_not_mem_Jm {m i : ℤ} (hi : i ∉ Jm p ϖ hπ F hFfin L m) :
    cI p ϖ hπ F B L μ₂ μN₂ m i = 0 := by
  rw [cI]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun n hn => ?_)
  have hi' : i ∉ Ifin p F hFfin (isCompact_shell p (rep p ϖ hπ (m - 2 * n, n))) := by
    intro h
    exact hi (Finset.mem_biUnion.mpr ⟨n, hn, h⟩)
  rw [βI_eq_zero_of_not_mem p F B hFfin μ₂ _ hi', mul_zero]

def JU (m : ℤ) : Finset ℤ := SQ.biUnion fun ab => Jm p ϖ hπ F hFfin L (m - ab.1)

def TQ (m : ℤ) : Finset ((ℤ × ℤ) × ℤ) := SQ ×ˢ JU p ϖ hπ F hFfin L SQ m

theorem eYQ_zpow_eq (y : ℂ) (hy : y ≠ 0) (m : ℤ) :
    eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => y ^ i) m =
      ∑ x ∈ TQ p ϖ hπ F hFfin L SQ m, (q x.1 * cI p ϖ hπ F B L μ₂ μN₂ (m - x.1.1) x.2) * y ^ (x.1.2 + x.2) := by
  have hexp : ∀ ab ∈ SQ,
      q ab * (fun i : ℤ => y ^ i) ab.2 * eY p ϖ hπ F B hFfin L μ₂ μN₂ (fun i => y ^ i) (m - ab.1) =
        ∑ i ∈ JU p ϖ hπ F hFfin L SQ m, (q ab * cI p ϖ hπ F B L μ₂ μN₂ (m - ab.1) i) * y ^ (ab.2 + i) := by
    intro ab hab
    have hsub : Jm p ϖ hπ F hFfin L (m - ab.1) ⊆ JU p ϖ hπ F hFfin L SQ m := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨ab, hab, hi⟩
    have hJ : eY p ϖ hπ F B hFfin L μ₂ μN₂ (fun i => y ^ i) (m - ab.1) =
        ∑ i ∈ JU p ϖ hπ F hFfin L SQ m, y ^ i * cI p ϖ hπ F B L μ₂ μN₂ (m - ab.1) i := by
      unfold eY
      apply Finset.sum_subset hsub
      intro i _ hi
      rw [cI_eq_zero_of_not_mem_Jm p ϖ hπ F B hFfin L μ₂ μN₂ hi, mul_zero]
    rw [hJ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zpow_add₀ hy]
    ring
  unfold eYQ TQ
  rw [Finset.sum_product, Finset.sum_congr rfl hexp]

end Cleared

section Level

variable (ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p)
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) (HeightOneSpectrum.adicCompletion ℚ p) ϖ ≠ 0)
  (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) (HeightOneSpectrum.adicCompletion ℚ p) ϖ) =
    WithZero.exp (-1 : ℤ))
  (F : ℤ → GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (B : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (hF : ∀ i : ℤ, IsLocallyConstant (F i)) (hB : IsLocallyConstant B)
  (hFB : ∀ (i : ℤ) (x : HeightOneSpectrum.adicCompletion ℚ p) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    F i (unipotent x * g) * B (unipotent x * g) = F i g * B g)
  (hFfin : ∀ C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)), IsCompact C → {i : ℤ | ∃ g ∈ C, F i g ≠ 0}.Finite)
  (L : ℕ)
  (hcutL : ∀ (i : ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ × ℤ,
    (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
      F i (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
        diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n.1 * k) = 0)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) [μ₂.IsHaarMeasure]
  (μN₂ : Measure ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range) [μN₂.IsHaarMeasure]
  (SQ : Finset (ℤ × ℤ)) (q : ℤ × ℤ → ℂ)

theorem piCoeff_eq_zero_of_lt_neg (P : Polynomial ℂ) (m₀ : ℤ) {m : ℤ} (hm : m < -m₀) : piCoeff P m₀ m = 0 := by
  unfold piCoeff
  rw [if_neg (by omega)]

theorem summable_norm_piCoeff (P : Polynomial ℂ) (m₀ : ℤ) (r : ℝ) :
    Summable fun m : ℤ => ‖piCoeff P m₀ m‖ * r ^ m := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-m₀) ((P.natDegree : ℤ) - m₀)) fun m hm => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hm
  rcases hm with hm | hm
  · rw [piCoeff_eq_zero_of_lt_neg P m₀ hm, norm_zero, zero_mul]
  · rw [piCoeff_eq_zero_of_lt P m₀ hm, norm_zero, zero_mul]

include hϖ hF hB hFB hFfin hcutL in

theorem eYQ_eq_piCoeff (u : ℝ) (P : Polynomial ℂ) (mP : ℤ) (σ : ℝ)
    (hint : ∀ s : ℂ, σ < s.re →
      Integrable (fS p (fun g => ∑ᶠ i : ℤ, (qC p) ^ (-(i : ℂ) * (u : ℂ)) * F i g) B s)
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂)))
    (hLau : ∀ s : ℂ, σ < s.re →
      (∫ g, fS p (fun g => ∑ᶠ i : ℤ, (qC p) ^ (-(i : ℂ) * (u : ℂ)) * F i g) B s g
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) *
          (∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * s) * (qC p) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
        (qC p) ^ ((mP : ℂ) * s) * P.eval ((qC p) ^ (-s))) :
    ∀ m : ℤ, eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => (qC p) ^ (-(i : ℂ) * (u : ℂ))) m = piCoeff P mP m := by
  set Y : ℤ → ℂ := fun i => (qC p) ^ (-(i : ℂ) * (u : ℂ)) with hY
  have hq : 1 < Ideal.absNorm p.asIdeal := one_lt_q p
  have hq1 : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by positivity
  have hlogq : 0 < Real.log ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := Real.log_pos hq1
  set r₁ : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-(σ + 2)) with hr₁
  set r₂ : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-(σ + 1)) with hr₂
  have h0 : 0 < r₁ := Real.rpow_pos_of_pos hqpos _
  have h12 : r₁ < r₂ := Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)
  set E : ℤ → ℂ := fun m => eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q Y m - piCoeff P mP m with hE

  have hsE : ∀ t : ℝ, σ < t → Summable fun m : ℤ => ‖E m‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t)) ^ m := by
    intro t ht
    have h1 := summable_norm_eYQ p ϖ hπ hϖ F B hF hB hFB hFfin L hcutL μ₂ μN₂ SQ q Y t (hint (t : ℂ) (by simpa using ht))
    have h2 := summable_norm_piCoeff P mP (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t))
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (zpow_nonneg (by positivity) _))
      (fun m => ?_) (h1.add h2)
    have hr : 0 ≤ (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t)) ^ m := zpow_nonneg (by positivity) _
    calc ‖E m‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t)) ^ m
        ≤ (‖eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q Y m‖ + ‖piCoeff P mP m‖) * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-t)) ^ m :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) hr
      _ = _ := by ring

  have hz : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → ∑' m : ℤ, E m * z ^ m = 0 := by
    intro z hz1 hz2
    have hz0 : z ≠ 0 := norm_pos_iff.mp (h0.trans hz1)
    have hnz : 0 < ‖z‖ := h0.trans hz1
    set sC : ℂ := -Complex.log z / ((Real.log ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) with hsC
    have hlogC : Complex.log (qC p) = ((Real.log ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [qC, Complex.natCast_log]
    have hlog0 : (((Real.log ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hlogq.ne'
    have hXz : (qC p) ^ (-sC) = z := by
      rw [Complex.cpow_def_of_ne_zero (qC_ne_zero p), hlogC, hsC, neg_div, neg_neg, mul_div_cancel₀ _ hlog0,
        Complex.exp_log hz0]
    have hre : σ < sC.re := by
      rw [hsC, Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
      rw [lt_div_iff₀ hlogq]
      have h2 : Real.log ‖z‖ < Real.log r₂ := Real.log_lt_log hnz hz2
      rw [hr₂, Real.log_rpow hqpos] at h2
      nlinarith
    have h1s := hasSum_eYQ p ϖ hπ hϖ F B hF hB hFB hFfin L hcutL μ₂ μN₂ SQ q Y sC (hint sC hre)
    have h2s := hasSum_piCoeff (Ideal.absNorm p.asIdeal) hq P mP sC
    have hLau2 : (qC p) ^ ((mP : ℂ) * sC) * P.eval ((qC p) ^ (-sC)) =
        (∫ g, fS p (fun g => ∑ᶠ i : ℤ, Y i * F i g) B sC g
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) *
          ∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * sC) * Y ab.2 := (hLau sC hre).symm
    rw [hLau2] at h2s
    have h3 := h1s.sub h2s
    rw [sub_self, hXz] at h3
    have h4 : HasSum (fun m : ℤ => E m * z ^ m) 0 := by
      convert h3 using 1 <;> try with_reducible_and_instances rfl
      funext m
      simp only [hE, sub_mul]
    exact h4.tsum_eq
  have hEz := Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero E h0 h12
    (hsE (σ + 2) (by linarith)) (hsE (σ + 1) (by linarith)) hz
  intro m
  have := congrFun hEz m
  simp only [hE, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

end Level

end

end FlatClearedGL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell.FlatClearedGL2"

open FlatClearedGL2 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (F : ℤ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hF : ∀ i : ℤ, IsLocallyConstant (F i)) (hB : IsLocallyConstant B)
    (hFB : ∀ (i : ℤ) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      F i (unipotent x * g) * B (unipotent x * g) = F i g * B g)
    (hFfin : ∀ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C → {i : ℤ | ∃ g ∈ C, F i g ≠ 0}.Finite)
    (hcut : ∃ L : ℕ, ∀ (i : ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ × ℤ,
      (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
        F i (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n.1 * k) = 0)

    (G : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (Gc : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hG : ∀ (u : ℂ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      G u g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * F i g)
    (hGc : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), Gc g = ∑ᶠ i : ℤ, F i g)

    (SQ : Finset (ℤ × ℤ)) (q : ℤ × ℤ → ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],

      (∃ u₀ : ℝ, ∀ u : ℝ, u₀ < u →
        ∃ (P : Polynomial ℂ) (m : ℤ) (σ : ℝ),
          (∀ s : ℂ, σ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (G u g * B g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (G u) B *
                (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) →

      ∃ (M : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ),
        (∀ (u : ℂ) (s : ℂ),
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (G u g * B g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (G u) B *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * u)) =
            ∑ mi ∈ M, c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * u) *
              (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s)) ∧
        (∀ s : ℂ,
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (Gc g * B g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s Gc B *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s)) =
            ∑ mi ∈ M, c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s)) := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ μN₂ _ hlev
  classical
  obtain ⟨u₀, hu₀⟩ := hlev
  obtain ⟨L, hcutL⟩ := hcut
  have hq : 1 < Ideal.absNorm p.asIdeal := one_lt_q p
  have hqC : (qC p) = (Ideal.absNorm p.asIdeal : ℂ) := rfl

  have hGY : ∀ u : ℂ, G u = fun g => ∑ᶠ i : ℤ, (qC p) ^ (-(i : ℂ) * u) * F i g := fun u => funext (hG u)
  have hGc1 : Gc = fun g => ∑ᶠ i : ℤ, (fun _ : ℤ => (1 : ℂ)) i * F i g := by
    funext g
    rw [hGc g]
    exact finsum_congr fun i => (one_mul _).symm

  have hYpow : ∀ u : ℂ, (fun i : ℤ => (qC p) ^ (-(i : ℂ) * u)) = fun i : ℤ => ((qC p) ^ (-u)) ^ i := by
    intro u; funext i; exact cpow_neg_int_mul (Ideal.absNorm p.asIdeal) i u
  have hYne : ∀ u : ℂ, (qC p) ^ (-u) ≠ 0 := fun u => Complex.cpow_ne_zero_iff.mpr (Or.inl (qC_ne_zero p))

  have hlevel : ∀ v : {u : ℝ // u₀ < u}, ∃ K : ℤ, ∀ m : ℤ, K < m →
      eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => (qC p) ^ (-(i : ℂ) * ((v : ℝ) : ℂ))) m = 0 := by
    intro v
    obtain ⟨P, mP, σ, hI, hLau⟩ := hu₀ v.1 v.2
    refine ⟨(P.natDegree : ℤ) - mP, fun m hm => ?_⟩
    have hI' : ∀ s : ℂ, σ < s.re →
        Integrable (fS p (fun g => ∑ᶠ i : ℤ, (qC p) ^ (-(i : ℂ) * ((v : ℝ) : ℂ)) * F i g) B s)
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂)) := by
      intro s hs
      have := hI s hs
      rw [hGY] at this
      exact this
    have hLau' : ∀ s : ℂ, σ < s.re →
        (∫ g, fS p (fun g => ∑ᶠ i : ℤ, (qC p) ^ (-(i : ℂ) * ((v : ℝ) : ℂ)) * F i g) B s g
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) *
          (∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * s) * (qC p) ^ (-(ab.2 : ℂ) * ((v : ℝ) : ℂ))) =
          (qC p) ^ ((mP : ℂ) * s) * P.eval ((qC p) ^ (-s)) := by
      intro s hs
      have := hLau s hs
      rw [hGY] at this
      exact this
    rw [eYQ_eq_piCoeff p ϖ hπ hϖ F B hF hB hFB hFfin L hcutL μ₂ μN₂ SQ q v.1 P mP σ hI' hLau' m]
    exact piCoeff_eq_zero_of_lt P mP hm
  choose Kf hKf using hlevel

  have huncount : ∃ Kt : ℤ, {v : {u : ℝ // u₀ < u} | Kf v ≤ Kt}.Infinite := by
    by_contra hcon
    push Not at hcon
    have hcov : (Set.univ : Set {u : ℝ // u₀ < u}) ⊆ ⋃ Kt : ℤ, {v : {u : ℝ // u₀ < u} | Kf v ≤ Kt} := by
      intro v _
      exact Set.mem_iUnion.mpr ⟨Kf v, show Kf v ≤ Kf v from le_rfl⟩
    have hcount : (Set.univ : Set {u : ℝ // u₀ < u}).Countable :=
      (Set.countable_iUnion fun Kt => (hcon Kt).countable).mono hcov
    have hIoi : (Set.Ioi u₀).Countable := by
      have : Countable {u : ℝ // u₀ < u} := Set.countable_univ_iff.mp hcount
      exact Set.countable_coe_iff.mp this
    have h0 := hIoi.measure_zero (volume : Measure ℝ)
    rw [Real.volume_Ioi] at h0
    exact ENNReal.top_ne_zero h0
  obtain ⟨Kt, hKt⟩ := huncount
  set Sr : Set ℝ := Subtype.val '' {v : {u : ℝ // u₀ < u} | Kf v ≤ Kt} with hSr
  have hSrinf : Sr.Infinite := hKt.image Subtype.val_injective.injOn
  obtain ⟨hSinf, hSne⟩ := infinite_image_cpow_neg (Ideal.absNorm p.asIdeal) hq Sr hSrinf

  have hvan : ∀ m : ℤ, Kt < m → ∀ y : ℂ, y ≠ 0 →
      ∑ x ∈ TQ p ϖ hπ F hFfin L SQ m, (q x.1 * cI p ϖ hπ F B L μ₂ μN₂ (m - x.1.1) x.2) * y ^ (x.1.2 + x.2) = 0 := by
    intro m hm
    refine laurent_eq_zero_of_infinite (TQ p ϖ hπ F hFfin L SQ m)
      (fun x => q x.1 * cI p ϖ hπ F B L μ₂ μN₂ (m - x.1.1) x.2) (fun x => x.1.2 + x.2) _ hSinf hSne ?_
    rintro _ ⟨t, ⟨v, hv, rfl⟩, rfl⟩
    have hv' : Kf v ≤ Kt := hv
    have h := hKf v m (lt_of_le_of_lt hv' hm)
    rw [hYpow, eYQ_zpow_eq p ϖ hπ F B hFfin L μ₂ μN₂ SQ q _ (hYne _) m] at h
    exact h
  have hvanY : ∀ (u : ℂ) (m : ℤ), Kt < m →
      eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => (qC p) ^ (-(i : ℂ) * u)) m = 0 := by
    intro u m hm
    rw [hYpow, eYQ_zpow_eq p ϖ hπ F B hFfin L μ₂ μN₂ SQ q _ (hYne u) m]
    exact hvan m hm _ (hYne u)
  have hvan1 : ∀ m : ℤ, Kt < m → eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun _ => (1 : ℂ)) m = 0 := by
    intro m hm
    have h1 : (fun _ : ℤ => (1 : ℂ)) = fun i : ℤ => (1 : ℂ) ^ i := by funext i; exact (one_zpow i).symm
    rw [h1, eYQ_zpow_eq p ϖ hπ F B hFfin L μ₂ μN₂ SQ q _ one_ne_zero m]
    exact hvan m hm 1 one_ne_zero

  set Icut : Finset ℤ := Finset.Icc (-(3 * L : ℤ) - (shiftBound SQ : ℤ)) Kt with hIcut
  set Jall : Finset ℤ := Icut.biUnion fun m => (TQ p ϖ hπ F hFfin L SQ m).image fun x => x.1.2 + x.2 with hJall
  set c : ℤ × ℤ → ℂ := fun mj => ∑ x ∈ (TQ p ϖ hπ F hFfin L SQ mj.1).filter (fun x => x.1.2 + x.2 = mj.2),
      q x.1 * cI p ϖ hπ F B L μ₂ μN₂ (mj.1 - x.1.1) x.2 with hc

  have hregroup : ∀ (y X : ℂ) (hy : y ≠ 0),
      ∑ mj ∈ Icut ×ˢ Jall, c mj * y ^ mj.2 * X ^ mj.1 =
        ∑ m ∈ Icut, eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => y ^ i) m * X ^ m := by
    intro y X hy
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eYQ_zpow_eq p ϖ hπ F B hFfin L μ₂ μN₂ SQ q y hy m, Finset.sum_mul]
    have hmaps : ∀ x ∈ TQ p ϖ hπ F hFfin L SQ m, x.1.2 + x.2 ∈ Jall := by
      intro x hx
      rw [hJall, Finset.mem_biUnion]
      exact ⟨m, hm, Finset.mem_image_of_mem _ hx⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
  refine ⟨Icut ×ˢ Jall, c, ?_, ?_⟩
  ·
    intro u s hint
    rw [hGY] at hint ⊢
    have hHS := hasSum_eYQ p ϖ hπ hϖ F B hF hB hFB hFfin L hcutL μ₂ μN₂ SQ q (fun i => (qC p) ^ (-(i : ℂ) * u)) s hint
    have hzero : ∀ m ∉ Icut, eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => (qC p) ^ (-(i : ℂ) * u)) m * ((qC p) ^ (-s)) ^ m = 0 := by
      intro m hm
      simp only [hIcut, Finset.mem_Icc, not_and_or, not_le] at hm
      rcases hm with hm | hm
      · rw [eYQ_eq_zero_of_lt p ϖ hπ F B hFfin L hcutL μ₂ μN₂ SQ q _ hm, zero_mul]
      · rw [hvanY u m hm, zero_mul]
    have hfin : HasSum (fun m : ℤ => eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => (qC p) ^ (-(i : ℂ) * u)) m * ((qC p) ^ (-s)) ^ m)
        (∑ m ∈ Icut, eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun i => (qC p) ^ (-(i : ℂ) * u)) m * ((qC p) ^ (-s)) ^ m) :=
      hasSum_sum_of_ne_finset_zero hzero
    show (∫ g, fS p (fun g => ∑ᶠ i : ℤ, (qC p) ^ (-(i : ℂ) * u) * F i g) B s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) *
        (∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * s) * (qC p) ^ (-(ab.2 : ℂ) * u)) = _
    rw [hHS.unique hfin, hYpow u, ← hregroup _ _ (hYne u)]
    refine Finset.sum_congr rfl fun mj _ => ?_
    rw [← cpow_neg_int_mul (Ideal.absNorm p.asIdeal) mj.2 u, ← cpow_neg_int_mul (Ideal.absNorm p.asIdeal) mj.1 s]
  ·
    intro s hint
    rw [hGc1] at hint ⊢
    have hHS := hasSum_eYQ p ϖ hπ hϖ F B hF hB hFB hFfin L hcutL μ₂ μN₂ SQ q (fun _ => (1 : ℂ)) s hint
    have hzero : ∀ m ∉ Icut, eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun _ => (1 : ℂ)) m * ((qC p) ^ (-s)) ^ m = 0 := by
      intro m hm
      simp only [hIcut, Finset.mem_Icc, not_and_or, not_le] at hm
      rcases hm with hm | hm
      · rw [eYQ_eq_zero_of_lt p ϖ hπ F B hFfin L hcutL μ₂ μN₂ SQ q _ hm, zero_mul]
      · rw [hvan1 m hm, zero_mul]
    have hfin : HasSum (fun m : ℤ => eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun _ => (1 : ℂ)) m * ((qC p) ^ (-s)) ^ m)
        (∑ m ∈ Icut, eYQ p ϖ hπ F B hFfin L μ₂ μN₂ SQ q (fun _ => (1 : ℂ)) m * ((qC p) ^ (-s)) ^ m) :=
      hasSum_sum_of_ne_finset_zero hzero
    have h1 : (fun _ : ℤ => (1 : ℂ)) = fun i : ℤ => (1 : ℂ) ^ i := by funext i; exact (one_zpow i).symm
    show (∫ g, fS p (fun g => ∑ᶠ i : ℤ, (fun _ : ℤ => (1 : ℂ)) i * F i g) B s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range μN₂))) *
        (∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * s)) = _
    have hQ1 : (∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * s)) =
        ∑ ab ∈ SQ, q ab * (qC p) ^ (-(ab.1 : ℂ) * s) * (fun _ : ℤ => (1 : ℂ)) ab.2 := by
      refine Finset.sum_congr rfl fun ab _ => ?_
      simp
    rw [hQ1, hHS.unique hfin, h1, ← hregroup 1 _ one_ne_zero]
    refine Finset.sum_congr rfl fun mj _ => ?_
    rw [one_zpow, mul_one, ← cpow_neg_int_mul (Ideal.absNorm p.asIdeal) mj.1 s]

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell (solution)
