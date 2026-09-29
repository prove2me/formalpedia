-- Prove2me | solution 1 for NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a2d562c6-eddb-5699-9391-76a303af71a7

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TransversalMeasure
open scoped TensorProduct
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open scoped ENNReal
open AutomorphicForm AutomorphicForm.TransversalMeasure

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] TransversalMeasure.semiLocalUnitsBorel TransversalMeasure.archUnitsBorel
attribute [local instance] semiLocalUnitsBorel archUnitsBorel

namespace TransversalMeasure

@[reducible] private noncomputable def unitsBorelK (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K)ˣ :=
  borel _

@[reducible] private noncomputable def archUnitsBorelK (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) :
    MeasurableSpace (v.Completion)ˣ :=
  borel _

end TransversalMeasure

attribute [local instance] TransversalMeasure.unitsBorelK TransversalMeasure.archUnitsBorelK

namespace TransversalMeasure

private theorem coe_valOneUnitsSubgroup (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (valOneUnitsSubgroup K v : Set (v.adicCompletion K)ˣ) = valOneUnits K v := by
  ext s
  simp only [valOneUnitsSubgroup, valOneUnits, SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp,
    Function.comp_apply, Units.coeHom_apply, Set.mem_setOf_eq]
  exact Iff.rfl

open scoped TensorProduct.RightActions in

private theorem continuousMul_semiLocal (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : ContinuousMul (L ⊗[K] v.adicCompletion K) :=
  Topology.IsInducing.continuousMul (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v)
    (AutomorphicForm.semiLocalHomeomorph K L v).isInducing

open scoped TensorProduct.RightActions in

private theorem t2Space_semiLocal (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : T2Space (L ⊗[K] v.adicCompletion K) :=
  (AutomorphicForm.semiLocalHomeomorph K L v).isEmbedding.t2Space

open scoped TensorProduct.RightActions in

private theorem isCompact_semiLocalIntegers (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (AutomorphicForm.semiLocalIntegers K L v) := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage]
  exact (AutomorphicForm.semiLocalHomeomorph K L v).isCompact_preimage.2 (AutomorphicForm.isCompact_piIntegers K L v)

open scoped TensorProduct.RightActions in

private theorem isOpen_semiLocalIntegers (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (AutomorphicForm.semiLocalIntegers K L v) := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage]
  exact (AutomorphicForm.isOpen_piIntegers K L v).preimage (AutomorphicForm.semiLocalHomeomorph K L v).continuous

open WithZeroTopology in

private theorem continuous_valued (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (Valued.v : v.adicCompletion K → WithZero (Multiplicative ℤ)) :=
  Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)

open WithZeroTopology in

private theorem isOpen_valued_eq_one (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : IsOpen
    {x : v.adicCompletion K | Valued.v x = 1} := by
  have h1 : IsOpen ({1} : Set (WithZero (Multiplicative ℤ))) := by
    refine isOpen_iff_mem_nhds.2 fun γ hγ => ?_
    rw [Set.mem_singleton_iff.1 hγ]
    exact WithZeroTopology.singleton_mem_nhds_of_ne_zero one_ne_zero
  exact h1.preimage (continuous_valued K v)

open WithZeroTopology in

private theorem isClosed_valued_eq_one (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : IsClosed
    {x : v.adicCompletion K | Valued.v x = 1} := by
  have h1 : IsClosed ({1} : Set (WithZero (Multiplicative ℤ))) := by
    rw [← isOpen_compl_iff, WithZeroTopology.isOpen_iff]
    exact Or.inr ⟨1, one_ne_zero, fun x hx => ne_of_lt hx⟩
  exact h1.preimage (continuous_valued K v)

open scoped TensorProduct.RightActions in

private theorem continuous_norm_semiLocal (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) := by
  classical
  let b := Module.Free.chooseBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  have h : (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) =
      fun t => (Algebra.leftMulMatrix b t).det := by
    funext t
    exact Algebra.norm_eq_matrix_det b t
  rw [h]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det

open scoped TensorProduct.RightActions in

private theorem coe_normOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) =
      (fun t : (L ⊗[K] v.adicCompletion K)ˣ => Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) ⁻¹'
        {x : v.adicCompletion K | Valued.v x = 1} := by
  ext t
  simp only [normOneUnits, SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    Units.coeHom_apply, Set.mem_preimage, Set.mem_setOf_eq]
  exact Iff.rfl

open scoped TensorProduct.RightActions in

private theorem continuous_norm_val (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous
      (fun t : (L ⊗[K] v.adicCompletion K)ˣ => Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) :=
  (continuous_norm_semiLocal K L v).comp Units.continuous_val

open scoped TensorProduct.RightActions in

private noncomputable def normLog (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ) : ℤ :=
  WithZero.log (Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)))

open scoped TensorProduct.RightActions in

private theorem valued_norm_ne_zero (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ) :
    Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (t.isUnit.map (Algebra.norm (v.adicCompletion K))).ne_zero

open scoped TensorProduct.RightActions in

private theorem normLog_mul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t t' : (L ⊗[K] v.adicCompletion K)ˣ) :
    normLog K L v (t * t') = normLog K L v t + normLog K L v t' := by
  unfold normLog
  rw [Units.val_mul, map_mul, map_mul, WithZero.log_mul (valued_norm_ne_zero K L v t) (valued_norm_ne_zero K L v t')]

open scoped TensorProduct.RightActions in

private theorem mem_normOneUnits_iff_normLog (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ) :
    t ∈ normOneUnits K L v ↔ normLog K L v t = 0 := by
  have h : t ∈ normOneUnits K L v ↔ Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) = 1 :=
    Iff.rfl
  rw [h, normLog]
  constructor
  · intro h1
    rw [h1, WithZero.log_one]
  · intro h0
    rw [← WithZero.exp_log (valued_norm_ne_zero K L v t), h0, WithZero.exp_zero]

open scoped TensorProduct.RightActions in

private theorem normLog_includeUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (s : (v.adicCompletion K)ˣ) :
    normLog K L v (includeUnits K L v s) =
      (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) : ℤ) * WithZero.log
        (Valued.v (s : v.adicCompletion K)) := by
  have hval : ((includeUnits K L v s : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = algebraMap
    (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (s : v.adicCompletion K) := rfl
  unfold normLog
  rw [hval, Algebra.norm_algebraMap, map_pow, WithZero.log_pow, nsmul_eq_mul]

open scoped TensorProduct.RightActions in

private theorem normLog_zpow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ) (m : ℤ) :
    normLog K L v (t ^ m) = m * normLog K L v t := by
  have hone : normLog K L v 1 = 0 := by
    have h := normLog_mul K L v 1 1
    rw [one_mul] at h
    linarith
  have hinv : normLog K L v t⁻¹ = -normLog K L v t := by
    have h := normLog_mul K L v t⁻¹ t
    rw [inv_mul_cancel, hone] at h
    linarith
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, hone, zero_mul]
  | succ i hi => rw [zpow_add_one, normLog_mul, hi]; ring
  | pred i hi => rw [zpow_sub_one, normLog_mul, hi, hinv]; ring

private theorem nonempty_extension (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsum := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact Module.finrank_pos.ne' hsum.symm

private theorem isClosed_valOneUnits (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : IsClosed
    (valOneUnits K v) :=
  (isClosed_valued_eq_one K v).preimage Units.continuous_val

private theorem includeUnits_mem_integralUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) {s : (v.adicCompletion K)ˣ} (hs : s ∈ valOneUnits K v) :
    includeUnits K L v s ∈ integralUnits K L v := by
  have hmem : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) = 1 →
      ((1 : L) ⊗ₜ[K] (x : v.adicCompletion K)) ∈
        (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubmonoid := by
    intro x hx
    have hxi : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hx.le
    change _ ∈ (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range
    rw [AlgHom.mem_range]
    refine ⟨(1 : 𝓞 L) ⊗ₜ[𝓞 K] (⟨(x : v.adicCompletion K), hxi⟩ : v.adicCompletionIntegers K), ?_⟩
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, map_one]
  have hs1 : Valued.v (s : v.adicCompletion K) = 1 := hs
  have hs2 : Valued.v ((s⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hs1, inv_one]
  have hval : ∀ x : (v.adicCompletion K)ˣ,
    ((includeUnits K L v x : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = (1 : L) ⊗ₜ[K]
    (x : v.adicCompletion K) := by
    intro x
    simp [includeUnits]
  rw [integralUnits, Submonoid.mem_units_iff, ← map_inv, hval, hval]
  exact ⟨hmem s hs1, hmem s⁻¹ hs2⟩

private theorem ramificationIdx_ne_zero_extension (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    (w.1.under (𝓞 K)).asIdeal.ramificationIdx' w.1.asIdeal ≠ 0 := by
  haveI : w.1.asIdeal.IsPrime := w.1.isPrime
  haveI : w.1.asIdeal.LiesOver (w.1.under (𝓞 K)).asIdeal := ⟨rfl⟩
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.1.asIdeal (w.1.under (𝓞 K)).ne_bot

private theorem mem_valOneUnits_of_includeUnits_mem (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) {s : (v.adicCompletion K)ˣ}
    (hs : includeUnits K L v s ∈ integralUnits K L v) : s ∈ valOneUnits K v := by
  obtain ⟨w⟩ := nonempty_extension K L v
  have hval : ∀ x : (v.adicCompletion K)ˣ,
    ((includeUnits K L v x : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = (1 : L) ⊗ₜ[K]
    (x : v.adicCompletion K) := by
    intro x
    simp [includeUnits]
  rw [integralUnits, Submonoid.mem_units_iff, ← map_inv, hval, hval] at hs

  have hcomp : ∀ x : v.adicCompletion K, ((1 : L) ⊗ₜ[K] x) ∈
        (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubmonoid →
      Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x) ≤ 1 := by
    intro x hx
    have h1 : ((1 : L) ⊗ₜ[K] x) ∈ AutomorphicForm.semiLocalIntegers K L v := by
      change _ ∈ (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range at hx
      exact hx
    rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers,
      Set.mem_univ_pi] at h1
    have h2 := h1 w
    have h3 : AutomorphicForm.semiLocalHomeomorph K L v ((1 : L) ⊗ₜ[K] x) w =
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x := by
      change algebraMap L (w.1.adicCompletion L) (1 : L) * algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x = _
      rw [map_one, one_mul]
    rw [h3] at h2
    exact h2
  have hx1 := hcomp _ hs.1
  have hx2 := hcomp _ hs.2
  rw [Units.val_inv_eq_inv_val, map_inv₀, map_inv₀] at hx2
  have hne : Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (s : v.adicCompletion K)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 s.ne_zero)
  have hw : Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (s : v.adicCompletion K)) = 1 :=
    le_antisymm hx1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 hx2)

  have hs0 : Valued.v (s : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  have hw' : Valued.v (HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w (s : v.adicCompletion K)) = 1 := hw
  have he := HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w (s : v.adicCompletion K)
  rw [hw'] at he
  have hlog := congrArg WithZero.log he
  rw [WithZero.log_one, WithZero.log_pow] at hlog
  have he0 : ((w.1.under (𝓞 K)).asIdeal.ramificationIdx' w.1.asIdeal : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.2 (ramificationIdx_ne_zero_extension K L v w)
  have hlog0 : WithZero.log (Valued.v (s : v.adicCompletion K)) = 0 := by
    rcases mul_eq_zero.1 hlog.symm with h | h
    · exact absurd h he0
    · exact h
  show Valued.v (s : v.adicCompletion K) = 1
  rw [← WithZero.exp_log hs0, hlog0, WithZero.exp_zero]

private def piece {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] (B : Subgroup H) (ϖ : H) (m : ℤ) : Set H :=
  (fun s => (ϖ ^ m)⁻¹ * s) ⁻¹' (B : Set H)

private theorem mem_piece {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] (B : Subgroup H) (ϖ : H) (m : ℤ) (s : H) :
    s ∈ piece B ϖ m ↔ (ϖ ^ m)⁻¹ * s ∈ B := Iff.rfl

private theorem measurableSet_piece {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (B : Subgroup H) (hB : MeasurableSet (B : Set H)) (ϖ : H)
    (m : ℤ) : MeasurableSet (piece B ϖ m) :=
  hB.preimage (measurable_const_mul _)

private theorem pairwise_disjoint_piece {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (B : Subgroup H) (ϖ : H)
    (hϖ : ∀ s : H, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ B) : Pairwise (Function.onFun Disjoint (piece B ϖ)) := by
  intro m n hmn
  refine Set.disjoint_left.2 fun s hm hn => hmn ?_
  exact (hϖ s).unique hm hn

private theorem iUnion_piece {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] (B : Subgroup H) (ϖ : H)
    (hϖ : ∀ s : H, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ B) : ⋃ m, piece B ϖ m = Set.univ := by
  refine Set.eq_univ_of_forall fun s => ?_
  obtain ⟨m, hm, -⟩ := hϖ s
  exact Set.mem_iUnion.2 ⟨m, hm⟩

private theorem lintegral_eq_tsum_of_graded {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulLeftInvariant] (B : Subgroup H)
    (hBm : MeasurableSet (B : Set H)) (hB1 : μH (B : Set H) = 1) (ϖ : H)
    (hϖ : ∀ s : H, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ B) (F : H → ℝ≥0∞)
    (hF : ∀ (m : ℤ) (b : H), b ∈ B → F (ϖ ^ m * b) = F (ϖ ^ m)) :
    ∫⁻ s, F s ∂μH = ∑' m : ℤ, F (ϖ ^ m) := by
  have hcover : ∫⁻ s, F s ∂μH = ∫⁻ s in ⋃ m, piece B ϖ m, F s ∂μH := by
    rw [iUnion_piece B ϖ hϖ, Measure.restrict_univ]
  rw [hcover, lintegral_iUnion (measurableSet_piece B hBm ϖ) (pairwise_disjoint_piece B ϖ hϖ)]
  refine tsum_congr fun m => ?_
  have hconst : ∫⁻ s in piece B ϖ m, F s ∂μH = ∫⁻ _ in piece B ϖ m, F (ϖ ^ m) ∂μH := by
    refine setLIntegral_congr_fun (measurableSet_piece B hBm ϖ m) fun s hs => ?_
    have hs' : (ϖ ^ m)⁻¹ * s ∈ B := hs
    have : F s = F (ϖ ^ m * ((ϖ ^ m)⁻¹ * s)) := by rw [mul_inv_cancel_left]
    rw [this, hF m _ hs']
  have hmass : μH (piece B ϖ m) = 1 := by
    unfold piece
    rw [measure_preimage_mul, hB1]
  rw [hconst, setLIntegral_const, hmass, mul_one]

private theorem tsum_measure_inter_eq {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {ι : Type} [Countable ι] (S : ι → Set G)
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (Function.onFun Disjoint S)) (E : Set G) (hE : MeasurableSet E) :
    ∑' i, μ (E ∩ S i) = μ (E ∩ ⋃ i, S i) := by
  rw [Set.inter_iUnion, measure_iUnion]
  · exact hd.mono fun i j h => h.mono Set.inter_subset_right Set.inter_subset_right
  · exact fun i => hE.inter (hS i)

private def coset {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (U : Set G) (x : G) : Set G := (fun t => t * x⁻¹) ⁻¹' U

private theorem measurableSet_coset {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {U : Set G} (hU : MeasurableSet U) (x : G) :
    MeasurableSet (coset U x) :=
  hU.preimage (measurable_mul_const _)

private theorem measure_preimage_mul_right_inter {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (U : Set G)
    (E : Set G) (x : G) : μ ((fun t => t * x) ⁻¹' E ∩ U) = μ (E ∩ coset U x) := by
  have h : (fun t => t * x) ⁻¹' E ∩ U = (fun t => t * x) ⁻¹' (E ∩ coset U x) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, coset, mul_inv_cancel_right]
  rw [h, measure_preimage_mul_right]

private theorem lintegral_normalised_restrict {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsMulLeftInvariant]
    (μH : Measure H) [μH.IsMulLeftInvariant] (ι : H →* G) (U : Subgroup G) (hU : MeasurableSet (U : Set G))
    (B : Subgroup H) (hBm : MeasurableSet (B : Set H)) (hB1 : μH (B : Set H) = 1) (hBU : ∀ b ∈ B, ι b ∈ U)
    (hUB : ∀ s : H, ι s ∈ U → s ∈ B) (ϖ : H) (hϖ : ∀ s : H, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ B) {E : Set G}
    (hE : MeasurableSet E) :
    ∫⁻ s, ((μ (U : Set G))⁻¹ • μ.restrict (U : Set G)) ((fun t => t * ι s) ⁻¹' E) ∂μH =
      (μ (U : Set G))⁻¹ * μ (E ∩ ((U : Set G) * Set.range ι)) := by

  have hval : ∀ s : H, ((μ (U : Set G))⁻¹ • μ.restrict (U : Set G)) ((fun t => t * ι s) ⁻¹' E) =
      (μ (U : Set G))⁻¹ * μ (E ∩ coset (U : Set G) (ι s)) := by
    intro s
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hU, measure_preimage_mul_right_inter]
  simp_rw [hval]

  have hcoset : ∀ (m : ℤ) (b : H), b ∈ B → coset (U : Set G) (ι (ϖ ^ m * b)) = coset (U : Set G) (ι (ϖ ^ m)) := by
    intro m b hb
    ext t
    simp only [coset, Set.mem_preimage, map_mul, mul_inv_rev, SetLike.mem_coe]
    constructor
    · intro h
      rw [mul_comm (ι b)⁻¹, ← mul_assoc] at h
      have := U.mul_mem h (hBU b hb)
      rwa [inv_mul_cancel_right] at this
    · intro h
      have := U.mul_mem h (U.inv_mem (hBU b hb))
      rw [mul_comm (ι b)⁻¹, ← mul_assoc]
      exact this
  rw [lintegral_eq_tsum_of_graded μH B hBm hB1 ϖ hϖ _ (fun m b hb => by rw [hcoset m b hb]),
    ENNReal.tsum_mul_left]
  congr 1

  have hunion : (⋃ m : ℤ, coset (U : Set G) (ι (ϖ ^ m))) = (U : Set G) * Set.range ι := by
    ext t
    simp only [Set.mem_iUnion, coset, Set.mem_preimage, SetLike.mem_coe, Set.mem_mul, Set.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨t * (ι (ϖ ^ m))⁻¹, hm, ι (ϖ ^ m), ⟨ϖ ^ m, rfl⟩, by simp⟩
    · rintro ⟨u, hu, _, ⟨s, rfl⟩, rfl⟩
      obtain ⟨m, hm, -⟩ := hϖ s
      refine ⟨m, ?_⟩
      have hb : ι ((ϖ ^ m)⁻¹ * s) ∈ U := hBU _ hm
      rw [map_mul, map_inv] at hb
      convert U.mul_mem hu hb using 1
      rw [mul_comm (ι (ϖ ^ m))⁻¹, ← mul_assoc]
  rw [tsum_measure_inter_eq μ _ (fun m => measurableSet_coset hU (ι (ϖ ^ m))) ?_ E hE, hunion]
  intro m n hmn
  refine Set.disjoint_left.2 fun t hm hn => hmn ?_
  simp only [coset, Set.mem_preimage, SetLike.mem_coe] at hm hn
  have h1 : ι ((ϖ ^ n)⁻¹ * ϖ ^ m) ∈ U := by
    have := U.mul_mem (U.inv_mem hm) hn
    simpa [map_mul, map_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using this
  have h2 : (ϖ ^ n)⁻¹ * ϖ ^ m ∈ B := hUB _ h1
  have hmm : (ϖ ^ m)⁻¹ * ϖ ^ m ∈ B := by
    rw [inv_mul_cancel]
    exact B.one_mem
  exact (hϖ (ϖ ^ m)).unique hmm h2

private theorem map_val_preimage_mul_right {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) [MeasurableSpace N] [BorelSpace N]
    (μN : Measure N) [μN.IsMulLeftInvariant] {g : G} (hg : g ∈ N) {Y : Set G} (hY : MeasurableSet Y) :
    Measure.map (Subtype.val : N → G) μN ((fun t => t * g) ⁻¹' Y) = Measure.map (Subtype.val : N → G) μN Y := by
  have hval : Measurable (Subtype.val : N → G) := continuous_subtype_val.measurable
  rw [Measure.map_apply hval (hY.preimage (measurable_mul_const _)), Measure.map_apply hval hY]
  have h : (Subtype.val : N → G) ⁻¹' ((fun t => t * g) ⁻¹' Y) =
      (fun n : N => n * ⟨g, hg⟩) ⁻¹' ((Subtype.val : N → G) ⁻¹' Y) := by
    ext n
    simp only [Set.mem_preimage, Subgroup.coe_mul]
  rw [h, measure_preimage_mul_right]

private theorem mul_map_val_apply {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G)
    [μ.IsHaarMeasure] (N : Subgroup G) (hN : IsOpen (N : Set G)) [MeasurableSpace N] [BorelSpace N] (μN : Measure N)
    [μN.IsHaarMeasure] (U : Set G) (hU : MeasurableSet U) (hUN : U ⊆ N) {E : Set G} (hE : MeasurableSet E) :
    μ U * Measure.map (Subtype.val : N → G) μN E = μN ((Subtype.val : N → G) ⁻¹' U) * μ (E ∩ N) := by
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := (inferInstance : SecondCountableTopology (N : Set G))
  have hval : Measurable (Subtype.val : N → G) := continuous_subtype_val.measurable
  have hemb : Topology.IsOpenEmbedding (N.subtype) := hN.isOpenEmbedding_subtypeVal
  have hme : MeasurableEmbedding (Subtype.val : N → G) := hemb.measurableEmbedding
  haveI : (μ.comap N.subtype).IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μ hemb
  have hmap : Measure.map (Subtype.val : N → G) μN =
      Measure.haarScalarFactor μN (μ.comap N.subtype) • μ.restrict (N : Set G) := by
    refine (congrArg (Measure.map (Subtype.val : N → G))
      (Measure.isMulLeftInvariant_eq_smul μN (μ.comap N.subtype))).trans ?_
    rw [Measure.map_smul]
    congr 1
    rw [show (μ.comap N.subtype) = μ.comap (Subtype.val : N → G) from rfl, hme.map_comap, Subtype.range_coe]
  have h1 : Measure.map (Subtype.val : N → G) μN E =
      (Measure.haarScalarFactor μN (μ.comap N.subtype) : ℝ≥0∞) * μ (E ∩ N) := by
    rw [hmap, Measure.smul_apply, Measure.restrict_apply hE, ENNReal.smul_def, smul_eq_mul]
  have h2 : μN ((Subtype.val : N → G) ⁻¹' U) = (Measure.haarScalarFactor μN (μ.comap N.subtype) : ℝ≥0∞) * μ U := by
    have h := Measure.map_apply (μ := μN) hval hU
    rw [← h, hmap, Measure.smul_apply, Measure.restrict_apply hU, Set.inter_eq_left.2 hUN, ENNReal.smul_def,
      smul_eq_mul]
  rw [h1, h2]
  ring

private theorem mem_coset_iff {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (N : Subgroup G) (x t : G) : t ∈ coset (N : Set G) x ↔ x⁻¹ * t ∈ N := by
  simp only [coset, Set.mem_preimage, SetLike.mem_coe, mul_comm t]

private theorem mul_sum_lintegral_map_eq {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (hN : IsOpen (N : Set G))
    [MeasurableSpace N] [BorelSpace N] (μN : Measure N) [μN.IsHaarMeasure] (μH : Measure H) [μH.IsMulLeftInvariant]
    (ι : H →* G) (U : Subgroup G) (hU : MeasurableSet (U : Set G)) (hUN : U ≤ N) (B : Subgroup H)
    (hBm : MeasurableSet (B : Set H)) (hB1 : μH (B : Set H) = 1) (hBU : ∀ b ∈ B, ι b ∈ U) (ϖ : H)
    (hϖ : ∀ s : H, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ B) {r : ℕ} (π : Fin r → G)
    (hπ : ∀ t : G, ∃! p : Fin r × ℤ, (ι ϖ ^ p.2 * π p.1)⁻¹ * t ∈ N) {E : Set G} (hE : MeasurableSet E) :
    μ (U : Set G) * ∑ j, ∫⁻ s, Measure.map (fun t => π j * t) (Measure.map (Subtype.val : N → G) μN)
        ((fun t => t * ι s) ⁻¹' E) ∂μH =
      μN ((Subtype.val : N → G) ⁻¹' (U : Set G)) * μ E := by

  have hF : ∀ (j : Fin r) (s : H), Measure.map (fun t => π j * t) (Measure.map (Subtype.val : N → G) μN)
      ((fun t => t * ι s) ⁻¹' E) = Measure.map (Subtype.val : N → G) μN ((fun t => t * (π j * ι s)) ⁻¹' E) := by
    intro j s
    rw [Measure.map_apply (measurable_const_mul _) (hE.preimage (measurable_mul_const _))]
    congr 1
    ext t
    simp only [Set.mem_preimage, mul_comm (π j), mul_assoc]
  simp_rw [hF]

  have hj : ∀ j : Fin r, ∫⁻ s, Measure.map (Subtype.val : N → G) μN ((fun t => t * (π j * ι s)) ⁻¹' E) ∂μH =
      ∑' m : ℤ, Measure.map (Subtype.val : N → G) μN ((fun t => t * (π j * ι (ϖ ^ m))) ⁻¹' E) := by
    intro j
    refine lintegral_eq_tsum_of_graded μH B hBm hB1 ϖ hϖ _ fun m b hb => ?_
    have hset : (fun t => t * (π j * ι (ϖ ^ m * b))) ⁻¹' E =
        (fun t => t * ι b) ⁻¹' ((fun t => t * (π j * ι (ϖ ^ m))) ⁻¹' E) := by
      ext t
      simp only [Set.mem_preimage, map_mul, mul_assoc, mul_comm (ι b)]
    rw [hset, map_val_preimage_mul_right N μN (hUN (hBU b hb)) (hE.preimage (measurable_mul_const _))]
  simp_rw [hj]

  have hterm : ∀ (j : Fin r) (m : ℤ), μ (U : Set G) * Measure.map (Subtype.val : N → G) μN
      ((fun t => t * (π j * ι (ϖ ^ m))) ⁻¹' E) =
      μN ((Subtype.val : N → G) ⁻¹' (U : Set G)) * μ (E ∩ coset (N : Set G) (π j * ι (ϖ ^ m))) := by
    intro j m
    rw [mul_map_val_apply μ N hN μN (U : Set G) hU hUN (hE.preimage (measurable_mul_const _)),
      measure_preimage_mul_right_inter]
  rw [Finset.mul_sum]
  simp_rw [← ENNReal.tsum_mul_left, hterm, ENNReal.tsum_mul_left]
  rw [← Finset.mul_sum]
  congr 1

  have hpair : ∑' p : Fin r × ℤ, μ (E ∩ coset (N : Set G) (π p.1 * ι (ϖ ^ p.2))) =
      ∑ j, ∑' m : ℤ, μ (E ∩ coset (N : Set G) (π j * ι (ϖ ^ m))) :=
    ENNReal.tsum_prod'.trans (tsum_fintype _)
  rw [← hpair]
  have hmem : ∀ (p : Fin r × ℤ) (t : G),
      t ∈ coset (N : Set G) (π p.1 * ι (ϖ ^ p.2)) ↔ (ι ϖ ^ p.2 * π p.1)⁻¹ * t ∈ N := by
    intro p t
    rw [mem_coset_iff, map_zpow, mul_comm (π p.1)]
  rw [tsum_measure_inter_eq μ (fun p : Fin r × ℤ => coset (N : Set G) (π p.1 * ι (ϖ ^ p.2)))
    (fun p => measurableSet_coset hN.measurableSet _) ?_ E hE]
  · have huniv : ⋃ p : Fin r × ℤ, coset (N : Set G) (π p.1 * ι (ϖ ^ p.2)) = Set.univ := by
      refine Set.eq_univ_of_forall fun t => ?_
      obtain ⟨p, hp, -⟩ := hπ t
      exact Set.mem_iUnion.2 ⟨p, (hmem p t).2 hp⟩
    rw [huniv, Set.inter_univ]
  · intro p q hpq
    refine Set.disjoint_left.2 fun t hp hq => hpq ?_
    exact (hπ t).unique ((hmem p t).1 hp) ((hmem q t).1 hq)

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem continuousSMul_completion_extension (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) (w : v.Extension L) :
    ContinuousSMul v.Completion w.1.Completion := by
  refine ⟨?_⟩
  have h : (fun p : v.Completion × w.1.Completion => p.1 • p.2) =
      fun p => algebraMap v.Completion w.1.Completion p.1 * p.2 := by
    funext p
    exact Algebra.smul_def p.1 p.2
  rw [h]
  exact ((M4aHerbrand.ArchSemilocal.continuous_algebraMap_completion v w.1).comp continuous_fst).mul continuous_snd

private theorem finite_archExtension (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) : Finite (v.Extension L) :=
  Finite.of_equiv _ (M4aHerbrand.ArchSemilocal.extensionEquivPlacesOver (K := K) (L := L) v).symm

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem continuous_archNorm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    Continuous (Algebra.norm v.Completion : (∀ w : v.Extension L, w.1.Completion) → v.Completion) := by
  classical
  letI := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion v
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => M4aHerbrand.ArchSemilocal.finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, ContinuousSMul v.Completion w.1.Completion :=
    fun w => continuousSMul_completion_extension K L v w
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  haveI : Finite (v.Extension L) := finite_archExtension K L v
  haveI : Module.Free v.Completion (∀ w : v.Extension L, w.1.Completion) := Module.Free.pi _ _
  haveI : Module.Finite v.Completion (∀ w : v.Extension L, w.1.Completion) := Module.Finite.pi
  let b := Module.Free.chooseBasis v.Completion (∀ w : v.Extension L, w.1.Completion)
  have h : (Algebra.norm v.Completion : (∀ w : v.Extension L, w.1.Completion) → v.Completion) =
      fun t => (Algebra.leftMulMatrix b t).det := by
    funext t
    exact Algebra.norm_eq_matrix_det b t
  rw [h]
  exact (LinearMap.continuous_of_finiteDimensional (Algebra.leftMulMatrix b).toLinearMap).matrix_det

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem coe_archNormOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ) =
      (fun t : (∀ w : v.Extension L, w.1.Completion)ˣ =>
        normHom (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion))) ⁻¹' {1} := by
  ext t
  simp only [archNormOneUnits, SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    Units.coeHom_apply, Set.mem_preimage, Set.mem_singleton_iff]
  exact Iff.rfl

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem continuous_abs_archNorm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    Continuous (fun t : (∀ w : v.Extension L, w.1.Completion)ˣ =>
      normHom (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion))) := by
  have h : (fun t : (∀ w : v.Extension L, w.1.Completion)ˣ =>
      normHom (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion))) =
        fun t : (∀ w : v.Extension L, w.1.Completion)ˣ =>
          ‖Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion)‖ := rfl
  rw [h]
  exact ((continuous_archNorm K L v).comp Units.continuous_val).norm

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem isClosed_archNormOneUnits_aux (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) :
    IsClosed (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ) := by
  rw [coe_archNormOneUnits]
  exact isClosed_singleton.preimage (continuous_abs_archNorm K L v)

private theorem mem_integralUnits_iff_aux (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ) :
    t ∈ integralUnits K L v ↔
      (t : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v ∧
        ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v :=
          by
  exact Iff.rfl

private theorem exists_norm_eq_completion (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : ∃ x : v.Completion, ‖x‖ = ρ := by
  rcases v.isReal_or_isComplex with hv | hv
  · obtain ⟨x, hx⟩ := NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hv ρ
    refine ⟨x, ?_⟩
    have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).dist_eq x 0
    rw [map_zero, dist_zero_right, dist_zero_right, hx, Real.norm_eq_abs, abs_of_nonneg hρ] at h
    exact h.symm
  · obtain ⟨x, hx⟩ := NumberField.InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hv (ρ : ℂ)
    refine ⟨x, ?_⟩
    have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).dist_eq x 0
    rw [map_zero, dist_zero_right, dist_zero_right, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ] at h
    exact h.symm

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem continuous_algebraMap_archSemiLocal (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) :
    Continuous (algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion)) := by
  refine continuous_pi fun w => ?_
  have h : (fun c : v.Completion => algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) c w) =
      algebraMap v.Completion w.1.Completion := by
    funext c
    exact Pi.algebraMap_apply _ _ _ _
  rw [h]
  exact M4aHerbrand.ArchSemilocal.continuous_algebraMap_completion v w.1

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem coe_includeArchUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) (s : (v.Completion)ˣ) :
    ((includeArchUnits K L v s : (∀ w : v.Extension L, w.1.Completion)ˣ) : ∀ w : v.Extension L, w.1.Completion) =
      algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) (s : v.Completion) := rfl

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem coe_inv_includeArchUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) (s : (v.Completion)ˣ) :
    (((includeArchUnits K L v s)⁻¹ : (∀ w : v.Extension L, w.1.Completion)ˣ) : ∀ w : v.Extension L, w.1.Completion) =
      algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) ((s⁻¹ : (v.Completion)ˣ) : v.Completion) := by
  rw [← map_inv]
  rfl

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem continuous_includeArchUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) : Continuous (includeArchUnits K L v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (Units.val ∘ includeArchUnits K L v) =
        fun s : (v.Completion)ˣ => algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) (s : v.Completion) :=
      funext fun s => coe_includeArchUnits K L v s
    rw [h]
    exact (continuous_algebraMap_archSemiLocal K L v).comp Units.continuous_val
  · have h : (fun s : (v.Completion)ˣ =>
          (((includeArchUnits K L v s)⁻¹ : (∀ w : v.Extension L, w.1.Completion)ˣ) :
            ∀ w : v.Extension L, w.1.Completion)) =
        fun s => algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) ((s⁻¹ : (v.Completion)ˣ) : v.Completion)
          :=
      funext fun s => coe_inv_includeArchUnits K L v s
    rw [h]
    exact (continuous_algebraMap_archSemiLocal K L v).comp Units.continuous_coe_inv

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem abs_archNorm_includeArchUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) (s : (v.Completion)ˣ) :
    normHom (Algebra.norm v.Completion
        ((includeArchUnits K L v s : (∀ w : v.Extension L, w.1.Completion)ˣ) : ∀ w : v.Extension L, w.1.Completion)) =
      ‖(s : v.Completion)‖ ^ Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) := by
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => M4aHerbrand.ArchSemilocal.finiteDimensional_completion v w.1
  haveI : Finite (v.Extension L) := finite_archExtension K L v
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion := fun w => Module.Free.of_divisionRing _ _
  haveI : Module.Free v.Completion (∀ w : v.Extension L, w.1.Completion) := Module.Free.pi _ _
  rw [coe_includeArchUnits, Algebra.norm_algebraMap, map_pow]
  rfl

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem finrank_archSemiLocal_ne_zero (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) :
    Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) ≠ 0 := by
  rw [M4aHerbrand.ArchSemilocal.finrank_pi_extension v]
  exact Module.finrank_pos.ne'

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem abs_archNorm_pos (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) (t : (∀ w : v.Extension L, w.1.Completion)ˣ) :
    0 < normHom (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion)) := by
  have h : Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion) ≠ 0 :=
    (t.isUnit.map (Algebra.norm v.Completion)).ne_zero
  exact norm_pos_iff.2 h

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem surjective_archProduct (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    Function.Surjective (fun p : (v.Completion)ˣ × archNormOneUnits K L v =>
      ((p.2 : (∀ w : v.Extension L, w.1.Completion)ˣ)) * includeArchUnits K L v p.1) := by
  intro t
  have hx : 0 < normHom (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion)) := abs_archNorm_pos K L v
    t
  have hd : Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) ≠ 0 := finrank_archSemiLocal_ne_zero K L
    v
  obtain ⟨s₀, hs₀⟩ :=
    exists_norm_eq_completion K v
      (Real.rpow_nonneg hx.le ((Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) : ℕ) : ℝ)⁻¹)
  have hs₀0 : s₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs₀
    exact (Real.rpow_pos_of_pos hx _).ne hs₀
  have hιs : normHom (Algebra.norm v.Completion
      ((includeArchUnits K L v (Units.mk0 s₀ hs₀0) : (∀ w : v.Extension L, w.1.Completion)ˣ) :
        ∀ w : v.Extension L, w.1.Completion)) =
      normHom (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion)) := by
    rw [abs_archNorm_includeArchUnits, Units.val_mk0, hs₀]
    exact Real.rpow_inv_natCast_pow hx.le hd
  have hn : t * (includeArchUnits K L v (Units.mk0 s₀ hs₀0))⁻¹ ∈ archNormOneUnits K L v := by
    show normHom (Algebra.norm v.Completion
      ((t * (includeArchUnits K L v (Units.mk0 s₀ hs₀0))⁻¹ : (∀ w : v.Extension L, w.1.Completion)ˣ) :
        ∀ w : v.Extension L, w.1.Completion)) = 1
    have hinv : normHom (Algebra.norm v.Completion
        (((includeArchUnits K L v (Units.mk0 s₀ hs₀0))⁻¹ : (∀ w : v.Extension L, w.1.Completion)ˣ) :
          ∀ w : v.Extension L, w.1.Completion)) =
        (normHom (Algebra.norm v.Completion
          ((includeArchUnits K L v (Units.mk0 s₀ hs₀0) : (∀ w : v.Extension L, w.1.Completion)ˣ) :
            ∀ w : v.Extension L, w.1.Completion)))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rw [Units.val_mul, map_mul, map_mul, hinv, hιs]
    exact mul_inv_cancel₀ hx.ne'
  exact ⟨(Units.mk0 s₀ hs₀0, ⟨t * (includeArchUnits K L v (Units.mk0 s₀ hs₀0))⁻¹, hn⟩), inv_mul_cancel_right t _⟩

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem abs_archNorm_coe_mul_includeArchUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) (n : archNormOneUnits K L v) (s : (v.Completion)ˣ) :
    normHom (Algebra.norm v.Completion
        (((n : (∀ w : v.Extension L, w.1.Completion)ˣ) * includeArchUnits K L v s :
          (∀ w : v.Extension L, w.1.Completion)ˣ) : ∀ w : v.Extension L, w.1.Completion)) =
      ‖(s : v.Completion)‖ ^ Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) := by
  have hn : normHom
    (Algebra.norm v.Completion ((n : (∀ w : v.Extension L, w.1.Completion)ˣ) : ∀ w : v.Extension L, w.1.Completion)) =
    1 := n.2
  rw [Units.val_mul, map_mul, map_mul, hn, one_mul, abs_archNorm_includeArchUnits]

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem isCompact_annulus (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) {a b : ℝ} (ha : 0 < a) :
    IsCompact {s : (v.Completion)ˣ |
      a ≤ ‖(s : v.Completion)‖ ^ Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) ∧
        ‖(s : v.Completion)‖ ^ Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) ≤ b} := by
  letI := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion v
  haveI : ProperSpace v.Completion :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace v.Completion
  set d : ℕ := Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) with hd_def
  have hd : d ≠ 0 := finrank_archSemiLocal_ne_zero K L v
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himage : Units.val '' {s : (v.Completion)ˣ | a ≤ ‖(s : v.Completion)‖ ^ d ∧ ‖(s : v.Completion)‖ ^ d ≤ b} =
      {x : v.Completion | a ≤ ‖x‖ ^ d} ∩ {x : v.Completion | ‖x‖ ^ d ≤ b} := by
    ext x
    constructor
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hx : x ≠ 0 := by
        rintro rfl
        simp only [Set.mem_setOf_eq, norm_zero, zero_pow hd] at h1
        exact ha.not_ge h1
      exact ⟨Units.mk0 x hx, ⟨h1, h2⟩, rfl⟩
  rw [himage]
  have hcont : Continuous fun x : v.Completion => ‖x‖ ^ d := continuous_norm.pow _
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le continuous_const hcont).inter (isClosed_le hcont continuous_const)) ?_
  refine (Metric.isBounded_closedBall (x := (0 : v.Completion)) (r := max 1 b)).subset fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases h1 : ‖x‖ ≤ 1
  · exact h1.trans (le_max_left _ _)
  · push Not at h1
    refine le_trans ?_ (le_max_right _ _)
    calc ‖x‖ = ‖x‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖x‖ ^ d := pow_le_pow_right₀ h1.le (Nat.one_le_iff_ne_zero.2 hd)
      _ ≤ b := hx.2

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem isCompact_preimage_archProduct (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) {C : Set (∀ w : v.Extension L, w.1.Completion)ˣ} (hC : IsCompact C) :
    IsCompact ((fun p : (v.Completion)ˣ × archNormOneUnits K L v =>
      ((p.2 : (∀ w : v.Extension L, w.1.Completion)ˣ)) * includeArchUnits K L v p.1) ⁻¹' C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp only [Set.preimage_empty, isCompact_empty]
  set ι := includeArchUnits K L v with hι_def
  set d : ℕ := Module.finrank v.Completion (∀ w : v.Extension L, w.1.Completion) with hd_def
  have hmul : ∀ (n : archNormOneUnits K L v) (s : (v.Completion)ˣ),
      normHom (Algebra.norm v.Completion
          (((n : (∀ w : v.Extension L, w.1.Completion)ˣ) * ι s : (∀ w : v.Extension L, w.1.Completion)ˣ) :
            ∀ w : v.Extension L, w.1.Completion)) =
        ‖(s : v.Completion)‖ ^ d :=
    fun n s => abs_archNorm_coe_mul_includeArchUnits K L v n s
  have hpos : ∀ t : (∀ w : v.Extension L, w.1.Completion)ˣ, 0 < normHom
    (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion)) :=
    abs_archNorm_pos K L v
  set φ : (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ := fun t => normHom
    (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion)) with hφ_def
  have hφ : Continuous φ := continuous_abs_archNorm K L v
  obtain ⟨t₀, -, ht₀⟩ := hC.exists_isMinOn hne hφ.continuousOn
  obtain ⟨t₁, -, ht₁⟩ := hC.exists_isMaxOn hne hφ.continuousOn
  set S : Set (v.Completion)ˣ :=
    {s | φ t₀ ≤ ‖(s : v.Completion)‖ ^ d ∧ ‖(s : v.Completion)‖ ^ d ≤ φ t₁} with hS_def
  have hS : IsCompact S := isCompact_annulus K L v (hpos t₀)
  set g : (∀ w : v.Extension L, w.1.Completion)ˣ × (v.Completion)ˣ → (∀ w : v.Extension L, w.1.Completion)ˣ := fun q =>
    q.1 * (ι q.2)⁻¹ with hg_def
  have hg : Continuous g := continuous_fst.mul ((continuous_includeArchUnits K L v).comp continuous_snd).inv
  have hN : IsCompact
    ((Subtype.val : archNormOneUnits K L v → (∀ w : v.Extension L, w.1.Completion)ˣ) ⁻¹' (g '' (C ×ˢ S))) :=
    (isClosed_archNormOneUnits_aux K L v).isClosedEmbedding_subtypeVal.isCompact_preimage ((hC.prod hS).image hg)
  have hF : Continuous
    (fun p : (v.Completion)ˣ × archNormOneUnits K L v => ((p.2 : (∀ w : v.Extension L, w.1.Completion)ˣ)) * ι p.1) :=
    (continuous_subtype_val.comp continuous_snd).mul ((continuous_includeArchUnits K L v).comp continuous_fst)
  refine (hS.prod hN).of_isClosed_subset (hC.isClosed.preimage hF) ?_
  rintro ⟨s, n⟩ hp
  have hpC : (n : (∀ w : v.Extension L, w.1.Completion)ˣ) * ι s ∈ C := hp
  have hsS : s ∈ S := by
    have h1 : φ t₀ ≤ φ ((n : (∀ w : v.Extension L, w.1.Completion)ˣ) * ι s) := ht₀ hpC
    have h2 : φ ((n : (∀ w : v.Extension L, w.1.Completion)ˣ) * ι s) ≤ φ t₁ := ht₁ hpC
    rw [hφ_def] at h1 h2
    simp only at h1 h2
    rw [hmul] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨hsS, ?_⟩
  show (n : (∀ w : v.Extension L, w.1.Completion)ˣ) ∈ g '' (C ×ˢ S)
  exact ⟨((n : (∀ w : v.Extension L, w.1.Completion)ˣ) * ι s, s), ⟨hpC, hsS⟩, mul_inv_cancel_right _ _⟩

private theorem secondCountableTopology_completion (F : Type) [Field F] [NumberField F] (u : InfinitePlace F) :
    SecondCountableTopology u.Completion := by
  letI := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion u
  haveI : ProperSpace u.Completion :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace u.Completion
  infer_instance

private theorem secondCountableTopology_units_of (M : Type) [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem secondCountableTopology_archUnits_aux (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) : SecondCountableTopology (∀ w : v.Extension L, w.1.Completion)ˣ := by
  haveI : ∀ w : v.Extension L, SecondCountableTopology w.1.Completion :=
    fun w => secondCountableTopology_completion L w.1
  exact secondCountableTopology_units_of _

private theorem exists_measure_eq_mul_lintegral_map_of_proper {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G)
    [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N] (μN : Measure N)
    [μN.IsHaarMeasure]
    (μH : Measure H) [μH.IsHaarMeasure] (ι : H →* G) (hι : Continuous ι)
    (hsurj : Function.Surjective (fun p : H × N => (p.2 : G) * ι p.1))
    (hproper : Filter.Tendsto (fun p : H × N => (p.2 : G) * ι p.1) (Filter.cocompact (H × N)) (Filter.cocompact G)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ E : Set G, MeasurableSet E →
      μ E = c * ∫⁻ s, Measure.map (Subtype.val : N → G) μN ((fun t => t * ι s) ⁻¹' E) ∂μH := by

  let F : H × N →* G :=
    { toFun := fun p => (p.2 : G) * ι p.1
      map_one' := by simp
      map_mul' := by
        intro p q
        simp only [Prod.snd_mul, Subgroup.coe_mul, Prod.fst_mul, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hF : Continuous F := (continuous_subtype_val.comp continuous_snd).mul (hι.comp continuous_fst)
  have hFsurj : Function.Surjective F := hsurj
  have hFprop : Filter.Tendsto F (Filter.cocompact (H × N)) (Filter.cocompact G) := hproper

  haveI : (Measure.map F (μH.prod μN)).IsHaarMeasure := Measure.isHaarMeasure_map (μH.prod μN) F hF hFsurj hFprop
  have hval : Measurable (Subtype.val : N → G) := continuous_subtype_val.measurable

  have himage : ∀ E : Set G, MeasurableSet E →
      Measure.map F (μH.prod μN) E =
        ∫⁻ s, Measure.map (Subtype.val : N → G) μN ((fun t => t * ι s) ⁻¹' E) ∂μH := by
    intro E hE
    rw [Measure.map_apply hF.measurable hE, Measure.prod_apply (hE.preimage hF.measurable)]
    refine lintegral_congr fun s => ?_
    rw [Measure.map_apply hval (hE.preimage (measurable_mul_const _))]
    rfl

  obtain ⟨c, hc0, hctop, hc⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ Measure.map F (μH.prod μN) = c • μ := by
    refine ⟨(Measure.haarScalarFactor (Measure.map F (μH.prod μN)) μ : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
    · exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
    · exact (Measure.isMulLeftInvariant_eq_smul _ _).trans (ENNReal.smul_def _ _)
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.2 hctop, ENNReal.inv_ne_top.2 hc0, fun E hE => ?_⟩
  rw [← himage E hE, hc, Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]

private theorem det_blockDiagonal'_eq_prod {ι : Type} [Fintype ι] [LinearOrder ι] {R : Type} [CommRing R]
    {n : ι → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] (d : ∀ i, Matrix (n i) (n i) R) :
    (Matrix.blockDiagonal' d).det = ∏ i, (d i).det := by
  classical
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_

  let e : n k ≃ {a : Σ i, n i // a.1 = k} :=
    { toFun := fun a => ⟨⟨k, a⟩, rfl⟩
      invFun := fun s => cast (congrArg n s.2) s.1.2
      left_inv := fun a => rfl
      right_inv := by
        rintro ⟨⟨i, a⟩, hi⟩
        subst hi
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.toSquareBlock_def, Matrix.of_apply, e, Equiv.coe_fn_mk,
    Matrix.blockDiagonal'_apply_eq]

private theorem norm_pi_eq_prod {F : Type} [Field F] {ι : Type} [Fintype ι] [LinearOrder ι] (E : ι → Type)
    [∀ i, CommRing (E i)] [∀ i, Algebra F (E i)] [∀ i, Module.Finite F (E i)] (x : ∀ i, E i) :
    Algebra.norm F x = ∏ i, Algebra.norm F (x i) := by
  classical
  let b : ∀ i, Module.Basis (Fin (Module.finrank F (E i))) F (E i) := fun i => Module.finBasis F (E i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b) x]
  have hblock : Algebra.leftMulMatrix (Pi.basis b) x =
      Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (b i) (x i) := by
    ext ⟨i, a⟩ ⟨j, c⟩
    rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul]
      simp only [Pi.mul_apply, Pi.single_eq_same]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij]
      simp only [Pi.mul_apply, Pi.single_eq_of_ne hij, mul_zero, map_zero, Finsupp.zero_apply]
  rw [hblock, det_blockDiagonal'_eq_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Algebra.norm_eq_matrix_det (b i) (x i)]

open scoped TensorProduct.RightActions in

private noncomputable def semiLocalPiEquiv (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v)
    (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v)

open scoped TensorProduct.RightActions in

private theorem semiLocalHomeomorph_eq_semiLocalPiEquiv (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : L ⊗[K] v.adicCompletion K) :
    AutomorphicForm.semiLocalHomeomorph K L v x = semiLocalPiEquiv K L v x :=
  rfl

open scoped TensorProduct.RightActions in

private theorem norm_eq_prod_norm_component (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))] (x : L ⊗[K] v.adicCompletion K) :
    Algebra.norm (v.adicCompletion K) x =
      ∏ w : v.Extension (𝓞 L), Algebra.norm (v.adicCompletion K) (semiLocalPiEquiv K L v x w) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  letI : LinearOrder (v.Extension (𝓞 L)) :=
    LinearOrder.lift' (Fintype.equivFin (v.Extension (𝓞 L))) (Fintype.equivFin (v.Extension (𝓞 L))).injective
  rw [← Algebra.norm_eq_of_algEquiv (semiLocalPiEquiv K L v) x,
    norm_pi_eq_prod (fun w : v.Extension (𝓞 L) => w.1.adicCompletion L)]

open scoped TensorProduct.RightActions in

private theorem isIntegral_integralTensor (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (z : 𝓞 L ⊗[𝓞 K] v.adicCompletionIntegers K) : IsIntegral (v.adicCompletionIntegers K)
      z := by
  induction z using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul b o =>
    have hb : IsIntegral (𝓞 K) b := Algebra.IsIntegral.isIntegral b
    have h1 : IsIntegral (v.adicCompletionIntegers K)
      ((b ⊗ₜ[𝓞 K] (1 : v.adicCompletionIntegers K) : 𝓞 L ⊗[𝓞 K] v.adicCompletionIntegers K)) :=
      (hb.map (Algebra.TensorProduct.includeLeft (R := 𝓞 K) (S := 𝓞 K) (A := 𝓞 L)
        (B := v.adicCompletionIntegers K))).tower_top
    have h2 : IsIntegral (v.adicCompletionIntegers K) (((1 : 𝓞 L) ⊗ₜ[𝓞 K] o : 𝓞 L ⊗[𝓞 K] v.adicCompletionIntegers K))
      := by
      have h : ((1 : 𝓞 L) ⊗ₜ[𝓞 K] o : 𝓞 L ⊗[𝓞 K] v.adicCompletionIntegers K) = algebraMap (v.adicCompletionIntegers K)
        _ o := rfl
      rw [h]
      exact isIntegral_algebraMap
    have h : (b ⊗ₜ[𝓞 K] o : 𝓞 L ⊗[𝓞 K] v.adicCompletionIntegers K) =
        (b ⊗ₜ[𝓞 K] (1 : v.adicCompletionIntegers K)) * ((1 : 𝓞 L) ⊗ₜ[𝓞 K] o) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    exact h1.mul h2
  | add x y hx hy => exact hx.add hy

open scoped TensorProduct.RightActions in

private theorem valued_norm_le_one_of_mem_integers (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    {y : w.1.adicCompletion L} (hy : y ∈ w.1.adicCompletionIntegers L) : Valued.v (Algebra.norm (v.adicCompletion K) y)
      ≤ 1 := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hrange := w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L (𝓞 L) v
  have hy' : y ∈ Set.range (w.tensorAdicCompletionIntegersToAdicCompletion K L (𝓞 L) v) := by
    rw [hrange]
    exact hy
  obtain ⟨z, rfl⟩ := hy'
  have hz : IsIntegral (v.adicCompletionIntegers K) (w.tensorAdicCompletionIntegersToAdicCompletion K L (𝓞 L) v z) :=
    (isIntegral_integralTensor K L v z).map _
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm (v.adicCompletion K) hz)
  rw [← ho]
  exact o.2

open scoped TensorProduct.RightActions in

private theorem component_mem_integers_of_mem_semiLocalIntegers (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) {x : L ⊗[K] v.adicCompletion K}
    (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) (w : v.Extension (𝓞 L)) :
    semiLocalPiEquiv K L v x w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers,
    Set.mem_univ_pi] at hx
  rw [← semiLocalHomeomorph_eq_semiLocalPiEquiv]
  exact hx w

open scoped TensorProduct.RightActions in

private theorem valued_norm_le_one_of_mem_semiLocalIntegers (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]
    {x : L ⊗[K] v.adicCompletion K}
    (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) : Valued.v (Algebra.norm (v.adicCompletion K) x) ≤ 1 := by
  rw [norm_eq_prod_norm_component, map_prod]
  exact Finset.prod_le_one' fun w _ =>
    valued_norm_le_one_of_mem_integers K L v w (component_mem_integers_of_mem_semiLocalIntegers K L v hx w)

open scoped TensorProduct.RightActions in

private theorem mem_normOneUnits_of_valued_norm_le (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ)
    (ha : Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) ≤ 1)
    (hb : Valued.v (Algebra.norm (v.adicCompletion K)
      ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) ≤ 1) :
    t ∈ normOneUnits K L v := by
  have hmul : Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) *
      Valued.v (Algebra.norm (v.adicCompletion K) ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) =
        1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hge : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v
    (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) := by
    calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
      _ ≤ Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) * 1 := by gcongr
      _ = _ := mul_one _
  exact le_antisymm ha hge

private theorem prod_exp_eq_exp_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (m i) = WithZero.exp (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, WithZero.exp_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, WithZero.exp_add]

private theorem zpow_sum_of_ne_zero {ι : Type} (s : Finset ι) (m : ι → ℤ) {a : ℝ} (ha : a ≠ 0) :
    a ^ (∑ i ∈ s, m i) = ∏ i ∈ s, a ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zpow_zero, Finset.prod_empty]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add₀ ha, ih]

private theorem absNorm_extension_eq_pow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ Ideal.inertiaDeg' v.asIdeal w.1.asIdeal := by
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  haveI : w.1.asIdeal.LiesOver (w.1.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal (w.1.under (𝓞 K)).asIdeal
    (w.1.under (𝓞 K)).isPrime (w.1.under (𝓞 K)).ne_bot
  rw [w.2] at h
  exact h

private theorem absNorm_asIdeal_ne_zero (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)

open scoped TensorProduct.RightActions in

private theorem valued_component_ne_zero (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ) (w : v.Extension (𝓞 L)) :
    Valued.v (semiLocalPiEquiv K L v (t : L ⊗[K] v.adicCompletion K) w) ≠ 0 := by
  have hu : IsUnit (semiLocalPiEquiv K L v (t : L ⊗[K] v.adicCompletion K)) := t.isUnit.map (semiLocalPiEquiv K L v)
  have hw : IsUnit (semiLocalPiEquiv K L v (t : L ⊗[K] v.adicCompletion K) w) := hu.map (Pi.evalMonoidHom _ w)
  exact (Valuation.ne_zero_iff _).2 hw.ne_zero

open scoped TensorProduct.RightActions in

private theorem log_valued_norm_eq_sum (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))] (t : (L ⊗[K] v.adicCompletion K)ˣ) :
    WithZero.log (Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K))) =
      ∑ w : v.Extension (𝓞 L), (Ideal.inertiaDeg' v.asIdeal w.1.asIdeal : ℤ) * WithZero.log
        (Valued.v (semiLocalPiEquiv K L v (t : L ⊗[K] v.adicCompletion K) w)) := by
  have h : Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) =
      WithZero.exp (∑ w : v.Extension (𝓞 L),
        (Ideal.inertiaDeg' v.asIdeal w.1.asIdeal : ℤ) * WithZero.log
          (Valued.v (semiLocalPiEquiv K L v (t : L ⊗[K] v.adicCompletion K) w))) := by
    rw [norm_eq_prod_norm_component, map_prod, ← prod_exp_eq_exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg K L v w,
      ← WithZero.exp_log (valued_component_ne_zero K L v t w), WithZero.log_exp, ← zpow_natCast,
      ← WithZero.exp_zsmul, smul_eq_mul]
  rw [h, WithZero.log_exp]

open scoped TensorProduct.RightActions in

private theorem isCompact_integralUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : IsCompact (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  haveI := t2Space_semiLocal K L v
  haveI := continuousMul_semiLocal K L v
  have hI := isCompact_semiLocalIntegers K L v
  rw [Units.isInducing_embedProduct.isCompact_iff]
  have hset : Units.embedProduct (L ⊗[K] v.adicCompletion K) ''
        (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) =
      (AutomorphicForm.semiLocalIntegers K L v ×ˢ
          (MulOpposite.op '' AutomorphicForm.semiLocalIntegers K L v)) ∩
        Set.range (Units.embedProduct (L ⊗[K] v.adicCompletion K)) := by
    ext p
    simp only [Set.mem_image, SetLike.mem_coe, Set.mem_inter_iff, Set.mem_prod, Set.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨h1, h2⟩ := (mem_integralUnits_iff_aux K L v t).1 ht
      exact ⟨⟨h1, ⟨_, h2, rfl⟩⟩, t, rfl⟩
    · rintro ⟨⟨h1, y, hy, hop⟩, t, rfl⟩
      refine ⟨t, (mem_integralUnits_iff_aux K L v t).2 ⟨h1, ?_⟩, rfl⟩
      have hy' : y = ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) :=
        MulOpposite.op_injective hop
      rwa [← hy']
  rw [hset]
  exact (hI.prod (hI.image MulOpposite.continuous_op)).inter_right
    Units.isClosedEmbedding_embedProduct.isClosed_range

open scoped TensorProduct.RightActions in

private theorem isOpen_integralUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : IsOpen (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  have hI := isOpen_semiLocalIntegers K L v
  have hset : (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) =
      Units.val ⁻¹' AutomorphicForm.semiLocalIntegers K L v ∩
        (fun t : (L ⊗[K] v.adicCompletion K)ˣ =>
            ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) ⁻¹'
          AutomorphicForm.semiLocalIntegers K L v := by
    ext t
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage]
    exact mem_integralUnits_iff_aux K L v t
  rw [hset]
  exact (hI.preimage Units.continuous_val).inter (hI.preimage Units.continuous_coe_inv)

open scoped TensorProduct.RightActions in

private theorem secondCountableTopology_units (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (L ⊗[K] v.adicCompletion K)ˣ := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable (WithVal (v.valuation K)) := (WithVal.equiv (v.valuation K)).injective.countable
  haveI : Countable (Multiplicative ℤ) := Multiplicative.toAdd.injective.countable
  haveI : ∀ (G : Type) [Countable G], Countable (WithZero G) := fun G _ => inferInstanceAs (Countable (Option G))
  haveI : ∀ (G : Type) [Monoid G] [Countable G], Countable Gˣ := fun G _ _ => Units.val_injective.countable
  haveI : (uniformity (v.adicCompletion K)).IsCountablyGenerated :=
    (Valued.hasBasis_uniformity (v.adicCompletion K) _).isCountablyGenerated
  haveI : TopologicalSpace.SeparableSpace (v.adicCompletion K) :=
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective (K := K) (v := v)).denseRange.comp
      UniformSpace.Completion.denseRange_coe
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v)).separableSpace
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v).comp
        (UniformSpace.Completion.continuous_coe _))
  haveI : SecondCountableTopology (v.adicCompletion K) := UniformSpace.secondCountable_of_separable _
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Finite (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : ∀ w : v.Extension (𝓞 L), SecondCountableTopology (w.1.adicCompletion L) := fun w =>
    Module.Finite.secondCountabletopology (v.adicCompletion K) (w.1.adicCompletion L)
  haveI : SecondCountableTopology (L ⊗[K] v.adicCompletion K) :=
    (AutomorphicForm.semiLocalHomeomorph K L v).isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (L ⊗[K] v.adicCompletion K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem integralUnits_le_normOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : integralUnits K L v ≤ normOneUnits K L v := by
  haveI : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  intro t ht
  obtain ⟨h1, h2⟩ := (mem_integralUnits_iff_aux K L v t).1 ht
  exact mem_normOneUnits_of_valued_norm_le K L v t (valued_norm_le_one_of_mem_semiLocalIntegers K L v h1)
    (valued_norm_le_one_of_mem_semiLocalIntegers K L v h2)

private theorem mem_integralUnits_iff (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (t : (L ⊗[K] v.adicCompletion K)ˣ) :
    t ∈ integralUnits K L v ↔
      (t : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v ∧
        ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v :=
          by
  exact mem_integralUnits_iff_aux K L v t

open scoped TensorProduct.RightActions in

private theorem measure_integralUnits_ne_zero_and_ne_top (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
      (μv : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μv.IsHaarMeasure] :
    μv (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ≠ 0 ∧ μv
      (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ≠ ⊤ := by
  exact ⟨(isOpen_integralUnits K L v).measure_ne_zero μv ⟨1, (integralUnits K L v).one_mem⟩,
    (isCompact_integralUnits K L v).measure_lt_top.ne⟩

private theorem exists_uniformizer (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : (v.adicCompletion K)ˣ, ∀ s : (v.adicCompletion K)ˣ, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ valOneUnits K v := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (R := 𝓞 K) (K := K) (v := v)
  have hπv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact WithZero.exp_ne_zero hπv.symm
  refine ⟨Units.mk0 _ hπ0, fun s => ?_⟩
  have hs0 : Valued.v (s : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  have hval : ∀ m : ℤ, Valued.v (((Units.mk0 _ hπ0 ^ m)⁻¹ * s : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp m * Valued.v (s : v.adicCompletion K) := by
    intro m
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val, map_zpow₀,
      Units.val_mk0, hπv, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, ← WithZero.exp_neg, neg_neg]
  refine ⟨-WithZero.log (Valued.v (s : v.adicCompletion K)), ?_, fun m hm => ?_⟩
  · show Valued.v _ = 1
    rw [hval, ← WithZero.exp_log hs0, ← WithZero.exp_add, WithZero.log_exp, neg_add_cancel, WithZero.exp_zero]
  · have hm' : Valued.v (((Units.mk0 _ hπ0 ^ m)⁻¹ * s : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := hm
    rw [hval, ← WithZero.exp_log hs0, ← WithZero.exp_add] at hm'
    have h2 := congrArg WithZero.log hm'
    rw [WithZero.log_exp, WithZero.log_one] at h2
    linarith

private theorem exists_representatives (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ (r : ℕ) (π : Fin r → (L ⊗[K] v.adicCompletion K)ˣ),
      ∀ ϖ : (v.adicCompletion K)ˣ, (∀ s : (v.adicCompletion K)ˣ, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ valOneUnits K v) →
        ∀ t : (L ⊗[K] v.adicCompletion K)ˣ, ∃! p : Fin r × ℤ,
          (includeUnits K L v ϖ ^ p.2 * π p.1)⁻¹ * t ∈ normOneUnits K L v := by
  classical
  have hone : normLog K L v 1 = 0 := by
    have h := normLog_mul K L v 1 1
    rw [one_mul] at h
    linarith
  have hinv : ∀ t : (L ⊗[K] v.adicCompletion K)ˣ, normLog K L v t⁻¹ = -normLog K L v t := by
    intro t
    have h := normLog_mul K L v t⁻¹ t
    rw [inv_mul_cancel, hone] at h
    linarith

  let H : AddSubgroup ℤ :=
    { carrier := Set.range (normLog K L v)
      zero_mem' := ⟨1, hone⟩
      add_mem' := by
        rintro _ _ ⟨t, rfl⟩ ⟨t', rfl⟩
        exact ⟨t * t', normLog_mul K L v t t'⟩
      neg_mem' := by
        rintro _ ⟨t, rfl⟩
        exact ⟨t⁻¹, hinv t⟩ }
  obtain ⟨d, hd⟩ := Int.subgroup_cyclic H
  have hmemH : ∀ x : ℤ, (∃ t : (L ⊗[K] v.adicCompletion K)ˣ, normLog K L v t = x) ↔ ∃ k : ℤ, k * d = x := by
    intro x
    have h : x ∈ H ↔ x ∈ AddSubgroup.closure ({d} : Set ℤ) := by rw [hd]
    rw [AddSubgroup.mem_closure_singleton] at h
    simp only [smul_eq_mul] at h
    exact h

  haveI : Nonempty (v.Extension (𝓞 L)) := nonempty_extension K L v
  haveI : Inhabited (v.Extension (𝓞 L)) := ⟨(nonempty_extension K L v).some⟩
  open scoped TensorProduct.RightActions in
  haveI : Nontrivial (L ⊗[K] v.adicCompletion K) := (AutomorphicForm.semiLocalHomeomorph K L v).surjective.nontrivial
  have hn : (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) : ℤ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  obtain ⟨u, hu⟩ : ∃ u : (v.adicCompletion K)ˣ, WithZero.log (Valued.v (u : v.adicCompletion K)) = -1 := by
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (R := 𝓞 K) (K := K) (v := v)
    have hπv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
      rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
    have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
      intro h
      rw [h, map_zero] at hπv
      exact WithZero.exp_ne_zero hπv.symm
    exact ⟨Units.mk0 _ hπ0, by rw [Units.val_mk0, hπv, WithZero.log_exp]⟩
  obtain ⟨q, hq⟩ : ∃ k : ℤ, k * d = -(Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) : ℤ) := by
    rw [← hmemH]
    exact ⟨includeUnits K L v u, by rw [normLog_includeUnits, hu, mul_neg_one]⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hn (neg_eq_zero.1 hq.symm)
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hq
    exact hn (neg_eq_zero.1 hq.symm)

  have hrpos : (0 : ℤ) < q.natAbs := by exact_mod_cast Int.natAbs_pos.2 hq0
  choose π hπ using fun j : Fin q.natAbs => (hmemH ((j : ℤ) * d)).2 ⟨j, rfl⟩
  refine ⟨q.natAbs, π, fun ϖ hϖ t => ?_⟩

  have hb : WithZero.log (Valued.v (ϖ : v.adicCompletion K)) = 1 ∨
      WithZero.log (Valued.v (ϖ : v.adicCompletion K)) = -1 := by
    obtain ⟨m, hm, -⟩ := hϖ u
    have h1 : Valued.v (((ϖ ^ m)⁻¹ * u : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := hm
    have hϖ0 : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 ϖ.ne_zero
    have hu0 : Valued.v (u : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val, map_zpow₀] at h1
    have h2 := congrArg WithZero.log h1
    rw [WithZero.log_mul (inv_ne_zero (zpow_ne_zero m hϖ0)) hu0, WithZero.log_inv, WithZero.log_zpow, hu,
      WithZero.log_one, smul_eq_mul] at h2
    have hmb : m * WithZero.log (Valued.v (ϖ : v.adicCompletion K)) = -1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hmb with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have ha : normLog K L v (includeUnits K L v ϖ) =
      -(q * d) * WithZero.log (Valued.v (ϖ : v.adicCompletion K)) := by
    rw [normLog_includeUnits]
    linear_combination (WithZero.log (Valued.v (ϖ : v.adicCompletion K))) * hq
  obtain ⟨σ, hσσ, haσ⟩ : ∃ σ : ℤ, σ * σ = 1 ∧
      normLog K L v (includeUnits K L v ϖ) = σ * (q.natAbs : ℤ) * d := by
    rcases Int.natAbs_eq q with hqa | hqa <;> rcases hb with hb1 | hb1
    · exact ⟨-1, by norm_num, by rw [ha, hb1, ← hqa]; ring⟩
    · exact ⟨1, by norm_num, by rw [ha, hb1, ← hqa]; ring⟩
    · refine ⟨1, by norm_num, ?_⟩
      rw [ha, hb1]
      have hq' : (q.natAbs : ℤ) = -q := by omega
      rw [hq']
      ring
    · refine ⟨-1, by norm_num, ?_⟩
      rw [ha, hb1]
      have hq' : (q.natAbs : ℤ) = -q := by omega
      rw [hq']
      ring

  obtain ⟨k, hk⟩ := (hmemH (normLog K L v t)).1 ⟨t, rfl⟩
  have hmem : ∀ (j : Fin q.natAbs) (m : ℤ),
      (includeUnits K L v ϖ ^ m * π j)⁻¹ * t ∈ normOneUnits K L v ↔ m * σ * (q.natAbs : ℤ) + (j : ℤ) = k := by
    intro j m
    rw [mem_normOneUnits_iff_normLog, normLog_mul, hinv, normLog_mul, normLog_zpow, haσ, hπ, ← hk]
    constructor
    · intro h
      have h' : (m * σ * (q.natAbs : ℤ) + (j : ℤ)) * d = k * d := by linear_combination (-1 : ℤ) * h
      exact mul_right_cancel₀ hd0 h'
    · intro h
      rw [← h]
      ring
  have hj0 : 0 ≤ k % (q.natAbs : ℤ) := Int.emod_nonneg _ hrpos.ne'
  have hj1 : k % (q.natAbs : ℤ) < q.natAbs := Int.emod_lt_of_pos _ hrpos
  let j₀ : Fin q.natAbs := ⟨(k % (q.natAbs : ℤ)).toNat, by omega⟩
  have hj₀ : (j₀ : ℤ) = k % (q.natAbs : ℤ) := Int.toNat_of_nonneg hj0
  refine ⟨(j₀, σ * (k / (q.natAbs : ℤ))), ?_, ?_⟩
  · show (includeUnits K L v ϖ ^ (σ * (k / (q.natAbs : ℤ))) * π j₀)⁻¹ * t ∈ normOneUnits K L v
    rw [hmem, hj₀]
    have hdiv := Int.emod_add_mul_ediv k (q.natAbs : ℤ)
    linear_combination (k / (q.natAbs : ℤ)) * (q.natAbs : ℤ) * hσσ + hdiv
  · rintro ⟨j, m⟩ hjm
    have h := (hmem j m).1 hjm
    have hj : (0 : ℤ) ≤ (j : ℤ) := by positivity
    have hj' : (j : ℤ) < q.natAbs := by exact_mod_cast j.isLt
    have huniq : k / (q.natAbs : ℤ) = m * σ ∧ k % (q.natAbs : ℤ) = j :=
      (Int.ediv_emod_unique hrpos).2 ⟨by rw [← h]; ring, hj, hj'⟩
    refine Prod.ext ?_ ?_
    · refine Fin.ext ?_
      have h2 := huniq.2
      rw [← hj₀] at h2
      exact_mod_cast h2.symm
    · show m = σ * (k / (q.natAbs : ℤ))
      rw [huniq.1]
      linear_combination (-m) * hσσ

open scoped TensorProduct.RightActions in

private theorem isTopologicalGroup_units_aux (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (L ⊗[K] v.adicCompletion K)ˣ := by
  haveI := continuousMul_semiLocal K L v
  infer_instance

open scoped TensorProduct.RightActions in

private theorem locallyCompactSpace_units_aux (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ := by
  haveI := isTopologicalGroup_units_aux K L v
  exact (isCompact_integralUnits K L v).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_integralUnits K L v).mem_nhds (integralUnits K L v).one_mem)

private theorem grading_valOneUnitsSubgroup (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : ∀ s : (v.adicCompletion K)ˣ, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ valOneUnits K v) :
    ∀ s : (v.adicCompletion K)ˣ, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ valOneUnitsSubgroup K v := by
  intro s
  have h := hϖ s
  simpa only [← SetLike.mem_coe, coe_valOneUnitsSubgroup] using h

private theorem measurableSet_valOneUnitsSubgroup (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] :
    MeasurableSet (valOneUnitsSubgroup K v : Set (v.adicCompletion K)ˣ) := by
  rw [coe_valOneUnitsSubgroup]
  exact (isClosed_valOneUnits K v).measurableSet

open scoped TensorProduct.RightActions in

private theorem includeUnits_mem_of_mem_valOneUnitsSubgroup (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∀ b ∈ valOneUnitsSubgroup K v, includeUnits K L v b ∈ integralUnits K L v := by
  intro b hb
  rw [← SetLike.mem_coe, coe_valOneUnitsSubgroup] at hb
  exact includeUnits_mem_integralUnits K L v hb

open scoped TensorProduct.RightActions in

private theorem mem_valOneUnitsSubgroup_of_includeUnits_mem (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∀ s : (v.adicCompletion K)ˣ, includeUnits K L v s ∈ integralUnits K L v → s ∈ valOneUnitsSubgroup K v := by
  intro s hs
  rw [← SetLike.mem_coe, coe_valOneUnitsSubgroup]
  exact mem_valOneUnits_of_includeUnits_mem K L v hs

open scoped TensorProduct.RightActions in

private theorem lintegral_normalised_restrict_integralUnits (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
      (μv : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μv.IsHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] (μK : Measure (v.adicCompletion K)ˣ)
    [μK.IsHaarMeasure] (hK : μK (valOneUnits K v) = 1) {E : Set (L ⊗[K] v.adicCompletion K)ˣ} (hE : MeasurableSet E) :
    ∫⁻ s,
        ((μv (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
            μv.restrict (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
          ((fun t => t * includeUnits K L v s) ⁻¹' E) ∂μK =
      (μv (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ * μv (E ∩ saturatedUnits K L v) := by
  haveI := isTopologicalGroup_units_aux K L v
  haveI : μv.IsMulLeftInvariant := ‹μv.IsHaarMeasure›.toIsMulLeftInvariant
  haveI : μK.IsMulLeftInvariant := ‹μK.IsHaarMeasure›.toIsMulLeftInvariant
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hB1 : μK (valOneUnitsSubgroup K v : Set (v.adicCompletion K)ˣ) = 1 := by
    rw [coe_valOneUnitsSubgroup]
    exact hK
  have h := lintegral_normalised_restrict μv μK (includeUnits K L v) (integralUnits K L v)
    (isOpen_integralUnits K L v).measurableSet (valOneUnitsSubgroup K v) (measurableSet_valOneUnitsSubgroup K v) hB1
    (includeUnits_mem_of_mem_valOneUnitsSubgroup K L v) (mem_valOneUnitsSubgroup_of_includeUnits_mem K L v) ϖ
    (grading_valOneUnitsSubgroup K v hϖ) hE
  unfold saturatedUnits
  exact h

open scoped TensorProduct.RightActions in

private theorem measure_mul_sum_lintegral_map_normOne (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
      (μv : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μv.IsHaarMeasure]
    [MeasurableSpace (normOneUnits K L v)] [BorelSpace (normOneUnits K L v)]
    (μN : Measure (normOneUnits K L v)) [μN.IsHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] (μK : Measure (v.adicCompletion K)ˣ)
    [μK.IsHaarMeasure] (hK : μK (valOneUnits K v) = 1) (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : ∀ s : (v.adicCompletion K)ˣ, ∃! m : ℤ, (ϖ ^ m)⁻¹ * s ∈ valOneUnits K v) {r : ℕ}
      (π : Fin r → (L ⊗[K] v.adicCompletion K)ˣ)
    (hπ : ∀ t : (L ⊗[K] v.adicCompletion K)ˣ,
      ∃! p : Fin r × ℤ, (includeUnits K L v ϖ ^ p.2 * π p.1)⁻¹ * t ∈ normOneUnits K L v)
    {E : Set (L ⊗[K] v.adicCompletion K)ˣ} (hE : MeasurableSet E) :
    μv (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) *
        ∑ j, ∫⁻ s, Measure.map (fun t => π j * t) (Measure.map Subtype.val μN)
          ((fun t => t * includeUnits K L v s) ⁻¹' E) ∂μK =
      μN (Subtype.val ⁻¹' (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)) * μv E := by
  haveI := isTopologicalGroup_units_aux K L v
  haveI := locallyCompactSpace_units_aux K L v
  haveI := secondCountableTopology_units K L v
  have hN : IsOpen (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
    rw [coe_normOneUnits]
    exact (isOpen_valued_eq_one K v).preimage (continuous_norm_val K L v)
  have hB1 : μK (valOneUnitsSubgroup K v : Set (v.adicCompletion K)ˣ) = 1 := by
    rw [coe_valOneUnitsSubgroup]
    exact hK
  exact mul_sum_lintegral_map_eq μv (normOneUnits K L v) hN μN μK (includeUnits K L v) (integralUnits K L v)
    (isOpen_integralUnits K L v).measurableSet (integralUnits_le_normOneUnits K L v) (valOneUnitsSubgroup K v)
    (measurableSet_valOneUnitsSubgroup K v) hB1 (includeUnits_mem_of_mem_valOneUnitsSubgroup K L v) ϖ
    (grading_valOneUnitsSubgroup K v hϖ) π hπ hE

open scoped TensorProduct.RightActions in

private theorem map_map_normOne_compl_coset (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
      [MeasurableSpace (normOneUnits K L v)] [BorelSpace (normOneUnits K L v)]
    (μN : Measure (normOneUnits K L v)) (g : (L ⊗[K] v.adicCompletion K)ˣ) :
    Measure.map (fun t => g * t) (Measure.map Subtype.val μN)
        {t : (L ⊗[K] v.adicCompletion K)ˣ | g⁻¹ * t ∈ normOneUnits K L v}ᶜ = 0 := by
  have hN : MeasurableSet (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
    rw [coe_normOneUnits]
    exact ((isClosed_valued_eq_one K v).preimage (continuous_norm_val K L v)).measurableSet
  haveI : ContinuousMul (L ⊗[K] v.adicCompletion K)ˣ := (isTopologicalGroup_units_aux K L v).toContinuousMul
  have hmulinv : Measurable (fun t : (L ⊗[K] v.adicCompletion K)ˣ => g⁻¹ * t) :=
    (continuous_const.mul continuous_id).measurable
  have hmul : Measurable (fun t : (L ⊗[K] v.adicCompletion K)ˣ => g * t) :=
    (continuous_const.mul continuous_id).measurable
  have hS : MeasurableSet {t : (L ⊗[K] v.adicCompletion K)ˣ | g⁻¹ * t ∈ normOneUnits K L v} := hN.preimage hmulinv
  have hval : Measurable (Subtype.val : normOneUnits K L v → (L ⊗[K] v.adicCompletion K)ˣ) :=
    continuous_subtype_val.measurable
  rw [Measure.map_apply hmul hS.compl, Measure.map_apply hval (hS.compl.preimage hmul)]
  convert measure_empty (μ := μN)
  ext n
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, inv_mul_cancel_left, SetLike.coe_mem,
    not_true_eq_false, Set.mem_empty_iff_false]

private theorem exists_measure_eq_mul_lintegral_map_archNormOne (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : InfinitePlace K)
    [MeasurableSpace (∀ w : v.Extension L, w.1.Completion)ˣ] [BorelSpace (∀ w : v.Extension L, w.1.Completion)ˣ]
      (μv : Measure (∀ w : v.Extension L, w.1.Completion)ˣ) [μv.IsHaarMeasure]
    [MeasurableSpace (archNormOneUnits K L v)] [BorelSpace (archNormOneUnits K L v)]
    (μN : Measure (archNormOneUnits K L v)) [μN.IsHaarMeasure]
    [MeasurableSpace (v.Completion)ˣ] [BorelSpace (v.Completion)ˣ] (μK : Measure (v.Completion)ˣ) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ E : Set (∀ w : v.Extension L, w.1.Completion)ˣ, MeasurableSet E →
        μv E = c * ∫⁻ s, Measure.map Subtype.val μN ((fun t => t * includeArchUnits K L v s) ⁻¹' E) ∂μK := by
  haveI : Finite (v.Extension L) := finite_archExtension K L v
  haveI : SecondCountableTopology (∀ w : v.Extension L, w.1.Completion)ˣ := secondCountableTopology_archUnits_aux K L v
  haveI : SecondCountableTopology (v.Completion)ˣ := by
    haveI := secondCountableTopology_completion K v
    exact secondCountableTopology_units_of _
  haveI : LocallyCompactSpace (archNormOneUnits K L v) := (isClosed_archNormOneUnits_aux K L v).locallyCompactSpace
  haveI : SecondCountableTopology (archNormOneUnits K L v) :=
    inferInstanceAs (SecondCountableTopology (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ))
  have hF : Continuous (fun p : (v.Completion)ˣ × archNormOneUnits K L v =>
      ((p.2 : (∀ w : v.Extension L, w.1.Completion)ˣ)) * includeArchUnits K L v p.1) :=
    (continuous_subtype_val.comp continuous_snd).mul ((continuous_includeArchUnits K L v).comp continuous_fst)
  have hproper := (isProperMap_iff_tendsto_cocompact.1
    (isProperMap_iff_isCompact_preimage.2 ⟨hF, fun _ hC => isCompact_preimage_archProduct K L v hC⟩)).2
  exact exists_measure_eq_mul_lintegral_map_of_proper μv (archNormOneUnits K L v) μN μK (includeArchUnits K L v)
    (continuous_includeArchUnits K L v) (surjective_archProduct K L v) hproper

open scoped TensorProduct.RightActions in

private theorem prod_absNorm_zpow_log_valued_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]
    (t : (L ⊗[K] v.adicCompletion K)ˣ) :
    ∏ w : v.Extension (𝓞 L),
        (Ideal.absNorm w.1.asIdeal : ℝ) ^ WithZero.log
          (Valued.v (AutomorphicForm.semiLocalHomeomorph K L v (t : L ⊗[K] v.adicCompletion K) w)) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log
        (Valued.v (Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K))) := by
  simp only [semiLocalHomeomorph_eq_semiLocalPiEquiv]
  rw [log_valued_norm_eq_sum K L v t, zpow_sum_of_ne_zero _ _ (absNorm_asIdeal_ne_zero K v)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [absNorm_extension_eq_pow K L v w, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]

private theorem prod_absNorm_zpow_log_valued_eq_one_of_mem_normOneUnits (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype (v.Extension (𝓞 L))] {t : (L ⊗[K] v.adicCompletion K)ˣ} (ht : t ∈ normOneUnits K L v) :
    ∏ w : v.Extension (𝓞 L),
        (Ideal.absNorm w.1.asIdeal : ℝ) ^ WithZero.log
          (Valued.v (AutomorphicForm.semiLocalHomeomorph K L v (t : L ⊗[K] v.adicCompletion K) w)) = 1 := by
  have h0 : normLog K L v t = 0 := (mem_normOneUnits_iff_normLog K L v t).1 ht
  rw [prod_absNorm_zpow_log_valued_eq K L v t]
  change (Ideal.absNorm v.asIdeal : ℝ) ^ normLog K L v t = 1
  rw [h0, zpow_zero]

private theorem archNorm_norm_self (F : Type) [Field F] (y : F) : Algebra.norm F y = y := by
  simp

private theorem archNorm_norm_map {A B F : Type} [NormedField A] [NormedField B] [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Isometry f) (a : A) : ‖f a‖ = ‖a‖ := by
  rw [← dist_zero_right, ← map_zero f, hf.dist_eq, dist_zero_right]

private theorem archNorm_norm_norm_eq {A₁ B₁ A₂ B₂ : Type} [NormedField A₁] [Field B₁] [NormedField A₂] [Field B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp (e₁ : A₁ →+* A₂) = (e₂ : B₁ →+* B₂).comp (algebraMap A₁ B₁))
    (h₁ : ∀ a, ‖e₁ a‖ = ‖a‖) (x : B₁) : ‖Algebra.norm A₁ x‖ = ‖Algebra.norm A₂ (e₂ x)‖ := by
  rw [Algebra.norm_eq_of_equiv_equiv e₁ e₂ he x, ← h₁ (e₁.symm (Algebra.norm A₂ (e₂ x))),
    RingEquiv.apply_symm_apply]

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem archNorm_finite (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) (w : v.Extension L) : Module.Finite v.Completion w.1.Completion := by
  by_cases hun : w.1.IsUnramified K
  · exact Module.finite_of_finrank_eq_succ (NumberField.InfinitePlace.Completion.finrank_eq_one_of_isUnramified v hun)
  · exact Module.finite_of_finrank_eq_succ (NumberField.InfinitePlace.Completion.finrank_eq_two_of_isRamified v hun)

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem archNorm_norm_pow_mult_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) (w : v.Extension L) (x : w.1.Completion) :
    ‖x‖ ^ w.1.mult = ‖Algebra.norm v.Completion x‖ ^ v.mult := by
  have hcomap : w.1.comap (algebraMap K L) = v := w.2
  by_cases hun : w.1.IsUnramified K
  · have hmult : v.mult = w.1.mult := by simpa [hcomap] using hun.eq
    rw [← hmult]
    congr 1
    rcases v.isReal_or_isComplex with hv | hv
    · have hw : w.1.IsReal := hun.liesOver_isReal_over _ _ hv
      have := NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w.1 hv
      rw [archNorm_norm_norm_eq (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by simp)
          (archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
            (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv)) x,
        archNorm_norm_self, archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw) x]
    · have hw : w.1.IsComplex := NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under _ hv
      cases NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w.1 v with
      | inl hl =>
        have : NumberField.ComplexEmbedding.LiesOver w.1.embedding v.embedding := ⟨hl⟩
        have := NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding w.1 v
        rw [archNorm_norm_norm_eq (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
            (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (by ext; simp)
            (archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
              (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v)) x,
          archNorm_norm_self, archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
            (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1) x]
      | inr hr =>
        have : NumberField.ComplexEmbedding.LiesOver (NumberField.ComplexEmbedding.conjugate w.1.embedding)
            v.embedding := ⟨hr⟩
        have := NumberField.InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding w.1 v
        rw [archNorm_norm_norm_eq (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
            ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).trans (starRingAut (R := ℂ)))
            (by ext; simp [← NumberField.ComplexEmbedding.conjugate_coe_eq])
            (archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
              (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v)) x,
          archNorm_norm_self, RingEquiv.trans_apply, starRingAut_apply, norm_star,
          archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
            (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1) x]
  · obtain ⟨hw, hv'⟩ := NumberField.InfinitePlace.isRamified_iff.mp hun
    have hv : v.IsReal := hcomap ▸ hv'
    rw [NumberField.InfinitePlace.mult_isComplex ⟨w.1, hw⟩, NumberField.InfinitePlace.mult_isReal ⟨v, hv⟩, pow_one]
    have := NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w.1 hv
    rw [archNorm_norm_norm_eq (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (by ext; simp)
        (archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
          (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv)) x,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
      archNorm_norm_map (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1) x, norm_pow, norm_norm]

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

private theorem prod_norm_pow_mult_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) [Fintype (v.Extension L)] (t : (∀ w : v.Extension L, w.1.Completion)ˣ) :
    ∏ w : v.Extension L, ‖((t : ∀ w : v.Extension L, w.1.Completion)) w‖ ^ w.1.mult =
      normHom (Algebra.norm v.Completion (t : ∀ w : v.Extension L, w.1.Completion)) ^ v.mult := by
  haveI : ∀ w : v.Extension L, Module.Finite v.Completion w.1.Completion := fun w => archNorm_finite K L v w
  letI : LinearOrder (v.Extension L) :=
    LinearOrder.lift' (Fintype.equivFin (v.Extension L)) (Fintype.equivFin (v.Extension L)).injective
  rw [norm_pi_eq_prod (fun w : v.Extension L => w.1.Completion), map_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun w _ => by
    rw [normHom_apply]
    exact archNorm_norm_pow_mult_eq K L v w _

open scoped TensorProduct.RightActions in

private theorem isClosed_normOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  rw [coe_normOneUnits]
  exact (isClosed_valued_eq_one K v).preimage (continuous_norm_val K L v)

open scoped TensorProduct.RightActions in

private theorem isOpen_normOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  rw [coe_normOneUnits]
  exact (isOpen_valued_eq_one K v).preimage (continuous_norm_val K L v)

private theorem isClosed_archNormOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : InfinitePlace K) :
    IsClosed (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ) := by
  exact isClosed_archNormOneUnits_aux K L v

open scoped TensorProduct.RightActions in

private theorem isTopologicalGroup_units (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsTopologicalGroup (L ⊗[K] v.adicCompletion K)ˣ := by
  exact isTopologicalGroup_units_aux K L v

open scoped TensorProduct.RightActions in

private theorem locallyCompactSpace_units (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ := by
  exact locallyCompactSpace_units_aux K L v

open scoped TensorProduct.RightActions in

private theorem t2Space_units (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    T2Space (L ⊗[K] v.adicCompletion K)ˣ := by
  haveI := t2Space_semiLocal K L v
  infer_instance

private theorem isTopologicalGroup_archUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : InfinitePlace K) :
    IsTopologicalGroup (∀ w : v.Extension L, w.1.Completion)ˣ := by
  infer_instance

private theorem locallyCompactSpace_archUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (v : InfinitePlace K) :
    LocallyCompactSpace (∀ w : v.Extension L, w.1.Completion)ˣ := by
  infer_instance

private theorem t2Space_archUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    T2Space (∀ w : v.Extension L, w.1.Completion)ˣ := by
  infer_instance

private theorem semiLocalHomeomorph_semiLocalEval_apply (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L v (AutomorphicForm.semiLocalEval K L v x) w =
      AdelicLevel.finAdeleEval (𝓞 L) L w.1 x := by
  show (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v)
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (RingHom.pi (fun u : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L u.1) x)) w = _
  erw [AlgEquiv.apply_symm_apply]
  rfl

end TransversalMeasure

namespace Transversal
namespace Product

private theorem mem_levelSubgroup_iff {B α κ : Type*} [Group B] {A : α → Type*} [∀ a, Group (A a)]
    {G : κ → Type*} [∀ k, Group (G k)] (q : ∀ a, B →* A a) (NA : ∀ a, Subgroup (A a)) (p : ∀ k, B →* G k)
    (N U : ∀ k, Subgroup (G k)) (bad : Finset κ) (b : B) :
    b ∈ levelSubgroup q NA p N U bad ↔ (∀ a, q a b ∈ NA a) ∧ (∀ k ∈ bad, p k b ∈ N k) ∧ ∀ k ∉ bad, p k b ∈ U k :=
  Iff.rfl

private theorem lintegral_fin_prod_eq_prod {n : ℕ} {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (h : ∀ i, X i → ENNReal) (hh : ∀ i, Measurable (h i)) :
    ∫⁻ x, ∏ i, h i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, h i y ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : X 0 × (∀ i : Fin n, X (Fin.succ i)), h 0 x.1 * ∏ i : Fin n, h (Fin.succ i) (x.2 i)
              ∂((μ 0).prod (Measure.pi fun i => μ i.succ)) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ,
            Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
          rfl
        _ = (∫⁻ y, h 0 y ∂μ 0) * ∏ i : Fin n, ∫⁻ y, h (Fin.succ i) y ∂μ i.succ := by
          rw [← ih (fun i => μ i.succ) (fun i => h i.succ) (fun i => hh i.succ)]
          exact lintegral_prod_mul (hh 0).aemeasurable
            (Finset.measurable_prod _ fun (i : Fin n) _ => (hh i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ y, h i y ∂μ i := by rw [Fin.prod_univ_succ]

private theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (h : ∀ i, X i → ENNReal)
    (hh : ∀ i, Measurable (h i)) : ∫⁻ x, ∏ i, h i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, h i y ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod_eq_prod (fun i => μ (e i)) (fun i => h (e i)) fun i => hh (e i)

private theorem lintegral_inv_smul_restrict_eq_lintegral_haarMeasure_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (U : Subgroup G) (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) (f : G → ENNReal)
    (hf : Measurable f) :
    haveI : CompactSpace U := isCompact_iff_compactSpace.1 hUc
    ∫⁻ x, f x ∂((μ (U : Set G))⁻¹ • μ.restrict (U : Set G)) =
      ∫⁻ z, f (z : G) ∂(Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts U)) := by
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hUc
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  have hemb : Topology.IsOpenEmbedding (U.subtype : U → G) := hUo.isOpenEmbedding_subtypeVal
  have hme : MeasurableEmbedding ((↑) : U → G) := by
    have h := hemb.measurableEmbedding
    rwa [Subgroup.coe_subtype] at h
  set lam : Measure U := μ.comap ((↑) : U → G) with hlam
  haveI : lam.IsHaarMeasure := by
    have h := Measure.IsHaarMeasure.comap (mH := inferInstance) μ hemb
    rwa [Subgroup.coe_subtype] at h
  set ν : Measure U := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts U) with hν
  have huniq := Measure.isMulLeftInvariant_eq_smul lam ν
  have hint : ∀ g : U → ENNReal,
      ∫⁻ z, g z ∂lam = (Measure.haarScalarFactor lam ν : ENNReal) * ∫⁻ z, g z ∂ν := fun g => by
    conv_lhs => rw [huniq]
    rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hνtop : ν Set.univ = 1 := by
    rw [hν, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self
  have hlamU : lam Set.univ = μ (U : Set G) := by
    rw [hlam, hme.comap_apply, Set.image_univ, Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
  have hsub : ∫⁻ z, f (z : G) ∂lam = ∫⁻ x in (U : Set G), f x ∂μ := by
    rw [← lintegral_map hf hme.measurable, hlam, hme.map_comap, Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
  have hdU : (Measure.haarScalarFactor lam ν : ENNReal) = μ (U : Set G) := by
    have h := hint fun _ => 1
    simp only [lintegral_const, one_mul, hνtop, mul_one] at h
    rw [hlamU] at h
    exact h.symm
  have hU0 : μ (U : Set G) ≠ 0 := (hUo.measure_pos μ ⟨1, U.one_mem⟩).ne'
  have hUtop : μ (U : Set G) ≠ ⊤ := hUc.measure_lt_top.ne
  rw [lintegral_smul_measure, smul_eq_mul, ← hsub, hint, hdU, ← mul_assoc, ENNReal.inv_mul_cancel hU0 hUtop,
    one_mul]

private theorem isClosed_levelSubgroup
    {B α κ : Type*} [Group B] [TopologicalSpace B] {A : α → Type*} [∀ a, Group (A a)]
    [∀ a, TopologicalSpace (A a)] {G : κ → Type*} [∀ k, Group (G k)] [∀ k, TopologicalSpace (G k)]
    [∀ k, T2Space (G k)]
    (q : ∀ a, B →* A a) (hq : ∀ a, Continuous (q a)) (NA : ∀ a, Subgroup (A a))
    (hNA : ∀ a, IsClosed (NA a : Set (A a)))
    (p : ∀ k, B →* G k) (hp : ∀ k, Continuous (p k)) (N U : ∀ k, Subgroup (G k)) (bad : Finset κ)
    (hN : ∀ k ∈ bad, IsClosed (N k : Set (G k))) (hU : ∀ k ∉ bad, IsCompact (U k : Set (G k))) :
    IsClosed (levelSubgroup q NA p N U bad : Set B) := by
  have hset : (levelSubgroup q NA p N U bad : Set B) =
      (⋂ a, q a ⁻¹' (NA a : Set (A a))) ∩ ((⋂ k ∈ bad, p k ⁻¹' (N k : Set (G k))) ∩
        ⋂ (k) (_ : k ∉ bad), p k ⁻¹' (U k : Set (G k))) := by
    ext b
    simp only [SetLike.mem_coe, mem_levelSubgroup_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact (isClosed_iInter fun a => (hNA a).preimage (hq a)).inter
    ((isClosed_biInter fun k hk => (hN k hk).preimage (hp k)).inter
      (isClosed_iInter fun k => isClosed_iInter fun hk => (hU k hk).isClosed.preimage (hp k)))

private theorem map_mul_subtype_apply_compl_image_eq_zero
    {B α κ : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B]
    {A : α → Type*} [∀ a, Group (A a)] [∀ a, TopologicalSpace (A a)]
    {G : κ → Type*} [∀ k, Group (G k)] [∀ k, TopologicalSpace (G k)] [∀ k, T2Space (G k)]
    (q : ∀ a, B →* A a) (hq : ∀ a, Continuous (q a)) (NA : ∀ a, Subgroup (A a))
    (hNA : ∀ a, IsClosed (NA a : Set (A a)))
    (p : ∀ k, B →* G k) (hp : ∀ k, Continuous (p k)) (N U : ∀ k, Subgroup (G k)) (bad : Finset κ)
    (hN : ∀ k ∈ bad, IsClosed (N k : Set (G k))) (hU : ∀ k ∉ bad, IsCompact (U k : Set (G k)))
    (η : Measure ↥(levelSubgroup q NA p N U bad)) (π : B) :
    Measure.map (fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B)) η
        ((fun b : B => π * b) '' (levelSubgroup q NA p N U bad : Set B))ᶜ = 0 := by
  have hM : IsClosed (levelSubgroup q NA p N U bad : Set B) := isClosed_levelSubgroup q hq NA hNA p hp N U bad hN hU
  have hmeasT : Measurable fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B) :=
    (measurable_const_mul π).comp measurable_subtype_coe
  have himg : IsClosed ((fun b : B => π * b) '' (levelSubgroup q NA p N U bad : Set B)) :=
    (Homeomorph.mulLeft π).isClosedMap _ hM
  rw [Measure.map_apply hmeasT himg.measurableSet.compl]
  convert measure_empty (μ := η)
  ext m
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_image, SetLike.mem_coe, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact ⟨m, m.2, rfl⟩

private theorem isFiniteMeasureOnCompacts_map_mul_subtype
    {B α κ : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [T2Space B]
    [MeasurableSpace B] [BorelSpace B]
    {A : α → Type*} [∀ a, Group (A a)] [∀ a, TopologicalSpace (A a)]
    {G : κ → Type*} [∀ k, Group (G k)] [∀ k, TopologicalSpace (G k)] [∀ k, T2Space (G k)]
    (q : ∀ a, B →* A a) (hq : ∀ a, Continuous (q a)) (NA : ∀ a, Subgroup (A a))
    (hNA : ∀ a, IsClosed (NA a : Set (A a)))
    (p : ∀ k, B →* G k) (hp : ∀ k, Continuous (p k)) (N U : ∀ k, Subgroup (G k)) (bad : Finset κ)
    (hN : ∀ k ∈ bad, IsClosed (N k : Set (G k))) (hU : ∀ k ∉ bad, IsCompact (U k : Set (G k)))
    (η : Measure ↥(levelSubgroup q NA p N U bad)) [η.IsHaarMeasure] (π : B) :
    IsFiniteMeasureOnCompacts (Measure.map (fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B)) η) := by
  have hM : IsClosed (levelSubgroup q NA p N U bad : Set B) := isClosed_levelSubgroup q hq NA hNA p hp N U bad hN hU
  have hT : Continuous fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B) :=
    (continuous_const_mul π).comp continuous_subtype_val
  refine ⟨fun K hK => ?_⟩
  rw [Measure.map_apply hT.measurable hK.measurableSet]
  refine IsCompact.measure_lt_top ?_
  have hK' : IsCompact ((fun b : B => π⁻¹ * b) '' K) := hK.image (continuous_const_mul _)
  have hpre : (fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B)) ⁻¹' K =
      ((↑) : ↥(levelSubgroup q NA p N U bad) → B) ⁻¹' ((fun b : B => π⁻¹ * b) '' K) := by
    ext m
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h; exact ⟨_, h, by group⟩
    · rintro ⟨b, hb, hbm⟩; have : π * (m : B) = b := by rw [← hbm]; group
      rwa [this]
  rw [hpre]
  exact hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK'

private theorem exists_lintegral_prod_mul_prod_eq
    {B α κ : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [T2Space B]
    [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    [Fintype α] [Nonempty α] {A : α → Type*} [∀ a, Group (A a)] [∀ a, TopologicalSpace (A a)]
    [∀ a, IsTopologicalGroup (A a)] [∀ a, LocallyCompactSpace (A a)] [∀ a, T2Space (A a)]
    [∀ a, SecondCountableTopology (A a)] [∀ a, MeasurableSpace (A a)] [∀ a, BorelSpace (A a)]
    {G : κ → Type*} [∀ k, Group (G k)] [∀ k, TopologicalSpace (G k)] [∀ k, IsTopologicalGroup (G k)]
    [∀ k, LocallyCompactSpace (G k)] [∀ k, T2Space (G k)] [∀ k, SecondCountableTopology (G k)]
    [∀ k, MeasurableSpace (G k)] [∀ k, BorelSpace (G k)] [DecidableEq κ]
    (q : ∀ a, B →* A a) (hq : ∀ a, Continuous (q a)) (NA : ∀ a, Subgroup (A a))
    (hNA : ∀ a, IsClosed (NA a : Set (A a)))
    (p : ∀ k, B →* G k) (hp : ∀ k, Continuous (p k)) (N U : ∀ k, Subgroup (G k)) (bad : Finset κ)
    (hN : ∀ k ∈ bad, IsClosed (N k : Set (G k))) (hU : ∀ k ∉ bad, IsCompact (U k : Set (G k)))
    (hU' : ∀ k ∉ bad, IsOpen (U k : Set (G k)))
    (hsurj : ∀ (Sf : Finset κ) (y : ∀ a, A a) (x : ∀ k, G k), (∀ k ∉ Sf, x k ∈ U k) →
      ∃ b : B, (∀ a, q a b = y a) ∧ ∀ k, p k b = x k)
    (hbox : ∀ (D : ∀ a, Set (A a)) (C : ∀ k, Set (G k)), (∀ a, IsCompact (D a)) → (∀ k, IsCompact (C k)) →
      {k | C k ≠ (U k : Set (G k))}.Finite → IsCompact {b : B | (∀ a, q a b ∈ D a) ∧ ∀ k, p k b ∈ C k})
    (η : Measure ↥(levelSubgroup q NA p N U bad)) [η.IsHaarMeasure] :
    ∃ (μA : ∀ a, Measure ↥(NA a)) (μN : ∀ k, Measure ↥(N k)) (μ : ∀ k, Measure (G k)),
      (∀ a, (μA a).IsHaarMeasure) ∧ (∀ k ∈ bad, (μN k).IsHaarMeasure) ∧ (∀ k, (μ k).IsHaarMeasure) ∧
      ∀ (π : B), (∀ a, q a π = 1) → (∀ k ∉ bad, p k π = 1) →
      ∀ (Sf : Finset κ), bad ⊆ Sf → ∀ (g : ∀ a, A a → ENNReal) (f : ∀ k, G k → ENNReal),
        (∀ a, Measurable (g a)) → (∀ k, Measurable (f k)) →
        ∫⁻ b, (∏ a, g a (q a b)) * ∏ k ∈ Sf, f k (p k b)
            ∂(Measure.map (fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B)) η) =
          (∏ a, ∫⁻ x, g a x ∂(Measure.map ((↑) : ↥(NA a) → A a) (μA a))) *
            ((∏ k ∈ bad, ∫⁻ x, f k x
                ∂(Measure.map (fun x : G k => p k π * x) (Measure.map ((↑) : ↥(N k) → G k) (μN k)))) *
              ∏ k ∈ Sf \ bad, ∫⁻ x, f k x
                ∂(((μ k) (U k : Set (G k)))⁻¹ • (μ k).restrict (U k : Set (G k)))) := by
  classical

  haveI hA_lc : ∀ a, LocallyCompactSpace ↥(NA a) := fun a => (hNA a).locallyCompactSpace
  haveI hN_lc : ∀ k : ↥bad, LocallyCompactSpace ↥(N (k : κ)) := fun k => (hN k k.2).locallyCompactSpace
  have hU_cs : ∀ (Sf : Finset κ) (k : ↥(Sf \ bad)), CompactSpace ↥(U (k : κ)) := fun Sf k =>
    isCompact_iff_compactSpace.1 (hU k (Finset.mem_sdiff.1 k.2).2)
  have hM : IsClosed (levelSubgroup q NA p N U bad : Set B) := isClosed_levelSubgroup q hq NA hNA p hp N U bad hN hU
  haveI : LocallyCompactSpace ↥(levelSubgroup q NA p N U bad) := hM.locallyCompactSpace
  haveI hA_sc : ∀ a, SecondCountableTopology ↥(NA a) := fun a =>
    TopologicalSpace.Subtype.secondCountableTopology (NA a : Set (A a))
  haveI hN_sc : ∀ k : ↥bad, SecondCountableTopology ↥(N (k : κ)) := fun k =>
    TopologicalSpace.Subtype.secondCountableTopology (N (k : κ) : Set (G k))
  have hU_sc : ∀ (Sf : Finset κ) (k : ↥(Sf \ bad)), SecondCountableTopology ↥(U (k : κ)) := fun Sf k =>
    TopologicalSpace.Subtype.secondCountableTopology (U (k : κ) : Set (G k))

  set haarA : ∀ a, Measure ↥(NA a) := fun a => Measure.haar with hhaarA
  set haarN : ∀ k : ↥bad, Measure ↥(N (k : κ)) := fun k => Measure.haar with hhaarN

  have core : ∀ Sf : Finset κ, bad ⊆ Sf → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ (π : B), (∀ a, q a π = 1) → (∀ k ∉ bad, p k π = 1) →
      ∀ (g : ∀ a, A a → ENNReal) (f : ∀ k, G k → ENNReal), (∀ a, Measurable (g a)) → (∀ k, Measurable (f k)) →
        ∫⁻ b, (∏ a, g a (q a b)) * ∏ k ∈ Sf, f k (p k b)
            ∂(Measure.map (fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B)) η) =
          c * ((∏ a, ∫⁻ y, g a (y : A a) ∂haarA a) *
            ((∏ k : ↥bad, ∫⁻ y, f k (p k π * (y : G k)) ∂haarN k) *
              ∏ k : ↥(Sf \ bad), haveI := hU_cs Sf k;
                ∫⁻ z, f k (z : G k) ∂(Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ)))))) := by
    intro Sf hSf
    haveI := hU_cs Sf
    haveI := hU_sc Sf

    let H := (∀ a, ↥(NA a)) × ((∀ k : ↥bad, ↥(N (k : κ))) × (∀ k : ↥(Sf \ bad), ↥(U (k : κ))))
    have memN : ∀ (m : ↥(levelSubgroup q NA p N U bad)) (k : ↥bad), p k (m : B) ∈ N (k : κ) := fun m k =>
      ((mem_levelSubgroup_iff q NA p N U bad m).1 m.2).2.1 k k.2
    have memU : ∀ (m : ↥(levelSubgroup q NA p N U bad)) (k : ↥(Sf \ bad)), p k (m : B) ∈ U (k : κ) := fun m k =>
      ((mem_levelSubgroup_iff q NA p N U bad m).1 m.2).2.2 k (Finset.mem_sdiff.1 k.2).2
    have memA : ∀ (m : ↥(levelSubgroup q NA p N U bad)) (a : α), q a (m : B) ∈ NA a := fun m a =>
      ((mem_levelSubgroup_iff q NA p N U bad m).1 m.2).1 a
    let φ : ↥(levelSubgroup q NA p N U bad) →* H :=
      { toFun := fun m => (fun a => ⟨q a m, memA m a⟩, (fun k => ⟨p k m, memN m k⟩, fun k => ⟨p k m, memU m k⟩))
        map_one' := by
          refine Prod.ext (funext fun a => Subtype.ext ?_)
            (Prod.ext (funext fun k => Subtype.ext ?_) (funext fun k => Subtype.ext ?_)) <;>
          simp only [OneMemClass.coe_one, map_one, Prod.fst_one, Prod.snd_one, Pi.one_apply]
        map_mul' := fun m m' =>
          Prod.ext (funext fun a => Subtype.ext (by simp only [MulMemClass.coe_mul, map_mul]; rfl))
            (Prod.ext (funext fun k => Subtype.ext (by simp only [MulMemClass.coe_mul, map_mul]; rfl))
              (funext fun k => Subtype.ext (by simp only [MulMemClass.coe_mul, map_mul]; rfl))) }
    have hφ_apply : ∀ m,
        φ m = (fun a => ⟨q a m, memA m a⟩, (fun k => ⟨p k m, memN m k⟩, fun k => ⟨p k m, memU m k⟩)) :=
      fun m => rfl
    have hφc : Continuous φ := by
      refine continuous_prodMk.2 ⟨continuous_pi fun a => ?_, continuous_prodMk.2 ⟨continuous_pi fun k => ?_,
        continuous_pi fun k => ?_⟩⟩
      · exact ((hq a).comp continuous_subtype_val).subtype_mk _
      · exact ((hp k).comp continuous_subtype_val).subtype_mk _
      · exact ((hp k).comp continuous_subtype_val).subtype_mk _
    have hφs : Function.Surjective φ := by
      rintro ⟨y, z, u⟩
      let x : ∀ k, G k := fun k =>
        if hk : k ∈ bad then (z ⟨k, hk⟩ : G k) else if hk' : k ∈ Sf then (u ⟨k, Finset.mem_sdiff.2 ⟨hk', hk⟩⟩ : G k)
          else 1
      obtain ⟨b, hbA, hb⟩ := hsurj Sf (fun a => (y a : A a)) x fun k hk => by
        have hkb : k ∉ bad := fun h => hk (hSf h)
        simp only [x, dif_neg hkb, dif_neg hk]; exact one_mem _
      have hbM : b ∈ levelSubgroup q NA p N U bad := by
        refine (mem_levelSubgroup_iff q NA p N U bad b).2 ⟨fun a => ?_, fun k hk => ?_, fun k hk => ?_⟩
        · rw [hbA]; exact (y a).2
        · rw [hb]; simp only [x, dif_pos hk]; exact (z ⟨k, hk⟩).2
        · rw [hb]; by_cases hk' : k ∈ Sf
          · simp only [x, dif_neg hk, dif_pos hk']; exact (u ⟨k, _⟩).2
          · simp only [x, dif_neg hk, dif_neg hk']; exact one_mem _
      refine ⟨⟨b, hbM⟩, ?_⟩
      rw [hφ_apply]
      refine Prod.ext (funext fun a => Subtype.ext (by simp [hbA])) (Prod.ext (funext fun k => Subtype.ext ?_)
        (funext fun k => Subtype.ext ?_))
      · simp [hb, x, k.2]
      · have hk := Finset.mem_sdiff.1 k.2
        simp [hb, x, hk.1, hk.2]
    have hφp : Filter.Tendsto φ (Filter.cocompact _) (Filter.cocompact _) := by
      refine (Filter.hasBasis_cocompact.tendsto_right_iff).2 fun K hK => ?_

      have hpre : IsCompact (φ ⁻¹' K) := by
        let D : ∀ a, Set (A a) := fun a => Subtype.val '' ((fun w : ∀ a, ↥(NA a) => w a) '' (Prod.fst '' K))
        let C : ∀ k, Set (G k) := fun k =>
          if hk : k ∈ bad then
            Subtype.val '' ((fun w : ∀ j : ↥bad, ↥(N (j : κ)) => w ⟨k, hk⟩) '' (Prod.fst '' (Prod.snd '' K)))
          else if hk' : k ∈ Sf then
            Subtype.val '' ((fun w : ∀ j : ↥(Sf \ bad), ↥(U (j : κ)) => w ⟨k, Finset.mem_sdiff.2 ⟨hk', hk⟩⟩) ''
              (Prod.snd '' (Prod.snd '' K)))
          else (U k : Set (G k))
        have hD : ∀ a, IsCompact (D a) := fun a =>
          ((hK.image continuous_fst).image (continuous_apply a)).image continuous_subtype_val
        have hC : ∀ k, IsCompact (C k) := by
          intro k
          by_cases hk : k ∈ bad
          · simp only [C, dif_pos hk]
            exact (((hK.image continuous_snd).image continuous_fst).image
              (continuous_apply (⟨k, hk⟩ : ↥bad))).image continuous_subtype_val
          · by_cases hk' : k ∈ Sf
            · simp only [C, dif_neg hk, dif_pos hk']
              exact (((hK.image continuous_snd).image continuous_snd).image
                (continuous_apply (⟨k, Finset.mem_sdiff.2 ⟨hk', hk⟩⟩ : ↥(Sf \ bad)))).image continuous_subtype_val
            · simp only [C, dif_neg hk, dif_neg hk']; exact hU k hk
        have hfin : {k | C k ≠ (U k : Set (G k))}.Finite := by
          refine (Sf.finite_toSet).subset fun k hk => ?_
          by_contra hkSf
          have hkb : k ∉ bad := fun h => hkSf (hSf h)
          exact hk (by simp only [C, dif_neg hkb, dif_neg (show k ∉ Sf from hkSf)])
        have hbig := hbox D C hD hC hfin
        have hsub : φ ⁻¹' K ⊆ ((↑) : ↥(levelSubgroup q NA p N U bad) → B) ⁻¹'
            {b : B | (∀ a, q a b ∈ D a) ∧ ∀ k, p k b ∈ C k} := by
          intro m hm
          refine ⟨fun a => ⟨⟨q a m, memA m a⟩, ⟨(φ m).1, ⟨φ m, hm, rfl⟩, rfl⟩, rfl⟩, fun k => ?_⟩
          by_cases hk : k ∈ bad
          · simp only [C, dif_pos hk]
            exact ⟨⟨p k m, memN m ⟨k, hk⟩⟩, ⟨(φ m).2.1, ⟨(φ m).2, ⟨φ m, hm, rfl⟩, rfl⟩, rfl⟩, rfl⟩
          · by_cases hk' : k ∈ Sf
            · simp only [C, dif_neg hk, dif_pos hk']
              exact ⟨⟨p k m, memU m ⟨k, Finset.mem_sdiff.2 ⟨hk', hk⟩⟩⟩,
                ⟨(φ m).2.2, ⟨(φ m).2, ⟨φ m, hm, rfl⟩, rfl⟩, rfl⟩, rfl⟩
            · simp only [C, dif_neg hk, dif_neg hk']
              exact ((mem_levelSubgroup_iff q NA p N U bad m).1 m.2).2.2 k hk
        exact (hM.isClosedEmbedding_subtypeVal.isCompact_preimage hbig).of_isClosed_subset
          (hK.isClosed.preimage hφc) hsub
      exact Filter.mem_of_superset hpre.compl_mem_cocompact fun x hx => hx
    haveI : (Measure.map φ η).IsHaarMeasure := Measure.isHaarMeasure_map (μ := η) φ hφc hφs hφp

    set ρ : Measure H := (Measure.pi haarA).prod ((Measure.pi haarN).prod
      (Measure.pi fun k : ↥(Sf \ bad) => Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ)))))
      with hρ
    haveI hHA : (Measure.pi haarA).IsHaarMeasure := inferInstance
    haveI hHN : (Measure.pi haarN).IsHaarMeasure := inferInstance
    haveI hHU : (Measure.pi fun k : ↥(Sf \ bad) =>
        Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ)))).IsHaarMeasure := inferInstance
    haveI hHNU : ((Measure.pi haarN).prod (Measure.pi fun k : ↥(Sf \ bad) =>
        Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ))))).IsHaarMeasure := inferInstance
    haveI : ρ.IsHaarMeasure := by rw [hρ]; infer_instance
    set c := Measure.haarScalarFactor (Measure.map φ η) ρ with hc
    have huniq : Measure.map φ η = c • ρ := Measure.isMulLeftInvariant_eq_smul _ _
    refine ⟨c, ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ENNReal.coe_ne_top,
      fun π hπA hπ g f hg hf => ?_⟩
    have hT : Measurable fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B) :=
      ((continuous_const_mul π).comp continuous_subtype_val).measurable

    let Φ : H → ENNReal := fun w =>
      (∏ a, g a (w.1 a : A a)) * ((∏ k : ↥bad, f k (p k π * (w.2.1 k : G k))) * ∏ k : ↥(Sf \ bad), f k (w.2.2 k : G k))
    have hΦ : Measurable Φ := by
      refine (Finset.measurable_prod _ fun (a : α) _ => ?_).mul
        ((Finset.measurable_prod _ fun (k : ↥bad) _ => ?_).mul
          (Finset.measurable_prod _ fun (k : ↥(Sf \ bad)) _ => ?_))
      · exact (hg a).comp (measurable_subtype_coe.comp ((measurable_pi_apply a).comp measurable_fst))
      · exact ((hf k).comp (measurable_const_mul _)).comp
          (measurable_subtype_coe.comp ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)))
      · exact (hf k).comp
          (measurable_subtype_coe.comp ((measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)))
    have hF : Measurable fun b : B => (∏ a, g a (q a b)) * ∏ k ∈ Sf, f k (p k b) :=
      (Finset.measurable_prod _ fun (a : α) _ => (hg a).comp (hq a).measurable).mul
        (Finset.measurable_prod _ fun (k : κ) _ => (hf k).comp (hp k).measurable)
    have hpt : ∀ m : ↥(levelSubgroup q NA p N U bad),
        (∏ a, g a (q a (π * (m : B)))) * ∏ k ∈ Sf, f k (p k (π * (m : B))) = Φ (φ m) := by
      intro m
      have h1 : ∏ a, g a (q a (π * (m : B))) = ∏ a, g a (q a (m : B)) :=
        Finset.prod_congr rfl fun a _ => by rw [map_mul, hπA, one_mul]
      have h2 : ∏ k ∈ Sf, f k (p k (π * (m : B))) =
          (∏ k ∈ bad, f k (p k π * p k (m : B))) * ∏ k ∈ Sf \ bad, f k (p k (m : B)) := by
        rw [← Finset.prod_sdiff hSf, mul_comm]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => by rw [map_mul])
          (Finset.prod_congr rfl fun k hk => by rw [map_mul, hπ k (Finset.mem_sdiff.1 hk).2, one_mul])
      rw [h1, h2, ← Finset.prod_coe_sort bad fun k => f k (p k π * p k (m : B)),
        ← Finset.prod_coe_sort (Sf \ bad) fun k => f k (p k (m : B))]
      simp only [Φ, hφ_apply]
    rw [lintegral_map hF hT]
    simp_rw [hpt]
    have hL : ∫⁻ w, Φ w ∂(Measure.map φ η) = (c : ENNReal) * ∫⁻ w, Φ w ∂ρ := by
      conv_lhs => rw [huniq]
      rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [← lintegral_map hΦ hφc.measurable, hL]
    congr 1

    have hmA : Measurable fun y : ∀ a, ↥(NA a) => ∏ a, g a (y a : A a) :=
      Finset.measurable_prod _ fun (a : α) _ => (hg a).comp (measurable_subtype_coe.comp (measurable_pi_apply a))
    have hmN : Measurable fun z : ∀ k : ↥bad, ↥(N (k : κ)) => ∏ k : ↥bad, f k (p k π * (z k : G k)) :=
      Finset.measurable_prod _ fun (k : ↥bad) _ =>
        ((hf k).comp (measurable_const_mul _)).comp (measurable_subtype_coe.comp (measurable_pi_apply k))
    have hmU : Measurable fun u : ∀ k : ↥(Sf \ bad), ↥(U (k : κ)) => ∏ k : ↥(Sf \ bad), f k (u k : G k) :=
      Finset.measurable_prod _ fun (k : ↥(Sf \ bad)) _ =>
        (hf k).comp (measurable_subtype_coe.comp (measurable_pi_apply k))
    have h1 : ∫⁻ w, Φ w ∂ρ = (∫⁻ y, ∏ a, g a (y a : A a) ∂Measure.pi haarA) *
        ∫⁻ w, (∏ k : ↥bad, f k (p k π * (w.1 k : G k))) * ∏ k : ↥(Sf \ bad), f k (w.2 k : G k)
          ∂(Measure.pi haarN).prod (Measure.pi fun k : ↥(Sf \ bad) =>
            Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ)))) :=
      lintegral_prod_mul hmA.aemeasurable ((hmN.comp measurable_fst).mul (hmU.comp measurable_snd)).aemeasurable
    rw [h1, lintegral_prod_mul hmN.aemeasurable hmU.aemeasurable,
      lintegral_fintype_prod_eq_prod haarA (fun (a : α) (y : ↥(NA a)) => g a (y : A a)) fun a =>
        (hg a).comp measurable_subtype_coe,
      lintegral_fintype_prod_eq_prod haarN (fun (k : ↥bad) (y : ↥(N (k : κ))) => f k (p k π * (y : G k))) fun k =>
        ((hf k).comp (measurable_const_mul _)).comp measurable_subtype_coe,
      lintegral_fintype_prod_eq_prod
        (fun k : ↥(Sf \ bad) => Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ))))
        (fun (k : ↥(Sf \ bad)) (z : ↥(U (k : κ))) => f k (z : G k)) fun k => (hf k).comp measurable_subtype_coe]

  obtain ⟨c₀, hc₀0, hc₀top, hc₀⟩ := core bad Finset.Subset.rfl
  obtain ⟨a₀⟩ := ‹Nonempty α›
  set μA : ∀ a, Measure ↥(NA a) := fun a => (if a = a₀ then c₀ else 1) • haarA a with hμA
  set μN : ∀ k, Measure ↥(N k) := fun k => if hk : k ∈ bad then haarN ⟨k, hk⟩ else 0 with hμN
  have hsm : ∀ a, (μA a).IsHaarMeasure := by
    intro a
    by_cases ha : a = a₀
    · rw [hμA]; simp only [if_pos ha]; exact Measure.IsHaarMeasure.smul _ hc₀0 hc₀top
    · rw [hμA]; simp only [if_neg ha, one_smul]; infer_instance
  have hsmN : ∀ k ∈ bad, (μN k).IsHaarMeasure := by
    intro k hk; rw [hμN]; simp only [dif_pos hk]; infer_instance
  refine ⟨μA, μN, fun k => Measure.haar, hsm, hsmN, fun k => inferInstance, ?_⟩
  intro π hπA hπ Sf hSf g f hg hf
  haveI := hU_cs Sf
  obtain ⟨cSf, -, -, hcSf⟩ := core Sf hSf

  have hcc : cSf = c₀ := by
    let KA : ∀ a, TopologicalSpace.PositiveCompacts ↥(NA a) := fun a => Classical.arbitrary _
    let KN : ∀ k : ↥bad, TopologicalSpace.PositiveCompacts ↥(N (k : κ)) := fun k => Classical.arbitrary _
    let g₀ : ∀ a, A a → ENNReal := fun a => (Subtype.val '' (KA a : Set ↥(NA a))).indicator 1
    let f₀ : ∀ k, G k → ENNReal := fun k =>
      if hk : k ∈ bad then fun x => (Subtype.val '' (KN ⟨k, hk⟩ : Set ↥(N k))).indicator 1 ((p k π)⁻¹ * x)
      else fun _ => 1
    have hKA : ∀ a, MeasurableSet (Subtype.val '' (KA a : Set ↥(NA a))) := fun a =>
      ((KA a).isCompact.image continuous_subtype_val).isClosed.measurableSet
    have hKN : ∀ k : ↥bad, MeasurableSet (Subtype.val '' (KN k : Set ↥(N (k : κ)))) := fun k =>
      ((KN k).isCompact.image continuous_subtype_val).isClosed.measurableSet
    have hg₀ : ∀ a, Measurable (g₀ a) := fun a => measurable_const.indicator (hKA a)
    have hf₀ : ∀ k, Measurable (f₀ k) := by
      intro k
      by_cases hk : k ∈ bad
      · simp only [f₀, dif_pos hk]
        exact (measurable_const.indicator (hKN ⟨k, hk⟩)).comp (measurable_const_mul _)
      · simp only [f₀, dif_neg hk]; exact measurable_const

    have hsame : ∫⁻ b, (∏ a, g₀ a (q a b)) * ∏ k ∈ Sf, f₀ k (p k b)
          ∂(Measure.map (fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B)) η) =
        ∫⁻ b, (∏ a, g₀ a (q a b)) * ∏ k ∈ bad, f₀ k (p k b)
          ∂(Measure.map (fun m : ↥(levelSubgroup q NA p N U bad) => π * (m : B)) η) := by
      refine lintegral_congr fun b => ?_
      rw [Finset.prod_subset hSf fun k _ hkb => by simp only [f₀, dif_neg hkb]]

    have hIA : ∀ a, ∫⁻ y, g₀ a (y : A a) ∂haarA a = haarA a (KA a) := by
      intro a
      have : (fun y : ↥(NA a) => g₀ a (y : A a)) = (KA a : Set ↥(NA a)).indicator 1 := by
        funext y
        simp only [g₀, Set.indicator_apply, Subtype.val_injective.mem_set_image, Pi.one_apply]
      rw [this, lintegral_indicator_one (KA a).isCompact.measurableSet]
    have hIN : ∀ k : ↥bad, ∫⁻ y, f₀ k (p k π * (y : G k)) ∂haarN k = haarN k (KN k) := by
      intro k
      have : (fun y : ↥(N (k : κ)) => f₀ k (p k π * (y : G k))) = (KN k : Set ↥(N (k : κ))).indicator 1 := by
        funext y
        simp only [f₀, dif_pos k.2, inv_mul_cancel_left, Set.indicator_apply, Subtype.val_injective.mem_set_image,
          Pi.one_apply]
      rw [this, lintegral_indicator_one (KN k).isCompact.measurableSet]
    have hIU : ∀ (Sg : Finset κ) (k : ↥(Sg \ bad)), (haveI := hU_cs Sg k;
        ∫⁻ z, f₀ k (z : G k) ∂(Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ))))) = 1 := by
      intro Sg k
      haveI := hU_cs Sg k
      simp only [f₀, dif_neg (Finset.mem_sdiff.1 k.2).2, lintegral_const, one_mul]
      rw [← TopologicalSpace.PositiveCompacts.coe_top (α := ↥(U (k : κ))), Measure.haarMeasure_self]
    have hX0 : (∏ a, ∫⁻ y, g₀ a (y : A a) ∂haarA a) * ∏ k : ↥bad, ∫⁻ y, f₀ k (p k π * (y : G k)) ∂haarN k ≠ 0 := by
      refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => ?_) (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
      · rw [hIA]; exact (Measure.measure_pos_of_nonempty_interior (μ := haarA a) (KA a).interior_nonempty).ne'
      · rw [hIN]; exact (Measure.measure_pos_of_nonempty_interior (μ := haarN k) (KN k).interior_nonempty).ne'
    have hXtop : (∏ a, ∫⁻ y, g₀ a (y : A a) ∂haarA a) * ∏ k : ↥bad, ∫⁻ y, f₀ k (p k π * (y : G k)) ∂haarN k ≠ ⊤ := by
      refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun a _ => ?_) (ENNReal.prod_ne_top fun k _ => ?_)
      · rw [hIA]; exact (KA a).isCompact.measure_lt_top.ne
      · rw [hIN]; exact (KN k).isCompact.measure_lt_top.ne
    have h1 := hcSf π hπA hπ g₀ f₀ hg₀ hf₀
    have h2 := hc₀ π hπA hπ g₀ f₀ hg₀ hf₀
    rw [hsame, h2] at h1
    simp only [hIU, Finset.prod_const_one, mul_one] at h1
    exact ((ENNReal.mul_left_inj hX0 hXtop).1 h1).symm
  rw [hcSf π hπA hπ g f hg hf, hcc]

  have eA : (∏ a, ∫⁻ x, g a x ∂Measure.map ((↑) : ↥(NA a) → A a) (μA a)) =
      c₀ * ∏ a, ∫⁻ y, g a (y : A a) ∂haarA a := by
    have : ∀ a, ∫⁻ x, g a x ∂Measure.map ((↑) : ↥(NA a) → A a) (μA a) =
        (if a = a₀ then c₀ else 1) * ∫⁻ y, g a (y : A a) ∂haarA a := fun a => by
      rw [hμA]
      simp only []
      rw [Measure.map_smul, lintegral_smul_measure, lintegral_map (hg a) measurable_subtype_coe, smul_eq_mul]
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ a₀ fun _ => c₀]
    simp
  have eN : (∏ k ∈ bad, ∫⁻ x, f k x ∂Measure.map (fun x : G k => p k π * x)
      (Measure.map ((↑) : ↥(N k) → G k) (μN k))) = ∏ k : ↥bad, ∫⁻ y, f k (p k π * (y : G k)) ∂haarN k := by
    rw [← Finset.prod_coe_sort bad fun k => ∫⁻ x, f k x ∂Measure.map (fun x : G k => p k π * x)
      (Measure.map ((↑) : ↥(N k) → G k) (μN k))]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hk : μN k = haarN k := by rw [hμN]; simp only [dif_pos k.2]
    rw [hk, lintegral_map (hf k) (measurable_const_mul _),
      lintegral_map (show Measurable fun x : G k => f k (p k π * x) from (hf k).comp (measurable_const_mul _))
        measurable_subtype_coe]
  have eU : (∏ k ∈ Sf \ bad, ∫⁻ x, f k x
      ∂((Measure.haar (U k : Set (G k)))⁻¹ • (Measure.haar).restrict (U k : Set (G k)))) =
      ∏ k : ↥(Sf \ bad), ∫⁻ z, f k (z : G k)
        ∂(Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ↥(U (k : κ)))) := by
    rw [← Finset.prod_coe_sort (Sf \ bad) fun k => ∫⁻ x, f k x
      ∂((Measure.haar (U k : Set (G k)))⁻¹ • (Measure.haar).restrict (U k : Set (G k)))]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact lintegral_inv_smul_restrict_eq_lintegral_haarMeasure_top Measure.haar (U k)
      (hU k (Finset.mem_sdiff.1 k.2).2) (hU' k (Finset.mem_sdiff.1 k.2).2) (f k) (hf k)
  rw [eA, eN, eU]
  ring

private theorem isHaarMeasure_map_restrict
    {B α κ : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [T2Space B]
    [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    [Fintype α] {A : α → Type*} [∀ a, Group (A a)] [∀ a, TopologicalSpace (A a)]
    [∀ a, IsTopologicalGroup (A a)] [∀ a, LocallyCompactSpace (A a)] [∀ a, T2Space (A a)]
    [∀ a, SecondCountableTopology (A a)] [∀ a, MeasurableSpace (A a)] [∀ a, BorelSpace (A a)]
    {G : κ → Type*} [∀ k, Group (G k)] [∀ k, TopologicalSpace (G k)] [∀ k, IsTopologicalGroup (G k)]
    [∀ k, LocallyCompactSpace (G k)] [∀ k, T2Space (G k)] [∀ k, SecondCountableTopology (G k)]
    [∀ k, MeasurableSpace (G k)] [∀ k, BorelSpace (G k)]
    (q : ∀ a, B →* A a) (hq : ∀ a, Continuous (q a)) (p : ∀ k, B →* G k) (hp : ∀ k, Continuous (p k))
    (U : ∀ k, Subgroup (G k)) (Sf : Finset κ) (hU : ∀ k ∉ Sf, IsCompact (U k : Set (G k)))
    (hP : IsOpen {b : B | ∀ k ∉ Sf, p k b ∈ U k})
    (hsurj : ∀ (y : ∀ a, A a) (x : ∀ k, G k), (∀ k ∉ Sf, x k ∈ U k) →
      ∃ b : B, (∀ a, q a b = y a) ∧ ∀ k, p k b = x k)
    (hbox : ∀ (D : ∀ a, Set (A a)) (C : ∀ k, Set (G k)), (∀ a, IsCompact (D a)) → (∀ k, IsCompact (C k)) →
      {k | C k ≠ (U k : Set (G k))}.Finite → IsCompact {b : B | (∀ a, q a b ∈ D a) ∧ ∀ k, p k b ∈ C k})
    (ν : Measure B) [ν.IsHaarMeasure] :
    (Measure.map (fun b : B => ((fun a => q a b : ∀ a, A a), (fun k : ↥Sf => p k b : ∀ k : ↥Sf, G k)))
      (ν.restrict {b : B | ∀ k ∉ Sf, p k b ∈ U k})).IsHaarMeasure := by
  classical

  set P : Set B := {b : B | ∀ k ∉ Sf, p k b ∈ U k} with hPdef
  have hPmul : ∀ {b₀ b : B}, b₀ ∈ P → (b₀ * b ∈ P ↔ b ∈ P) := by
    intro b₀ b hb₀
    simp only [hPdef, Set.mem_setOf_eq, map_mul]
    exact ⟨fun h k hk => by simpa using mul_mem (inv_mem (hb₀ k hk)) (h k hk),
      fun h k hk => mul_mem (hb₀ k hk) (h k hk)⟩

  let ψ : B →* (∀ a, A a) × (∀ k : ↥Sf, G k) :=
    { toFun := fun b => ((fun a => q a b : ∀ a, A a), (fun k : ↥Sf => p k b : ∀ k : ↥Sf, G k))
      map_one' := by ext <;> simp
      map_mul' := fun b b' => by ext <;> simp }
  have hψ_apply : ∀ b, ψ b = ((fun a => q a b : ∀ a, A a), (fun k : ↥Sf => p k b : ∀ k : ↥Sf, G k)) := fun b => rfl
  have hψc : Continuous ψ :=
    continuous_prodMk.2 ⟨continuous_pi fun a => hq a, continuous_pi fun k => hp k⟩
  have hψP : ∀ w : (∀ a, A a) × (∀ k : ↥Sf, G k), ∃ b ∈ P, ψ b = w := by
    rintro ⟨y, z⟩
    obtain ⟨b, hbA, hb⟩ := hsurj y (fun k => if hk : k ∈ Sf then z ⟨k, hk⟩ else 1) fun k hk => by
      simp only [dif_neg hk]; exact one_mem _
    refine ⟨b, fun k hk => by rw [hb]; simp only [dif_neg hk]; exact one_mem _, ?_⟩
    rw [hψ_apply]
    exact Prod.ext (funext hbA) (funext fun k => by simp [hb, k.2])
  change (Measure.map ψ (ν.restrict P)).IsHaarMeasure
  have hmapply : ∀ s, MeasurableSet s → Measure.map ψ (ν.restrict P) s = ν (ψ ⁻¹' s ∩ P) := fun s hs => by
    rw [Measure.map_apply hψc.measurable hs, Measure.restrict_apply (hs.preimage hψc.measurable)]
  refine
    { lt_top_of_isCompact := fun K hK => ?_
      map_mul_left_eq_self := fun h => ?_
      open_pos := fun O hO hOne => ?_ }
  ·
    rw [hmapply K hK.measurableSet]
    let D : ∀ a, Set (A a) := fun a => (fun y : ∀ a, A a => y a) '' (Prod.fst '' K)
    let C : ∀ k, Set (G k) := fun k =>
      if hk : k ∈ Sf then (fun z : ∀ j : ↥Sf, G j => z ⟨k, hk⟩) '' (Prod.snd '' K) else (U k : Set (G k))
    have hD : ∀ a, IsCompact (D a) := fun a => (hK.image continuous_fst).image (continuous_apply a)
    have hC : ∀ k, IsCompact (C k) := fun k => by
      by_cases hk : k ∈ Sf
      · simp only [C, dif_pos hk]; exact (hK.image continuous_snd).image (continuous_apply _)
      · simp only [C, dif_neg hk]; exact hU k hk
    have hfin : {k | C k ≠ (U k : Set (G k))}.Finite :=
      (Sf.finite_toSet).subset fun k hk => by
        by_contra hkSf; exact hk (by simp only [C, dif_neg (show k ∉ Sf from hkSf)])
    refine lt_of_le_of_lt (measure_mono ?_) (hbox D C hD hC hfin).measure_lt_top
    rintro b ⟨hbK, hbP⟩
    refine ⟨fun a => ⟨(ψ b).1, ⟨ψ b, hbK, rfl⟩, rfl⟩, fun k => ?_⟩
    by_cases hk : k ∈ Sf
    · simp only [C, dif_pos hk]; exact ⟨(ψ b).2, ⟨ψ b, hbK, rfl⟩, rfl⟩
    · simp only [C, dif_neg hk]; exact hbP k hk
  ·
    obtain ⟨b₀, hb₀, rfl⟩ := hψP h
    rw [Measure.map_map (measurable_const_mul _) hψc.measurable]
    have hcomp : (fun w => ψ b₀ * w) ∘ ψ = ψ ∘ fun b => b₀ * b := by
      funext b; simp only [Function.comp_apply, map_mul]
    rw [hcomp, ← Measure.map_map hψc.measurable (measurable_const_mul _)]
    congr 1
    ext s hs
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.restrict_apply hs,
      Measure.restrict_apply ((measurable_const_mul _) hs)]
    have hset : (fun b => b₀ * b) ⁻¹' s ∩ P = (fun b => b₀ * b) ⁻¹' (s ∩ P) := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_preimage, hPmul hb₀]
    rw [hset, measure_preimage_mul]
  ·
    rw [hmapply O hO.measurableSet]
    obtain ⟨w, hw⟩ := hOne
    obtain ⟨b, hbP, hbw⟩ := hψP w
    exact ((hO.preimage hψc).inter hP).measure_ne_zero ν ⟨b, by rw [Set.mem_preimage, hbw]; exact hw, hbP⟩

open scoped TensorProduct.RightActions in
private scoped instance borelSpace_semiLocalUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ :=
  ⟨rfl⟩

private scoped instance borelSpace_archUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) : BorelSpace (∀ w : v.Extension L, w.1.Completion)ˣ :=
  ⟨rfl⟩

open scoped TensorProduct.RightActions in

private theorem continuousMul_semiLocalAlgebra (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) : ContinuousMul (L ⊗[K] v.adicCompletion K) :=
  Topology.IsInducing.continuousMul (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v)
    (AutomorphicForm.semiLocalHomeomorph K L v).isInducing

private theorem secondCountableTopology_ideles (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

open scoped TensorProduct.RightActions in

private theorem semiLocalIdele_mem_integralUnits_iff (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (t : (AdeleRing (𝓞 L) L)ˣ) :
    TransversalMeasure.semiLocalIdele K L v t ∈ TransversalMeasure.integralUnits K L v ↔
      ∀ w : v.Extension (𝓞 L), (t : AdeleRing (𝓞 L) L).2 w.1 ∈ w.1.adicCompletionIntegers L ∧
        ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [TransversalMeasure.mem_integralUnits_iff, AutomorphicForm.semiLocalIntegers_eq_preimage]
  have h1 : ((TransversalMeasure.semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K) = AutomorphicForm.semiLocalEval K L v ((t : AdeleRing (𝓞 L) L).2) := rfl
  have h2 : (((TransversalMeasure.semiLocalIdele K L v t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K) =
        AutomorphicForm.semiLocalEval K L v (((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2) := by
    rw [← map_inv]; rfl
  rw [h1, h2]
  simp only [Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi,
    TransversalMeasure.semiLocalHomeomorph_semiLocalEval_apply, SetLike.mem_coe, ← forall_and]
  exact Iff.rfl

open scoped TensorProduct.RightActions in

private theorem semiLocalHomeomorph_apply_mem_of_mem_integralUnits (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (u : (L ⊗[K] v.adicCompletion K)ˣ)
    (hu : u ∈ TransversalMeasure.integralUnits K L v) (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L v (u : L ⊗[K] v.adicCompletion K) w ∈ w.1.adicCompletionIntegers L ∧
      AutomorphicForm.semiLocalHomeomorph K L v
        ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) w ∈ w.1.adicCompletionIntegers L := by
  rw [TransversalMeasure.mem_integralUnits_iff, AutomorphicForm.semiLocalIntegers_eq_preimage] at hu
  simp only [Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi, SetLike.mem_coe] at hu
  exact ⟨hu.1 w, hu.2 w⟩

open scoped TensorProduct.RightActions in

private theorem semiLocalHomeomorph_semiLocalIdele_apply (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (t : (AdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L (HeightOneSpectrum.under (𝓞 K) w)
        ((TransversalMeasure.semiLocalIdele K L (HeightOneSpectrum.under (𝓞 K) w) t :
          (L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w).adicCompletion K)ˣ) : L ⊗[K] _) ⟨w, rfl⟩ =
      (t : AdeleRing (𝓞 L) L).2 w := by
  change AutomorphicForm.semiLocalHomeomorph K L _ (AutomorphicForm.semiLocalEval K L _ ((t : AdeleRing (𝓞 L) L).2))
    ⟨w, rfl⟩ = _
  rw [TransversalMeasure.semiLocalHomeomorph_semiLocalEval_apply]
  rfl

private scoped instance countable_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) :=
  haveI : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _ Rat.HeightOneSpectrum.primesEquiv.symm
  Set.Countable.of_preimage_singleton fun y =>
    ((HeightOneSpectrum.preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K)) {y} (Set.finite_singleton y)).countable

private theorem isCompact_setOf_forall_apply_mem {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    {A : ∀ i, Set (R i)} (E : ∀ i, Set (R i)) (hE : ∀ i, IsCompact (E i))
    (hEA : ∀ᶠ i in Filter.cofinite, E i ⊆ A i) :
    IsCompact {x : RestrictedProduct R A Filter.cofinite | ∀ i, x i ∈ E i} := by
  set S : Set ι := {i | E i ⊆ A i} with hSdef
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 hEA
  have h1 : IsCompact {x : RestrictedProduct R A (Filter.principal S) | ∀ i, x i ∈ E i} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have himg : ((↑) : RestrictedProduct R A (Filter.principal S) → ∀ i, R i) '' {x | ∀ i, x i ∈ E i} =
        Set.univ.pi E := by
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_univ_pi]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy; exact ⟨⟨y, Filter.eventually_principal.2 fun i hi => hi (hy i)⟩, hy, rfl⟩
    rw [himg]
    exact isCompact_univ_pi hE
  have h2 : {x : RestrictedProduct R A Filter.cofinite | ∀ i, x i ∈ E i} =
      RestrictedProduct.inclusion R A hS '' {x | ∀ i, x i ∈ E i} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hx
      exact ⟨⟨(x : ∀ i, R i), Filter.eventually_principal.2 fun i hi => hi (hx i)⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  rw [h2]
  exact h1.image (RestrictedProduct.continuous_inclusion hS)

private theorem continuous_finiteUnitsComponent (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v) := by
  unfold NumberField.AdeleRing.finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.unitsComponent
    NumberField.AdeleRing.finitePartUnits
  exact (Continuous.units_map _ (RestrictedProduct.continuous_eval v)).comp (Continuous.units_map _ continuous_snd)

private theorem continuous_infiniteUnitsComponent (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) :
    Continuous (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w) := by
  unfold NumberField.AdeleRing.infiniteUnitsComponent
  exact Continuous.units_map _ ((continuous_apply w).comp continuous_fst)

private theorem exists_archSemiLocalIdele_eq_and_semiLocalIdele_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sf : Finset (HeightOneSpectrum (𝓞 K))) (y : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hx : ∀ v, v ∉ Sf → x v ∈ TransversalMeasure.integralUnits K L v) :
    ∃ t : (AdeleRing (𝓞 L) L)ˣ, (∀ v, TransversalMeasure.archSemiLocalIdele K L v t = y v) ∧
      ∀ v, TransversalMeasure.semiLocalIdele K L v t = x v := by
  open scoped TensorProduct.RightActions in
  classical

  have hHmul : ∀ (v : HeightOneSpectrum (𝓞 K)) (a b : L ⊗[K] v.adicCompletion K),
      AutomorphicForm.semiLocalHomeomorph K L v (a * b) =
        AutomorphicForm.semiLocalHomeomorph K L v a * AutomorphicForm.semiLocalHomeomorph K L v b :=
    fun v a b => map_mul (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v) a b
  have hH1 : ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.semiLocalHomeomorph K L v 1 = 1 := fun v =>
    map_one (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v)

  let X : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ := fun w =>
    ⟨AutomorphicForm.semiLocalHomeomorph K L (HeightOneSpectrum.under (𝓞 K) w)
        ((x (HeightOneSpectrum.under (𝓞 K) w) : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w).adicCompletion K))
        ⟨w, rfl⟩,
      AutomorphicForm.semiLocalHomeomorph K L (HeightOneSpectrum.under (𝓞 K) w)
        (((x (HeightOneSpectrum.under (𝓞 K) w))⁻¹ :
          (L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w).adicCompletion K)ˣ) : L ⊗[K] _)
        ⟨w, rfl⟩,
      by
        have h := congrFun (hHmul (HeightOneSpectrum.under (𝓞 K) w) (x (HeightOneSpectrum.under (𝓞 K) w) : _)
          ↑(x (HeightOneSpectrum.under (𝓞 K) w))⁻¹) ⟨w, rfl⟩
        rw [Units.mul_inv, hH1] at h
        exact h.symm,
      by
        have h := congrFun (hHmul (HeightOneSpectrum.under (𝓞 K) w) ↑(x (HeightOneSpectrum.under (𝓞 K) w))⁻¹
          (x (HeightOneSpectrum.under (𝓞 K) w) : _)) ⟨w, rfl⟩
        rw [Units.inv_mul, hH1] at h
        exact h.symm⟩

  have hX : ∀ᶠ w in Filter.cofinite, X w ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units := by
    refine Filter.eventually_cofinite.2
      ((HeightOneSpectrum.preimage_comap_finite (𝓞 K) K L (𝓞 L) (Sf : Set (HeightOneSpectrum (𝓞 K)))
        Sf.finite_toSet).subset fun w hw => ?_)
    by_contra h
    exact hw ((Submonoid.mem_units_iff _ _).2
      (semiLocalHomeomorph_apply_mem_of_mem_integralUnits K L _ _ (hx _ h) ⟨w, rfl⟩))
  let z : (FiniteAdeleRing (𝓞 L) L)ˣ := RestrictedProduct.mkUnit X hX

  let u : (InfiniteAdeleRing L)ˣ :=
    MulEquiv.piUnits.symm fun w => MulEquiv.piUnits (y (w.comap (algebraMap K L))) ⟨w, rfl⟩
  refine ⟨MulEquiv.prodUnits.symm (u, z), fun v => Units.ext (funext fun w' => ?_), fun v => Units.ext ?_⟩
  · obtain ⟨w, rfl⟩ := w'
    rfl
  · apply (AutomorphicForm.semiLocalHomeomorph K L v).injective
    funext w'
    change AutomorphicForm.semiLocalHomeomorph K L v
        (AutomorphicForm.semiLocalEval K L v ((z : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)) w' = _
    rw [TransversalMeasure.semiLocalHomeomorph_semiLocalEval_apply]
    obtain ⟨w, rfl⟩ := w'
    rfl

end Transversal.Product
p2m_reactivate "P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal.Product"
p2m_reactivate "P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal"

namespace TransversalMeasure

private theorem continuous_archSemiLocalIdele (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) : Continuous (archSemiLocalIdele K L v) := by
  exact (Continuous.units_map
      (RingHom.pi fun w : v.Extension L => Pi.evalRingHom (fun u : InfinitePlace L => u.Completion) w.1 :
        InfiniteAdeleRing L →+* (∀ w : v.Extension L, w.1.Completion)).toMonoidHom
      (continuous_pi fun w => continuous_apply w.1)).comp
    (Continuous.units_map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom continuous_fst)

open scoped TensorProduct.RightActions in

private theorem continuous_semiLocalIdele (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) : Continuous (semiLocalIdele K L v) := by
  have h1 : Continuous (AutomorphicForm.semiLocalEval K L v) := by
    have h2 : Continuous fun x : FiniteAdeleRing (𝓞 L) L => fun w : v.Extension (𝓞 L) =>
        AdelicLevel.finAdeleEval (𝓞 L) L w.1 x :=
      continuous_pi fun w => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1
    exact (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).symm.continuous.comp h2
  exact (Continuous.units_map (AutomorphicForm.semiLocalEval K L v).toMonoidHom h1).comp
    (Continuous.units_map (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom continuous_snd)

end TransversalMeasure
p2m_reactivate "P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal.Product"

namespace Transversal
namespace Product

open scoped TensorProduct.RightActions in

private theorem isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ)
    (C : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ)
    (hD : ∀ v, IsCompact (D v)) (hC : ∀ v, IsCompact (C v))
    (hfin : {v | C v ≠ (TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite) :
    IsCompact {t : (AdeleRing (𝓞 L) L)ˣ | (∀ v, TransversalMeasure.archSemiLocalIdele K L v t ∈ D v) ∧
      ∀ v, TransversalMeasure.semiLocalIdele K L v t ∈ C v} := by
  open scoped TensorProduct.RightActions in
  haveI := fun v : HeightOneSpectrum (𝓞 K) => TransversalMeasure.t2Space_units K L v
  haveI := fun v : InfinitePlace K => TransversalMeasure.t2Space_archUnits K L v

  let E₁ : ∀ D' : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ, ∀ w : InfinitePlace L,
      Set w.Completion := fun D' w =>
    (fun y : (∀ w' : (w.comap (algebraMap K L)).Extension L, w'.1.Completion)ˣ =>
      (y : ∀ w' : (w.comap (algebraMap K L)).Extension L, w'.1.Completion) ⟨w, rfl⟩) '' D' (w.comap (algebraMap K L))
  let E₂ : ∀ C' : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ, ∀ w : HeightOneSpectrum (𝓞 L),
      Set (w.adicCompletion L) := fun C' w =>
    (fun y : (L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w).adicCompletion K)ˣ =>
      AutomorphicForm.semiLocalHomeomorph K L (HeightOneSpectrum.under (𝓞 K) w)
        (y : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w).adicCompletion K) ⟨w, rfl⟩) ''
          C' (HeightOneSpectrum.under (𝓞 K) w)
  have hpi : ∀ D' : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ, (∀ v, IsCompact (D' v)) →
      IsCompact {a : InfiniteAdeleRing L | ∀ w, a w ∈ E₁ D' w} := fun D' hD' => by
    have : {a : InfiniteAdeleRing L | ∀ w, a w ∈ E₁ D' w} = Set.univ.pi fun w => E₁ D' w := by
      ext a
      exact Set.mem_univ_pi.symm
    rw [this]
    exact isCompact_univ_pi fun w => (hD' _).image ((continuous_apply _).comp Units.continuous_val)
  have hint : ∀ C' : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ, (∀ v, IsCompact (C' v)) →
      {v | C' v ≠ (TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite →
      IsCompact {z : FiniteAdeleRing (𝓞 L) L | ∀ w, z w ∈ E₂ C' w} := fun C' hC' hf => by
    refine isCompact_setOf_forall_apply_mem (E₂ C') (fun w => (hC' _).image
      (((continuous_apply _).comp (AutomorphicForm.semiLocalHomeomorph K L
        (HeightOneSpectrum.under (𝓞 K) w)).continuous).comp Units.continuous_val))
      (Filter.eventually_cofinite.2
        ((HeightOneSpectrum.preimage_comap_finite (𝓞 K) K L (𝓞 L) _ hf).subset fun w hw => ?_))
    intro h'
    refine hw ?_
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ TransversalMeasure.integralUnits K L (HeightOneSpectrum.under (𝓞 K) w) := by
      rw [h'] at hu
      exact hu
    exact (semiLocalHomeomorph_apply_mem_of_mem_integralUnits K L _ u hu' ⟨w, rfl⟩).1
  haveI := fun v : HeightOneSpectrum (𝓞 K) => continuousMul_semiLocalAlgebra K L v
  have hD' : ∀ v, IsCompact (D v)⁻¹ := fun v => (hD v).inv
  have hC' : ∀ v, IsCompact (C v)⁻¹ := fun v => (hC v).inv
  have hfin' : {v | (C v)⁻¹ ≠ (TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite := by
    refine hfin.subset fun v hv => ?_
    exact fun h => hv (by rw [h]; exact Set.ext fun u => by simp only [Set.mem_inv, SetLike.mem_coe, inv_mem_iff])
  have hbig : IsCompact (({a : InfiniteAdeleRing L | ∀ w, a w ∈ E₁ D w} ×ˢ {z : FiniteAdeleRing (𝓞 L) L |
      ∀ w, z w ∈ E₂ C w}) ×ˢ (MulOpposite.op '' ({a : InfiniteAdeleRing L | ∀ w, a w ∈ E₁ (fun v => (D v)⁻¹) w} ×ˢ
        {z : FiniteAdeleRing (𝓞 L) L | ∀ w, z w ∈ E₂ (fun v => (C v)⁻¹) w}))) :=
    ((hpi D hD).prod (hint C hC hfin)).prod (((hpi _ hD').prod (hint _ hC' hfin')).image MulOpposite.continuous_op)
  have hclosed : IsClosed {t : (AdeleRing (𝓞 L) L)ˣ | (∀ v, TransversalMeasure.archSemiLocalIdele K L v t ∈ D v) ∧
      ∀ v, TransversalMeasure.semiLocalIdele K L v t ∈ C v} := by
    have : {t : (AdeleRing (𝓞 L) L)ˣ | (∀ v, TransversalMeasure.archSemiLocalIdele K L v t ∈ D v) ∧
        ∀ v, TransversalMeasure.semiLocalIdele K L v t ∈ C v} =
        (⋂ v, TransversalMeasure.archSemiLocalIdele K L v ⁻¹' D v) ∩
          ⋂ v, TransversalMeasure.semiLocalIdele K L v ⁻¹' C v := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact (isClosed_iInter fun v =>
        (hD v).isClosed.preimage (TransversalMeasure.continuous_archSemiLocalIdele K L v)).inter
      (isClosed_iInter fun v => (hC v).isClosed.preimage (TransversalMeasure.continuous_semiLocalIdele K L v))
  refine ((Units.isClosedEmbedding_embedProduct (α := AdeleRing (𝓞 L) L)).isCompact_preimage hbig).of_isClosed_subset
    hclosed ?_
  rintro t ⟨htD, htC⟩
  refine ⟨⟨fun w => ⟨_, htD _, rfl⟩, fun w => ⟨_, htC _, semiLocalHomeomorph_semiLocalIdele_apply K L t w⟩⟩,
    ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L),
    ⟨fun w => ⟨(TransversalMeasure.archSemiLocalIdele K L (w.comap (algebraMap K L)) t)⁻¹, Set.inv_mem_inv.2 (htD _),
        ?_⟩,
      fun w => ⟨(TransversalMeasure.semiLocalIdele K L (HeightOneSpectrum.under (𝓞 K) w) t)⁻¹,
        Set.inv_mem_inv.2 (htC _), ?_⟩⟩, rfl⟩
  · rw [← map_inv]; rfl
  · rw [← map_inv]; exact semiLocalHomeomorph_semiLocalIdele_apply K L t⁻¹ w

private theorem finite_setOf_semiLocalIdele_not_mem_integralUnits
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (t : (AdeleRing (𝓞 L) L)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) | TransversalMeasure.semiLocalIdele K L v t ∉
      TransversalMeasure.integralUnits K L v}.Finite := by
  open scoped TensorProduct.RightActions in
  have hfin₁ : {w : HeightOneSpectrum (𝓞 L) | (t : AdeleRing (𝓞 L) L).2 w ∉ w.adicCompletionIntegers L}.Finite :=
    Filter.eventually_cofinite.1 (RestrictedProduct.eventually _ _ ((t : AdeleRing (𝓞 L) L).2))
  have hfin₂ : {w : HeightOneSpectrum (𝓞 L) |
      ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w ∉ w.adicCompletionIntegers L}.Finite :=
    Filter.eventually_cofinite.1
      (RestrictedProduct.eventually _ _ (((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2))
  refine ((hfin₁.union hfin₂).image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, semiLocalIdele_mem_integralUnits_iff, not_forall, not_and_or] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

private theorem forall_semiLocalIdele_mem_integralUnits_iff
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sf : Finset (HeightOneSpectrum (𝓞 K))) (t : (AdeleRing (𝓞 L) L)ˣ) :
    (∀ v, v ∉ Sf → TransversalMeasure.semiLocalIdele K L v t ∈ TransversalMeasure.integralUnits K L v) ↔
      t ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 L) L
        {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w ∈ Sf} := by
  open scoped TensorProduct.RightActions in
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  simp only [semiLocalIdele_mem_integralUnits_iff]
  constructor
  · intro h w hw
    exact h (HeightOneSpectrum.under (𝓞 K) w) hw ⟨w, rfl⟩
  · intro h v hv w
    exact h w.1 fun hw => hv (w.2 ▸ hw)

private theorem isOpen_setOf_forall_semiLocalIdele_mem_integralUnits
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sf : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen {t : (AdeleRing (𝓞 L) L)ˣ |
      ∀ v, v ∉ Sf → TransversalMeasure.semiLocalIdele K L v t ∈ TransversalMeasure.integralUnits K L v} := by
  open scoped TensorProduct.RightActions in
  have hset : {t : (AdeleRing (𝓞 L) L)ˣ |
      ∀ v, v ∉ Sf → TransversalMeasure.semiLocalIdele K L v t ∈ TransversalMeasure.integralUnits K L v} =
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 L) L
          {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w ∈ Sf} : Set (AdeleRing (𝓞 L) L)ˣ) :=
    Set.ext fun t => forall_semiLocalIdele_mem_integralUnits_iff K L Sf t
  rw [hset]
  exact NumberField.Idele.isOpen_unitIdelesOutside L _

private theorem isPiSystem_isBox
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    IsPiSystem {E : Set (AdeleRing (𝓞 L) L)ˣ | IsBox K L E} := by
  open scoped TensorProduct.RightActions in
  classical
  rintro E₁ ⟨D₁, C₁, hD₁, hC₁, hf₁, rfl⟩ E₂ ⟨D₂, C₂, hD₂, hC₂, hf₂, rfl⟩ -
  refine ⟨fun v => D₁ v ∩ D₂ v, fun v => C₁ v ∩ C₂ v, fun v => (hD₁ v).inter (hD₂ v),
    fun v => (hC₁ v).inter (hC₂ v), (hf₁.union hf₂).subset fun v hv => ?_, ?_⟩
  · by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (by show C₁ v ∩ C₂ v = _; rw [h.1, h.2, Set.inter_self])
  · ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨fun v => ⟨h.1.1 v, h.2.1 v⟩, fun v => ⟨h.1.2 v, h.2.2 v⟩⟩,
      fun h => ⟨⟨fun v => (h.1 v).1, fun v => (h.2 v).1⟩, fun v => (h.1 v).2, fun v => (h.2 v).2⟩⟩

end Transversal.Product
p2m_reactivate "P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal.Product"
p2m_reactivate "P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal.Product"

namespace TransversalMeasure

private theorem secondCountableTopology_archUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) : SecondCountableTopology (∀ w : v.Extension L, w.1.Completion)ˣ := by
  haveI : ∀ w : v.Extension L, SecondCountableTopology w.1.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w.1).isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (∀ w : v.Extension L, w.1.Completion)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end TransversalMeasure
p2m_reactivate "P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.Transversal.Product"

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      IsTopologicalGroup (L ⊗[K] v.adicCompletion K)ˣ ∧ LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ ∧
        T2Space (L ⊗[K] v.adicCompletion K)ˣ ∧ SecondCountableTopology (L ⊗[K] v.adicCompletion K)ˣ ∧
        IsCompact (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ∧ IsOpen (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)) ∧
    (∀ v : InfinitePlace K,
      IsTopologicalGroup (∀ w : v.Extension L, w.1.Completion)ˣ ∧ LocallyCompactSpace (∀ w : v.Extension L, w.1.Completion)ˣ ∧
        T2Space (∀ w : v.Extension L, w.1.Completion)ˣ ∧ SecondCountableTopology (∀ w : v.Extension L, w.1.Completion)ˣ) ∧
    (∀ Sf : Finset (HeightOneSpectrum (𝓞 K)),
      IsOpen {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v, v ∉ Sf → semiLocalIdele K L v t ∈ integralUnits K L v}) ∧
    (∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))) (y : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ)
      (x : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ),
      (∀ v, v ∉ Sf → x v ∈ integralUnits K L v) →
        ∃ t : (AdeleRing (𝓞 L) L)ˣ, (∀ v, archSemiLocalIdele K L v t = y v) ∧ ∀ v, semiLocalIdele K L v t = x v) ∧
    (∀ (D : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ) (C : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ),
      (∀ v, IsCompact (D v)) → (∀ v, IsCompact (C v)) →
        {v | C v ≠ (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite →
        IsCompact {t : (AdeleRing (𝓞 L) L)ˣ | (∀ v, archSemiLocalIdele K L v t ∈ D v) ∧ ∀ v, semiLocalIdele K L v t ∈ C v}) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), IsClosed (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)) ∧
    (∀ v : InfinitePlace K, IsClosed (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ)) := by
  refine ⟨?_, fun v => ?_, fun v => ?_, fun Sf => ?_, fun Sf y x hx => ?_, fun D C hD hC hfin => ?_, fun v => ?_, fun v => ?_⟩
  · exact Transversal.Product.secondCountableTopology_ideles L
  · exact ⟨TransversalMeasure.isTopologicalGroup_units K L v, TransversalMeasure.locallyCompactSpace_units K L v,
      TransversalMeasure.t2Space_units K L v, TransversalMeasure.secondCountableTopology_units K L v,
      TransversalMeasure.isCompact_integralUnits K L v, TransversalMeasure.isOpen_integralUnits K L v⟩
  · exact ⟨TransversalMeasure.isTopologicalGroup_archUnits K L v, TransversalMeasure.locallyCompactSpace_archUnits K L v,
      TransversalMeasure.t2Space_archUnits K L v, TransversalMeasure.secondCountableTopology_archUnits K L v⟩
  · exact Transversal.Product.isOpen_setOf_forall_semiLocalIdele_mem_integralUnits K L Sf
  · exact Transversal.Product.exists_archSemiLocalIdele_eq_and_semiLocalIdele_eq K L Sf y x hx
  · exact Transversal.Product.isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem K L D C hD hC hfin
  · exact TransversalMeasure.isClosed_normOneUnits K L v
  · exact TransversalMeasure.isClosed_archNormOneUnits K L v

end S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
end P2MW
export P2MW.S_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box (solution)
