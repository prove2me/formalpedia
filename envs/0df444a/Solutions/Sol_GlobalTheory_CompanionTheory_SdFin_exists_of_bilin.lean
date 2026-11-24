-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.exists_of_bilin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:19.734509+00:00
-- url     : https://prove2.me/submissions/079a3c82-6633-4e51-9805-dc8b2c298e19

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_exists_of_std
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_properSpace_Fv
import Theorems.Thm_GlobalTheory_CharConductor_exists_exponent_of_valued
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.CompanionTheory.SdFin
theorem _root_.solution (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hne : ∃ t, ψ t ≠ 1) (V : Type) [AddCommGroup V] [Module (Fv F v) V] [Module.Finite (Fv F v) V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (β : LinearMap.BilinForm (Fv F v) V) (hs : ∀ x y, β x y = β y x)
    (hn : ∀ x, (∀ y, β x y = 0) → x = 0) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by
  haveI hp : ProperSpace (Fv F v) := properSpace_Fv v
  letI : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : IsModuleTopology (Fv F v) V := isModuleTopologyOfFiniteDimensional
  let c' := (Module.finBasis (Fv F v) V).equivFun
  have hcc : Continuous c' := IsModuleTopology.continuous_of_linearMap c'.toLinearMap
  have hcc' : Continuous c'.symm := IsModuleTopology.continuous_of_linearMap c'.symm.toLinearMap
  let eV : V ≃ₜ (Fin (Module.finrank (Fv F v) V) → Fv F v) :=
    { c'.toEquiv with continuous_toFun := hcc, continuous_invFun := hcc' }
  haveI : LocallyCompactSpace V := eV.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology V := eV.secondCountableTopology
  obtain ⟨n, hc⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued ψ hψ hne
  obtain ⟨c, hcv⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hcv.symm.trans (map_zero _))
  have hstd : GlobalTheory.JR.IsStdChar (ψ.mulShift c) := by
    constructor
    · intro x hx
      exact (hc c).2 hcv.le x (Valued.toNormedField.norm_le_one_iff.1 hx)
    · obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
      have h1 : ¬ ∀ s : Fv F v, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (c * t * s) = 1 := by
        rw [hc, map_mul, hcv, ht, ← WithZero.exp_add, WithZero.exp_le_exp]
        omega
      push Not at h1
      obtain ⟨s, hs1, hs2⟩ := h1
      refine ⟨t * s, by rwa [AddChar.mulShift_apply, ← mul_assoc], fun y hy => ?_⟩
      rw [Valued.toNormedField.norm_lt_one_iff] at hy
      rw [Valued.toNormedField.norm_le_one_iff, mul_right_comm, map_mul]
      refine mul_le_one' ?_ hs1
      rw [map_mul, ht]
      rcases eq_or_ne (Valued.v y : WithZero (Multiplicative ℤ)) 0 with h | h
      · simp [h]
      · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
        rw [← WithZero.exp_log h, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
  have hn' : ∀ x, (∀ y, (c⁻¹ • β) x y = 0) → x = 0 := fun x h => hn x fun y => by
    simpa [hc0] using h y
  have hs' : ∀ x y, (c⁻¹ • β) x y = (c⁻¹ • β) y x := fun x y => by simp [hs x y]
  have key := exists_of_std (ψ.mulShift c) hstd (fun t => hu _) V (c⁻¹ • β) ⟨hs'⟩
    ⟨hn', fun y h => hn' y fun x => (hs' y x).trans (h x)⟩
  have e : ∀ x y, ψ.mulShift c ((c⁻¹ • β) x y) = ψ (β x y) := fun x y => by
    simp [AddChar.mulShift_apply, hc0]
  simpa only [e] using key
end GlobalTheory.CompanionTheory.SdFin
