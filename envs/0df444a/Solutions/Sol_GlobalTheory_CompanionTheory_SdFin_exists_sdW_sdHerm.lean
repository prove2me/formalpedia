-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.exists_sdW_sdHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:44:51.687036+00:00
-- url     : https://prove2.me/submissions/836bb29a-63ce-45ba-a7d6-1481662baa57

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_properSpace_Fv
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_exists_of_bilin
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_BR_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_BR_nondeg
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_pairHerm_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_pairHerm_nondeg
import Theorems.Thm_GlobalTheory_T_adelic_character_local_nontrivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
namespace GlobalTheory.CompanionTheory.SdFin
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), (∃ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) n μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) n ν := by
  intro F E _ _ _ _ _ σ h M J hJ n ψ hψ v
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hc, hne⟩ := (GlobalTheory.T.adelic_character_local_nontrivial F ψ hψ).1 v
  have hu : ∀ t, ‖psiChar ψ v t‖ = 1 := fun t => hψ.2.1 _
  haveI hp : ProperSpace (Fv F v) := properSpace_Fv v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  let cE := (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)).equivFun
  let eE : (Fv F v ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Fv F v) :=
    { cE.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap cE.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap cE.symm.toLinearMap }
  haveI : T2Space (Fv F v ⊗[F] E) := eE.isEmbedding.t2Space
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eE.secondCountableTopology
  refine ⟨exists_of_bilin v (psiChar ψ v) hc hu hne _ (bilinW (Fv F v) σ J n) (BR_symm _ σ J hσ hJ)
    (BR_nondeg _ σ J hσ hJ), ?_⟩
  letI := hermModule (Fv F v) σ n
  haveI : Module.Finite (Fv F v) (HermR (Fv F v) σ n) :=
    Module.Finite.of_injective
      ({ toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
        HermR (Fv F v) σ n →ₗ[Fv F v] Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) Subtype.val_injective
  haveI : ContinuousSMul (Fv F v) (HermR (Fv F v) σ n) :=
    ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  exact exists_of_bilin v (psiChar ψ v) hc hu hne _ (bilinH (Fv F v) σ n) (pairHerm_symm _ σ n)
    (pairHerm_nondeg _ σ hσ n)
end GlobalTheory.CompanionTheory.SdFin
