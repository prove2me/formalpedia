-- Prove2me | solution 1 for GlobalTheory.HalfPairing.exists_equiv_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:55.264867+00:00
-- url     : https://prove2.me/submissions/fb770a01-9045-4d96-a0d4-411eb1af6c56

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HalfPairing
namespace GlobalTheory.HalfPairing
theorem _root_.solution {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (x : Fin r → Q) (hx : Submodule.span R (Set.range x) = ⊤) :
    ∃ ψ : (Fin r → R ⧸ I) ≃ₗ[R] Q, ∀ b, ψ (Pi.single b 1) = x b := by
  have hk : ∀ a ∈ I, ∀ q : Q, a • q = 0 := by
    intro a ha q
    apply e.injective
    rw [map_smul, map_zero]
    funext i
    rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
    rfl
  let f : Fin r → ((R ⧸ I) →ₗ[R] Q) := fun b =>
    Submodule.liftQ I (LinearMap.toSpanSingleton R Q (x b)) (fun a ha => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hk a ha _)
  have hf : ∀ b, f b 1 = x b := fun b => by
    have : f b (Submodule.Quotient.mk (1 : R)) = x b := by
      simp only [f, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    exact this
  let ψ : (Fin r → R ⧸ I) →ₗ[R] Q := ∑ b, (f b) ∘ₗ LinearMap.proj b
  have hψ : ∀ b, ψ (Pi.single b 1) = x b := fun b => by
    simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single b]
    · rw [Pi.single_eq_same, hf]
    · intro i _ hi; rw [Pi.single_eq_of_ne hi, map_zero]
    · simp
  have hs : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hx, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact ⟨_, hψ b⟩
  have hi : Function.Injective (e.toLinearMap ∘ₗ ψ) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hs)
  exact ⟨LinearEquiv.ofBijective ψ ⟨Function.Injective.of_comp (f := e) hi, hs⟩, hψ⟩
end GlobalTheory.HalfPairing
