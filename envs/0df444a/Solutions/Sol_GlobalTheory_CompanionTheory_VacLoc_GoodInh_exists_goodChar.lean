-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:12.007685+00:00
-- url     : https://prove2.me/submissions/85b45e48-0586-4dd9-aa1f-8544aadad4ce

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_GoodInh_goodChar_of_hasConductor
import Theorems.Thm_GlobalTheory_SplitWeil_conductor_exists
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.GoodInh
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.VacLoc.GoodInh
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      (∃ ψ : AddChar k ℂ, GoodChar ψ 𝒪[k] 1) ∧
      ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ x, ‖ψ x‖ = 1) → ψ ≠ 1 → ∃ u : kˣ, GoodChar ψ 𝒪[k] u := by
  intro k _ _ _ _
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  refine ⟨?_, fun ψ hψc hψn hψ1 => ?_⟩
  · obtain ⟨-, ⟨χ, -, -, hχ⟩, -⟩ := GlobalTheory.SplitWeil.conductor_exists k
    exact ⟨_, goodChar_of_hasConductor χ 1 hχ⟩
  · let χ : AddChar k Circle :=
      { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (hψn x)⟩
        map_zero_eq_one' := Circle.ext (by simp)
        map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
    have hχψ : Circle.coeHom.compAddChar χ = ψ := AddChar.ext _ _ fun x => rfl
    have hχc : Continuous χ := hψc.subtype_mk _
    have hχ1 : χ ≠ 1 := by
      intro h1
      apply hψ1
      rw [← hχψ, h1]
      exact AddChar.ext _ _ fun x => by simp
    obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
    exact ⟨c, hχψ ▸ goodChar_of_hasConductor χ c hc⟩
end GlobalTheory.CompanionTheory.VacLoc.GoodInh
