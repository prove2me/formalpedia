-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSupport.exists_generalizedInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:13.801572+00:00
-- url     : https://prove2.me/submissions/5111aa1c-c045-459d-b42f-15144d889775

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalSupportExists
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSupport
namespace GlobalTheory.CompanionTheory.TyFinSupport
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) : ∃ g : W →ₗ[ℂ] V, Φ ∘ₗ g ∘ₗ Φ = Φ := by
  obtain ⟨r, hr⟩ := Φ.rangeRestrict.exists_rightInverse_of_surjective Φ.range_rangeRestrict
  obtain ⟨π, hπ⟩ := (LinearMap.range Φ).subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))
  refine ⟨r ∘ₗ π, ?_⟩
  ext x
  have h1 : π (Φ x) = Φ.rangeRestrict x := LinearMap.congr_fun hπ (Φ.rangeRestrict x)
  have h2 : Φ.rangeRestrict (r (Φ.rangeRestrict x)) = Φ.rangeRestrict x :=
    LinearMap.congr_fun hr (Φ.rangeRestrict x)
  have h3 := congrArg Subtype.val h2
  simp only [LinearMap.comp_apply, h1]
  exact h3
end GlobalTheory.CompanionTheory.TyFinSupport
