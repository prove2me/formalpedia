-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.isTopologicalBasis_vball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:15.782493+00:00
-- url     : https://prove2.me/submissions/1e568c6c-d2c0-47d3-827c-d0403144fda4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_IsRadius_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_isOpen_vball
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution :
    TopologicalSpace.IsTopologicalBasis {s : Set K | ∃ (x : K) (γ : ℤᵐ⁰), s = vball x γ ∧ IsRadius K γ} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨x, γ, rfl, hγ⟩
    exact isOpen_vball x hγ
  · intro a u ha hu
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (hu.mem_nhds ha)
    have hr : IsRadius K (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) := ⟨γ, rfl⟩
    refine ⟨vball a _, ⟨a, _, rfl, hr⟩, ?_, ?_⟩
    · simpa [vball] using zero_lt_iff.2 hr.ne_zero
    · intro y hy
      apply hγ
      simpa only [vball, Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] using hy
end GlobalTheory.CompanionTheory.SW.QuadIso
