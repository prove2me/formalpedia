-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:24:00.942868+00:00
-- url     : https://prove2.me/submissions/c40c4785-d920-4d0e-860d-cff272470ab1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_measure_quad
import Theorems.Thm_GlobalTheory_T_completion_is_local_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ a c : Fv F v, Valued.v a = 1 → c ∈ v.adicCompletionIntegers F → ∀ A : Set (Fv F v), MeasurableSet A → lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  intro F _ _ v lam hlam _ a c ha hc A hA
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hH, h1⟩ := hlam
  haveI := hH
  obtain ⟨_, _, hsc, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := hsc
  have hfin : lam {s : Fv F v | Valued.v s < 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    rw [← h1]
    refine measure_mono fun s hs => ?_
    exact (Valuation.mem_integer_iff _ _).2 (le_of_lt hs)
  exact GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad lam hfin ha hc hA
end GlobalTheory.CompanionTheory.SW.QuadIso
