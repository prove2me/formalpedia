-- Prove2me | solution 1 for GlobalTheory.T.rank_zero_gram_fiber_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:52.761867+00:00
-- url     : https://prove2.me/submissions/03c49817-f2d3-4fee-a191-a24f75b4b93e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankZeroGramFiberMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankZeroGramFiberMeasureStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramEmpty_fibre_gram_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | exact GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | (intros; apply GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero <;> assumption)
end _root_.GlobalTheory.T
