-- Prove2me | solution 1 for GlobalTheory.T.local_gram_fiber_rank_one_set_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:52.928478+00:00
-- url     : https://prove2.me/submissions/263f39c7-b22b-4931-8c67-9b0622de71a9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_fibre_mass_ratio


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ s : Fv F v, s ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 s, ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermScal (Fv F v) σ s) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  first | exact @GlobalTheory.CompanionTheory.SW.fibre_mass_ratio | exact GlobalTheory.CompanionTheory.SW.fibre_mass_ratio | (intros; apply GlobalTheory.CompanionTheory.SW.fibre_mass_ratio <;> assumption)
end _root_.GlobalTheory.T
