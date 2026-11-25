-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:46.239821+00:00
-- url     : https://prove2.me/submissions/85d551a8-ff75-4110-a84a-fdd77ce03dbc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalBinaryGramIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreCpt_masses_field
import Theorems.Thm_GlobalTheory_T_completion_is_local_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreCpt
open GlobalTheory.CompanionTheory.SW.FibreRatio
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace GlobalTheory.CompanionTheory.SW.FibreCpt
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  intro F E _ _ _ _ _ σ hσ J hJ d b v lam hlam m hfib A hAc hAo hAU
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b lam hlam.1 m hfib A hAc hAo hAU
end GlobalTheory.CompanionTheory.SW.FibreCpt
