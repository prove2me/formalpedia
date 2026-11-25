-- Prove2me | solution 1 for GlobalTheory.T.adelic_unitary_finite_set_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:16:36.619814+00:00
-- url     : https://prove2.me/submissions/9d04eb62-e14f-4bbe-9b03-14a830bbca4f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecompositionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_pure_h


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PureH.pure_h | exact GlobalTheory.CompanionTheory.SW.PureH.pure_h | (intros; apply GlobalTheory.CompanionTheory.SW.PureH.pure_h <;> assumption)
end _root_.GlobalTheory.T
