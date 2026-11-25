-- Prove2me | solution 1 for GlobalTheory.T.hermitian_forms_integrally_equivalent_almost_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:48:57.774692+00:00
-- url     : https://prove2.me/submissions/f8cefd4b-5cc6-4595-a667-1ad4f62b4471

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormsIntegrallyEquivalentAlmostAll
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormsIntegrallyEquivalentAlmostAllStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodIso_good_iso


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ g : GL (Fin M) (Fv F v ⊗[F] E), JR (Fv F v) J' = cT (sigR (Fv F v) σ) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) g X ∈ latV b v ↔ X ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodIso.good_iso | exact GlobalTheory.CompanionTheory.SW.GoodIso.good_iso | (intros; apply GlobalTheory.CompanionTheory.SW.GoodIso.good_iso <;> assumption)
end _root_.GlobalTheory.T
