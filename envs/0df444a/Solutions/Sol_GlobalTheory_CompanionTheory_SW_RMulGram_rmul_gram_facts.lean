-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:08:13.697467+00:00
-- url     : https://prove2.me/submissions/ec439b19-642c-4e84-a276-05502930846f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_gramR_rmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_rmul_rmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_rmul_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_actTup_rmul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RMulGram
namespace GlobalTheory.CompanionTheory.SW.RMulGram
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g ∧ rmul R (rmul R X g) g' = rmul R X (g * g') ∧ rmul R X 1 = X ∧ ∀ k : GL (Fin M) (R ⊗[F] E), actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  intro F E _ _ _ _ _ σ _ R _ _ M n J X g g'
  exact ⟨gramR_rmul R σ J X g, rmul_rmul R X g g', rmul_one R X, fun k => actTup_rmul R k X g⟩
end GlobalTheory.CompanionTheory.SW.RMulGram
