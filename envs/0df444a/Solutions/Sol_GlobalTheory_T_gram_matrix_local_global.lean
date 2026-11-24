-- Prove2me | solution 1 for GlobalTheory.T.gram_matrix_local_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:10:59.901234+00:00
-- url     : https://prove2.me/submissions/443de216-7d63-47e9-bf91-8a6fd870aa77

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_gram_local


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : (Fin n → Fin M → AF F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) E), (gramR (AF F) σ J X = T.map (inclR (AF F)) ↔ gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) ∧ ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) ∧ ∀ Y : Fin n → Fin M → E, gramR (AF F) σ J (ratTup (AF F) Y) = (gramE σ J Y).map (inclR (AF F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramLocal.gram_local | exact GlobalTheory.CompanionTheory.SW.GramLocal.gram_local | (intros; apply GlobalTheory.CompanionTheory.SW.GramLocal.gram_local <;> assumption)
end _root_.GlobalTheory.T
