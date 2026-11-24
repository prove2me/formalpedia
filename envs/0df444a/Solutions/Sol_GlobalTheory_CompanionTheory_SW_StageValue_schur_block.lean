-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StageValue.schur_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:55.593311+00:00
-- url     : https://prove2.me/submissions/e6d54398-525a-4d46-afff-1fe410beeb5d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_schurM_block
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__schur_coe_f974b9be1078


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageValue
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (t : F) (a : R → Rˣ) {n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.StageValue
theorem _root_.solution (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) :
    schur R σ t a (hermOf R σ _ hT') = hermOf R σ T hT := by
  apply Subtype.ext
  have hm : schurM R σ t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
    show schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) ∈ HermR R σ n
    rw [schurM_block]
    exact map_mem_HermR R σ T hT
  rw [schur_coe R σ t a _ hm]
  exact schurM_block R σ t a T
end GlobalTheory.CompanionTheory.SW.StageValue
