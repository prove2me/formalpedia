-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockAlg.gramE_consTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:28:08.959887+00:00
-- url     : https://prove2.me/submissions/fae6d47b-9ca2-4dcf-96d8-22bbb3542490

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_hE_blockOne_cons
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_hE_zero_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_hE_zero_right

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.BlockAlg
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : E) {n : ℕ}
    (X : Fin n → Fin M → E) :
    gramE σ (blockOne t J) (consTup X) = blockOne t (gramE σ J X) := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 1 (fun _ => 0)) = t
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 0 (X b)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 1 (fun _ => 0)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_right]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 0 (X b)) = hE σ J (X a) (X b)
    rw [hE_blockOne_cons]
    simp
end GlobalTheory.CompanionTheory.SW.BlockAlg
