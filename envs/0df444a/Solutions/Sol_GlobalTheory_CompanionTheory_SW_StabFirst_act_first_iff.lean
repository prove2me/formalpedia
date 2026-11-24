-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.act_first_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:33:37.886548+00:00
-- url     : https://prove2.me/submissions/0a725b32-0e54-43b0-a57a-ef36e95a68f1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mulVec_first

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution {n : ℕ} (h : HA R σ (blockOne s J)) :
    actW R σ _ h (fun _ : Fin n.succ => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin n.succ => Fin.cons 1 (fun _ => 0)) ↔
      ((HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) 0 0 = 1 ∧
        ∀ i : Fin M, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) i.succ 0 = 0) := by
  constructor
  · intro e
    have e' : ∀ a, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) a 0 =
        (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) a := by
      intro a
      exact (mulVec_first _ a).symm.trans (congrFun (congrFun e 0) a)
    exact ⟨by simpa using e' 0, fun i => by simpa using e' i.succ⟩
  · rintro ⟨h0, hi⟩
    funext c a
    change (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec _ a = _
    rw [mulVec_first]
    refine Fin.cases ?_ (fun i => ?_) a
    · simpa using h0
    · simpa using hi i
end GlobalTheory.CompanionTheory.SW.StabFirst
