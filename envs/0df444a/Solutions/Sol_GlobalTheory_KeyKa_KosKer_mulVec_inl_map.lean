-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosKer.mulVec_inl_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:14.640521+00:00
-- url     : https://prove2.me/submissions/aed99eae-ea40-4bba-9600-f68f35dcfd2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulVecCongrDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosKer
open Matrix
variable {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa.KosKer
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d' : ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (ev' : ∀ j, Matrix (Fin d') (Fin (N j)) S)
    (u : KIx g d N → R) (u' : KIx g d' N → S) (hu : ∀ q, u' (.inl q) = f (u (.inl q))) (p) :
    (kosD (fun i j j' => (m i j j').map f) ev' *ᵥ u') (.inl p) = f ((kosD m ev *ᵥ u) (.inl p)) := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    map_sum, map_mul, hu, apply_ite f, map_zero, map_pow, map_neg, map_one, Matrix.map_apply]
end GlobalTheory.KeyKa.KosKer
