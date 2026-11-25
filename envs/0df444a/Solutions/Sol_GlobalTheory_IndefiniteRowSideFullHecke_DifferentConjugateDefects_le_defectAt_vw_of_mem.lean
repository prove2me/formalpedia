-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.le_defectAt_vw_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:45.198599+00:00
-- url     : https://prove2.me/submissions/48f1e955-e821-40a3-a39f-90756a1bb250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K))
    (h : ((n' : ℕ) : 𝓞 K) ∈ la.asIdeal) : a ≤ defectAt_vw σ n' a la := by
  have h1 : 0 < ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}) :=
    dvd_iff_multiplicity_pos.mpr (Ideal.dvd_span_singleton.mpr h)
  exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le h1 (le_max_right _ _))
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
