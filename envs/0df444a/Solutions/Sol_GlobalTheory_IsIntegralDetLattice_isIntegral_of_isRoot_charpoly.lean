-- Prove2me | solution 1 for GlobalTheory.IsIntegralDetLattice.isIntegral_of_isRoot_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:53:56.875+00:00
-- url     : https://prove2.me/submissions/9c46aad9-a57f-41e8-85a6-4300e32e1095

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegralDetOfPreservesLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IsIntegralDetLattice
namespace GlobalTheory.IsIntegralDetLattice
theorem _root_.solution {R K : Type} [CommRing R] [Field K] [Algebra R K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (hA : IsIntegral R A) (x : K) (hx : A.charpoly.IsRoot x) :
    IsIntegral R x := by
  obtain ⟨p, hp, hpA⟩ := hA

  have hmem : x ∈ spectrum K A := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hx
  have h2 := spectrum.subset_polynomial_aeval A (p.map (algebraMap R K)) ⟨x, hmem, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hpA, spectrum.mem_iff, sub_zero] at h2
  refine ⟨p, hp, ?_⟩
  rw [eval₂_eq_eval_map]
  by_contra hne
  exact h2 ((Ne.isUnit hne).map (algebraMap K (Matrix (Fin N) (Fin N) K)))
end GlobalTheory.IsIntegralDetLattice
