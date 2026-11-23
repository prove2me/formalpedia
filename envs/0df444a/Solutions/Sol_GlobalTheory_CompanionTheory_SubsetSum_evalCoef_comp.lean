-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.evalCoef_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:03.369653+00:00
-- url     : https://prove2.me/submissions/43368c8c-7065-494b-bded-7c9d799ce6c4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubsetSum
namespace GlobalTheory.CompanionTheory.SubsetSum
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (P : R[X]) :
    f.comp (evalCoef n P) = evalCoef n (P.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp [evalCoef]
  · intro j; simp [evalCoef, coeff_map]
end GlobalTheory.CompanionTheory.SubsetSum
