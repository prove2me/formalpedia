-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.hform_sub_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:11:12.103253+00:00
-- url     : https://prove2.me/submissions/f26c64fc-af1a-4586-bc15-488211946536

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
open GlobalTheory.CompanionTheory.SW.QuasiRefl
variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}
namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
theorem _root_.solution (x y y' : Fin N → A) :
    hform τ H x (y - y') = hform τ H x y - hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_sub, dotProduct_sub]
end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
