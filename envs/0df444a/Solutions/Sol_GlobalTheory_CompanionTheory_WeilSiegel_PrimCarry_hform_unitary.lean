-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.hform_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:11:14.020363+00:00
-- url     : https://prove2.me/submissions/d5c5575d-51db-43e7-92b5-7f436d3485ea

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
theorem _root_.solution {g : GL (Fin N) A} (hg : g ∈ UJ τ H) (x y : Fin N → A) :
    hform τ H ((g : Matrix (Fin N) (Fin N) A) *ᵥ x) ((g : Matrix (Fin N) (Fin N) A) *ᵥ y) =
      hform τ H x y := by
  rw [hform_mulVec']
  have hg' : cT τ (g : Matrix (Fin N) (Fin N) A) * H * (g : Matrix (Fin N) (Fin N) A) = H := hg
  rw [hg']
end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
