-- Prove2me | solution 1 for GlobalTheory.etale_mvPolynomial_map_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:58.754744+00:00
-- url     : https://prove2.me/submissions/caed33c8-6a8b-4942-93a2-aebacb684e92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {B A N : Type} [CommRing B] [CommRing A] (g : B →+* A)
    (hg : g.Etale) : (MvPolynomial.map (σ := N) g).Etale := by
  letI := g.toAlgebra
  letI : Algebra (MvPolynomial N B) (MvPolynomial N A) := MvPolynomial.algebraMvPolynomial
  exact RingHom.Etale.isStableUnderBaseChange B A (MvPolynomial N B) (MvPolynomial N A) hg
end _root_.GlobalTheory
end GlobalTheory
