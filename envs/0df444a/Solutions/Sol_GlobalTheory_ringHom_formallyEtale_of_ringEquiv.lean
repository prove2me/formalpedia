-- Prove2me | solution 1 for GlobalTheory.ringHom_formallyEtale_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:52.549476+00:00
-- url     : https://prove2.me/submissions/41a4d3b3-1feb-48cd-8a94-613ed1d1c301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) : (e : S →+* T).FormallyEtale := by
  algebraize [(e : S →+* T)]
  exact Algebra.FormallyEtale.of_equiv (R := S) (A := S) (B := T)
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))
end GlobalTheory
