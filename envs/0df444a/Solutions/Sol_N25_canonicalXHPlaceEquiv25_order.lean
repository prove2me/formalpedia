-- Prove2me | solution 1 for N25.canonicalXHPlaceEquiv25_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:19:47.689723+00:00
-- url     : https://prove2.me/submissions/c08953db-9dd6-406c-8e96-eaf21a1df1fa

import Definitions.Def_N25_CanonicalModularDictionary

/-! Coordinates, degrees and orders under the canonical modular dictionary. -/
namespace N25

/-- Valuations of every rational function agree through the field dictionary. -/
theorem _root_.solution
    (P : AlgebraicCurve.Place ℚ (CanonicalFF25 ℚ)) (f : CanonicalFF25 ℚ) :
    (canonicalXHPlaceEquiv25 P).ord (canonicalXHAlgEquiv25 f) = P.ord f :=
  AlgebraicCurve.Place.ord_congrRingEquiv canonicalXHAlgEquiv25.toRingEquiv
    (fun a => canonicalXHAlgEquiv25.commutes a) P f

end N25
