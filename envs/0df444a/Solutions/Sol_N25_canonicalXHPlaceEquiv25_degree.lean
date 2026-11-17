-- Prove2me | solution 1 for N25.canonicalXHPlaceEquiv25_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:19:47.143319+00:00
-- url     : https://prove2.me/submissions/778acb6f-8db6-4f57-ad7f-a49cc0da0eb8

import Definitions.Def_N25_CanonicalModularDictionary

/-! Coordinates, degrees and orders under the canonical modular dictionary. -/
namespace N25

/-- The specified place identification preserves residue degrees. -/
theorem _root_.solution
    (P : AlgebraicCurve.Place ℚ (CanonicalFF25 ℚ)) :
    (canonicalXHPlaceEquiv25 P).deg = P.deg :=
  AlgebraicCurve.Place.deg_congrRingEquiv canonicalXHAlgEquiv25.toRingEquiv
    (fun a => canonicalXHAlgEquiv25.commutes a) P

end N25
