-- Prove2me | solution 1 for N25.Endgame.cuspChoice25_spec
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:49.117688+00:00
-- url     : https://prove2.me/submissions/e976eb51-ab7b-4fe8-8030-2e0b246d97bb

import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_five_qPlaces_distinct

set_option autoImplicit false

namespace N25.Endgame

/-- The selected rational and geometric cusps share their free diamond orbit,
residue degrees, Galois invariance, and normalized rational orders. -/
theorem _root_.solution :
    (∀ f : FQ, gammaF25 (emb25 f) = emb25 (cuspChoice25.tauQ f)) ∧
    Function.Injective pQ25 ∧ Function.Injective pG25 ∧
    (∀ i : Fin 5, (pQ25 i).deg = 1 ∧ (pG25 i).deg = 1) ∧
    (∀ σ : N25.Gal, ∀ i : Fin 5,
      ModularCurve.arithmeticGalois FQ σ • pG25 i = pG25 i) ∧
    (∀ i : Fin 5, ∀ f : FQ,
      (pG25 i).ord (emb25 f) = (pQ25 i).ord f) := by
  exact N25.five_qPlaces_distinct.choose_spec.choose_spec.choose_spec

end N25.Endgame
