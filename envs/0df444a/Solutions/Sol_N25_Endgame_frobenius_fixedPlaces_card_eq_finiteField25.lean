-- Prove2me | solution 1 for N25.Endgame.frobenius_fixedPlaces_card_eq_finiteField25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:56.381113+00:00
-- url     : https://prove2.me/submissions/37c4f267-989a-4647-801c-e3e73c27ac03

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_N25_Endgame_frobenius_fixedPlaces_card_eq_finiteField_of_algebra25

/-! Fixed-place counts of prime Frobenius iterates over finite coefficient fields. -/
noncomputable section

namespace N25.Endgame

/-- Prime Frobenius iterated by the finite-field degree counts its degree-one places. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (hn : 0 < n) (hk : Nat.card k = p ^ n) :
    Nat.card (Function.fixedPoints ((ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n])) =
      Nat.card {P : AlgebraicCurve.Place k (FBase k) // P.deg = 1} := by
  let : Algebra (ZMod p) k := ZMod.algebra _ _
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  let : Module.Finite (ZMod p) k := Module.Finite.of_finite
  let e : k →ₐ[ZMod p] K := IsAlgClosed.lift
  let : Algebra k K := e.toRingHom.toAlgebra
  exact frobenius_fixedPlaces_card_eq_finiteField_of_algebra25 p k K n hn hk

end N25.Endgame
