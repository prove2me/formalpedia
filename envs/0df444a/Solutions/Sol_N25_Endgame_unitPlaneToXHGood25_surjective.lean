-- Prove2me | solution 1 for N25.Endgame.unitPlaneToXHGood25_surjective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:12:43.652786+00:00
-- url     : https://prove2.me/submissions/e94ade6f-3d6d-42e5-a9bb-2e230cf6b8a0

import Mathlib
import Theorems.Thm_N25_Endgame_unitPlaneToXHGood25_coordinates
import Definitions.Def_N25_UnitPlaneModularMapGoodCharacteristic
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Theorems.Thm_N25_Endgame_xHGood_eq_adjoin_units25
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le

/-! Generation by the two modular units makes plane evaluation surjective. -/
namespace N25.Endgame

/-- Every modular function in good characteristic is a rational function of the two plane units. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    Function.Surjective (unitPlaneToXHGood25 p hp K) := by
  let φ : N25.UnitPlaneFF25C K →ₐ[K] FBase K := unitPlaneToXHGood25 p hp K
  change Function.Surjective φ
  let L : IntermediateField K (FBase K) :=
    { φ.toRingHom.fieldRange with
      algebraMap_mem' := fun a =>
        ⟨algebraMap K (N25.UnitPlaneFF25C K) a, φ.commutes a⟩ }
  have hgen : IntermediateField.adjoin K
      ({N25.U25C K 0, N25.U25C K 0 / N25.U25C K 1} : Set (FBase K)) ≤ L := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨algebraMap (N25.UnitPlaneRing25C K) (N25.UnitPlaneFF25C K)
        (N25.unitPlaneU25C K), (unitPlaneToXHGood25_coordinates p hp K).1⟩
    · have hy' : y = N25.U25C K 0 / N25.U25C K 1 := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨algebraMap (N25.UnitPlaneRing25C K) (N25.UnitPlaneFF25C K)
        (N25.unitPlaneV25C K), (unitPlaneToXHGood25_coordinates p hp K).2⟩
  rw [xHGood_eq_adjoin_units25 p hp K] at hgen
  intro y
  exact hgen (show y ∈ (⊤ : IntermediateField K (FBase K)) from trivial)

end N25.Endgame
