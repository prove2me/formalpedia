-- Prove2me | solution 1 for N25.cuspArithmeticCensus_geometric
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:56.297589+00:00
-- url     : https://prove2.me/submissions/67a226cb-1084-4fbb-bc82-8d92543639c9

import Mathlib
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_cusp_pole_lift_bijection
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

namespace N25

open Endgame

/-- There are fourteen geometric cusps of the actual rational level-twenty-five field. -/
theorem _root_.solution (ι : Qbar →+* ℂ) :
    Finite {P : GPlace // P.ord (emb25 j25) < 0} ∧
      Nat.card {P : GPlace // P.ord (emb25 j25) < 0} = 14 := by
  obtain ⟨κ,j,jC,hκ,hj,hjC,hκj,hfin,hfinC,hcard,hcardC,hlift⟩ :=
    cusp_pole_lift_bijection ι
  have heq : j = emb25 j25 := by
    apply Subtype.ext
    exact hj.trans (map_jqModC (algebraMap ℚ Qbar)).symm
  rw [heq] at hfin hcard
  exact ⟨hfin,hcard⟩

end N25
