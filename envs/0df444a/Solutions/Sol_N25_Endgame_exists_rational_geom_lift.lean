-- Prove2me | solution 1 for N25.Endgame.exists_rational_geom_lift
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:53.531824+00:00
-- url     : https://prove2.me/submissions/db4fab65-1225-4478-bda7-049a5403051d

import Mathlib
import Definitions.Def_N25_ConstantFieldLift
import Theorems.Thm_N25_Endgame_exists_unique_constantFieldLift25
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
import Theorems.Thm_N25_Endgame_constantFieldLift25_degree_one
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_N25_Endgame_constantFieldLift25_galois_fixed
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false

namespace N25.Endgame

theorem _root_.solution (P : QPlace) (hP : P.deg = 1) :
    ∃ P' : GPlace, IsRationalGeomPlace P' ∧
      P'.toValuationSubring.comap emb25.toRingHom = P.toValuationSubring ∧
      ∀ f : FQ, P'.ord (emb25 f) = P.ord f := by
  obtain ⟨P', hLift, huniq⟩ := exists_unique_constantFieldLift25 P hP
  exact ⟨P', ⟨constantFieldLift25_degree_one P hP P' hLift,
    constantFieldLift25_galois_fixed P P' hLift huniq⟩, hLift⟩

end N25.Endgame
