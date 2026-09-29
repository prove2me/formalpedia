-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8e1b9a40-5f81-585b-8f46-a495923764f9

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W)) :
    Psp.reduceSnd β hβ δ W =
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα W)) := by
  have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).injective
  rcases hTD W with h1 | h2
  ·
    have hfix' : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα W))) =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ W) := by
      rw [← h1]; exact hfix
    exact (hinj hfix').symm
  · exact h2.symm

end S_ModularCurve_JHPlaceSpecialization_reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy (solution)
