-- Prove2me | solution 1 for ModularCurve.exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2218ca14-5907-5aa2-ba32-3a227059f7d9

import Definitions.Def_ModularCurve_X0
import Theorems.Thm_LaurentSeries_exists_eq_C_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldFull"
p2m_open "ModularCurve"

namespace AlgClosedFull

variable (N : ℕ) [NeZero N]

def v : ↥(modularFunctionFieldFull N) →+* LaurentSeries ℚ :=
  { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl,
    map_zero' := rfl, map_add' := fun _ _ => rfl }

theorem isAlgebraic_coe (x : ↥(modularFunctionFieldFull N)) (hx : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (x : LaurentSeries ℚ) := by
  obtain ⟨p, hp0, hpx⟩ := hx
  have key : ((Polynomial.aeval x p : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
      Polynomial.aeval (x : LaurentSeries ℚ) p := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    change v N (Polynomial.eval₂ (algebraMap ℚ ↥(modularFunctionFieldFull N)) x p) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    · exact Subsingleton.elim _ _
  refine ⟨p, hp0, ?_⟩
  rw [← key, hpx]
  rfl

theorem main (x : ↥(modularFunctionFieldFull N)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(modularFunctionFieldFull N) c := by
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic (x : LaurentSeries ℚ) (isAlgebraic_coe N x hx)
  refine ⟨c, Subtype.ext ?_⟩
  rw [hc]

  exact congrArg (fun f : ℚ →+* LaurentSeries ℚ => f c)
    (Subsingleton.elim (HahnSeries.C : ℚ →+* LaurentSeries ℚ) ((v N).comp (algebraMap ℚ ↥(modularFunctionFieldFull N))))

end AlgClosedFull

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull.ModularCurve"

theorem solution
    (N : ℕ) [NeZero N] (x : ↥(modularFunctionFieldFull N)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(modularFunctionFieldFull N) c :=
  ModularCurve.AlgClosedFull.main N x hx

end S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull
end P2MW
export P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull (solution)
