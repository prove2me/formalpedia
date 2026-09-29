-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses.centerALower_contains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:24:49.171685+00:00
-- url     : https://prove2.me/submissions/9724dfb5-1dd0-418c-9945-86aa5cc92e39

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_E8_Prod0001_endpoint_data
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage_checked_yBox_d0_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_endpointLogTwo_checked

namespace GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000














theorem centerALower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerALowerAlpha) centerALowerExp centerALowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerALowerExp) centerALowerLog fastLogWitness = true := by decide +kernel

theorem centerALower_denominators : DenominatorsPositive centerALowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerALower_yBox_eq : (yBox centerALowerInput).d0 = centerALowerYBox := by decide +kernel
































































































































































































































































end GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

namespace GeneralCK.Certificates.DyadicInterval
open GeneralCK.Certificates.DyadicInterval
theorem scale_pos (p : ℕ) : 0 < scale p := by unfold scale; positivity
theorem scale_cast_pos (p : ℕ) : 0 < (scale p : ℝ) := by exact_mod_cast scale_pos p
end GeneralCK.Certificates.DyadicInterval

namespace GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage
open GeneralCK.Certificates.DyadicInterval
theorem point_contains (p : ℕ) (n : ℤ) :
    (⟨n, n⟩ : DyadicInterval p).Contains ((n : ℝ) / (scale p : ℝ)) := by
  have he : (scale p : ℝ) * ((n : ℝ) / (scale p : ℝ)) = n := by
    field_simp [(scale_cast_pos p).ne']
  simpa only [Contains, he] using And.intro (le_refl (n : ℝ)) (le_refl (n : ℝ))
end GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage

open GeneralCK GeneralCK.Certificates
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses
theorem solution :
    centerALowerYBox.Contains (Y (lower E8TAxisProd0001PaddedInputs.centerAInput.alpha)) := by
  rw [← centerALower_yBox_eq]
  apply checked_yBox_d0_contains centerALower_primitive_checks.1
    centerALower_primitive_checks.2 endpointLogTwo_checked centerALower_denominators
  exact point_contains precision 3798893981423257492988718450954299577395399644
