-- Prove2me | solution 1 for GlobalTheory.CoeffFunctional.coeffMap_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:34.588709+00:00
-- url     : https://prove2.me/submissions/35f5918d-34bc-494b-9bc1-6df397b71c8a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemHHaOfCoeffFunctional
import Theorems.Thm_GlobalTheory_CoeffFunctional_coeff_coeffMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffFunctional
open MvPolynomial
variable {σ K L : Type} [Field K] [Field L] [Algebra K L]
namespace GlobalTheory.CoeffFunctional
theorem _root_.solution (φ : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coeffMap φ (P + Q) = coeffMap φ P + coeffMap φ Q := by
  ext μ
  simp [coeff_coeffMap]
end GlobalTheory.CoeffFunctional
