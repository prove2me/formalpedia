-- Prove2me | solution 1 for GlobalTheory.GenSep.val_eq_of_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:28.04194+00:00
-- url     : https://prove2.me/submissions/1fc70678-1da8-4b27-bd77-620fcf6dc1ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {Ω F F' : Type} [Field Ω] [Field F] [Field F'] (w : AddValuation F (WithTop ℤ))
  (w' : AddValuation F' (WithTop ℤ)) (ι : Ω →+* F) (ι' : Ω →+* F')
namespace GlobalTheory.GenSep
theorem _root_.solution {r a : F} {n : ℤ} (h : ((n + 1 : ℤ) : WithTop ℤ) ≤ w (r - a)) :
    w r = n ↔ w a = n := by
  have hlt : (n : WithTop ℤ) < w (r - a) := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by omega)) h
  constructor
  · intro hr
    have : a = r + -(r - a) := by ring
    rw [this, AddValuation.map_add_eq_of_lt_left _ (by rw [AddValuation.map_neg, hr]; exact hlt), hr]
  · intro ha
    have : r = a + (r - a) := by ring
    rw [this, AddValuation.map_add_eq_of_lt_left _ (by rw [ha]; exact hlt), ha]
end GlobalTheory.GenSep
