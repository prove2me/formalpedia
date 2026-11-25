-- Prove2me | solution 1 for GlobalTheory.GenSep.subst_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:32:41.112516+00:00
-- url     : https://prove2.me/submissions/0984a96e-8d00-4c86-bb56-841f57609976

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_Formalism_L2_Pj_LocAlg_C_mem_intPoly
import Theorems.Thm_Formalism_L2_Pj_LocAlg_X_mem_intPoly


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
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace GlobalTheory.GenSep
theorem _root_.solution (x : Fin N → Ω) (j0 : Fin N) {W : Subring Ω} (hW : ∀ k, x k / x j0 ∈ W)
    (p : Fin (D + 1) × Fin N) : subst x j0 p ∈ Formalism.L2.Pj.LocAlg.intPoly _ W := by
  unfold subst
  split_ifs
  · exact Formalism.L2.Pj.LocAlg.X_mem_intPoly _
  · exact Subring.neg_mem _ (sum_mem fun k _ => Subring.mul_mem _
      (Formalism.L2.Pj.LocAlg.C_mem_intPoly (hW _)) (Formalism.L2.Pj.LocAlg.X_mem_intPoly _))
end GlobalTheory.GenSep
