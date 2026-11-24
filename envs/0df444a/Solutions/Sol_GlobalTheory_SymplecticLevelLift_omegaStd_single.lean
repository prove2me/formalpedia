-- Prove2me | solution 1 for GlobalTheory.SymplecticLevelLift.omegaStd_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:14:53.035814+00:00
-- url     : https://prove2.me/submissions/bb7cefe5-8668-48d2-a215-7f4e11a6e90c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticZmodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSymplecticBasisCongrLevelMod
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymplecticLevelLift
open Matrix Module
namespace GlobalTheory.SymplecticLevelLift
theorem _root_.solution {h : ℕ} (i j : Fin h ⊕ Fin h) :
    omegaStd (Pi.single i 1) (Pi.single j 1) = (-Matrix.J (Fin h) ℤ) i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [omegaStd, Matrix.J, Pi.single_apply, Matrix.one_apply, eq_comm]
end GlobalTheory.SymplecticLevelLift
