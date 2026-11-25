-- Prove2me | solution 1 for GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:39.354517+00:00
-- url     : https://prove2.me/submissions/e3f956f1-b365-47ba-9b0a-9ae0e68ca21e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChartStatement
import Theorems.Thm_GlobalTheory_ResidueDegreeChart_residueDegree_eq_inertiaDeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  first | exact @GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | exact GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | (intros; apply GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg <;> assumption)
end _root_.GlobalTheory.T
