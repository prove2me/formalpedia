-- Prove2me | solution 1 for GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:40.357915+00:00
-- url     : https://prove2.me/submissions/4305d203-587d-4dfa-b3f3-c848ac4b0057

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart
import Theorems.Thm_GlobalTheory_ResidueDegreeChart_inertiaDeg_eq_finrank_of_ker
import Theorems.Thm_GlobalTheory_ResidueDegreeChart_mem_primeIdealOf_iff
import Theorems.Thm_GlobalTheory_ResidueDegreeChart_exists_eq_div_evaluation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ResidueDegreeChart
namespace GlobalTheory.ResidueDegreeChart
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  intro X Y g V hV hU w hw
  let _ : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  let _ : Algebra (X.residueField (g w)) (Y.residueField w) := (g.residueFieldMap w).hom.toAlgebra
  symm
  exact inertiaDeg_eq_finrank_of_ker (X.evaluation V (g w) hw).hom
    (Y.evaluation (g ⁻¹ᵁ V) w hw).hom _ (mem_primeIdealOf_iff hU w hw)
    (exists_eq_div_evaluation hV (g w) hw) (exists_eq_div_evaluation hU w hw)
    (fun r => Scheme.evaluation_naturality_apply g w hw r)
end GlobalTheory.ResidueDegreeChart
