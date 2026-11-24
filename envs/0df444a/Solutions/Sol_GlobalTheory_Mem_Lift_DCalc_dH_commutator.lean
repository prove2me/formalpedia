-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.dH_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:47.275707+00:00
-- url     : https://prove2.me/submissions/244972bc-8f55-4aa4-a791-df8255f63f38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_skew
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_dH_dH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.DCalc
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.Mem.Lift.DCalc
theorem _root_.solution (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have hs : IsSymmSndFDerivAt ℝ (fun u => ρ u f) 0 := hf'.contDiffAt.isSymmSndFDerivAt
    (by simpa using (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [dH_dH h hf u v, dH_dH h hf v u, hs v u, skew h0 u v, add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  push_cast
  ring
end GlobalTheory.Mem.Lift.DCalc
