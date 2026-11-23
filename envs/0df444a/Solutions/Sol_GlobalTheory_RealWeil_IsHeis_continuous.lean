-- Prove2me | solution 1 for GlobalTheory.RealWeil.IsHeis.continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:20.038888+00:00
-- url     : https://prove2.me/submissions/4d4168d0-c477-4327-a669-2a769c2ac375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
namespace GlobalTheory.RealWeil
namespace IsHeis
theorem _root_.solution {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) {Y : Type} [TopologicalSpace Y]
    {a : Y → V} {x : Y → B} (ha : Continuous a) (hx : Continuous x) : Continuous fun y => ρ (a y) (x y) := by
  have : Continuous fun p : B × V => ρ p.2 p.1 :=
    continuous_prod_of_continuous_lipschitzWith (fun p : B × V => ρ p.2 p.1) 1
      (fun f => h.2.2.2 f) fun v => LipschitzWith.of_dist_le_mul fun x y => by
        simp only [dist_eq_norm, ← map_sub, h.2.2.1]; simp
  exact this.comp (hx.prodMk ha)
end IsHeis
end GlobalTheory.RealWeil
