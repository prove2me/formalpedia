-- Prove2me | solution 1 for GlobalTheory.RiemannRel.differentiableOn_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:38.415948+00:00
-- url     : https://prove2.me/submissions/8f945f1d-31bc-49f1-8f69-b271c22f9702

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {g : ℕ}
namespace GlobalTheory.RiemannRel
namespace _root_.GlobalTheory.RiemannRel
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} (A : V → Matrix (Fin g) (Fin g) ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) :
    DifferentiableOn ℂ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  refine (differentiableOn_const _).mul ?_
  have hprod : (fun b => ∏ i, A b (σ i) i) = ∏ i, (fun b => A b (σ i) i) := by
    ext b; simp [Finset.prod_apply]
  rw [hprod]
  exact Finset.prod_induction _ (fun f => DifferentiableOn ℂ f B) (fun f f' hf hf' => hf.mul hf')
    (differentiableOn_const 1) fun i _ => hA (σ i) i
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
