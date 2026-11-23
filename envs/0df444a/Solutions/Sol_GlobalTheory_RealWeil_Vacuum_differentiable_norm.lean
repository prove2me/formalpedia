-- Prove2me | solution 1 for GlobalTheory.RealWeil.Vacuum.differentiable_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:13.028434+00:00
-- url     : https://prove2.me/submissions/6751f1c9-8358-49db-9d37-d16adfd69513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Theorems.Thm_GlobalTheory_RealWeil_contDiff_gau_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Vacuum
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.RealWeil.Vacuum
theorem _root_.solution (f : B) (hf : Sm ρ f) : Differentiable ℝ fun u => (gau u)⁻¹ • ρ u f :=
  ((contDiff_gau_inv (V := V)).smul hf).differentiable (by simp)
end GlobalTheory.RealWeil.Vacuum
