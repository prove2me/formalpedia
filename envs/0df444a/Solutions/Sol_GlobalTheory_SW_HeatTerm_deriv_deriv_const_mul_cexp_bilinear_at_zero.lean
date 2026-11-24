-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.deriv_deriv_const_mul_cexp_bilinear_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:08.01281+00:00
-- url     : https://prove2.me/submissions/89a8ba1d-6d86-4f38-afea-46ca913a74b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution (K w q u v c : ℂ) :
    deriv (fun s : ℂ => deriv (fun t : ℂ =>
      K * cexp (w * (q + s * u + t * (v + s * c)))) 0) 0 =
      (w * c + w * w * (u * v)) * (K * cexp (w * q)) := by
  have h1 : ∀ s : ℂ, deriv (fun t : ℂ => K * cexp (w * (q + s * u + t * (v + s * c)))) 0 =
      K * (cexp (w * (q + s * u)) * (w * (v + s * c))) := by
    intro s
    have := ((((((hasDerivAt_id (0 : ℂ)).mul_const (v + s * c)).const_add (q + s * u)).const_mul
      w).cexp).const_mul K).deriv
    simpa using this
  simp only [h1]
  have h2 := (((((hasDerivAt_id (0 : ℂ)).mul_const u).const_add q).const_mul w).cexp)
  have h3 := (((hasDerivAt_id (0 : ℂ)).mul_const c).const_add v).const_mul w
  have := ((h2.fun_mul h3).const_mul K).deriv
  simp only [id] at this
  rw [this]
  simp
  ring
end GlobalTheory.SW.HeatTerm
