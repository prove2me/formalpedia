-- Prove2me | solution 1 for GlobalTheory.DualFormValues.trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:26.979737+00:00
-- url     : https://prove2.me/submissions/8e3f9ffa-fee4-4202-b77f-00d8243d95c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannClEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DualFormValues
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.DualFormValues
theorem _root_.solution (x : E) : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ => σ x) _ (fun σ => rfl)).symm
end GlobalTheory.DualFormValues
