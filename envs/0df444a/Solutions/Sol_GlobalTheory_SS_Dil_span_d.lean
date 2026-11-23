-- Prove2me | solution 1 for GlobalTheory.SS.Dil.span_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:20.522806+00:00
-- url     : https://prove2.me/submissions/5b445e9c-c9df-49f1-aae1-ad412363a955

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution (R B S : Type) [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (Q : Submodule S (S ⊗[B] (KaehlerDifferential R B))) (h : ∀ b, (1 : S) ⊗ₜ[B] KaehlerDifferential.D R B b ∈ Q) :
    ∀ x, x ∈ Q := by
  have h1 : ∀ ω : KaehlerDifferential R B, (1 : S) ⊗ₜ[B] ω ∈ Q := by
    intro ω
    have : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact h b
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact Q.add_mem hx hy
    | smul b x _ hx =>
      rw [tmul_smul, ← algebraMap_smul S b]; exact Q.smul_mem _ hx
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact Q.zero_mem
  | tmul s ω =>
    have := Q.smul_mem s (h1 ω)
    rwa [smul_tmul', smul_eq_mul, mul_one] at this
  | add x y hx hy => exact Q.add_mem hx hy
end GlobalTheory.SS.Dil
