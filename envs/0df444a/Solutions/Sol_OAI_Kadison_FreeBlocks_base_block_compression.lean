-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.base_block_compression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:56:56.258386+00:00
-- url     : https://prove2.me/submissions/100ee6b7-036c-432c-913c-7a6fda0296ca

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FreeBlocks_base_block_intertwines

section
-- module Solutions.OAIQ039_CM.Commutator_FreeStageHankel
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments DihedralCorner

lemma compressed_commutator_eq {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] H) (G L : H →L[ℂ] H) (B : E →L[ℂ] E)
    (hG : G.comp U=U.comp B) (hG' : G.adjoint.comp U=U.comp B.adjoint) :
    U.adjoint.comp ((G*L-L*G).comp U)=
      B*(U.adjoint.comp (L.comp U))-(U.adjoint.comp (L.comp U))*B := by
  have hl : U.adjoint.comp G=B.comp U.adjoint := by
    simpa only [adjoint_comp,adjoint_adjoint] using
      congrArg (adjoint (𝕜:=ℂ) (E:=E) (F:=H)) hG'
  calc
    _ = (U.adjoint.comp G).comp (L.comp U) -
        (U.adjoint.comp L).comp (G.comp U) := by
      change U.adjoint.comp ((G.comp L-L.comp G).comp U)=_
      simp only [sub_comp,comp_sub,←comp_assoc]
    _ = (B.comp U.adjoint).comp (L.comp U) -
        (U.adjoint.comp L).comp (U.comp B) := by rw [hl,hG]
    _ = _ := by simp only [←comp_assoc]; rfl

section Base

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)

lemma base_block_compression_oai
    (G L : t.functional.GNS →L[ℂ] t.functional.GNS)
    (B : ∀ k, multiplicityLevel t S true k →L[ℂ] multiplicityLevel t S true k)
    (hb : ∀ k a (x : letterSpace t S false) v,
      G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k v)=
        repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k (B k v))
    (hb' : ∀ k a (x : letterSpace t S false) v,
      G.adjoint (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k v)=
        repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k ((B k).adjoint v))
    (sl : letterSpace t S true) (sn : ‖sl‖=1) :
    (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0) (F:=t.functional.GNS)
      (baseEmbedding t S hfree).toContinuousLinearMap).comp
      ((G*L-L*G).comp (baseEmbedding t S hfree).toContinuousLinearMap)=
    B 0*((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0) (F:=t.functional.GNS)
      (baseEmbedding t S hfree).toContinuousLinearMap).comp
      (L.comp (baseEmbedding t S hfree).toContinuousLinearMap))-
      ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0) (F:=t.functional.GNS)
      (baseEmbedding t S hfree).toContinuousLinearMap).comp
      (L.comp (baseEmbedding t S hfree).toContinuousLinearMap))*B 0 := by
  have h0 := base_block_intertwines t S f hf hS hfree G B hb sl sn
  have h1 := base_block_intertwines t S f hf hS hfree G.adjoint
    (fun k => (B k).adjoint) hb' sl sn
  exact @compressed_commutator_eq t.functional.GNS (multiplicityLevel t S true 0)
    (inferInstanceAs (NormedAddCommGroup t.functional.GNS))
    (inferInstanceAs (InnerProductSpace ℂ t.functional.GNS))
    (inferInstanceAs (CompleteSpace t.functional.GNS))
    (inferInstanceAs (NormedAddCommGroup (multiplicityLevel t S true 0)))
    (inferInstanceAs (InnerProductSpace ℂ (multiplicityLevel t S true 0)))
    (inferInstanceAs (CompleteSpace (multiplicityLevel t S true 0)))
    (baseEmbedding t S hfree).toContinuousLinearMap G L (B 0) h0 h1

end Base

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.base_block_compression_oai := @OAI.Kadison.FreeBlocks.base_block_compression_oai
