-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.base_block_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:57:19.005276+00:00
-- url     : https://prove2.me/submissions/2a41880c-819e-4489-bae5-806d4fdc631e

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FreeBlocks_base_intertwining

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

section Base

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)

lemma base_block_intertwines_oai
    (G : t.functional.GNS →L[ℂ] t.functional.GNS)
    (B : ∀ k, multiplicityLevel t S true k →L[ℂ] multiplicityLevel t S true k)
    (hb : ∀ k a (x : letterSpace t S false) v,
      G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k v)=
        repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k (B k v))
    (sl : letterSpace t S true) (sn : ‖sl‖=1) :
    G.comp (baseEmbedding t S hfree).toContinuousLinearMap=
      (baseEmbedding t S hfree).toContinuousLinearMap.comp (B 0) := by
  ext v
  change G (baseEmbedding t S hfree v)=baseEmbedding t S hfree (B 0 v)
  simpa only [map_one,one_apply_eq_self] using
    base_intertwining t S f hf hS hfree Bool.false_ne_true G B hb sl sn 0 1 v

end Base

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.base_block_intertwines_oai := @OAI.Kadison.FreeBlocks.base_block_intertwines_oai
