-- Prove2me | solution 1 for Nock.bridge_reflects_field_equality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:01.785749+00:00
-- url     : https://prove2.me/submissions/77192ee2-03e0-4b7b-91c8-439b6dde2b7b

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_FieldEmbedding_embBy_inj_of_boundedBy
public import Theorems.Thm_Nock_paper_field_bridge

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution (q : Nat) (hq : 1 < q)
    {fuel₁ fuel₂ : Nat} {s₁ f₁ s₂ f₂ r₁ r₂ : Noun}
    (hs₁ : FieldEmbedding.BoundedBy q s₁) (hf₁ : FieldEmbedding.BoundedBy q f₁)
    (hs₂ : FieldEmbedding.BoundedBy q s₂) (hf₂ : FieldEmbedding.BoundedBy q f₂)
    (hG₁ : evalGPaper q fuel₁ s₁ f₁ = some r₁)
    (hG₂ : evalGPaper q fuel₂ s₂ f₂ = some r₂)
    (himg : FieldEmbedding.embBy q r₁ = FieldEmbedding.embBy q r₂) : r₁ = r₂ :=
  FieldEmbedding.embBy_inj_of_boundedBy
    (paper_field_bridge q hq hs₁ hf₁ hG₁).2.2.2.2.2
    (paper_field_bridge q hq hs₂ hf₂ hG₂).2.2.2.2.2 himg
end Nock
