-- Prove2me | solution 1 for MatchingLogic.completedStar_mem_completedInterp_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:08.097011+00:00
-- url     : https://prove2.me/submissions/dddada07-28aa-4ea7-a0b3-f86824260d6c

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Theorems.Thm_MatchingLogic_completedEmbed_injective
public import Theorems.Thm_MatchingLogic_completedStar_ne_embed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCompletion
namespace MatchingLogic
theorem _root_.solution
    {root : CanonicalCarrier S} (hmissing : Missing root) {sigma : S.Sym}
    (components : Fin (S.arity sigma) → GeneratedCarrier root) :
    completedStar hmissing ∈
        completedInterp root sigma (fun i => completedEmbed root (components i)) ↔
      ∃ i, components i = generatedRoot root := by
  constructor
  · rintro ⟨components', hinputs, hreal | hstar⟩
    · rcases hreal with ⟨world, hout, _⟩
      exact False.elim (completedStar_ne_embed hmissing world hout)
    · have hcomponents : components = components' := by
        funext i
        exact completedEmbed_injective root (hinputs i)
      subst components'
      exact hstar.2
  · intro hroot
    exact ⟨components, fun _ => rfl, Or.inr ⟨rfl, hroot⟩⟩
end MatchingLogic
