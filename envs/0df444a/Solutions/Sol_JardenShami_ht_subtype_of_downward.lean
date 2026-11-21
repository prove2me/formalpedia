-- Prove2me | solution 1 for JardenShami.ht_subtype_of_downward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:19.428166+00:00
-- url     : https://prove2.me/submissions/4ba3f15a-c35a-4c46-97a2-b0bfa46a1ef9

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {S : Set T} (hS : ∀ s ∈ S, ∀ t < s, t ∈ S) (x : S) :
    ht x = ht (x : T) := by
  unfold ht
  refine RelIso.ordinalType_congr ?_
  exact
    { toFun := fun y => ⟨y.1.1, y.2⟩
      invFun := fun t => ⟨⟨t.1, hS x x.2 t.1 t.2⟩, t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
end JardenShami
