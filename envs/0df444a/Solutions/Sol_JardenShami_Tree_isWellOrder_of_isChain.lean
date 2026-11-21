-- Prove2me | solution 1 for JardenShami.Tree.isWellOrder_of_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:06.974117+00:00
-- url     : https://prove2.me/submissions/1550921a-59dd-460d-bc4d-2e5dcd19311d

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {b : Set T} (hb : IsChain (· ≤ ·) b) :
    IsWellOrder b (fun x y => (x : T) < y) := by
  have : Std.Trichotomous (fun x y : b => (x : T) < y) := ⟨fun x y hxy hyx => by
    rcases hb.total x.2 y.2 with h | h
    · exact Subtype.ext (h.lt_or_eq.resolve_left hxy)
    · exact Subtype.ext (h.lt_or_eq.resolve_left hyx).symm⟩
  exact @IsWellOrder.mk _ _ ⟨InvImage.wf (fun x : b => (x : T)) wellFounded_lt⟩ inferInstance
end JardenShami.Tree
