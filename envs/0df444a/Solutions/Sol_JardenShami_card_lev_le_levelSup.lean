-- Prove2me | solution 1 for JardenShami.card_lev_le_levelSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:53.626764+00:00
-- url     : https://prove2.me/submissions/c9f3cc77-af35-4ae9-8ce6-f45000fe98b3

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (α : Kappa κ) : #(Lev T (α : Ordinal.{w})) ≤ levelSup κ T :=
  le_ciSup (Cardinal.bddAbove_of_small (s := Set.range fun α : Kappa κ => #(Lev T α))) α
end JardenShami
