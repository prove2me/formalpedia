-- Prove2me | solution 1 for JardenShami.Tree.ht_le_ht_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:45.985874+00:00
-- url     : https://prove2.me/submissions/d1795361-864a-4d8a-afbc-bfaa4d900b71

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {s t : T} (h : s ≤ t) : ht s ≤ ht t :=
  h.lt_or_eq.elim (fun h => (ht_lt_ht h).le) (fun h => h ▸ le_rfl)
end JardenShami.Tree
