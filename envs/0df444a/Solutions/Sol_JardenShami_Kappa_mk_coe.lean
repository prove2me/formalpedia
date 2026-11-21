-- Prove2me | solution 1 for JardenShami.Kappa.mk_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:42.215392+00:00
-- url     : https://prove2.me/submissions/f7721859-6c4d-4c32-828b-16348b1916be

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
namespace Kappa
theorem _root_.solution {κ : Cardinal.{w}} (x : Kappa κ) :
    Kappa.mk (x : Ordinal.{w}) (Kappa.coe_lt_ord x) = x :=
  Ordinal.ToType.mk.apply_symm_apply x
end Kappa
end JardenShami
