-- Prove2me | solution 1 for JardenShami.Kappa.mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:35.312932+00:00
-- url     : https://prove2.me/submissions/53dc17ee-e29a-4321-8d58-51500c95d648

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
namespace Kappa
theorem _root_.solution (κ : Cardinal.{w}) : #(Kappa κ) = κ := by
  rw [Cardinal.mk_toType, Cardinal.card_ord]
end Kappa
end JardenShami
