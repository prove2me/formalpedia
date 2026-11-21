-- Prove2me | solution 1 for JardenShami.Kappa.mk_Iic_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:08.965184+00:00
-- url     : https://prove2.me/submissions/875e0f41-2af5-4c83-b33a-b4b390ba48b9

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_mk_eq

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}
namespace JardenShami
namespace Kappa
theorem _root_.solution (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : #(Set.Iic x) < κ := by
  rw [← Set.Iio_insert]
  have h2 : #(Set.Iio x) < κ := by
    have := Cardinal.mk_Iio_lt x (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rwa [Kappa.mk_eq] at this
  exact (Cardinal.mk_insert_le (a := x) (s := Set.Iio x)).trans_lt
    (Cardinal.add_lt_of_lt hκ h2 (Cardinal.one_lt_aleph0.trans_le hκ))
end Kappa
end JardenShami
