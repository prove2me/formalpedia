-- Prove2me | solution 1 for NagataFactoriality.isUnit_of_dvd_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:00.24684+00:00
-- url     : https://prove2.me/submissions/1c3fbe9d-1218-4322-a381-d1ae1615aee5

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] {a : α} (h : a ∣ 1) : IsUnit a := by
  rcases h with ⟨b, hb⟩
  exact ⟨⟨a, b, hb.symm, by rw [mul_comm, ← hb]⟩, rfl⟩
end NagataFactoriality
