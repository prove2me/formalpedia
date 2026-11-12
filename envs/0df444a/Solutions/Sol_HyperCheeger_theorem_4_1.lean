-- Prove2me | solution 1 for HyperCheeger.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:35.16221+00:00
-- url     : https://prove2.me/submissions/44d6fefa-2428-47e9-a814-dd28ed3e0ed9

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_conductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Theorems.Thm_HyperCheeger_eq_13
import Theorems.Thm_HyperCheeger_eq_2

section
set_option autoImplicit false

namespace HyperCheeger.Dev.Thm41

open HyperCheeger

/-- A connected hypergraph on a nonempty vertex type has rank at least `2`. -/
theorem two_le_rank {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (H : Hypergraph V) (hconn : H.IsConnected) : 2 ≤ H.rank := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u⟩ := hne
  obtain ⟨ℓ, e, hℓ, he, hu, -, -⟩ := hconn u u
  have hmem : e 1 ∈ H.edges := he 1 le_rfl hℓ
  have h1 : (e 1).card ≠ 1 := H.card_ne_one _ hmem
  have h0 : 0 < (e 1).card := Finset.card_pos.mpr ⟨u, hu⟩
  have hle : (e 1).card ≤ H.rank := Finset.le_sup (f := Finset.card) hmem
  omega

end HyperCheeger.Dev.Thm41

namespace HyperCheeger

open HyperCheeger.Dev.Thm41 in
theorem chk_theorem_4_1 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (H : Hypergraph V) (hconn : H.IsConnected) :
    H.nu2 / (H.rank : ℝ) ≤ H.conductance ∧ H.conductance ≤ Real.sqrt (2 * H.nu2) := by
  obtain ⟨-, h13a, h13b⟩ := eq_13 hV H hconn
  obtain ⟨h2a, h2b⟩ := eq_2 hV H
  have hr : (2 : ℝ) ≤ (H.rank : ℝ) := by exact_mod_cast two_le_rank hV H hconn
  refine ⟨?_, le_trans h2a h13b⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_theorem_4_1 := @HyperCheeger.chk_theorem_4_1
