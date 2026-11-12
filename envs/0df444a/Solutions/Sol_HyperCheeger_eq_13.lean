-- Prove2me | solution 1 for HyperCheeger.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:32.703248+00:00
-- url     : https://prove2.me/submissions/3d921648-58f7-4b28-ba7b-8df960ceaf7a

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph
import Theorems.Thm_HyperCheeger_eq_12
import Theorems.Thm_HyperCheeger_lemma_3_4

section
set_option autoImplicit false

namespace HyperCheeger.Dev.Eq13

open HyperCheeger

/-- The two infima agree termwise, by Lemma 3.4. -/
theorem aeGraph_conductance_eq {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) :
    H.aeGraph.conductance = H.diffusionConductance := by
  unfold Hypergraph.conductance Hypergraph.diffusionConductance
  exact iInf_congr fun S => lemma_3_4 H S.1 S.2.1 S.2.2

end HyperCheeger.Dev.Eq13

namespace HyperCheeger

open HyperCheeger.Dev.Eq13 in
theorem chk_eq_13 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (H : Hypergraph V) (hconn : H.IsConnected) :
    H.aeGraph.conductance = H.diffusionConductance ∧
      H.nu2 / 2 ≤ H.diffusionConductance ∧ H.diffusionConductance ≤ Real.sqrt (2 * H.nu2) := by
  have h := eq_12 hV H hconn
  rw [aeGraph_conductance_eq] at h
  exact ⟨aeGraph_conductance_eq H, h⟩

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_eq_13 := @HyperCheeger.chk_eq_13
