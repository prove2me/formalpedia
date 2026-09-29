-- Prove2me | solution 1 for NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a9984ed8-d94d-56f9-98e3-483aae997b41

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_NumberField_FiniteSIdeleModule
import Theorems.Thm_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton
import Theorems.Thm_GroupCohomology_RepPi_subsingleton_tateHneg1_obj
import Theorems.Thm_Rep_nonempty_tateH0_coind_linearEquiv
import Theorems.Thm_Rep_nonempty_tateHneg1_coind_linearEquiv
import Theorems.Thm_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1
import Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tate_integerUnits_of_unramified
import Theorems.Thm_NumberField_PlaceDecomp_decomp_eq_one_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace P2mS26BJ

theorem under_above (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) : (NumberField.PlaceAbove.above E K v).under (𝓞 E) = v :=
  HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E K v)

end P2mS26BJ

open P2mS26BJ in
theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] [IsCyclic (K ≃ₐ[E] K)] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hSram : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    Nat.card (NumberField.FiniteSIdele.obj E K S).tateH0 = ∏ v ∈ S, Nat.card (NumberField.FiniteSIdele.D E K v) ∧
    Subsingleton (NumberField.FiniteSIdele.obj E K S).tateHneg1 := by
  classical

  have hinl : ∀ v : {v // v ∈ S},
      Nat.card (NumberField.FiniteSIdele.fibre E K S (Sum.inl v)).tateH0 = Nat.card (NumberField.FiniteSIdele.D E K v.1) ∧
      Subsingleton (NumberField.FiniteSIdele.fibre E K S (Sum.inl v)).tateHneg1 := by
    intro v
    obtain ⟨e0⟩ := Rep.nonempty_tateH0_coind_linearEquiv (NumberField.FiniteSIdele.D E K v.1) (NumberField.FiniteSIdele.localUnits E K v.1)
    obtain ⟨e1⟩ := Rep.nonempty_tateHneg1_coind_linearEquiv (NumberField.FiniteSIdele.D E K v.1) (NumberField.FiniteSIdele.localUnits E K v.1)
    have hT := NumberField.PlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1 E K (NumberField.PlaceAbove.above E K v.1)
    exact ⟨(Nat.card_congr e0.toEquiv).trans hT.1, e1.toEquiv.subsingleton_congr.2 hT.2⟩

  have hinr : ∀ v : {v // v ∉ S},
      Subsingleton (NumberField.FiniteSIdele.fibre E K S (Sum.inr v)).tateH0 ∧
      Subsingleton (NumberField.FiniteSIdele.fibre E K S (Sum.inr v)).tateHneg1 := by
    intro v
    obtain ⟨e0⟩ := Rep.nonempty_tateH0_coind_linearEquiv (NumberField.FiniteSIdele.D E K v.1) (NumberField.FiniteSIdele.localIntegerUnits E K v.1)
    obtain ⟨e1⟩ := Rep.nonempty_tateHneg1_coind_linearEquiv (NumberField.FiniteSIdele.D E K v.1) (NumberField.FiniteSIdele.localIntegerUnits E K v.1)
    have hw : ((NumberField.PlaceAbove.above E K v.1).under (𝓞 E)).asIdeal.ramificationIdx' (NumberField.PlaceAbove.above E K v.1).asIdeal = 1 :=
      hSram _ (by rw [under_above]; exact v.2)
    have hT := NumberField.PlaceDecomp.subsingleton_tate_integerUnits_of_unramified E K (NumberField.PlaceAbove.above E K v.1)
      (fun σ h => NumberField.PlaceDecomp.decomp_eq_one_of_ramificationIdx_eq_one E K (NumberField.PlaceAbove.above E K v.1) hw σ h)
    exact ⟨e0.toEquiv.subsingleton_congr.2 hT.1, e1.toEquiv.subsingleton_congr.2 hT.2⟩

  refine ⟨?_, ?_⟩
  · rw [GroupCohomology.RepPi.natCard_tateH0_obj_eq_prod_of_subsingleton (NumberField.FiniteSIdele.fibre E K S)
        (Finset.univ.map Function.Embedding.inl) ?_, Finset.prod_map, ← Finset.prod_coe_sort S]
    · exact Finset.prod_congr rfl fun a _ => (hinl a).1
    · rintro (a | b) hi
      · exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ a)) hi
      · exact (hinr b).1
  · exact GroupCohomology.RepPi.subsingleton_tateHneg1_obj (NumberField.FiniteSIdele.fibre E K S) fun i =>
      match i with
      | Sum.inl a => (hinl a).2
      | Sum.inr b => (hinr b).2

end S_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1
end P2MW
export P2MW.S_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1 (solution)
