-- Prove2me | solution 1 for N25.Endgame.simple_cusp_geometric_selected25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:55.028436+00:00
-- url     : https://prove2.me/submissions/328cecc3-470f-400e-8e94-b632737c9d33

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_N25_cusp_constant_place_lift
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_N25_cusp_complex_simple_poles_card_le_five
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_Endgame_pQ25_j_order
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

/-- The five selected geometric cusps exhaust the actual simple poles of j. -/
theorem _root_.solution (P : GPlace)
    (hP : P.ord (emb25 j25) = -1) : ∃ i : Fin 5, P = pG25 i := by
  classical
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨κ, hκ, hlift⟩ := N25.cusp_constant_place_lift ι.toRingHom
  have hj : (κ (emb25 j25) : LaurentSeries ℂ) = jqModC ℂ := by
    rw [hκ, coe_emb25]
    change ((jqModC ℚ).map (algebraMap ℚ Qbar)).map ι.toRingHom = _
    rw [map_jqModC, map_jqModC]
  let S := {Q : GPlace // Q.ord (emb25 j25) = -1}
  let SC := {W : Place ℂ (laurentBaseChange ℂ FQ) // W.ord (κ (emb25 j25)) = -1}
  have hSC : Finite SC ∧ Nat.card SC ≤ 5 :=
    N25.cusp_complex_simple_poles_card_le_five (κ (emb25 j25)) hj
  let : Finite SC := hSC.1
  have hall (Q : S) : ∃ W : SC, W.val.toValuationSubring.comap κ = Q.val.toValuationSubring := by
    obtain ⟨W, hm, ho, _⟩ := hlift Q.val
    exact ⟨⟨W, (ho (emb25 j25)).trans Q.property⟩, hm⟩
  choose lift hliftmem using hall
  have hinj : Function.Injective lift := by
    intro Q R h
    apply Subtype.ext
    apply Place.ext
    exact (hliftmem Q).symm.trans ((congrArg
      (fun W : SC => W.val.toValuationSubring.comap κ) h).trans (hliftmem R))
  let : Finite S := Finite.of_injective lift hinj
  have hcS : Nat.card S ≤ 5 := (Nat.card_le_card_of_injective lift hinj).trans hSC.2
  let selected : Fin 5 → S := fun i => ⟨pG25 i,
    (cuspChoice25_spec.2.2.2.2.2 i j25).trans (pQ25_j_order i)⟩
  have hs : Function.Injective selected := by
    intro i k h
    exact cuspChoice25_spec.2.2.1 (congrArg Subtype.val h)
  have hcard : Nat.card S = 5 := le_antisymm hcS (by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective selected hs)
  let : Fintype S := Fintype.ofFinite S
  have hc : Fintype.card (Fin 5) = Fintype.card S := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hcard.symm
  have hsurj : Function.Surjective selected :=
    ((Fintype.bijective_iff_injective_and_card selected).mpr ⟨hs, hc⟩).2
  obtain ⟨i, hi⟩ := hsurj ⟨P, hP⟩
  exact ⟨i, (congrArg Subtype.val hi).symm⟩

end N25.Endgame
