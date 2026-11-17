-- Prove2me | solution 1 for N25.cusp_width_twentyFive_card_le_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:22.39321+00:00
-- url     : https://prove2.me/submissions/86ffe557-3930-4cba-9146-0318c82fbb1f

import Mathlib
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_level25_subgroup_membership
import Definitions.Def_N25
import Theorems.Thm_N25_level25_indices
import Theorems.Thm_N25_level25_T_doubleCosets
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve AlgebraicCurve

namespace N25

open Endgame

private theorem finite_large_poles_bound {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] (j : F) (hjT : Transcendental K j)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F)
    (hdeg : Module.finrank (IntermediateField.adjoin K ({j} : Set F)) F = 150)
    (hc : Nat.card {P : Place K F // P.ord j < 0} = 14) :
    Finite {P : Place K F // P.ord j = -25} ∧
      Nat.card {P : Place K F // P.ord j = -25} ≤ 5 := by
  classical
  obtain ⟨S,hS,hsum⟩ := exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed K j hjT hfin
  rw [hdeg] at hsum
  have hsCard : S.card = 14 := by
    calc
      S.card = Nat.card {P : Place K F // P ∈ S} := by simp
      _ = Nat.card {P : Place K F // P.ord j < 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight hS)
      _ = 14 := hc
  let T := S.filter (fun P => P.ord j = -25)
  have ht : T ⊆ S := Finset.filter_subset _ _
  have heq : {P : Place K F // P ∈ T} ≃ {P : Place K F // P.ord j = -25} :=
    Equiv.subtypeEquivRight (fun P => by
      simp only [T,Finset.mem_filter,hS]
      constructor
      · exact And.right
      · intro h; exact ⟨by omega,h⟩)
  have htc : Nat.card {P : Place K F // P.ord j = -25} = T.card := by
    rw [← Nat.card_congr heq]
    simp
  have hsumT : ∑ P ∈ T, (-P.ord j) = 25 * (T.card : ℤ) := by
    calc
      _ = ∑ _P ∈ T, (25 : ℤ) := Finset.sum_congr rfl (fun P hP => by
        have h := (Finset.mem_filter.mp hP).2
        omega)
      _ = _ := by simp [mul_comm]
  have hrest : ((S \ T).card : ℤ) ≤ ∑ P ∈ S \ T, (-P.ord j) := by
    calc
      _ = ∑ _P ∈ S \ T, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun P hP => by
        have hp := (hS P).mp (Finset.mem_sdiff.mp hP).1
        omega)
  have hsc := Finset.sum_sdiff ht (f := fun P => -P.ord j)
  have hcc := Finset.card_sdiff_add_card_eq_card ht
  rw [hsCard] at hcc
  rw [hsum,hsumT] at hsc
  have hccZ : ((S \ T).card : ℤ) + (T.card : ℤ) = 14 := by exact_mod_cast hcc
  have hb : T.card ≤ 5 := by omega
  refine ⟨Finite.of_equiv {P : Place K F // P ∈ T} heq,?_⟩
  rw [htc]
  exact hb

/-- Total pole degree and the fourteen-place census bound the order-twenty-five fibre. -/
theorem _root_.solution :
    Finite {P : GPlace // P.ord (emb25 j25) = -25} ∧
      Nat.card {P : GPlace // P.ord (emb25 j25) = -25} ≤ 5 := by
  classical
  let j : FG := emb25 j25
  have hj : (j : LaurentSeries Qbar) = jqModC Qbar := map_jqModC _
  have : Γ25.FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH 25 H25)
  have hT : ModularGroup.T ∈ Γ25 := translation_mem_GammaH 25 H25
  obtain ⟨hjT,hfin⟩ :=
    transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      Qbar Γ25 hT j hj
  have hfull := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
    Qbar 25 H25 j hj
  have hc : Nat.card {P : GPlace // P.ord j < 0} = 14 :=
    (natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
      25 Γ25 (Gamma1_le_GammaH 25 H25) j hj hfull).2.2.trans level25_T_doubleCosets
  have hminus : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ25 := by
    apply CohCarrier.mem_GammaH_iff.mpr
    have h0 : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CongruenceSubgroup.Gamma0 25 := by
      rw [CongruenceSubgroup.Gamma0_mem]; decide
    refine ⟨h0,?_⟩
    rw [level25_subgroup_membership]
    change (-1 : ZMod 25)=1 ∨ (-1 : ZMod 25)=7 ∨ (-1 : ZMod 25)=18 ∨ (-1 : ZMod 25)=24
    decide
  have hjoin : Γ25 ⊔ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = Γ25 :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr hminus)
  have hd : Module.finrank (IntermediateField.adjoin Qbar ({j} : Set FG)) FG = 150 := by
    rw [hjoin] at hfull
    exact hfull.trans level25_indices.1
  exact finite_large_poles_bound j hjT hfin hd hc

end N25
