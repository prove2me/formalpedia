-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.one_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:41.264496+00:00
-- url     : https://prove2.me/submissions/fed2da2d-385c-448a-8947-7c79203c3fc3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_subst
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_X
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_sum_smul
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_subst_sum_smul
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_subst_sum
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_coeff_subst_tyS
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_lg_const
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_linearPart_lg
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_ex_lg
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_exists_sum_point
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_inv_int
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inv_int
import Theorems.Thm_GlobalTheory_FormalInv_coeff_substInv_mem
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution (hY : RLaw Y V) (g : Fin 2) (H : Y.CartHyp V g) (S : Sys (RawChart.cart H))
    (t : I g → MvPowerSeries (I g) C) (ht : S.IsT t) (E : κ → MvPowerSeries (I g) C)
    (hE : ∀ x, E x = subst (fun i : κ => ∑ c : I g, Y.u g c i • (X c : MvPowerSeries (I g) C)) (Y.ex x)) :
    (∃ Φ : κ → MvPowerSeries (I g) C, (∀ x, constantCoeff (Φ x) = 0) ∧ (∀ x, IntS V (Φ x)) ∧
      ∀ x, E x = subst t (Φ x)) ∧
    ∃ Ψ : I g → MvPowerSeries κ C, (∀ c, constantCoeff (Ψ c) = 0) ∧ (∀ c, IntS V (Ψ c)) ∧
      ∀ c, t c = subst E (Ψ c) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hts := hasSubst_of_constantCoeff_zero ht.1
  have hc : ∀ c, S.cur c ∈ Y.TySet V g := fun c => (S.curve c).1
  choose γ lam hγ _ hlog _ using hc
  have hX : ∀ c : I g, PowerSeries.HasSubst (X c : MvPowerSeries (I g) C) := fun c =>
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X c)
  have hX0 : ∀ c : I g, ∀ _ : Unit, constantCoeff (X c : MvPowerSeries (I g) C) = 0 := fun c _ => constantCoeff_X c
  obtain ⟨Φ, h0, hi, hΦ⟩ := exists_sum_point hY Finset.univ
    (fun (c : I g) i => PowerSeries.subst (X c : MvPowerSeries (I g) C) (γ c i))
    (fun c i => constantCoeff_subst_zero (hX0 c) (hγ c i).1)
    (fun c i => intS_subst (hX0 c) (fun _ => intS_X c) fun μ => by
      have := (hγ c i).2 (μ ())
      rwa [PowerSeries.coeff_def rfl] at this)
  have hΦs := hasSubst_of_constantCoeff_zero h0
  have hΦ' : ∀ i, subst Φ (Y.lg i) = ∑ x : I g, Y.u g x i •
      ∑ c : I g, PowerSeries.subst (X c : MvPowerSeries (I g) C) (tyS V.l fun s => S.al c s x) := by
    intro i
    rw [hΦ]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun j => (hγ c j).1) (hX c).const (Y.lg i)
    have e2 := hlog c i
    unfold alongCv at e2
    unfold PowerSeries.subst
    rw [← e, e2]
    exact subst_sum_smul (hX c).const _ _ _
  have hT : ∀ x, subst t (∑ c : I g, PowerSeries.subst (X c : MvPowerSeries (I g) C) (tyS V.l fun s => S.al c s x)) =
      (X x : MvPowerSeries (I g) C) := by
    intro x
    rw [subst_sum hts]
    ext μ
    rw [map_sum, coeff_X, ← ht.2 x μ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← coeff_subst_tyS hl _ (ht.1 c)]
    unfold PowerSeries.subst
    rw [subst_comp_subst_apply (hX c).const hts, subst_X hts]
  have hEΦ : ∀ x, E x = subst t (Φ x) := by
    intro x
    rw [hE, ← ex_lg hY (fun i => constantCoeff_subst_zero ht.1 (h0 i)) x]
    congr 1
    funext i
    rw [← subst_comp_subst_apply hΦs hts, hΦ', subst_sum_smul hts]
    simp only [hT]
  refine ⟨⟨Φ, h0, hi, hEΦ⟩, ?_⟩
  obtain ⟨w, hw, hsat⟩ := hY.sat g
  have hlin : ∀ i j, linearPart Φ i j = ∑ x : I g, Y.u g x i * S.tan j x := by
    intro i j
    have e := linearPart_subst (lg_const hY) h0
    rw [linearPart_lg hY, Matrix.one_mul] at e
    rw [← e]
    show coeff (Finsupp.single j 1) (subst Φ (Y.lg i)) = _
    rw [hΦ', map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_eq_mul, map_sum, Finset.sum_eq_single j]
    · rw [coeff_subst_tyS hl _ (constantCoeff_X j)]
      have h1 : S.al j 0 x = S.tan j x := by
        unfold Sys.al
        rw [(S.curve j).2.1]; rfl
      have h2 : ¬ (1 = V.l) := by omega
      have h3 : coeff (Finsupp.single j 1) ((X j : MvPowerSeries (I g) C) ^ V.l) = 0 := by
        rw [coeff_X_pow, if_neg]
        intro e'
        have := DFunLike.congr_fun e' j
        simp only [Finsupp.single_eq_same] at this
        exact h2 this
      rw [Finsupp.degree_single, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, pow_one, h3, h1,
        coeff_index_single_self_X, mul_one, mul_zero, add_zero]
    · intro c _ hcj
      rw [coeff_subst_tyS hl _ (constantCoeff_X c)]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [coeff_X_pow, if_neg, mul_zero]
      intro e'
      have := DFunLike.congr_fun e' j
      simp [hcj] at this
    · simp
  set Θ : I g → MvPowerSeries (I g) C := fun c => ∑ x, w x c • Φ x with hΘ
  have hΘ0 : ∀ c, constantCoeff (Θ c) = 0 := fun c => by
    simp [hΘ, map_sum, h0]
  have hΘi : ∀ c, IntS V (Θ c) := fun c => intS_sum_smul (fun x => hw x c) hi
  have hΘl : linearPart Θ = (Matrix.of S.tan).transpose := by
    ext c j
    show coeff (Finsupp.single j 1) (∑ x, w x c • Φ x) = S.tan j c
    rw [map_sum]
    have e : ∀ i, coeff (Finsupp.single j 1) (w i c • Φ i) = ∑ x : I g, (Y.u g x i * w i c) * S.tan j x := by
      intro i
      rw [map_smul, smul_eq_mul, show coeff (Finsupp.single j 1) (Φ i) = _ from hlin i j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [e]
    rw [Finset.sum_comm, Finset.sum_eq_single c]
    · rw [← Finset.sum_mul, (hsat c c).1 rfl, one_mul]
    · intro x _ hx
      rw [← Finset.sum_mul, (hsat x c).2 hx, zero_mul]
    · simp
  obtain ⟨hU, hinv⟩ := inv_int (V := V) (linearPart Θ) (fun i j => hΘi i _)
    (by rw [hΘl, Matrix.det_transpose]; exact S.unimod)
  have hE0 : ∀ x, constantCoeff (E x) = 0 := fun x => by
    rw [hEΦ]; exact constantCoeff_subst_zero ht.1 (h0 x)
  have hEs := hasSubst_of_constantCoeff_zero hE0
  have hW0 : ∀ c, constantCoeff (∑ x, w x c • (X x : MvPowerSeries κ C)) = 0 := fun c => by
    simp [map_sum]
  refine ⟨fun c => subst (fun c' => ∑ x, w x c' • (X x : MvPowerSeries κ C)) (substInv Θ c),
    fun c => constantCoeff_subst_zero hW0 (constantCoeff_substInv hΘ0 c),
    fun c => intS_subst hW0 (fun c' => intS_sum_smul (fun x => hw x c') intS_X) fun μ =>
      coeff_substInv_mem (S := intRing V) (g := μ.degree + 1) hΘ0 hinv (fun i d _ => hΘi i d) c μ
        (Nat.lt_succ_self _), fun c => ?_⟩
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hW0) hEs]
  have e : (fun c' => subst E (∑ x, w x c' • (X x : MvPowerSeries κ C))) = fun c' => subst t (Θ c') := by
    funext c'
    rw [subst_sum_smul hEs, subst_sum_smul hts]
    exact Finset.sum_congr rfl fun x _ => by rw [subst_X hEs, hEΦ]
  rw [e, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hΘ0) hts, subst_substInv_left hΘ0 hU, subst_X hts]
end GlobalTheory.RowLaw.GermRing
