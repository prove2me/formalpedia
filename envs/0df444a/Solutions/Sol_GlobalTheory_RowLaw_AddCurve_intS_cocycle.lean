-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.intS_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:22:04.575216+00:00
-- url     : https://prove2.me/submissions/213a7eb6-21d2-480e-aa4b-6047ba68cc27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_intS_subst
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_intS_pderiv
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_eq_zero_of_van
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_van_pderiv_mvExp
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_sg
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_pair_const
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_gp_const
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_pderiv_hAt
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_pderiv_subst_eq_zero
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_sum_const
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_formalAdd_const
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_addP
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.AddCurve
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) {v : κ → C} (hv : ∀ i, V.Ge 0 (v i)) :
    IntS V (subst (addP X a b) (X.sg v) - subst a (X.sg v) - subst b (X.sg v)) := by
  let c : Fin 3 × κ → MvPowerSeries τ C := fun p => if p.1 = 0 then a p.2 else if p.1 = 1 then b p.2 else 0
  have hc : ∀ p, constantCoeff (c p) = 0 := fun p => by
    simp only [c]
    split_ifs
    exacts [ha _, hb _, map_zero _]
  have hci : ∀ p, IntS V (c p) := fun p => by
    simp only [c]
    split_ifs
    exacts [hai _, hbi _, fun μ => by rw [map_zero]; exact VF.Ge.zero 0]
  have hc2 : ∀ x, c (2, x) = 0 := fun x => by simp [c]
  have hS := hasSubst_of_constantCoeff_zero hc
  have s0 : ∀ x, subst c (gp C κ (0 : Fin 3) x) = a x := fun x => by simp [gp, subst_X hS, c]
  have s1 : ∀ x, subst c (gp C κ (1 : Fin 3) x) = b x := fun x => by simp [gp, subst_X hS, c]
  have sA : ∀ x, subst c (addP X (gp C κ (0 : Fin 3)) (gp C κ 1) x) = addP X a b x := fun x => by
    rw [subst_addP h (gp_const 0) (gp_const 1) hc]
    simp only [s0, s1]
  have hvan : ∀ A : κ → MvPowerSeries (Fin 3 × κ) C, (∀ s, constantCoeff (A s) = 0) →
      Van {p : Fin 3 × κ | p.1 = 2} (hAt X A (gp C κ 2)) := by
    intro A hA
    refine Van.subst {s : Fin 2 × κ | s.1 = 1} (pair_const hA (gp_const 2)) ?_ (h.axes 1)
    rintro ⟨g, x⟩ (hg : g = 1)
    subst hg
    rw [if_neg (by simp)]
    intro ν hν
    unfold gp
    rw [coeff_X, if_neg]
    intro e
    exact hν (2, x) (by rw [e]; simp) rfl
  have hAc := formalAdd_const h (gp_const (C := C) (κ := κ) (0 : Fin 3)) (gp_const 1)
  have hH : Van {p : Fin 3 × κ | p.1 = 2} (hAt X (gp C κ (0 : Fin 3)) (gp C κ 2) + hAt X (gp C κ 1) (gp C κ 2) -
      hAt X (addP X (gp C κ 0) (gp C κ 1)) (gp C κ 2)) := by
    intro ν hν
    rw [map_sub, map_add, hvan _ (gp_const 0) ν hν, hvan _ (gp_const 1) ν hν, hvan _ hAc ν hν]
    simp
  have key : ∀ i, IntS V
      (subst (fun p : Fin 2 × κ => if p.1 = 0 then a p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h) +
        subst (fun p : Fin 2 × κ => if p.1 = 0 then b p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h) -
        subst (fun p : Fin 2 × κ => if p.1 = 0 then addP X a b p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h)) := by
    intro i
    have d0 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (0 : Fin 3) x) = 0 := fun x =>
      pderiv_X_of_ne (by simp)
    have d1 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (1 : Fin 3) x) = 0 := fun x =>
      pderiv_X_of_ne (by simp)
    have dA : ∀ x, pderiv C ((2 : Fin 3), i) (addP X (gp C κ (0 : Fin 3)) (gp C κ 1) x) = 0 := fun x =>
      pderiv_subst_eq_zero (sum_const h (gp_const 0) (gp_const 1)) (fun y => by
        rw [map_add, pderiv_subst_eq_zero (gp_const 0) d0, pderiv_subst_eq_zero (gp_const 1) d1, add_zero]) _
    have h1 := intS_subst hc hci (intS_pderiv h.ph1 ((2 : Fin 3), i))
    have h2 := subst_eq_zero_of_van hc (fun s (hs : s.1 = 2) => by
      rw [show s = (2, s.2) from Prod.ext hs rfl]; exact hc2 _) (van_pderiv_mvExp hH ((2 : Fin 3), i))
    rw [subst_sub hS, sub_eq_zero] at h2
    rw [h2, map_sub, map_add, subst_sub hS, subst_add hS, subst_pderiv_hAt X (gp_const 0) i d0 hc hc2,
      subst_pderiv_hAt X (gp_const 1) i d1 hc hc2, subst_pderiv_hAt X hAc i dA hc hc2] at h1
    simpa only [s0, s1, sA] using h1
  rw [subst_sg X v (formalAdd_const h ha hb), subst_sg X v ha, subst_sg X v hb]
  intro μ
  have := VF.Ge.sum (s := Finset.univ) fun i _ => (hv i).mul_int (key i μ)
  convert this using 1
  simp only [map_sub, map_add, map_neg, map_sum, coeff_smul, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring
end GlobalTheory.RowLaw.AddCurve
