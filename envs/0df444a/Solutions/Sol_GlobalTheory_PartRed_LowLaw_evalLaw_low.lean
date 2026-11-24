-- Prove2me | solution 1 for GlobalTheory.PartRed.LowLaw.evalLaw_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:56.723349+00:00
-- url     : https://prove2.me/submissions/d4207419-9e96-4268-a23b-29528cd1e608

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_mem_trans
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_rowAdd_fill
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_ch_rowAdd
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_embA_elem_inv_val
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_embA_elem_mem
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_simpleSum_elem
import Theorems.Thm_GlobalTheory_PartRed_chL_apply
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_T_integral_coordinate_shear_haar_localField
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_comp_affine_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.LowLaw
namespace GlobalTheory.PartRed.LowLaw
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), ρ < i.val → i.val ≤ l.val → ∀ E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.fixSet ρ ⊆ E → (GlobalTheory.PartRed.lowSet ρ).filter (fun e => GlobalTheory.PartRed.colIx e < i.val) ⊆ E → E ⊆ GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ → (Sum.inr l, Sum.inr i) ∉ E → GlobalTheory.PartRed.EvalLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) E (GlobalTheory.PartRed.transSet ρ) (Sum.inr l, Sum.inr i) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hi hil E hfix hlow hEsub hlE
  unfold GlobalTheory.PartRed.EvalLaw
  intro b Φ
  have hlc := l.isLt
  let r : Fin c := ⟨i.val - 1, by omega⟩
  have hr : r.val + 1 = i.val := by show i.val - 1 + 1 = i.val; omega
  have hrl' : r.val < l.val := by show i.val - 1 < l.val; omega
  have hrl : r ≠ l := fun h => by rw [h] at hrl'; exact lt_irrefl _ hrl'
  set β := basePt c (0 : Matrix n n' k) with hβ
  set T := GlobalTheory.PartRed.transSet (n := n) (n' := n') (c := c) ρ with hT
  set u := elem (k := k) r l hrl (-b) with hu
  have hgN : embA n u ∈ N k n c (ρ + 1) := embA_elem_mem r l hrl hrl' (-b) (ρ + 1)
  have hmem := GlobalTheory.T.schwartzBruhat_comp_affine_matrix k (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) (embA n u)⁻¹ 0 Φ.1 Φ.2
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨_, hmem⟩
  have hΦ₁ : ∀ t, Φ₁.1 t = Φ.1 (((embA n u)⁻¹).val * t) := fun t => by simp [Φ₁]
  have hL1 := hL u hgN Φ Φ₁ hΦ₁
  have hinv : ((embA n u)⁻¹).val = fromBlocks 1 0 0 (transvection r l b) := by
    rw [hu, embA_elem_inv_val, neg_neg]
  have hβli : β (Sum.inr l) (Sum.inr i) = if l.val = i.val then 1 else 0 := by
    simp [hβ, basePt]
  have hss : simpleSum (embA n u) = -(b * β (Sum.inr l) (Sum.inr i)) := by
    rw [hu, simpleSum_elem, hβli]
    by_cases h : l.val = i.val
    · rw [if_pos (by omega), if_pos h]; ring
    · rw [if_neg (by omega), if_neg h]; ring
  have hxli : ∀ x y, GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) (Sum.inr i) = x (Sum.inr l) (Sum.inr i) := by
    intro x y
    have h1 : (Sum.inr l, Sum.inr i) ∉ T := by rw [hT, mem_trans]; simp [Free]; omega
    simp only [GlobalTheory.PartRed.fillAt, of_apply, dif_neg h1, if_neg hlE]
  refine ⟨(ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) • Φ₁, ?_, ?_⟩
  · rw [map_smul, hL1, smul_smul, hss, neg_neg, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  · intro x
    dsimp only
    let s : (T → k) → (T → k) := fun y j =>
      if j.1.1 = Sum.inr r then b * GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) j.1.2 else 0
    have hfill : ∀ y, (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        GlobalTheory.PartRed.fillAt β E T x y = GlobalTheory.PartRed.fillAt β E T x (y + s y) :=
      fun y => rowAdd_fill ρ l r i hi hil hr E hfix hlow b x y
    have hch : ∀ y, ch (GlobalTheory.PartRed.fillAt β E T x (y + s y)) =
        ch (GlobalTheory.PartRed.fillAt β E T x y) + b * x (Sum.inr l) (Sum.inr i) := fun y => by
      rw [← hfill, ch_rowAdd l r i hr b, hxli]
    have hone : (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * ψ (-(b * x (Sum.inr l) (Sum.inr i))) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    let G : (T → k) → ℂ := fun y => Φ.1 (GlobalTheory.PartRed.fillAt β E T x y) *
      (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ)
    have key : ∀ y, Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) * (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) =
        (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * G (y + s y) := by
      intro y
      simp only [G]
      rw [hΦ₁, hinv, hfill, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (-(Φ.1 (GlobalTheory.PartRed.fillAt β E T x (y + s y)) *
        (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ))) * hone
    let S : Finset T := Finset.univ.filter fun j => j.1.1 = Sum.inr r
    have hs_cont : Continuous s := by
      refine continuous_pi fun j => ?_
      simp only [s]
      split_ifs
      · refine continuous_const.mul ?_
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | exact continuous_apply _ | exact continuous_const
      · exact continuous_const
    have hs_dep : ∀ y y' : T → k, (∀ j, j ∉ S → y j = y' j) → s y = s y' := by
      intro y y' h
      funext j
      simp only [s]
      split_ifs
      · congr 1
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | rfl | exact h _ (by simp [S]; exact Ne.symm hrl)
      · rfl
    have hs_supp : ∀ (y : T → k) j, j ∉ S → s y j = 0 := by
      intro y j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [s, if_neg hj]
    have hchg := GlobalTheory.T.integral_coordinate_shear_haar_localField k ν hν T S s hs_cont hs_dep hs_supp G
    simp only [GlobalTheory.PartRed.red, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.PartRed.chL_apply]
    calc ∫ y : T → k, (ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) *
          (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) ∂(Measure.pi fun _ => ν)
        = ∫ y : T → k, ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          G (y + s y) ∂(Measure.pi fun _ => ν) := by
          congr 1; funext y; rw [mul_assoc, key, mul_assoc]
      _ = ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          ∫ y : T → k, G y ∂(Measure.pi fun _ => ν) := by rw [integral_const_mul, hchg]
      _ = _ := by
          rw [show b * (x (Sum.inr l) (Sum.inr i) - β (Sum.inr l) (Sum.inr i)) =
            -(b * β (Sum.inr l) (Sum.inr i)) + b * x (Sum.inr l) (Sum.inr i) by ring,
            AddChar.map_add_eq_mul, Circle.coe_mul]
end GlobalTheory.PartRed.LowLaw
