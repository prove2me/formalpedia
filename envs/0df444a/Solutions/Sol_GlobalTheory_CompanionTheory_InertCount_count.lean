-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:52.429129+00:00
-- url     : https://prove2.me/submissions/0b62c498-29be-4360-acc8-37fa42e7abae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_trace_corner
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_small_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_corner_of_small
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_exists_int_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_small_out
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_vecMul_smul_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_isInt_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_v_det_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_eq_of_neg_add_out
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_neg_add_out_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mem_intV
import Theorems.Thm_GlobalTheory_InertZeta_mem_preLat
import Theorems.Thm_GlobalTheory_InertZeta_mem_traceZero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


section
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
private theorem inv_lemma' (hH : Heis) (hU : IsUnramInv ϖ σ q) {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    rowOf u⁻¹ = -rowOf u ∧ (rowOf u = 0 → cornerOf u⁻¹ = -cornerOf u) := by
  obtain ⟨hr1, -, hk1⟩ := (hH L ϖ σ q N hU).2.1 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at hr1 hk1
  have hrow1 : rowOf (1 : GU σ (N + 2)) = 0 := by
    have e : rowOf (1 : GU σ (N + 2)) + rowOf (1 : GU σ (N + 2)) = rowOf (1 : GU σ (N + 2)) + 0 := by rw [add_zero]; exact hr1.symm
    exact add_left_cancel e
  have hcor1 : cornerOf (1 : GU σ (N + 2)) = 0 := by
    rw [hrow1, zero_dotProduct, add_zero] at hk1
    have e : cornerOf (1 : GU σ (N + 2)) + cornerOf (1 : GU σ (N + 2)) = cornerOf (1 : GU σ (N + 2)) + 0 := by rw [add_zero]; exact hk1.symm
    exact add_left_cancel e
  obtain ⟨hr, -, hk⟩ := (hH L ϖ σ q N hU).2.1 u hu u⁻¹ (inv_mem hu)
  rw [mul_inv_cancel, hrow1] at hr
  rw [mul_inv_cancel, hcor1] at hk
  refine ⟨?_, fun h0 => ?_⟩
  · calc rowOf u⁻¹ = (rowOf u + rowOf u⁻¹) - rowOf u := by abel
      _ = -rowOf u := by rw [← hr]; abel
  · rw [h0, zero_dotProduct, add_zero] at hk
    calc cornerOf u⁻¹ = (cornerOf u + cornerOf u⁻¹) - cornerOf u := by abel
      _ = -cornerOf u := by rw [← hk]; abel
end GlobalTheory.CompanionTheory.InertCount
end
end

set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution (hH : Heis) (hL : LatIndex) (hT : TraceIndex) : Count := by
  unfold GlobalTheory.InertZeta.Count
  intro L _ _ ϖ σ q N hU C D l e f hC hdet hsurj hinv
  have hϖv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hϖ : ϖ ∈ intL L := by
    change Valued.v ϖ ≤ 1
    rw [hϖv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hrowS : ∀ u : GU σ (N + 2), Small ϖ e f C D u → rowOf u ∈ preLat (ϖ ^ e • C) := fun u hs => by
    unfold GlobalTheory.InertZeta.Small at hs
    exact mem_preLat.mpr fun j => by rw [vecMul_smul_apply]; exact hs.1 j
  have hub : ∀ b : (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))), ∃ u ∈ radQ σ N,
      rowOf u = ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) ∧ Small ϖ e f C D u :=
    fun b => hsurj _ (fun j => by
      have h1 := (mem_preLat.mp (Quotient.out b : preLat (ϖ ^ e • C)).2) j
      rwa [vecMul_smul_apply] at h1)
  choose ub hubR hubrow hubS using hub
  have hwt : ∀ t : (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))), ∃ w ∈ radQ σ N,
      rowOf w = 0 ∧ cornerOf w = ((Quotient.out t : traceZero σ (ϖ ^ f)) : L) :=
    fun t => (hH L ϖ σ q N hU).2.2 0 _ (by
      have h1 := (mem_traceZero.mp (Quotient.out t : traceZero σ (ϖ ^ f)).2).2
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero]
      rw [add_comm]
      exact h1)
  choose wt hwtR hwtrow hwtcorner using hwt
  have hwtint : ∀ t, ϖ ^ f * cornerOf (wt t) ∈ intL L := fun t => by
    rw [hwtcorner]
    exact (mem_traceZero.mp (Quotient.out t : traceZero σ (ϖ ^ f)).2).1
  have key_row : ∀ b t, rowOf (ub b * wt t) = ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) :=
    fun b t => by
      rw [((hH L ϖ σ q N hU).2.1 _ (hubR b) _ (hwtR t)).1, hwtrow, add_zero, hubrow]
  let G : (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))) × (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))) → {x : RadQuot σ N // Small ϖ e f C D (Quotient.out x : radQ σ N).1} :=
    fun p => ⟨QuotientGroup.mk (⟨ub p.1 * wt p.2, mul_mem (hubR p.1) (hwtR p.2)⟩ : radQ σ N),
      (small_out hinv _).mpr
        (small_mul hH hU (hubR p.1) (hwtR p.2) (hwtrow p.2) (hubS p.1) (hwtint p.2))⟩
  have hinj : Function.Injective G := by
    rintro ⟨b, t⟩ ⟨b', t'⟩ hGG
    have h1 : (QuotientGroup.mk (⟨ub b * wt t, mul_mem (hubR b) (hwtR t)⟩ : radQ σ N) : RadQuot σ N)
        = QuotientGroup.mk (⟨ub b' * wt t', mul_mem (hubR b') (hwtR t')⟩ : radQ σ N) :=
      congrArg Subtype.val hGG
    have hz : (ub b * wt t)⁻¹ * (ub b' * wt t') ∈ KU σ (N + 2) :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
    have hzR : (ub b * wt t)⁻¹ * (ub b' * wt t') ∈ radQ σ N :=
      mul_mem (inv_mem (mul_mem (hubR b) (hwtR t))) (mul_mem (hubR b') (hwtR t'))
    obtain ⟨hzrow, hzcorner⟩ := (((hH L ϖ σ q N hU).1 _ hzR).2.2).mp hz
    have hrowz : rowOf ((ub b * wt t)⁻¹ * (ub b' * wt t'))
        = -((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L)
          + ((Quotient.out b' : preLat (ϖ ^ e • C)) : Fin N → L) := by
      rw [((hH L ϖ σ q N hU).2.1 _ (inv_mem (mul_mem (hubR b) (hwtR t))) _
        (mul_mem (hubR b') (hwtR t'))).1, (inv_lemma' hH hU (mul_mem (hubR b) (hwtR t))).1, key_row, key_row]
    have hbb : b = b' := eq_of_neg_add_out b b' (by
      rw [AddSubgroup.mem_addSubgroupOf, mem_intV]
      intro i
      have h2 := hzrow i
      rw [hrowz] at h2
      simpa using h2)
    subst hbb
    have hz' : (ub b * wt t)⁻¹ * (ub b * wt t') = (wt t)⁻¹ * wt t' := by group
    rw [hz'] at hzcorner
    obtain ⟨-, -, hk⟩ := (hH L ϖ σ q N hU).2.1 _ (inv_mem (hwtR t)) _ (hwtR t')
    rw [hk, (inv_lemma' hH hU (hwtR t)).2 (hwtrow t), (inv_lemma' hH hU (hwtR t)).1, hwtrow, neg_zero,
      zero_dotProduct, add_zero, hwtcorner, hwtcorner] at hzcorner
    have htt : t = t' := eq_of_neg_add_out t t' (by
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceZero]
      refine ⟨by simpa using hzcorner, ?_⟩
      have h1 := (mem_traceZero.mp (Quotient.out t : traceZero σ (ϖ ^ f)).2).2
      have h2 := (mem_traceZero.mp (Quotient.out t' : traceZero σ (ϖ ^ f)).2).2
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, map_add, map_neg]
      linear_combination -h1 + h2)
    rw [htt]
  have hsurjG : Function.Surjective G := by
    rintro ⟨x, hx⟩
    have hxv : (QuotientGroup.mk (Quotient.out x) : RadQuot σ N) = x := QuotientGroup.out_eq' x
    have hvS : Small ϖ e f C D (Quotient.out x : radQ σ N).1 := hx
    have hvrow := hrowS _ hvS
    obtain ⟨b, hb⟩ : ∃ b : (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))),
        b = QuotientAddGroup.mk (⟨rowOf (Quotient.out x : radQ σ N).1, hvrow⟩ : preLat (ϖ ^ e • C)) := ⟨_, rfl⟩
    have hρ := neg_add_out_mem (S := (intV L N).addSubgroupOf (preLat (ϖ ^ e • C)))
      (⟨rowOf (Quotient.out x : radQ σ N).1, hvrow⟩ : preLat (ϖ ^ e • C))
    rw [← hb, AddSubgroup.mem_addSubgroupOf, mem_intV] at hρ
    obtain ⟨k, hkR, hkK, hkrow⟩ := exists_int_lift hH hU
      (fun i => -rowOf (Quotient.out x : radQ σ N).1 i + ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) i)
      (fun i => by simpa using hρ i)
    have hv'row : rowOf ((Quotient.out x : radQ σ N).1 * k) = ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) := by
      rw [((hH L ϖ σ q N hU).2.1 _ (Quotient.out x).2 _ hkR).1, hkrow]
      funext i
      simp
    have hv'S : Small ϖ e f C D ((Quotient.out x : radQ σ N).1 * k) := hinv _ (Quotient.out x).2 _ hkR hkK hvS
    have hwR : ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) ∈ radQ σ N := mul_mem (inv_mem (hubR b)) (mul_mem (Quotient.out x).2 hkR)
    have hw0 : rowOf ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) = 0 := by
      rw [((hH L ϖ σ q N hU).2.1 _ (inv_mem (hubR b)) _ (mul_mem (Quotient.out x).2 hkR)).1,
        (inv_lemma' hH hU (hubR b)).1, hubrow, hv'row, neg_add_cancel]
    have hmul : ub b * ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) = (Quotient.out x : radQ σ N).1 * k := by group
    have hcw := corner_of_small hH hU (hubR b) hwR hw0 (hubS b) (by rw [hmul]; exact hv'S)
    have htr := trace_corner hH hU hwR hw0
    obtain ⟨t, ht⟩ : ∃ t : (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))),
        t = QuotientAddGroup.mk (⟨cornerOf ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)), mem_traceZero.mpr ⟨hcw, htr⟩⟩ : traceZero σ (ϖ ^ f)) :=
      ⟨_, rfl⟩
    refine ⟨(b, t), Subtype.ext ?_⟩
    show (QuotientGroup.mk (⟨ub b * wt t, mul_mem (hubR b) (hwtR t)⟩ : radQ σ N) : RadQuot σ N) = x
    rw [← hxv]
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show (ub b * wt t)⁻¹ * (Quotient.out x : radQ σ N).1 ∈ KU σ (N + 2)
    have hy : (ub b * wt t)⁻¹ * (Quotient.out x : radQ σ N).1 = ((wt t)⁻¹ * ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k))) * k⁻¹ := by group
    rw [hy]
    refine mul_mem ?_ (inv_mem hkK)
    have hRR : (wt t)⁻¹ * ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) ∈ radQ σ N := mul_mem (inv_mem (hwtR t)) hwR
    refine (((hH L ϖ σ q N hU).1 _ hRR).2.2).mpr ⟨fun j => ?_, ?_⟩
    · obtain ⟨hr, -, -⟩ := (hH L ϖ σ q N hU).2.1 _ (inv_mem (hwtR t)) _ hwR
      rw [hr, (inv_lemma' hH hU (hwtR t)).1, hwtrow, hw0]
      simp
    · obtain ⟨-, -, hk⟩ := (hH L ϖ σ q N hU).2.1 _ (inv_mem (hwtR t)) _ hwR
      rw [hk, (inv_lemma' hH hU (hwtR t)).2 (hwtrow t), (inv_lemma' hH hU (hwtR t)).1, hwtrow, neg_zero,
        zero_dotProduct, add_zero, hwtcorner]
      have hm := neg_add_out_mem (S := (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f)))
        (⟨cornerOf ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)), mem_traceZero.mpr ⟨hcw, htr⟩⟩ : traceZero σ (ϖ ^ f))
      rw [← ht, AddSubgroup.mem_addSubgroupOf, mem_traceZero] at hm
      simpa using neg_mem hm.1
  have hbij : Function.Bijective G := ⟨hinj, hsurjG⟩
  have h1 := hL L ϖ σ q N hU (ϖ ^ e • C) (l + N * e) (isInt_smul hϖ e hC) (v_det_smul hϖv e l hdet)
  have h2 := hT L ϖ σ q f hU
  calc Nat.card {x : RadQuot σ N // Small ϖ e f C D (Quotient.out x : radQ σ N).1}
        = Nat.card ((↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))) × (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f)))) := (Nat.card_congr (Equiv.ofBijective G hbij)).symm
    _ = Nat.card (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))) * Nat.card (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))) := Nat.card_prod _ _
    _ = (intV L N).relIndex (preLat (ϖ ^ e • C)) * (traceZero σ 1).relIndex (traceZero σ (ϖ ^ f)) := rfl
    _ = q ^ (2 * (l + N * e) + f) := by rw [h1, h2, pow_add]
end GlobalTheory.CompanionTheory.InertCount
