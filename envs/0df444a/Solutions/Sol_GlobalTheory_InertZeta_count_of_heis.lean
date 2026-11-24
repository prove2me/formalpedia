-- Prove2me | solution 1 for GlobalTheory.InertZeta.count_of_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:39.066652+00:00
-- url     : https://prove2.me/submissions/3e5662ac-dc34-4a01-b2d6-6486ae1db46b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
import Theorems.Thm_GlobalTheory_InertZeta_colOf_eq_of_rowOf_eq
import Theorems.Thm_GlobalTheory_InertZeta_inv_mul_of_rowOf_eq
import Theorems.Thm_GlobalTheory_InertZeta_rowOf_inv_mul
import Theorems.Thm_GlobalTheory_InertZeta_mul_of_rowOf_eq_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_exists_trace_one
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



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution : Heis → LatIndex → TraceIndex → Count := by
  intro hH hL hT L _ _ ϖ σ q N hU C D l e f hC hdet hex hinv
  obtain ⟨h1, h2, h3⟩ := hH L ϖ σ q N hU
  have hσσ := hU.1
  have hσv := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := hU.2.2.2.1
  have hϖ1 : ϖ ∈ intL L := by show Valued.v ϖ ≤ 1; rw [hϖ]; exact oneLePart_eq_one.mp rfl
  have hσint : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx

  set A : Matrix (Fin N) (Fin N) L := ϖ ^ e • C with hA
  have hAint : IsInt A := fun i j => by
    rw [hA, Matrix.smul_apply, smul_eq_mul]; exact mul_mem (pow_mem hϖ1 _) (hC i j)
  have hAdet : Valued.v A.det = WithZero.exp (-((l + N * e : ℕ) : ℤ)) := by
    rw [hA, Matrix.det_smul, map_mul, map_pow, map_pow, hϖ, hdet, Fintype.card_fin, ← WithZero.exp_nsmul,
      ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1; push_cast; ring
  have iL := hL L ϖ σ q N hU A (l + N * e) hAint hAdet
  have iT := hT L ϖ σ q f hU
  set Λ := preLat A
  set I := intV L N
  set T := traceZero σ (ϖ ^ f)
  set T₀ := traceZero σ 1
  have memΛ : ∀ r : Fin N → L, r ∈ Λ ↔ ∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L := fun r => by
    rw [mem_preLat, hA, Matrix.vecMul_smul]; rfl
  rw [pow_add, ← iL, ← iT]

  have ex0 : ∀ r : Λ, ∃ u : radQ σ N, rowOf (u : GU σ (N + 2)) = r ∧ Small ϖ e f C D (u : GU σ (N + 2)) := fun r => by
    obtain ⟨u, hu, h, hs⟩ := hex r ((memΛ r).1 r.2)
    exact ⟨⟨u, hu⟩, h, hs⟩
  choose u₀ hu₀r hu₀s using ex0
  have exz : ∀ t : T, ∃ z : radQ σ N, rowOf (z : GU σ (N + 2)) = 0 ∧ cornerOf (z : GU σ (N + 2)) = t := fun t => by
    have ht := (mem_traceZero.1 t.2).2
    obtain ⟨z, hz, h, hc⟩ := h3 0 t (by
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero]; linear_combination ht)
    exact ⟨⟨z, hz⟩, h, hc⟩
  choose z hzr hzc using exz
  have smallOut : ∀ w : radQ σ N, Small ϖ e f C D (w : GU σ (N + 2)) →
      Small ϖ e f C D (((QuotientGroup.mk w : RadQuot σ N).out : radQ σ N) : GU σ (N + 2)) := fun w hw => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul ((KU σ (N + 2)).subgroupOf (radQ σ N)) w
    rw [hk]
    exact hinv w.1 w.2 k.1.1 k.1.2 (Subgroup.mem_subgroupOf.1 k.2) hw
  have smallW : ∀ (r : Λ) (t : T), Small ϖ e f C D ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) := fun r t => by
    obtain ⟨hr, hb, hc⟩ := mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)
    have hs := hu₀s r
    show Small ϖ e f C D ((u₀ r : GU σ (N + 2)) * (z t : GU σ (N + 2)))
    refine ⟨fun j => ?_, ?_⟩
    · rw [hr]; exact hs.1 j
    · rw [hr, hb, hc, hzc]
      convert add_mem hs.2 (mem_traceZero.1 t.2).1 using 1
      ring
  have rowW : ∀ (r : Λ) (t : T), rowOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) = r := fun r t =>
    ((mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).1).trans (hu₀r r)
  have cornerW : ∀ (r : Λ) (t : T), cornerOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) =
      cornerOf (u₀ r : GU σ (N + 2)) + t := fun r t => by
    rw [← hzc t]; exact (mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).2.2
  let Φ : (Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T) →
      {x : RadQuot σ N // Small ϖ e f C D (x.out : radQ σ N).1} := fun p =>
    ⟨QuotientGroup.mk (u₀ p.1.out * z p.2.out), smallOut _ (smallW _ _)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have hk := QuotientGroup.eq.1 (congrArg Subtype.val h)
      rw [Subgroup.mem_subgroupOf] at hk
      have hK := (h1 _ ((u₀ a.out * z b.out)⁻¹ * (u₀ a'.out * z b'.out)).2).2.2.1 hk
      have ha : a = a' := by
        rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' a', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_intV]
        intro j
        have := hK.1 j
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, rowOf_inv_mul h1 h2 (u₀ a.out * z b.out).2 (u₀ a'.out * z b'.out).2,
          rowW, rowW] at this
      subst ha
      have hb : b = b' := by
        rw [← QuotientAddGroup.out_eq' b, ← QuotientAddGroup.out_eq' b', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_traceZero]
        have hd := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out * z b.out).2 (u₀ a.out * z b'.out).2
          ((rowW _ _).trans (rowW _ _).symm)
        have hc := hK.2
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hd.2, cornerW, cornerW] at hc
        have t1 := (mem_traceZero.1 b.out.2).2
        have t2 := (mem_traceZero.1 b'.out.2).2
        refine ⟨?_, ?_⟩
        · convert hc using 1; push_cast; ring
        · push_cast; rw [map_add, map_neg]; linear_combination t2 - t1
      rw [hb]
    · rintro ⟨x, hx⟩

      have hrΛ : rowOf ((x.out : radQ σ N) : GU σ (N + 2)) ∈ Λ := (memΛ _).2 hx.1
      have hρ : (-(⟨_, hrΛ⟩ : Λ) + (QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) : Λ ⧸ I.addSubgroupOf Λ).out) ∈
          I.addSubgroupOf Λ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_intV] at hρ
      set a : Λ ⧸ I.addSubgroupOf Λ := QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) with ha
      set u : radQ σ N := x.out with hu
      set ρ : Fin N → L := -rowOf (u : GU σ (N + 2)) + (a.out : Fin N → L) with hρdef
      have hρ' : ∀ i, ρ i ∈ intL L := hρ
      obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
      set s : L := -∑ j, ρ j * σ (ρ j.rev) with hsdef
      have hs : σ s = s := by
        simp only [hsdef, map_neg, map_sum, map_mul, hσσ]
        congr 1
        exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [mul_comm])
      have hsint : s ∈ intL L := neg_mem (Subring.sum_mem _ fun j _ => mul_mem (hρ' j) (hσint _ (hρ' _)))
      obtain ⟨k, hk, hkr, hkc⟩ := h3 ρ (τ * s) (by rw [map_mul, hs]; linear_combination s * hτ1)
      have hkK : k ∈ KU σ (N + 2) := (h1 k hk).2.2.2 ⟨fun j => hkr ▸ hρ' j, hkc ▸ mul_mem hτ hsint⟩
      set uk : radQ σ N := u * ⟨k, hk⟩ with hukdef
      have hukS : Small ϖ e f C D (uk : GU σ (N + 2)) := hinv u.1 u.2 k hk hkK hx
      have hukr : rowOf (uk : GU σ (N + 2)) = a.out := by
        rw [hukdef, Subgroup.coe_mul, (h2 _ u.2 _ hk).1, hkr, hρdef, add_neg_cancel_left]
      have hv := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
      set v : radQ σ N := (u₀ a.out)⁻¹ * uk with hvdef
      have hvr : rowOf (v : GU σ (N + 2)) = 0 := hv.1
      have hvc : cornerOf (v : GU σ (N + 2)) = cornerOf (uk : GU σ (N + 2)) - cornerOf (u₀ a.out : GU σ (N + 2)) := hv.2
      have htT : cornerOf (v : GU σ (N + 2)) ∈ T := by
        rw [mem_traceZero]
        refine ⟨?_, ?_⟩
        · have hcol := colOf_eq_of_rowOf_eq h1 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
          have := sub_mem hukS.2 (hu₀s a.out).2
          rw [hukr, ← hcol, hu₀r] at this
          rw [hvc]
          convert this using 1
          ring
        · have := (h1 _ v.2).2.1
          rw [hvr, zero_dotProduct] at this
          linear_combination this
      set bq : T ⧸ T₀.addSubgroupOf T := QuotientAddGroup.mk (⟨_, htT⟩ : T) with hbq
      have hδ : (-(⟨_, htT⟩ : T) + bq.out) ∈ T₀.addSubgroupOf T := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceZero] at hδ
      refine ⟨(a, bq), Subtype.ext ?_⟩
      show (QuotientGroup.mk (u₀ a.out * z bq.out) : RadQuot σ N) = x
      have e1 : (QuotientGroup.mk u : RadQuot σ N) = QuotientGroup.mk uk :=
        QuotientGroup.eq.2 (by rw [hukdef, inv_mul_cancel_left]; exact Subgroup.mem_subgroupOf.2 hkK)
      rw [← QuotientGroup.out_eq' x, ← hu, e1, QuotientGroup.eq,
        show (u₀ a.out * z bq.out)⁻¹ * uk = (z bq.out)⁻¹ * v by rw [hvdef, _root_.mul_inv_rev, mul_assoc],
        Subgroup.mem_subgroupOf]
      have hzv := inv_mul_of_rowOf_eq h1 h2 (z bq.out).2 v.2 ((hzr _).trans hvr.symm)
      refine (h1 _ ((z bq.out)⁻¹ * v).2).2.2.2 ⟨fun j => ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.1]; exact zero_mem _
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.2, hzc]
        have := neg_mem hδ.1
        convert this using 1
        push_cast
        ring
  rw [show I.relIndex Λ * T₀.relIndex T = Nat.card ((Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T)) from
    (Nat.card_prod _ _).symm]
  exact (Nat.card_eq_of_bijective Φ hΦ).symm
end GlobalTheory.InertZeta
