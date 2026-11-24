-- Prove2me | solution 1 for GlobalTheory.TorusOrbitLat.orbit_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:57.074797+00:00
-- url     : https://prove2.me/submissions/367d797d-e1b5-4792-b87c-71cdabad3eee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho
import Theorems.Thm_GlobalTheory_TorusOrbitLat_mem_mulLat_unit
import Theorems.Thm_GlobalTheory_TorusOrbitLat_mulLat_eq_iff
import Theorems.Thm_GlobalTheory_TorusOrbitLat_rho_cond_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.TorusOrbitLat
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.TorusOrbitLat
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  intro K B L hSle hidx a hrho m k hmk hin hout
  set w : B.A := algebraMap K.O B.A a with hw
  set H : Subgroup B.T := (stabLat K.O L).subgroupOf B.T with hH
  set Kc : Subgroup B.T := (intUnits K.O B.A).subgroupOf B.T with hKc
  have hHK : H ≤ Kc := by
    intro x hx
    rw [hH, Subgroup.mem_subgroupOf] at hx
    rw [hKc, Subgroup.mem_subgroupOf]
    exact hSle ⟨hx, x.2⟩
  have hidx_eq : (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) = (H.subgroupOf Kc).index := by
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : intUnits K.O B.A ⊓ B.T ≤ B.T),
      Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right]
    rfl
  have hQfin : Finite (Kc ⧸ H.subgroupOf Kc) := by
    rw [← Subgroup.index_ne_zero_iff_finite, ← hidx_eq]; exact hidx
  have hRfin : ∀ j, Finite {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => (Nat.card_pos_iff.mp (hrho j)).2
  have hrho_eq : ∀ j, B.rho (w ^ j) = Nat.card {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => rfl
  let e := Subgroup.quotientEquivProdOfLE hHK
  have he1 : ∀ g : B.T, (e (QuotientGroup.mk g)).1 = QuotientGroup.mk g := fun g => rfl

  let Y := {c : B.T ⧸ H // w ^ k ∈ mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L}
  let fY : Y → {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ w ^ k ∈ M} :=
    fun c => ⟨mulLat K.O (((Quotient.out c.1 : B.T) : B.Aˣ) : B.A) L, ⟨_, (Quotient.out c.1).2, rfl⟩, c.2⟩
  have hfY : Function.Bijective fY := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      have h' : mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L = mulLat K.O (((Quotient.out c' : B.T) : B.Aˣ) : B.A) L :=
        congrArg Subtype.val h
      rw [mulLat_eq_iff] at h'
      apply Subtype.ext
      change c = c'
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h')
    · rintro ⟨M, ⟨t, ht, rfl⟩, hM⟩
      have hc := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H))
      rw [hH, Subgroup.mem_subgroupOf] at hc
      have key : mulLat K.O (((Quotient.out (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H) : B.T) : B.Aˣ) : B.A) L =
          mulLat K.O (t : B.A) L := by
        rw [mulLat_eq_iff]; simpa using hc
      exact ⟨⟨_, key ▸ hM⟩, Subtype.ext key⟩
  have hcardXY := Nat.card_congr (Equiv.ofBijective fY hfY)

  have key1 : ∀ g : B.T, ((((g : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w ^ k ∈ L) →
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A) := by
    intro g hg
    rw [he1 g, rho_cond_mk]
    have := hout _ hg
    convert this using 1
    rw [pow_add]; ring
  let U : Y → {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) := fun c =>
    (⟨(e c.1).1, by
      have := key1 (Quotient.out c.1) (by rw [← mem_mulLat_unit]; exact c.2)
      rwa [QuotientGroup.out_eq'] at this⟩, (e c.1).2)
  have hU : Function.Injective U := by
    intro c c' h
    apply Subtype.ext
    apply e.injective
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 h2
  have hYfin : Finite Y := by
    haveI := hRfin (k + m)
    exact Finite.of_injective U hU

  have key2 : ∀ g : B.T,
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A) →
      w ^ k ∈ mulLat K.O ((g : B.Aˣ) : B.A) L := by
    intro g hg
    rw [he1 g, rho_cond_mk] at hg
    rw [mem_mulLat_unit]
    have := hin _ hg
    convert this using 1
    rw [← Nat.add_sub_cancel' hmk, pow_add, Nat.add_sub_cancel_left]; ring
  let D : {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) → Y := fun p =>
    ⟨e.symm (p.1.1, p.2), by
      have hc : e (e.symm (p.1.1, p.2)) = (p.1.1, p.2) := e.apply_symm_apply _
      apply key2
      rw [QuotientGroup.out_eq', hc]
      exact p.1.2⟩
  have hD : Function.Injective D := by
    intro p p' h
    have h' := e.symm.injective (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) h2
  refine ⟨?_, ?_, ?_⟩
  · exact Finite.of_equiv Y (Equiv.ofBijective fY hfY)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    exact (Nat.card_prod _ _).symm.trans_le (Nat.card_le_card_of_injective D hD)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    haveI := hRfin (k + m)
    exact (Nat.card_le_card_of_injective U hU).trans_eq (Nat.card_prod _ _)
end GlobalTheory.TorusOrbitLat
