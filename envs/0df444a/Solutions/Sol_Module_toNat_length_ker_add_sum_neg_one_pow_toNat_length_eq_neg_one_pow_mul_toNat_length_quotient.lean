-- Prove2me | solution 1 for Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4cb60a0a-7621-5063-b6ff-b3251809b1b8

import Mathlib
import Theorems.Thm_Module_forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex
import Theorems.Thm_Module_length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact
import Theorems.Thm_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient

set_option autoImplicit false

universe u

open TensorProduct

namespace LocalAltLengthHelpers

variable {R : Type u} [CommRing R]

theorem isWeaklyRegular_of_flat {M : Type u} [AddCommGroup M] [Module R M] [Module.Flat R M] {rs : List R}
    (h : RingTheory.Sequence.IsWeaklyRegular R rs) : RingTheory.Sequence.IsWeaklyRegular M rs :=
  ((TensorProduct.lid R M).isWeaklyRegular_congr rs).mp h.isWeaklyRegular_rTensor

noncomputable def topEquiv {K : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (n : ℕ) (hK : LinearMap.ker (δ (n + 1)) = ⊤) :
    (LinearMap.ker (δ (n + 1)) ⧸ (LinearMap.range (δ n)).comap (LinearMap.ker (δ (n + 1))).subtype) ≃ₗ[R]
      (K (n + 1) ⧸ LinearMap.range (δ n)) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofTop _ hK) (by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.ofTop_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hK.symm ▸ Submodule.mem_top⟩, hx, rfl⟩)

end LocalAltLengthHelpers

open LocalAltLengthHelpers in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (g : ℕ) (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hlen : rs.length = g)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, g < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (N : ℕ)
    (htors0 : ∀ a ∈ IsLocalRing.maximalIdeal R ^ N, ∀ z : LinearMap.ker (δ 0), a • z = 0)
    (htors : ∀ (i : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ N,
      ∀ q : LinearMap.ker (δ (i + 1)) ⧸ (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype, a • q = 0)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIN : IsLocalRing.maximalIdeal R ^ N ≤ I)
    (hU : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.ker ((δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ J') →
      ((∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K 0, (δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
          ∃ w : (R ⧸ J') ⊗[R] K 0, (δ 0).baseChange (R ⧸ J') w = 0 ∧
            LinearMap.rTensor (K 0) (Submodule.factor hJ') w = z) ↔ I ≤ J')) :
    ((Module.length R (LinearMap.ker (δ 0))).toNat : ℤ) +
        ∑ i ∈ Finset.range g, (-1) ^ (i + 1) *
          ((Module.length R (LinearMap.ker (δ (i + 1)) ⧸
            (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype)).toNat : ℤ) =
      (-1) ^ g * ((Module.length R (R ⧸ I)).toNat : ℤ) := by
  classical

  obtain ⟨eE⟩ := Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
    R (K 0) (K 1) (δ 0) I hI ⟨N, hIN⟩ hU hW
  have hlenE := eE.length_eq

  have hkertop : ∀ m : ℕ, g < m + 1 → LinearMap.ker (δ m) = ⊤ := by
    intro m hm
    haveI := hbdd (m + 1) hm
    exact eq_top_iff.mpr fun x _ => LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
  cases g with
  | zero =>

    simp only [Finset.range_zero, Finset.sum_empty, add_zero, pow_zero, one_mul]
    congr 2
    have h0 : LinearMap.ker (δ 0) = ⊤ := hkertop 0 (Nat.zero_lt_succ 0)
    haveI : Subsingleton (K 1) := hbdd 1 Nat.one_pos
    have hr : LinearMap.range (δ 0).dualMap = ⊥ := by
      rw [eq_bot_iff]
      rintro φ ⟨ψ, rfl⟩
      have : ψ = 0 := Subsingleton.elim _ _
      rw [this, map_zero]
      exact Submodule.zero_mem _
    obtain ⟨⟨ι, b⟩⟩ := (inferInstance : Module.Free R (K 0))
    haveI : Finite ι := Module.Finite.finite_basis b
    calc Module.length R (LinearMap.ker (δ 0))
        = Module.length R (K 0) := (LinearEquiv.ofTop _ h0).length_eq
      _ = Module.length R (Module.Dual R (K 0)) := b.toDualEquiv.length_eq
      _ = Module.length R (Module.Dual R (K 0) ⧸ LinearMap.range (δ 0).dualMap) :=
          (Submodule.quotEquivOfEqBot _ hr).symm.length_eq
      _ = Module.length R (R ⧸ I) := hlenE
  | succ n =>

    have hwreg : ∀ i, RingTheory.Sequence.IsWeaklyRegular (K i) rs := fun i =>
      isWeaklyRegular_of_flat hreg.toIsWeaklyRegular
    have hF1 := Module.forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex R rs K hwreg δ hdd
      ⟨N, fun a ha z hz => by
        rw [hmax] at ha
        exact congrArg Subtype.val (htors0 a ha ⟨z, hz⟩)⟩
      (fun i => ⟨N, fun a ha z hz => by
        rw [hmax] at ha
        have h := htors i a ha (Submodule.Quotient.mk ⟨z, hz⟩)
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
        exact h⟩)
    rw [hlen] at hF1
    obtain ⟨hF10, hF1S⟩ := hF1

    have hH0 : Module.length R (LinearMap.ker (δ 0)) = 0 := by
      rw [Module.length_eq_zero_iff]
      refine ⟨fun a b => Subtype.ext ?_⟩
      rw [hF10 (Nat.zero_lt_succ n) a.1 a.2, hF10 (Nat.zero_lt_succ n) b.1 b.2]

    have hHmid : ∀ i, i < n → Module.length R (LinearMap.ker (δ (i + 1)) ⧸
        (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) = 0 := by
      intro i hi
      rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, eq_top_iff]
      rintro ⟨z, hz⟩ -
      exact hF1S i (by omega) z hz

    have htop : Module.length R (LinearMap.ker (δ (n + 1)) ⧸
        (LinearMap.range (δ n)).comap (LinearMap.ker (δ (n + 1))).subtype) = Module.length R (R ⧸ I) := by
      rw [(topEquiv δ n (hkertop (n + 1) (by omega))).length_eq, ← hlenE]
      refine Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact R n rs hreg hlen hmax K
        (fun i hi => hbdd i hi) δ hdd (hF10 (Nat.zero_lt_succ n)) (fun i hi => hF1S i (by omega)) ⟨N, ?_⟩
      intro a ha q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hx : x ∈ LinearMap.ker (δ (n + 1)) := by rw [hkertop (n + 1) (by omega)]; exact Submodule.mem_top
      have h := htors n a ha (Submodule.Quotient.mk ⟨x, hx⟩)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact h

    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => ?_), hH0, htop]
    · simp
    · rw [hHmid i (Finset.mem_range.mp hi)]
      simp

end S_Module_toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient
end P2MW
export P2MW.S_Module_toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient (solution)
