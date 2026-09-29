-- Prove2me | solution 1 for GlobalGaloisRep.IsUnramifiedAt.exists_apply_eq_apply_conj_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2d42af1a-4442-5e46-95ac-19f7722eed7a

import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt

open scoped Pointwise

namespace S18
namespace FrobConj

open ValuationSubring IsLocalRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_smul_nonunits_iff {τ : L ≃ₐ[K] L} {A : ValuationSubring L} {x : L} :
    x ∈ (τ • A).nonunits ↔ τ.symm x ∈ A.nonunits := by
  rw [mem_nonunits_iff_or, mem_nonunits_iff_or]
  constructor
  · rintro (h0 | hinv)
    · left
      rw [h0, map_zero]
    · by_cases hx0 : x = 0
      · left; rw [hx0, map_zero]
      right
      intro hmem
      apply hinv
      have : τ (τ.symm x)⁻¹ ∈ τ • A := by
        rw [mem_pointwise_smul_iff_inv_smul_mem]
        have h1 : (τ⁻¹ : L ≃ₐ[K] L) • τ (τ.symm x)⁻¹ = (τ.symm x)⁻¹ := by
          show τ.symm (τ (τ.symm x)⁻¹) = (τ.symm x)⁻¹
          exact τ.symm_apply_apply _
        rw [h1]
        exact hmem
      rwa [map_inv₀, τ.apply_symm_apply] at this
  · rintro (h0 | hinv)
    · left
      have := congrArg τ h0
      rwa [τ.apply_symm_apply, map_zero] at this
    · right
      intro hmem
      apply hinv
      rw [mem_pointwise_smul_iff_inv_smul_mem] at hmem
      have h1 : (τ⁻¹ : L ≃ₐ[K] L) • x⁻¹ = (τ.symm x)⁻¹ := by
        show τ.symm x⁻¹ = (τ.symm x)⁻¹
        exact map_inv₀ _ _
      rwa [h1] at hmem

theorem isFrobeniusAt_iff_forall_sub_pow_mem_nonunits
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ} :
    A.IsFrobeniusAt σ q ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ x ∈ A, σ x - x ^ q ∈ A.nonunits := by
  constructor
  · intro h
    refine ⟨h.mem_decompositionSubgroup, fun x hx => ?_⟩
    set a : A := ⟨x, hx⟩
    set g : A.decompositionSubgroup K := ⟨σ, h.mem_decompositionSubgroup⟩
    have h1 : residue A (g • a) = residue A (a ^ q) := by
      rw [map_pow, ResidueField.residue_smul]
      exact h.smul_residue_eq (residue A a)
    have h2 : g • a - a ^ q ∈ maximalIdeal A := by
      have h0 : residue A (g • a - a ^ q) = 0 := by rw [map_sub, h1, sub_self]
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    have hcoe : ((g • a - a ^ q : A) : L) = σ x - x ^ q := rfl
    exact hcoe ▸ (coe_mem_nonunits_iff (A := A)).mpr h2
  · rintro ⟨hd, hall⟩
    refine ⟨hd, fun y => ?_⟩
    obtain ⟨a, rfl⟩ := residue_surjective y
    rw [← ResidueField.residue_smul, ← map_pow]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← coe_mem_nonunits_iff]
    have hcoe : (((⟨σ, hd⟩ : A.decompositionSubgroup K) • a - a ^ q : A) : L)
        = σ (a : L) - (a : L) ^ q := rfl
    rw [hcoe]
    exact hall (a : L) a.2

theorem isFrobeniusAt_conj {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (hσ : A.IsFrobeniusAt σ q) (g : L ≃ₐ[K] L) :
    (g • A).IsFrobeniusAt (g * σ * g⁻¹) q := by
  obtain ⟨hσd, hσall⟩ := isFrobeniusAt_iff_forall_sub_pow_mem_nonunits.mp hσ
  have hd : g * σ * g⁻¹ ∈ (g • A).decompositionSubgroup K := by
    refine MulAction.mem_stabilizer_iff.mpr ?_
    have hσA : σ • A = A := MulAction.mem_stabilizer_iff.mp hσd
    rw [mul_smul, mul_smul, inv_smul_smul, hσA]
  refine isFrobeniusAt_iff_forall_sub_pow_mem_nonunits.mpr ⟨hd, fun y hy => ?_⟩
  have hx : g.symm y ∈ A := by
    have h1 : (g⁻¹ : L ≃ₐ[K] L) • y = g.symm y := by
      show g⁻¹ y = g.symm y; rw [AlgEquiv.aut_inv]
    rw [mem_pointwise_smul_iff_inv_smul_mem, h1] at hy
    exact hy
  have hkey : (g * σ * g⁻¹) y - y ^ q = g (σ (g.symm y) - (g.symm y) ^ q) := by
    rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      g.apply_symm_apply]
  rw [hkey, mem_smul_nonunits_iff, g.symm_apply_apply]
  exact hσall (g.symm y) hx

theorem mem_inertiaSubgroupIn {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K, (⟨σ, h⟩ : A.decompositionSubgroup K) ∈
        A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

theorem mul_inv_mem_inertiaSubgroupIn {A : ValuationSubring L} {σ τ : L ≃ₐ[K] L} {q : ℕ}
    (hσ : A.IsFrobeniusAt σ q) (hτ : A.IsFrobeniusAt τ q) :
    σ * τ⁻¹ ∈ A.inertiaSubgroupIn K := by
  obtain ⟨hσd, hσf⟩ := hσ
  obtain ⟨hτd, hτf⟩ := hτ
  have hd : σ * τ⁻¹ ∈ A.decompositionSubgroup K :=
    (A.decompositionSubgroup K).mul_mem hσd ((A.decompositionSubgroup K).inv_mem hτd)
  rw [mem_inertiaSubgroupIn]
  refine ⟨hd, ?_⟩
  simp only [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  have hsubtype : (⟨σ * τ⁻¹, hd⟩ : A.decompositionSubgroup K) =
      (⟨σ, hσd⟩ : A.decompositionSubgroup K) * (⟨τ, hτd⟩ : A.decompositionSubgroup K)⁻¹ := by
    ext
    rfl
  refine RingEquiv.ext fun x => ?_
  have hx : (⟨σ * τ⁻¹, hd⟩ : A.decompositionSubgroup K) • x = x := by
    rw [hsubtype, mul_smul]
    set y := (⟨τ, hτd⟩ : A.decompositionSubgroup K)⁻¹ • x with hy
    have hτy : (⟨τ, hτd⟩ : A.decompositionSubgroup K) • y = x := by
      rw [hy, smul_inv_smul]
    have hyq : y ^ q = x := by rw [← hτf y, hτy]
    rw [hσf y, hyq]
  simpa using hx

theorem eq_of_isFrobeniusAt {G : Type*} [Group G] {ρ : (L ≃ₐ[K] L) →* G} {q : ℕ}
    (hρ : GlobalGaloisRep.IsUnramifiedAt ρ q)
    {A : ValuationSubring L} (hA : A.LiesOverPrime q) {σ τ : L ≃ₐ[K] L}
    (hσ : A.IsFrobeniusAt σ q) (hτ : A.IsFrobeniusAt τ q) : ρ σ = ρ τ := by
  have hker : ρ (σ * τ⁻¹) = 1 := hρ A hA (mul_inv_mem_inertiaSubgroupIn hσ hτ)
  calc ρ σ = ρ ((σ * τ⁻¹) * τ) := by group
    _ = ρ (σ * τ⁻¹) * ρ τ := map_mul ρ _ _
    _ = 1 * ρ τ := by rw [hker]
    _ = ρ τ := one_mul _

end S18.FrobConj

theorem solution
    {G : Type*} [Group G] {ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G} {q : ℕ}
    (hq : q.Prime) (hunr : GlobalGaloisRep.IsUnramifiedAt ρ q)
    {A A' : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) (hA' : A'.LiesOverPrime q)
    {σ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : A.IsFrobeniusAt σ q) (hσ' : A'.IsFrobeniusAt σ' q) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ' = ρ (τ * σ * τ⁻¹) := by
  obtain ⟨τ, hτA⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hq A A' hA hA'
  have hfr : A'.IsFrobeniusAt (τ * σ * τ⁻¹) q := hτA ▸ S18.FrobConj.isFrobeniusAt_conj hσ τ
  exact ⟨τ, S18.FrobConj.eq_of_isFrobeniusAt hunr hA' hσ' hfr⟩

end S_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt
end P2MW
export P2MW.S_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt (solution)
