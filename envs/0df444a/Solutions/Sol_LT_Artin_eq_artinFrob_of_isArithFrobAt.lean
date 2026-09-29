-- Prove2me | solution 1 for LT.Artin.eq_artinFrob_of_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e6e27f60-050d-5d1d-be37-6dd135bb1e64

import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_Artin_eq_artinFrob_of_isArithFrobAt

set_option autoImplicit false

noncomputable section

namespace M4aP2R
namespace ArtinRows

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin
open scoped Pointwise

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

theorem inertia_smul_eq_bot (τ : G) (Q : Ideal S) (hI : Q.inertia G = ⊥) : (τ • Q).inertia G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : S, g • x - x ∈ τ • Q := fun x => hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia G := by
    intro x
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

theorem eq_of_isArithFrobAt_of_inertia_eq_bot {σ σ' : G} {Q : Ideal S} (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
    (hI : Q.inertia G = ⊥) : σ = σ' := by
  have h := H.mul_inv_mem_inertia H'
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

theorem pow_smul_sub_pow_mem {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) (k : ℕ) (x : S) :
    σ ^ k • x - x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hσQ : ∀ y ∈ Q, σ • y ∈ Q := fun y hy => by
      have hstab := H.mem_stabilizer
      rw [MulAction.mem_stabilizer_iff] at hstab
      have h := Ideal.smul_mem_pointwise_smul σ y Q hy
      rwa [hstab] at h
    have h1 : σ ^ (k + 1) • x - σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
      rw [pow_succ', mul_smul, ← smul_sub]
      exact hσQ _ (ih x)
    have h2 : σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) - x ^ (Nat.card (R ⧸ Q.under R) ^ (k + 1)) ∈ Q := by
      rw [smul_pow', pow_succ', pow_mul]
      exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ _) (H x)
    have h := Q.add_mem h1 h2
    rwa [sub_add_sub_cancel] at h

theorem smul_pow_zero_sub_mem {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) (x : S) :
    σ ^ 0 • x - x ^ (Nat.card (R ⧸ Q.under R) ^ 0) ∈ Q :=
  pow_smul_sub_pow_mem H 0 x

variable [Finite G] [Algebra.IsInvariant R S G]

theorem arithFrobAt_smul (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite (S ⧸ τ • Q)] (hI : Q.inertia G = ⊥) :
    arithFrobAt R G (τ • Q) = τ * arithFrobAt R G Q * τ⁻¹ := by
  have h1 : IsArithFrobAt R (arithFrobAt R G (τ • Q)) (τ • Q) := IsArithFrobAt.arithFrobAt R G (τ • Q)
  have h2 : IsArithFrobAt R (τ * arithFrobAt R G Q * τ⁻¹) (τ • Q) := (IsArithFrobAt.arithFrobAt R G Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end Transport
section Rows
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
variable (v : HeightOneSpectrum (𝓞 K))

theorem rowA [IsMulCommutative (M ≃ₐ[K] M)] (Q : Ideal (𝓞 M)) [Q.IsPrime] [Finite (𝓞 M ⧸ Q)]
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q = artinFrob K M v := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := v.isMaximal
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove K M v) Q (M ≃ₐ[K] M)
  subst hτ
  have hI₀ : (primeAbove K M v).inertia (M ≃ₐ[K] M) = ⊥ := by
    have h := inertia_smul_eq_bot τ⁻¹ (τ • primeAbove K M v) hI
    rwa [inv_smul_smul] at h
  rw [arithFrobAt_smul τ (primeAbove K M v) hI₀, IsMulCommutative.is_comm.comm τ, mul_inv_cancel_right]
  rfl

end Rows

theorem rowB (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (v : HeightOneSpectrum (𝓞 K)) [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M}
    {Q : Ideal (𝓞 M)} [Q.IsPrime] (H : IsArithFrobAt (𝓞 K) σ Q)
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = artinFrob K M v := by
  haveI := finite_quotient_of_under_eq K M v hQ
  rw [← rowA K M v Q hQ hI]
  exact eq_of_isArithFrobAt_of_inertia_eq_bot H (IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q) hI

end M4aP2R.ArtinRows

theorem M4aP2R.ArtinRows.eq_artinFrob_of_isArithFrobAt_impl

    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (NumberField.RingOfIntegers M)}
    [Q.IsPrime] (H : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q)
    (hQ : Q.under (NumberField.RingOfIntegers K) = v.asIdeal)
    (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = LanglandsTunnell.P2.Artin.artinFrob K M v :=
  M4aP2R.ArtinRows.rowB K M v H hQ hI

set_option autoImplicit false

theorem solution
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (NumberField.RingOfIntegers M)}
    [Q.IsPrime] (H : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q)
    (hQ : Q.under (NumberField.RingOfIntegers K) = v.asIdeal)
    (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = LanglandsTunnell.P2.Artin.artinFrob K M v := by
  exact M4aP2R.ArtinRows.eq_artinFrob_of_isArithFrobAt_impl K M v H hQ hI

end
end S_LT_Artin_eq_artinFrob_of_isArithFrobAt
end P2MW
export P2MW.S_LT_Artin_eq_artinFrob_of_isArithFrobAt (solution)
