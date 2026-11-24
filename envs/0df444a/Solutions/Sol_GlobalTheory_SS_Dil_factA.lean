-- Prove2me | solution 1 for GlobalTheory.SS.Dil.factA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:41.327557+00:00
-- url     : https://prove2.me/submissions/eb7e8907-c9a7-486e-8c86-50ee4dfb1d51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Theorems.Thm_GlobalTheory_SS_Dil_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R k C : Type} {n : ℕ} [CommRing R] [CommRing k] [CommRing C] [Algebra R k] [Algebra k C]
    [Algebra R C] [IsScalarTower R k C] (π : R) (hk : Function.Surjective (algebraMap R k))
    (hπ : ∀ r, algebraMap R k r = 0 ↔ π ∣ r) [Algebra.FormallySmooth k C]
    (σ : MvPolynomial (Fin n) R →ₐ[R] C) (hσ : Function.Surjective σ) (I : Ideal (MvPolynomial (Fin n) R))
    (hI : ∀ p, p ∈ I ↔ σ p = 0) :
    ∃ h : Fin n → MvPolynomial (Fin n) R, (∀ j, h j ∈ I) ∧
      ∀ g ∈ I, ∃ p, g - ∑ j, pderiv j g * h j - MvPolynomial.C π * p ∈ I * I := by
  let T : Ideal (MvPolynomial (Fin n) R) := Ideal.span {MvPolynomial.C π} ⊔ I * I
  have hπI : MvPolynomial.C π ∈ I := by
    rw [hI, ← algebraMap_eq, σ.commutes, IsScalarTower.algebraMap_apply R k C, (hπ π).2 dvd_rfl, map_zero]
  have hT : T ≤ I := sup_le ((Ideal.span_singleton_le_iff_mem _).2 hπI) Ideal.mul_le_left
  let A := MvPolynomial (Fin n) R ⧸ T
  let m : MvPolynomial (Fin n) R →ₐ[R] A := Ideal.Quotient.mkₐ R T
  have hm : Function.Surjective m := Ideal.Quotient.mkₐ_surjective R T
  have hm0 : ∀ p, m p = 0 ↔ p ∈ T := fun p => Ideal.Quotient.eq_zero_iff_mem
  let κ : k →+* A := RingHom.liftOfSurjective (algebraMap R k) hk ⟨algebraMap R A, by
    intro r hr
    obtain ⟨c, rfl⟩ := (hπ r).1 hr
    rw [RingHom.mem_ker, map_mul, ← m.commutes π, (hm0 _).2, zero_mul]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)⟩
  have hκ : ∀ r, κ (algebraMap R k r) = algebraMap R A r := fun r =>
    RingHom.liftOfSurjective_comp_apply _ _ _ _
  letI : Algebra k A := κ.toAlgebra
  let ρ0 : A →ₐ[R] C := Ideal.Quotient.liftₐ T σ (fun a ha => (hI a).1 (hT ha))
  have hρ0 : ∀ p, ρ0 (m p) = σ p := fun p => rfl
  let ρ : A →ₐ[k] C :=
    { ρ0.toRingHom with
      commutes' := fun c => by
        obtain ⟨r, rfl⟩ := hk c
        show ρ0 (κ _) = _
        rw [hκ, ρ0.commutes, IsScalarTower.algebraMap_apply R k C] }
  have hρ : ∀ p, ρ (m p) = σ p := fun p => rfl
  have hsq : ∀ x y : A, ρ x = 0 → ρ y = 0 → x * y = 0 := by
    intro x y hx hy
    obtain ⟨x, rfl⟩ := hm x; obtain ⟨y, rfl⟩ := hm y
    rw [← map_mul, hm0]
    exact Ideal.mem_sup_right (Ideal.mul_mem_mul ((hI x).2 hx) ((hI y).2 hy))
  have hnil : IsNilpotent (RingHom.ker (ρ : A →+* C)) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    exact hsq x y hx hy⟩
  have hρs : Function.Surjective ρ := fun c => by
    obtain ⟨p, rfl⟩ := hσ c; exact ⟨m p, rfl⟩
  let s : C →ₐ[k] A := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k C) ρ hρs hnil
  have hs : ∀ c, ρ (s c) = c := fun c =>
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k C) ρ hρs hnil c
  let D : MvPolynomial (Fin n) R → A := fun p => m p - s (σ p)
  have hD : ∀ p, ρ (D p) = 0 := fun p => by simp only [D, map_sub, hs, hρ, sub_self]
  have hch := chain (W := A) m.toRingHom D (fun x y => by simp only [D, map_add]; ring)
    (fun x y => by
      have := hsq _ _ (hD x) (hD y)
      simp only [D, map_mul, smul_eq_mul] at this ⊢
      show _ = m x * _ + m y * _
      linear_combination (-1 : A) * this)
    (fun r => by
      simp only [D]
      rw [← algebraMap_eq, m.commutes, σ.commutes, IsScalarTower.algebraMap_apply R k C, s.commutes, ← hκ]
      exact sub_self _)
  choose h hh using fun j => hm (D (X j))
  refine ⟨h, fun j => (hI _).2 (by rw [← hρ, hh, hD]), fun g hg => ?_⟩
  have h1 : g - ∑ j, pderiv j g * h j ∈ T := by
    rw [← hm0, map_sub, map_sum]
    have := hch g
    simp only [D, (hI g).1 hg, map_zero, sub_zero] at this
    rw [this, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hh]; rfl
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton.1 hx
  exact ⟨p, by rw [← hxy]; simpa using hy⟩
end GlobalTheory.SS.Dil
