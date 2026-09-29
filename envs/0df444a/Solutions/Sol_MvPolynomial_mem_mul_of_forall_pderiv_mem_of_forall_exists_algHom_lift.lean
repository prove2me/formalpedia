-- Prove2me | solution 1 for MvPolynomial.mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a637ce9e-08f5-53ca-94c4-18c1e8245f96

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift

set_option autoImplicit false

open MvPolynomial

open MvPolynomial
open scoped BigOperators

namespace K2Aux

theorem sub_eq_sum_pderiv {R : Type} [CommRing R] {n : ℕ} {D : Type} [CommRing D] [Algebra R D]
    (φ₁ φ₂ : MvPolynomial (Fin n) R →ₐ[R] D)
    (hδ : ∀ i j, (φ₁ (X i) - φ₂ (X i)) * (φ₁ (X j) - φ₂ (X j)) = 0) (f : MvPolynomial (Fin n) R) :
    φ₁ f - φ₂ f = ∑ i : Fin n, φ₂ (pderiv i f) * (φ₁ (X i) - φ₂ (X i)) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes, sub_self]
    symm
    exact Finset.sum_eq_zero fun i _ => by rw [MvPolynomial.algebraMap_eq, pderiv_C, map_zero, zero_mul]
  | add p q hp hq =>
    rw [map_add, map_add, show φ₁ p + φ₁ q - (φ₂ p + φ₂ q) = (φ₁ p - φ₂ p) + (φ₁ q - φ₂ q) by ring, hp, hq,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add, map_add, add_mul]
  | mul_X f k hf =>
    have e1 : φ₁ f = φ₂ f + ∑ i : Fin n, φ₂ (pderiv i f) * (φ₁ (X i) - φ₂ (X i)) := by rw [← hf]; ring
    have hz : (∑ i : Fin n, φ₂ (pderiv i f) * (φ₁ (X i) - φ₂ (X i))) * (φ₁ (X k) - φ₂ (X k)) = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hδ i k, mul_zero]
    have rhs : ∑ i : Fin n, φ₂ (pderiv i (f * X k)) * (φ₁ (X i) - φ₂ (X i)) =
        (∑ i : Fin n, φ₂ (pderiv i f) * (φ₁ (X i) - φ₂ (X i))) * φ₂ (X k) + φ₂ f * (φ₁ (X k) - φ₂ (X k)) := by
      simp_rw [pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · rw [Finset.sum_eq_single k]
        · rw [pderiv_X, Pi.single_eq_same, map_one, mul_one]
        · intro i _ hik
          rw [pderiv_X, Pi.single_eq_of_ne' hik, map_zero, mul_zero, zero_mul]
        · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [rhs, map_mul, map_mul, e1]
    linear_combination hz

end K2Aux

theorem solution
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)

    (D : ℕ → Type) [∀ N, CommRing (D N)] [∀ N, Algebra R (D N)]
    [∀ N, Algebra (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    [∀ N, IsScalarTower R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    [∀ N, Module.FaithfullyFlat (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    (σ : ∀ N, (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] D N)
    (hσ : ∀ (N : ℕ) (f : MvPolynomial (Fin n) R),
      σ N (Ideal.Quotient.mk I f) -
          algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
          (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)))
    (v : MvPolynomial (Fin n) R) (hv : v ∈ I) (hdv : ∀ i : Fin n, MvPolynomial.pderiv i v ∈ J) :
    v ∈ J * I := by
  classical

  have stepA : ∀ N : ℕ, v ∈ J ^ N ⊔ J * I := by
    intro N

    let φ₂ : MvPolynomial (Fin n) R →ₐ[R] D N :=
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)).comp (Ideal.Quotient.mkₐ R (J ^ N ⊔ J * I))
    let φ₁ : MvPolynomial (Fin n) R →ₐ[R] D N := (σ N).comp (Ideal.Quotient.mkₐ R I)
    have hφ₂ : ∀ f, φ₂ f = algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) :=
      fun f => rfl
    have hφ₁ : ∀ f, φ₁ f = σ N (Ideal.Quotient.mk I f) := fun f => rfl

    let mm : Ideal (MvPolynomial (Fin n) R) → Ideal (D N) := fun L =>
      Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) L)
    have hmm : ∀ (L : Ideal (MvPolynomial (Fin n) R)) (f : MvPolynomial (Fin n) R), f ∈ L → φ₂ f ∈ mm L :=
      fun L f hf => Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hf)
    have hmm_mul : ∀ L L' : Ideal (MvPolynomial (Fin n) R), mm L * mm L' = mm (L * L') := by
      intro L L'; show Ideal.map _ _ * Ideal.map _ _ = Ideal.map _ (Ideal.map _ (L * L')); rw [Ideal.map_mul, Ideal.map_mul]
    have hmm_mono : ∀ L L' : Ideal (MvPolynomial (Fin n) R), L ≤ L' → mm L ≤ mm L' :=
      fun L L' h => Ideal.map_mono (Ideal.map_mono h)
    have hkill : mm (J ^ N ⊔ J * I) = ⊥ := by
      show Ideal.map _ (Ideal.map _ _) = ⊥
      rw [Ideal.map_quotient_self, Ideal.map_bot]

    have hincl1 : (J ^ N ⊔ I) * (J ^ N ⊔ I) ≤ J ^ N ⊔ J * I := by
      rw [Ideal.mul_le]
      intro r hr s hs
      obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Submodule.mem_sup.mp hr
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs
      have e : (r₁ + r₂) * (s₁ + s₂) = (r₁ * (s₁ + s₂) + r₂ * s₁) + r₂ * s₂ := by ring
      rw [e]
      refine Submodule.add_mem_sup (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr₁) (Ideal.mul_mem_left _ _ hs₁)) ?_
      exact Ideal.mul_mono_left hIJ (Ideal.mul_mem_mul hr₂ hs₂)
    have hincl2 : J * (J ^ N ⊔ I) ≤ J ^ N ⊔ J * I := by
      rw [Ideal.mul_le]
      intro r hr s hs
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs
      rw [mul_add]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ hs₁) (Ideal.mul_mem_mul hr hs₂)

    have hb : ∀ i, φ₁ (X i) - φ₂ (X i) ∈ mm (J ^ N ⊔ I) := fun i => hσ N (X i)
    have hbb : mm (J ^ N ⊔ I) * mm (J ^ N ⊔ I) = ⊥ := by
      rw [hmm_mul]; exact le_bot_iff.mp ((hmm_mono _ _ hincl1).trans (le_of_eq hkill))
    have hδ : ∀ i j, (φ₁ (X i) - φ₂ (X i)) * (φ₁ (X j) - φ₂ (X j)) = 0 := by
      intro i j
      have := Ideal.mul_mem_mul (hb i) (hb j)
      rwa [hbb, Ideal.mem_bot] at this

    have T := K2Aux.sub_eq_sum_pderiv φ₁ φ₂ hδ v
    have h1 : φ₁ v = 0 := by rw [hφ₁, Ideal.Quotient.eq_zero_iff_mem.mpr hv, map_zero]
    have h2 : ∑ i : Fin n, φ₂ (pderiv i v) * (φ₁ (X i) - φ₂ (X i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have := Ideal.mul_mem_mul (hmm J _ (hdv i)) (hb i)
      rw [hmm_mul] at this
      have := hmm_mono _ _ hincl2 this
      rwa [hkill, Ideal.mem_bot] at this
    have h3 : φ₂ v = 0 := by
      rw [h1, h2, zero_sub, neg_eq_zero] at T; exact T

    haveI := Module.FaithfullyFlat.faithfulSMul (A := MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (B := D N)
    have h4 : Ideal.Quotient.mk (J ^ N ⊔ J * I) v = 0 :=
      FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (by rw [map_zero, ← hφ₂]; exact h3)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h4

  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul J (I : Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))
  have hAR := hk (k + 1) (Nat.le_succ k)
  rw [Nat.add_sub_cancel_left, pow_one] at hAR
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (stepA (k + 1))
  have hbI : b ∈ I := Ideal.mul_le_right hb
  have haI : a ∈ I := by
    have : a = v - b := by rw [← hab]; ring
    rw [this]; exact I.sub_mem hv hbI
  have ha' : a ∈ J ^ (k + 1) • (⊤ : Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)) ⊓ I := by
    refine ⟨?_, haI⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact ha
  rw [hAR] at ha'
  have ha'' : a ∈ J * I := by
    have hle : J • (J ^ k • (⊤ : Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)) ⊓ I) ≤ J • I :=
      Submodule.smul_mono le_rfl inf_le_right
    have := hle ha'
    rwa [Ideal.smul_eq_mul] at this
  rw [← hab]
  exact Ideal.add_mem _ ha'' hb

end S_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift
end P2MW
export P2MW.S_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift (solution)
