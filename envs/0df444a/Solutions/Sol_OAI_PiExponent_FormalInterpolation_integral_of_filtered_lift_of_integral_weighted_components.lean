-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.integral_of_filtered_lift_of_integral_weighted_components
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:28:31.537454+00:00
-- url     : https://prove2.me/submissions/1180cbff-e334-4e78-9c9f-401aa6c5a669

import Mathlib

open MvPolynomial

namespace PiD1

noncomputable def g2 : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1

noncomputable def φ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval (fun i : Fin 2 => if i = 0 then Polynomial.X else -Polynomial.X ^ 2)

lemma φ_g : φ g2 = 0 := by
  simp [φ, g2]

lemma not_int : ¬ IsIntegral (Algebra.adjoin ℂ (Set.range fun _ : Fin 1 => g2))
    (X 0 : MvPolynomial (Fin 2) ℂ) := by
  set A := Algebra.adjoin ℂ (Set.range fun _ : Fin 1 => g2)
  rintro ⟨p, hmon, hp⟩
  have hbot : ∀ a : A, φ a ∈ (⊥ : Subalgebra ℂ (Polynomial ℂ)) := by
    intro a
    have : A.map φ ≤ ⊥ := by
      rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [φ_g]; exact Subalgebra.zero_mem _
    exact this ⟨a, a.2, rfl⟩
  let ψ : A →+* ℂ := (Polynomial.constantCoeff).comp (φ.toRingHom.comp A.val.toRingHom)
  have hcomp : (φ : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ).comp
      (algebraMap A (MvPolynomial (Fin 2) ℂ)) = Polynomial.C.comp ψ := by
    refine RingHom.ext fun a => ?_
    obtain ⟨r, hr⟩ := Algebra.mem_bot.1 (hbot a)
    show φ (a : MvPolynomial (Fin 2) ℂ) = Polynomial.C (Polynomial.constantCoeff (φ a))
    rw [← hr]; simp
  have h0 := congrArg φ hp
  rw [map_zero, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcomp] at h0
  have hX : (φ : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ) (X 0) = Polynomial.X := by simp [φ]
  rw [hX, ← Polynomial.eval₂_map, Polynomial.eval₂_C_X] at h0
  exact (hmon.map ψ).ne_zero h0

lemma hbound : ∀ j : Fin 1, ∀ a ∈ ((fun _ : Fin 1 => g2) j).support,
    ∑ k, (((fun _ : Fin 2 => (1 : ℚ)) k : ℚ) : Real) * (a k : Real) ≤ ((2 : ℕ) : Real) := by
  classical
  intro j a ha
  have := MvPolynomial.support_add ha
  rw [Finset.mem_union, support_X_pow, support_X, Finset.mem_singleton, Finset.mem_singleton] at this
  rcases this with rfl | rfl <;> simp [Fin.sum_univ_two]

lemma comp_g2 : MvPolynomial.weightedHomogeneousComponent (fun _ : Fin 2 => (1 : ℚ)) ((2 : ℕ) : ℚ) g2 =
    X 0 ^ 2 := by
  have h1 : IsWeightedHomogeneous (fun _ : Fin 2 => (1 : ℚ)) (X 0 ^ 2 : MvPolynomial (Fin 2) ℂ) 2 := by
    have := (isWeightedHomogeneous_X ℂ (fun _ : Fin 2 => (1 : ℚ)) 0).pow 2
    simpa using this
  have h2 : IsWeightedHomogeneous (fun _ : Fin 2 => (1 : ℚ)) (X 1 : MvPolynomial (Fin 2) ℂ) 1 :=
    isWeightedHomogeneous_X ℂ _ 1
  rw [g2, map_add, Nat.cast_ofNat, h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_ne _ (by norm_num),
    add_zero]

lemma htop : IsIntegral
      (Algebra.adjoin Complex
        (Set.range (fun j : Fin 1 =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => ((fun _ : Fin 2 => (1 : ℚ)) k : ℚ)) ((2 : ℕ) : ℚ) ((fun _ : Fin 1 => g2) j))) :
        Subalgebra Complex (MvPolynomial (Fin 2) Complex))
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) Complex) := by
  refine IsIntegral.of_pow two_pos ?_
  have hmem : (X 0 ^ 2 : MvPolynomial (Fin 2) ℂ) ∈ Algebra.adjoin Complex
      (Set.range (fun j : Fin 1 =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => ((fun _ : Fin 2 => (1 : ℚ)) k : ℚ)) ((2 : ℕ) : ℚ) ((fun _ : Fin 1 => g2) j))) :=
    Algebra.subset_adjoin ⟨0, comp_g2⟩
  have : (X 0 ^ 2 : MvPolynomial (Fin 2) ℂ) = algebraMap _ _ (⟨_, hmem⟩ : Algebra.adjoin Complex
      (Set.range (fun j : Fin 1 =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => ((fun _ : Fin 2 => (1 : ℚ)) k : ℚ)) ((2 : ℕ) : ℚ) ((fun _ : Fin 1 => g2) j)))) := rfl
  rw [this]; exact isIntegral_algebraMap

end PiD1

theorem solution : ¬ (∀ {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hbound : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (i : Fin d)
    (htop : IsIntegral
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j))) :
        Subalgebra Complex (MvPolynomial (Fin d) Complex))
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex)),
    IsIntegral
      (Algebra.adjoin Complex (Set.range g) :
        Subalgebra Complex (MvPolynomial (Fin d) Complex))
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) := by
  intro h
  exact PiD1.not_int (h (d := 2) (fun _ => 1) (fun _ => by norm_num) 2 (by norm_num) 1 (fun _ => PiD1.g2)
    PiD1.hbound 0 PiD1.htop)
