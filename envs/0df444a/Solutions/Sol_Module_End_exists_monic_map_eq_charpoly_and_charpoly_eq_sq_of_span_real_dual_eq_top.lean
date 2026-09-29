-- Prove2me | solution 1 for Module.End.exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8fc568ca-55b9-5a77-97a1-d5fe101ab125

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top

set_option autoImplicit false

open Polynomial

namespace RatAnCharpoly

theorem map_charpoly_eq_mul_conj
    {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (T : S →ₗ[ℂ] S) (Λ : Submodule ℤ (Module.Dual ℂ S)) [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : LinearIndependent ℝ (fun i => ((b i : Λ) : Module.Dual ℂ S)))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : Λ) : Module.Dual ℂ S)) = ⊤)
    (τ : Module.End ℤ Λ)
    (hτ : ∀ x : Λ, ((τ x : Λ) : Module.Dual ℂ S) = (x : Module.Dual ℂ S) ∘ₗ T) :
    τ.charpoly.map (algebraMap ℤ ℂ) = T.charpoly * T.charpoly.map (starRingEnd ℂ) := by
  classical

  set A : Matrix (Fin n) (Fin n) ℤ := LinearMap.toMatrix b b τ with hA
  have hP : τ.charpoly = A.charpoly := (LinearMap.charpoly_toMatrix τ b).symm

  set g : Module.End ℂ (Module.Dual ℂ S) := Module.Dual.transpose (R := ℂ) T with hg
  have hgapp : ∀ φ : Module.Dual ℂ S, g φ = φ ∘ₗ T := fun φ => rfl
  set bR : Module.Basis (Fin n) ℝ (Module.Dual ℂ S) := Module.Basis.mk hli (by rw [hsp]) with hbR
  have hbR_apply : ∀ i, bR i = ((b i : Λ) : Module.Dual ℂ S) := fun i => Module.Basis.mk_apply hli _ i
  set gR : Module.End ℝ (Module.Dual ℂ S) := g.restrictScalars ℝ with hgR
  have hAR : LinearMap.toMatrix bR bR gR = A.map (Int.castRingHom ℝ) := by
    ext i j
    have h1 : (τ (b j) : Λ) = ∑ i, A i j • b i := by
      conv_lhs => rw [← b.sum_repr (τ (b j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA, LinearMap.toMatrix_apply]
    have h2 : gR (bR j) = ∑ i, ((A i j : ℤ) : ℝ) • bR i := by
      rw [hgR, LinearMap.restrictScalars_apply, hbR_apply j, hgapp, ← hτ, h1, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, hbR_apply i, Int.cast_smul_eq_zsmul]
    rw [LinearMap.toMatrix_apply, h2, bR.repr_sum_self, Matrix.map_apply, eq_intCast]

  set m : ℕ := Module.finrank ℂ S with hm
  set bC : Module.Basis (Fin m) ℂ S := Module.finBasis ℂ S with hbC
  set B : Matrix (Fin m) (Fin m) ℂ := LinearMap.toMatrix bC bC T with hB
  have hQ : T.charpoly = B.charpoly := (LinearMap.charpoly_toMatrix T bC).symm
  haveI : Finite (Fin m) := inferInstance
  have hgC : LinearMap.toMatrix bC.dualBasis bC.dualBasis g = B.transpose := by
    rw [hg, LinearMap.toMatrix_transpose]

  have heval : ∀ x : ℝ, ((A.charpoly.map (Int.castRingHom ℂ)).eval (x : ℂ)) =
      (B.charpoly * B.charpoly.map (starRingEnd ℂ)).eval (x : ℂ) := by
    intro x
    set hC : Module.End ℂ (Module.Dual ℂ S) := (x : ℂ) • LinearMap.id - g with hhC
    have hres : hC.restrictScalars ℝ = x • LinearMap.id - gR := by
      apply LinearMap.ext
      intro v
      rw [LinearMap.restrictScalars_apply, hhC, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, Complex.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hgR, LinearMap.restrictScalars_apply]
    have hdetR : LinearMap.det (hC.restrictScalars ℝ) =
        (Matrix.scalar (Fin n) x - A.map (Int.castRingHom ℝ)).det := by
      rw [← LinearMap.det_toMatrix bR, hres, map_sub, ← Matrix.toLin_scalar bR,
        LinearMap.toMatrix_toLin, hAR]
    have hdetC : LinearMap.det hC = (Matrix.scalar (Fin m) (x : ℂ) - B.transpose).det := by
      rw [← LinearMap.det_toMatrix bC.dualBasis, hhC, map_sub, ← Matrix.toLin_scalar bC.dualBasis,
        LinearMap.toMatrix_toLin, hgC]
    have hnorm : ((LinearMap.det (hC.restrictScalars ℝ) : ℝ) : ℂ) =
        LinearMap.det hC * starRingEnd ℂ (LinearMap.det hC) := by
      rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.mul_conj]

    have hL : (A.charpoly.map (Int.castRingHom ℂ)).eval (x : ℂ) =
        (((A.map (Int.castRingHom ℝ)).charpoly.eval x : ℝ) : ℂ) := by
      rw [Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval_map]
      change _ = Complex.ofRealHom (Polynomial.eval₂ (Int.castRingHom ℝ) x A.charpoly)
      rw [Polynomial.hom_eval₂, Complex.ofRealHom_eq_coe]
      congr 1
    have hconj : (B.charpoly.map (starRingEnd ℂ)).eval (x : ℂ) = starRingEnd ℂ (B.charpoly.eval (x : ℂ)) := by
      conv_lhs => rw [← Complex.conj_ofReal x]
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [hL, Matrix.eval_charpoly, ← hdetR, hnorm, hdetC, ← Matrix.eval_charpoly,
      Matrix.charpoly_transpose, Polynomial.eval_mul, hconj]

  have hpoly : A.charpoly.map (Int.castRingHom ℂ) = B.charpoly * B.charpoly.map (starRingEnd ℂ) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨x, rfl⟩
    exact heval x
  rw [hP, hQ, ← hpoly]
  rfl

theorem exists_map_rat_eq_of_sq_eq (n : ℕ) : ∀ (Rq : ℚ[X]), Rq.Monic → Rq.natDegree ≤ n →
    ∀ Q : ℂ[X], Q.Monic → Q ^ 2 = Rq.map (algebraMap ℚ ℂ) →
      ∃ Qq : ℚ[X], Qq.Monic ∧ Qq.map (algebraMap ℚ ℂ) = Q := by
  induction n with
  | zero =>
    intro Rq hRq hdeg Q hQ h
    have hR1 : Rq = 1 := by
      rw [← hRq.natDegree_eq_zero]; omega
    refine ⟨1, monic_one, ?_⟩
    rw [Polynomial.map_one]
    have hQdeg : Q.natDegree = 0 := by
      have := congrArg natDegree h
      rw [hQ.natDegree_pow, hR1, Polynomial.map_one, natDegree_one] at this
      omega
    exact ((hQ.natDegree_eq_zero).mp hQdeg).symm
  | succ n ih =>
    intro Rq hRq hdeg Q hQ h
    by_cases hd : Rq.natDegree ≤ n
    · exact ih Rq hRq hd Q hQ h
    have hpos : 0 < Rq.natDegree := by omega

    obtain ⟨g, hg, hgR⟩ := Polynomial.exists_irreducible_of_natDegree_pos hpos
    have hg0 : g ≠ 0 := hg.ne_zero
    set P : ℚ[X] := g * C (g.leadingCoeff)⁻¹ with hPdef
    have hPmonic : P.Monic := Polynomial.monic_mul_leadingCoeff_inv hg0
    have hPirr : Irreducible P := by
      refine (associated_mul_unit_right g (C (g.leadingCoeff)⁻¹) ?_).irreducible hg
      exact Polynomial.isUnit_C.mpr (IsUnit.inv (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hg0)))
    have hPR : P ∣ Rq := by
      refine (dvd_trans ?_ hgR)
      refine ⟨C g.leadingCoeff, ?_⟩
      rw [hPdef, mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hg0), C_1, mul_one]

    set ι := algebraMap ℚ ℂ with hι
    have hιinj : Function.Injective ι := (algebraMap ℚ ℂ).injective
    have hPsq : Squarefree (P.map ι) := (hPirr.separable.map (f := ι)).squarefree
    have hPQ2 : P.map ι ∣ Q ^ 2 := by
      rw [h]; exact Polynomial.map_dvd ι hPR
    have hPQ : P.map ι ∣ Q := (hPsq.dvd_pow_iff_dvd two_ne_zero).mp hPQ2
    obtain ⟨Q₁, hQ₁e⟩ := hPQ
    have hPmap : (P.map ι).Monic := hPmonic.map ι
    have hPmap0 : P.map ι ≠ 0 := hPmap.ne_zero
    have hQ₁ : Q₁.Monic := Monic.of_mul_monic_left hPmap (hQ₁e ▸ hQ)

    obtain ⟨R₁, hR₁⟩ := hPR
    have hR₁m : R₁.Monic := Monic.of_mul_monic_left hPmonic (hR₁ ▸ hRq)
    have hkey : P.map ι * Q₁ ^ 2 = R₁.map ι := by
      have h1 : (P.map ι) * (P.map ι * Q₁ ^ 2) = (P.map ι) * R₁.map ι := by
        rw [← Polynomial.map_mul, ← hR₁, ← h, hQ₁e]; ring
      exact mul_left_cancel₀ hPmap0 h1
    have hPR₁ : P ∣ R₁ := by
      rw [← Polynomial.map_dvd_map ι hιinj hPmonic, ← hkey]
      exact dvd_mul_right _ _
    obtain ⟨R₂, hR₂⟩ := hPR₁
    have hR₂m : R₂.Monic := Monic.of_mul_monic_left hPmonic (hR₂ ▸ hR₁m)
    have hQ₁sq : Q₁ ^ 2 = R₂.map ι := by
      have h1 : P.map ι * Q₁ ^ 2 = P.map ι * R₂.map ι := by
        rw [hkey, hR₂, Polynomial.map_mul]
      exact mul_left_cancel₀ hPmap0 h1
    have hR₂deg : R₂.natDegree ≤ n := by
      have h1 : Rq.natDegree = P.natDegree + (P.natDegree + R₂.natDegree) := by
        rw [hR₁, hPmonic.natDegree_mul hR₁m, hR₂, hPmonic.natDegree_mul hR₂m]
      have h2 : 0 < P.natDegree := hPirr.natDegree_pos
      omega
    obtain ⟨Qq₁, hQq₁m, hQq₁⟩ := ih R₂ hR₂m hR₂deg Q₁ hQ₁ hQ₁sq
    refine ⟨P * Qq₁, hPmonic.mul hQq₁m, ?_⟩
    rw [Polynomial.map_mul, hQq₁, ← hQ₁e]

theorem exists_map_int_eq_of_sq_eq (R : ℤ[X]) (hR : R.Monic) (Q : ℂ[X]) (hQ : Q.Monic)
    (h : Q ^ 2 = R.map (algebraMap ℤ ℂ)) :
    ∃ Q₀ : ℤ[X], Q₀.Monic ∧ Q₀.map (algebraMap ℤ ℂ) = Q := by
  have hcomp : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℂ := RingHom.ext_int _ _
  set Rq : ℚ[X] := R.map (algebraMap ℤ ℚ) with hRq
  have hRqm : Rq.Monic := hR.map _
  have h' : Q ^ 2 = Rq.map (algebraMap ℚ ℂ) := by
    rw [h, hRq, Polynomial.map_map, hcomp]
  obtain ⟨Qq, hQqm, hQq⟩ := exists_map_rat_eq_of_sq_eq Rq.natDegree Rq hRqm le_rfl Q hQ h'

  have hsq : Qq ^ 2 = Rq := by
    apply Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    rw [Polynomial.map_pow, hQq, h']
  have hdvd : Qq ∣ R.map (algebraMap ℤ ℚ) := ⟨Qq, by rw [← hRq, ← hsq, sq]⟩
  obtain ⟨Q₀, hQ₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hR hdvd
  rw [hQqm.leadingCoeff, C_1, mul_one] at hQ₀
  refine ⟨Q₀, ?_, ?_⟩
  · exact Polynomial.monic_of_injective (algebraMap ℤ ℚ).injective_int (hQ₀ ▸ hQqm)
  · rw [← hcomp, ← Polynomial.map_map, hQ₀, hQq]

end RatAnCharpoly

open RatAnCharpoly in
theorem solution
    {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (T : S →ₗ[ℂ] S) (hreal : T.charpoly.map (starRingEnd ℂ) = T.charpoly)
    (Λ : Submodule ℤ (Module.Dual ℂ S)) [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : LinearIndependent ℝ (fun i => ((b i : Λ) : Module.Dual ℂ S)))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : Λ) : Module.Dual ℂ S)) = ⊤)
    (τ : Module.End ℤ Λ)
    (hτ : ∀ x : Λ, ((τ x : Λ) : Module.Dual ℂ S) = (x : Module.Dual ℂ S) ∘ₗ T) :
    ∃ Q : Polynomial ℤ, Q.Monic ∧ Q.map (algebraMap ℤ ℂ) = T.charpoly ∧ τ.charpoly = Q ^ 2 := by
  have h1 : τ.charpoly.map (algebraMap ℤ ℂ) = T.charpoly ^ 2 := by
    rw [map_charpoly_eq_mul_conj T Λ b hli hsp τ hτ, hreal, sq]
  obtain ⟨Q, hQm, hQ⟩ :=
    exists_map_int_eq_of_sq_eq τ.charpoly (LinearMap.charpoly_monic τ) T.charpoly
      (LinearMap.charpoly_monic T) h1.symm
  refine ⟨Q, hQm, hQ, ?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℂ) (algebraMap ℤ ℂ).injective_int
  rw [h1, Polynomial.map_pow, hQ]

end S_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
end P2MW
export P2MW.S_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top (solution)
