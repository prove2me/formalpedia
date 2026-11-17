-- Prove2me | solution 1 for N25.Alg.charpoly_eq_cyclotomic_sq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:43.755197+00:00
-- url     : https://prove2.me/submissions/28752ef4-6ec8-49f0-adff-890a3481d7e8

import Mathlib

open Polynomial UniqueFactorizationMonoid

namespace N25.Alg

/-- An eight-dimensional rational representation annihilated by the fifth cyclotomic
polynomial has two copies of that polynomial as its characteristic polynomial. -/
theorem _root_.solution (A : Matrix (Fin 8) (Fin 8) ℚ)
    (hA : aeval A (cyclotomic 5 ℚ) = 0) :
    A.charpoly = (cyclotomic 5 ℚ) ^ 2 := by
  classical
  let L := AlgebraicClosure ℚ
  let ι : ℚ →+* L := algebraMap ℚ L
  let B := A.map ι
  have hB : aeval B ((cyclotomic 5 ℚ).map ι) = 0 := by
    have hn := Polynomial.map_aeval_eq_aeval_map
      (R := ℚ) (S := Matrix (Fin 8) (Fin 8) ℚ) (T := L)
      (U := Matrix (Fin 8) (Fin 8) L) (φ := ι)
      (ψ := ι.mapMatrix) (by
        ext q i j
        by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij, ι]) (cyclotomic 5 ℚ) A
    simpa [hA, B] using hn.symm
  have hF : ∀ f ∈ normalizedFactors A.charpoly, f = cyclotomic 5 ℚ := by
    intro f hf
    obtain ⟨hirr, hmonic, hdiv⟩ := (Polynomial.mem_normalizedFactors_iff
      (Matrix.charpoly_monic A).ne_zero).mp hf
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (f.map ι) (by
      rw [Polynomial.degree_map]
      exact ne_of_gt hirr.degree_pos)
    have hr : B.charpoly.IsRoot z := by
      rw [show B.charpoly = A.charpoly.map ι from Matrix.charpoly_map A ι]
      exact hz.dvd (Polynomial.map_dvd ι hdiv)
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly B.toLin' z).mpr
      (by simpa using hr)
    have hl : aeval B.toLin' ((cyclotomic 5 ℚ).map ι) = 0 := by
      have hn := Polynomial.aeval_algHom_apply
        (Matrix.toLinAlgEquiv' : Matrix (Fin 8) (Fin 8) L ≃ₐ[L] _).toAlgHom
        B ((cyclotomic 5 ℚ).map ι)
      have hlin : (Matrix.toLinAlgEquiv' : Matrix (Fin 8) (Fin 8) L ≃ₐ[L] _).toAlgHom B = B.toLin' := by
        ext v i
        rfl
      rw [hlin] at hn
      simpa only [hB, map_zero] using hn
    have hp : ((cyclotomic 5 ℚ).map ι).IsRoot z :=
      (Module.End.isRoot_of_hasEigenvalue he).dvd (minpoly.dvd L B.toLin' hl)
    have hfm : f = minpoly ℚ z := minpoly.eq_of_irreducible_of_monic hirr
      (by simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, ι] using hz) hmonic
    have hpm : cyclotomic 5 ℚ = minpoly ℚ z :=
      minpoly.eq_of_irreducible_of_monic (cyclotomic.irreducible_rat (by norm_num))
        (by simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, ι] using hp)
        (cyclotomic.monic 5 ℚ)
    exact hfm.trans hpm.symm
  have hprod : A.charpoly = (cyclotomic 5 ℚ) ^ (normalizedFactors A.charpoly).card := by
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors A.charpoly
    rw [(Matrix.charpoly_monic A).leadingCoeff, Polynomial.C_1, one_mul,
      Multiset.eq_replicate_card.mpr hF, Multiset.prod_replicate] at h
    exact h.symm
  have hdegree := congrArg Polynomial.natDegree hprod
  rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_pow,
    Polynomial.natDegree_cyclotomic] at hdegree
  have hn : (normalizedFactors A.charpoly).card = 2 := by
    norm_num [Nat.totient_prime (by norm_num : Nat.Prime 5)] at hdegree
    omega
  simpa [hn] using hprod

end N25.Alg
