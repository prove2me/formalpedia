-- Prove2me | solution 1 for MazurTransfer.PolynomialDistinctDegree.linearIndependent_of_injective_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:42:19.341015+00:00
-- url     : https://prove2.me/submissions/d1a70a71-5447-4c5b-ab05-01aa876058d3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: linear independence of nonzero polynomials of distinct degrees.
Named downstream consumer: actual single-section finite-algebra basis.
-/
import Mathlib

noncomputable section

open Polynomial
variable {R ι : Type*} [CommRing R] [IsDomain R]

theorem solution (v : ι → Polynomial R)
    (hn : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => (v i).natDegree)) :
    LinearIndependent R v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hs i hi
  by_contra hgi
  let k : Finset ι := s.filter (fun j => g j ≠ 0)
  have hk : k.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi,hgi⟩⟩
  obtain ⟨j,hj,hmax⟩ := k.exists_max_image (fun j => (v j).natDegree) hk
  obtain ⟨hjs,hgj⟩ := Finset.mem_filter.mp hj
  have hcoeff : (∑ l ∈ s, g l • v l).coeff (v j).natDegree =
      g j * (v j).leadingCoeff := by
    rw [finsetSum_coeff]
    apply Finset.sum_eq_single j
    · intro l hls hlj
      by_cases hgl : g l = 0
      · simp [hgl]
      · have hlk : l ∈ k := Finset.mem_filter.mpr ⟨hls,hgl⟩
        have hlt : (v l).natDegree < (v j).natDegree :=
          lt_of_le_of_ne (hmax l hlk) (fun he => hlj (hd he))
        rw [coeff_smul, coeff_eq_zero_of_natDegree_lt hlt, smul_zero]
    · exact fun h => (h hjs).elim
  have hz : g j * (v j).leadingCoeff = 0 := by rw [← hcoeff, hs, coeff_zero]
  exact (mul_ne_zero hgj (leadingCoeff_ne_zero.mpr (hn j))) hz


#print axioms solution
