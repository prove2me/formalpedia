-- Prove2me | solution 1 for HGASUndecidable.Main.paddingCode_spec
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:55.289809+00:00
-- url     : https://prove2.me/submissions/fd57c516-829a-41b0-b5b8-4ff192247271

import Definitions.Def_HGASUndecidable_Main_PaddingCodes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

private lemma canonical_codePolys {n d : ℕ} (p : Fin n → QPoly n) :
    codePolys (n,d,(List.ofFn (fun i : Fin n =>
      (polynomialTerms (p i)).map (fun t => (i.val,t)))).flatten) = p := by
  funext i
  simp [codePolys, polynomialTerms, List.sum_ofFn]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp only [ite_eq_right_iff]
    intro hbv
    exact (hbi (Fin.ext hbv)).elim
  · simp

private lemma paddingPolys_isHomogeneous {m n : ℕ} (h : m ≤ n) (j : ℕ)
    (H : Fin m → QPoly m) (hH : ∀ i, (H i).IsHomogeneous 3) (i : Fin n) :
    (paddingPolys h j H i).IsHomogeneous (3+2*j) := by
  have hs : (∑ k : Fin n, (MvPolynomial.X k : QPoly n) ^ 2).IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro k hk
    simpa using (MvPolynomial.isHomogeneous_X ℚ k).pow 2
  have hsj := hs.pow j
  rw [paddingPolys]
  split_ifs with hi
  · simpa [Nat.add_comm] using hsj.mul ((hH ⟨i.val, hi⟩).rename_isHomogeneous)
  · simpa [Nat.add_comm] using hsj.mul (((MvPolynomial.isHomogeneous_X ℚ i).pow 3).neg)

private lemma paddingCanonical_valid {m n : ℕ} (h : m ≤ n) (j : ℕ)
    (terms : List (ℕ × List ℕ × ℚ))
    (hv : ValidCode (m, 3, terms)) :
    ValidCode (n, 3+2*j, (List.ofFn (fun i : Fin n =>
      (polynomialTerms (paddingPolys h j (codePolys (m,3,terms)) i)).map
        (fun t => (i.val,t)))).flatten) := by
  have hcan := canonical_codePolys (d := 3+2*j)
    (paddingPolys h j (codePolys (m,3,terms)))
  constructor
  · exact le_trans hv.1 h
  constructor
  · show 1 ≤ 3+2*j
    omega
  constructor
  · intro t ht
    simp only [List.mem_flatten, List.mem_ofFn] at ht
    obtain ⟨l, ⟨i, rfl⟩, ht⟩ := ht
    simp only [List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    simp only [polynomialTerms, List.mem_map, Finset.mem_toList] at hu
    obtain ⟨mon, hm, rfl⟩ := hu
    constructor
    · exact i.isLt
    · simp
  · intro i mon hm
    rw [hcan] at hm
    have hhom : (paddingPolys h j (codePolys (m,3,terms)) i).IsHomogeneous (3+2*j) := by
      apply paddingPolys_isHomogeneous
      intro a mon hmon
      simpa [Finsupp.weight_apply] using hv.2.2.2 a mon (MvPolynomial.mem_support_iff.mpr hmon)
    simpa [Finsupp.weight_apply] using hhom (MvPolynomial.mem_support_iff.mp hm)

private lemma paddingPolys_eval {m n : ℕ} (h : m ≤ n) (j : ℕ) (H : Fin m → QPoly m) :
    evalQField (paddingPolys h j H) = padding h j (evalQField H) := by
  funext x
  ext i
  by_cases hi : i.val < m <;>
    simp [hi, evalQField, paddingPolys, padding, MvPolynomial.eval₂_rename]
  left
  rfl

private theorem paddingCode_spec_aux {m n : ℕ} (h : m ≤ n) (j : ℕ)
    (terms : List (ℕ × List ℕ × ℚ))
    (hv : ValidCode (m, 3, terms)) :
    ∃ outTerms : List (ℕ × List ℕ × ℚ),
      decodeField (paddingCode h j terms) = some (n, 3+2*j, outTerms) ∧
      ValidCode (n, 3+2*j, outTerms) ∧
      codeField (n, 3+2*j, outTerms) = padding h j (codeField (m, 3, terms)) := by
  let outTerms := (List.ofFn (fun i : Fin n =>
    (polynomialTerms (paddingPolys h j (codePolys (m,3,terms)) i)).map
      (fun t => (i.val,t)))).flatten
  refine ⟨outTerms, ?_, ?_, ?_⟩
  · simp [paddingCode, encodePolys, decodeField, outTerms]
  · exact paddingCanonical_valid h j terms hv
  · change evalQField (codePolys (n, 3+2*j, outTerms)) =
      padding h j (evalQField (codePolys (m, 3, terms)))
    rw [show codePolys (n, 3+2*j, outTerms) =
      paddingPolys h j (codePolys (m,3,terms)) from canonical_codePolys _]
    exact paddingPolys_eval h j _

end HGASUndecidable.Main

open HGASUndecidable.Main

theorem solution {m n : ℕ} (h : m ≤ n) (j : ℕ)
    (terms : List (ℕ × List ℕ × ℚ))
    (hv : ValidCode (m, 3, terms)) :
    ∃ outTerms : List (ℕ × List ℕ × ℚ),
      decodeField (paddingCode h j terms) = some (n, 3+2*j, outTerms) ∧
      ValidCode (n, 3+2*j, outTerms) ∧
      codeField (n, 3+2*j, outTerms) = padding h j (codeField (m, 3, terms)) := by
  exact paddingCode_spec_aux h j terms hv
