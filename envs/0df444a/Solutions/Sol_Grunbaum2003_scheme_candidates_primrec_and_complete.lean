-- Prove2me | solution 1 for Grunbaum2003.scheme_candidates_primrec_and_complete
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:01:31.575201+00:00
-- url     : https://prove2.me/submissions/caed3b1b-e0f0-480c-890b-61b75b03864c

import Definitions.Def_Grunbaum2003_SchemeRealizes
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Computability.Partrec

set_option autoImplicit false

theorem bounded_scheme_has_candidate (k : ℕ) (S : List (List ℕ))
    (hBound : ∀ L ∈ S, ∀ n ∈ L, n < k) :
    ∃ T ∈ ((List.range k).sublists').sublists',
      ∀ J : Finset ℕ,
        (∃ L ∈ T, L.toFinset = J) ↔ (∃ L ∈ S, L.toFinset = J) := by
  classical
  let rows := (List.range k).sublists'
  let T := rows.filter (fun R => ∃ L ∈ S, L.toFinset = R.toFinset)
  refine ⟨T, List.mem_sublists'.mpr (List.filter_sublist), ?_⟩
  intro J
  constructor
  · rintro ⟨L, hL, rfl⟩
    simpa only [T, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hL).2
  · rintro ⟨L, hL, rfl⟩
    let R := (List.range k).filter (fun n => n ∈ L)
    have hR : R.toFinset = L.toFinset := by
      ext n
      simp only [List.mem_toFinset, R, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨And.right, fun hn => ⟨hBound L hL n hn, hn⟩⟩
    refine ⟨R, List.mem_filter.mpr ⟨?_, by simpa only [decide_eq_true_eq] using (show ∃ L₀ ∈ S, L₀.toFinset = R.toFinset from ⟨L, hL, hR.symm⟩)⟩, hR⟩
    exact List.mem_sublists'.mpr (List.filter_sublist)

theorem primrec_sublists' {α : Type} [Primcodable α] :
    Primrec (@List.sublists' α) := by
  have hFold : Primrec (fun l : List α =>
      l.foldr (fun a r => r ++ r.map (List.cons a)) [[]]) := by
    apply Primrec.list_foldr (h := fun (_ : List α) (p : α × List (List α)) => p.2 ++ p.2.map (List.cons p.1)) Primrec.id (Primrec.const [[]])
    change Primrec (fun p : List α × (α × List (List α)) =>
      p.2.2 ++ p.2.2.map (List.cons p.2.1))
    exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd))
  apply hFold.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.sublists'_cons, ih]

theorem primrec_scheme_candidates : Primrec (fun k : ℕ => ((List.range k).sublists').sublists') :=
  primrec_sublists'.comp (primrec_sublists'.comp Primrec.list_range)


namespace Grunbaum2003

theorem schemeRealizes_has_candidate {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (h : SchemeRealizes k S P) :
    ∃ T ∈ ((List.range k).sublists').sublists',
      ∀ Q : Set (Fin d → ℝ), SchemeRealizes k S Q → SchemeRealizes k T Q := by
  have hBound : ∀ L ∈ S, ∀ n ∈ L, n < k := by
    obtain ⟨hP, V, hV, hRange, hFaces⟩ := h
    intro L hL n hn
    obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
    have hn' : n ∈ (L.toFinset : Set ℕ) := List.mem_toFinset.mpr hn
    rw [hInc] at hn'
    obtain ⟨i, hi, _⟩ := hn'
    exact hi ▸ i.isLt
  obtain ⟨T, hT, hRows⟩ := bounded_scheme_has_candidate k S hBound
  refine ⟨T, hT, ?_⟩
  rintro Q ⟨hQ, V, hV, hRange, hFaces⟩
  exact ⟨hQ, V, hV, hRange, fun J => (hRows J).trans (hFaces J)⟩

end Grunbaum2003


theorem solution :
    Primrec (fun k : ℕ => ((List.range k).sublists').sublists') ∧
    ∀ {d k : ℕ} {S : List (List ℕ)} {P : Set (Fin d → ℝ)},
      Grunbaum2003.SchemeRealizes k S P →
      ∃ T ∈ ((List.range k).sublists').sublists',
        ∀ Q : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S Q → Grunbaum2003.SchemeRealizes k T Q := by
  exact ⟨primrec_scheme_candidates, fun h => Grunbaum2003.schemeRealizes_has_candidate h⟩
