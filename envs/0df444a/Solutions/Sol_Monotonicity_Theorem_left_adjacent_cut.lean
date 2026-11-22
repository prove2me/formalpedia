-- Prove2me | solution 1 for Monotonicity_Theorem.left_adjacent_cut
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:37:56.986536+00:00
-- url     : https://prove2.me/submissions/c6dd9333-9c78-4260-a76b-04e612fc4c27

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_exception_list
import Theorems.Thm_Monotonicity_Theorem_exists_greatest_of_list

open Monotonicity_Theorem

namespace Monotonicity_Theorem

-- Left-endpoint side of piece transfer.
theorem alpha_side {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {α : Endpoint R} {M : R} {t0 s0 : R}
    (hαt : Endpoint.lt D α (Endpoint.finite t0))
    (hleV : ∀ v : R, α = Endpoint.finite v → (D.lt v M ∨ v = M))
    (hsM : D.lt M s0) :
    Endpoint.lt D α (Endpoint.finite s0) := by
  cases α with
  | negInf => exact trivial
  | finite v =>
    cases hleV v rfl with
    | inl h => exact D.trans h hsM
    | inr heq =>
      rw [heq]
      exact hsM
  | posInf => exact False.elim hαt

end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {A B : Set (Power R 1)}
    (hA : M.S 1 A) (hB : M.S 1 B)
    {c1 p : R} (hlt : D.lt c1 p)
    (hcov : forall x : Power R 1,
      openInterval D (Endpoint.finite c1) (Endpoint.finite p) x -> A x \/ B x) :
    exists c1' : R, D.lt c1' p /\ (D.lt c1 c1' \/ c1 = c1') /\
      ((forall x : Power R 1,
        openInterval D (Endpoint.finite c1') (Endpoint.finite p) x -> A x) \/
       (forall x : Power R 1,
        openInterval D (Endpoint.finite c1') (Endpoint.finite p) x -> B x)) := by
  classical
  obtain hFUIA := (M.ominimal A).mp hA
  obtain hFUIB := (M.ominimal B).mp hB
  obtain ⟨EA, hEA⟩ := Monotonicity_Theorem.exception_list D hFUIA
  obtain ⟨EB, hEB⟩ := Monotonicity_Theorem.exception_list D hFUIB
  set E : List R := (EA ++ EB).filter (fun c => decide (D.lt c p)) with hEdef
  have hne : E ++ [c1] ≠ [] := by
    intro h
    have hm : c1 ∈ E ++ [c1] :=
      List.mem_append.mpr (Or.inr (List.Mem.head _))
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨M, hMem, hMax⟩ :=
    Monotonicity_Theorem.exists_greatest_of_list D (E ++ [c1]) hne
  have hle : ∀ r : R, r ∈ EA ++ EB → D.lt r p → (D.lt r M ∨ r = M) := by
    intro r hr hlt
    exact hMax _ (List.mem_append.mpr (Or.inl (List.mem_filter.mpr
      ⟨hr, by rw [decide_eq_true_eq]; exact hlt⟩)))
  have hMp : D.lt M p := by
    cases List.mem_append.mp hMem with
    | inl hE =>
      rw [List.mem_filter] at hE
      exact of_decide_eq_true hE.right
    | inr hS =>
      cases hS with
      | head => exact hlt
      | tail _ h => cases h
  have hMc1 : D.lt c1 M ∨ c1 = M :=
    hMax _ (List.mem_append.mpr (Or.inr (List.Mem.head _)))
  have hsub : ∀ x : Power R 1,
      openInterval D (Endpoint.finite M) (Endpoint.finite p) x →
      openInterval D (Endpoint.finite c1) (Endpoint.finite p) x := by
    intro x hx
    have hx1 : D.lt M (Power.coord1 x) := hx.left
    have hx2 : D.lt (Power.coord1 x) p := hx.right
    show Endpoint.lt D (Endpoint.finite c1) (Endpoint.finite (x 0)) ∧
      Endpoint.lt D (Endpoint.finite (x 0)) (Endpoint.finite p)
    constructor
    · cases hMc1 with
      | inl h => exact D.trans h hx1
      | inr heq =>
        rw [heq]
        exact hx1
    · exact hx2
  by_cases hAex : ∃ x : Power R 1,
      openInterval D (Endpoint.finite M) (Endpoint.finite p) x ∧ ¬ A x
  · by_cases hBex : ∃ y : Power R 1,
        openInterval D (Endpoint.finite M) (Endpoint.finite p) y ∧ ¬ B y
    · obtain ⟨x, hxJ, hxNA⟩ := hAex
      obtain ⟨y, hyJ, hyNB⟩ := hBex
      have hxB : B x := by
        cases hcov x (hsub x hxJ) with
        | inl h => exact absurd h hxNA
        | inr h => exact h
      have hyA : A y := by
        cases hcov y (hsub y hyJ) with
        | inl h => exact h
        | inr h => exact absurd h hyNB
      have hxMx : D.lt M (Power.coord1 x) := hxJ.left
      have hxp : D.lt (Power.coord1 x) p := hxJ.right
      have hyM : D.lt M (Power.coord1 y) := hyJ.left
      have hyp : D.lt (Power.coord1 y) p := hyJ.right
      -- x's B-piece analysis toward y ∈ B
      have hyB : B y := by
        obtain hBx := hEB x hxB
        cases hBx with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inr hmem)) hxp
          cases hleM with
          | inl h => exact False.elim (D.irrefl M (D.trans hxMx h))
          | inr heq =>
            rw [heq] at hxMx
            exact False.elim (D.irrefl M hxMx)
        | inr hpiece =>
          obtain ⟨α, β, hxβ, hsubB, hLcond, hRcond⟩ := hpiece
          have hLE : ∀ v : R, α = Endpoint.finite v → (D.lt v M ∨ v = M) := by
            intro v hv
            have hvt0 : D.lt v (Power.coord1 x) := by
              have hleft : Endpoint.lt D α (Endpoint.finite (x 0)) := hxβ.left
              rw [hv] at hleft
              exact hleft
            have hvp : D.lt v p := D.trans hvt0 hxp
            exact hle _ (List.mem_append.mpr (Or.inr (hLcond v hv))) hvp
          cases β with
          | negInf =>
            have hF : False := hxβ.right
            exact False.elim hF
          | posInf =>
            have hmem : openInterval D α Endpoint.posInf y := by
              have hα : Endpoint.lt D α (Endpoint.finite (y 0)) :=
                Monotonicity_Theorem.alpha_side D hxβ.left hLE hyM
              exact ⟨hα, trivial⟩
            exact hsubB _ hmem
          | finite v =>
            rcases D.trichotomy v p with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hlt, _, _⟩
            · have hvE : v ∈ EB := hRcond v rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inr hvE)) hlt
              have hxv : D.lt (Power.coord1 x) v := hxβ.right
              cases hleM with
              | inl h =>
                exact False.elim (D.irrefl M (D.trans (D.trans hxMx hxv) h))
              | inr heq2 =>
                rw [heq2] at hxv
                exact False.elim (D.irrefl M (D.trans hxMx hxv))
            · have hmem : openInterval D α (Endpoint.finite v) y := by
                have hα : Endpoint.lt D α (Endpoint.finite (y 0)) :=
                  Monotonicity_Theorem.alpha_side D hxβ.left hLE hyM
                have hβ : Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite v) := by
                  rw [heq]
                  exact hyp
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
            · have hmem : openInterval D α (Endpoint.finite v) y := by
                have hα : Endpoint.lt D α (Endpoint.finite (y 0)) :=
                  Monotonicity_Theorem.alpha_side D hxβ.left hLE hyM
                have hβ : Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite v) :=
                  D.trans hyp hlt
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
      -- y's A-piece analysis toward False
      have hFalse : False := by
        obtain hAy := hEA y hyA
        cases hAy with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inl hmem)) hyp
          cases hleM with
          | inl h => exact D.irrefl M (D.trans hyM h)
          | inr heq =>
            rw [heq] at hyM
            exact D.irrefl M hyM
        | inr hpiece =>
          obtain ⟨α, β, hyβ, hsubA, hLcond, hRcond⟩ := hpiece
          have hLE : ∀ v : R, α = Endpoint.finite v → (D.lt v M ∨ v = M) := by
            intro v hv
            have hvt0 : D.lt v (Power.coord1 y) := by
              have hleft : Endpoint.lt D α (Endpoint.finite (y 0)) := hyβ.left
              rw [hv] at hleft
              exact hleft
            have hvp : D.lt v p := D.trans hvt0 hyp
            exact hle _ (List.mem_append.mpr (Or.inl (hLcond v hv))) hvp
          cases β with
          | negInf =>
            have hF : False := hyβ.right
            exact hF
          | posInf =>
            have hmem : openInterval D α Endpoint.posInf x := by
              have hα : Endpoint.lt D α (Endpoint.finite (x 0)) :=
                Monotonicity_Theorem.alpha_side D hyβ.left hLE hxMx
              exact ⟨hα, trivial⟩
            exact absurd (hsubA _ hmem) hxNA
          | finite v =>
            rcases D.trichotomy v p with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hlt, _, _⟩
            · have hvE : v ∈ EA := hRcond v rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inl hvE)) hlt
              have hyv : D.lt (Power.coord1 y) v := hyβ.right
              cases hleM with
              | inl h =>
                exact D.irrefl M (D.trans (D.trans hyM hyv) h)
              | inr heq2 =>
                rw [heq2] at hyv
                exact D.irrefl M (D.trans hyM hyv)
            · have hmem : openInterval D α (Endpoint.finite v) x := by
                have hα : Endpoint.lt D α (Endpoint.finite (x 0)) :=
                  Monotonicity_Theorem.alpha_side D hyβ.left hLE hxMx
                have hβ : Endpoint.lt D (Endpoint.finite (x 0)) (Endpoint.finite v) := by
                  rw [heq]
                  exact hxp
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
            · have hmem : openInterval D α (Endpoint.finite v) x := by
                have hα : Endpoint.lt D α (Endpoint.finite (x 0)) :=
                  Monotonicity_Theorem.alpha_side D hyβ.left hLE hxMx
                have hβ : Endpoint.lt D (Endpoint.finite (x 0)) (Endpoint.finite v) :=
                  D.trans hxp hlt
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
      exact False.elim hFalse
    · refine ⟨M, hMp, hMc1, Or.inr ?_⟩
      intro y hy
      by_contra hyNB
      exact hBex ⟨y, hy, hyNB⟩
  · refine ⟨M, hMp, hMc1, Or.inl ?_⟩
    intro x hx
    by_contra hxNA
    exact hAex ⟨x, hx, hxNA⟩
