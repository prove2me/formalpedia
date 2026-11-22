-- Prove2me | solution 1 for Monotonicity_Theorem.right_adjacent_cut
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:53:51.053636+00:00
-- url     : https://prove2.me/submissions/536e8558-4c5e-45ba-8297-070451837df8

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_exception_list
import Theorems.Thm_Monotonicity_Theorem_exists_least_of_list

open Monotonicity_Theorem

namespace Monotonicity_Theorem

-- Right-endpoint side of piece transfer.
theorem beta_side {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {β : Endpoint R} {m : R} {t0 s0 : R}
    (hβt : Endpoint.lt D (Endpoint.finite t0) β)
    (hleV : ∀ v : R, β = Endpoint.finite v → (D.lt m v ∨ m = v))
    (hsm : D.lt s0 m) :
    Endpoint.lt D (Endpoint.finite s0) β := by
  cases β with
  | negInf => exact False.elim hβt
  | finite v =>
    cases hleV v rfl with
    | inl h => exact D.trans hsm h
    | inr heq =>
      rw [← heq]
      exact hsm
  | posInf => exact trivial

end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {A B : Set (Power R 1)}
    (hA : M.S 1 A) (hB : M.S 1 B)
    {p c2 : R} (hlt : D.lt p c2)
    (hcov : forall x : Power R 1,
      openInterval D (Endpoint.finite p) (Endpoint.finite c2) x -> A x \/ B x) :
    exists m : R, D.lt p m /\ (D.lt m c2 \/ m = c2) /\
      ((forall x : Power R 1,
        openInterval D (Endpoint.finite p) (Endpoint.finite m) x -> A x) \/
       (forall x : Power R 1,
        openInterval D (Endpoint.finite p) (Endpoint.finite m) x -> B x)) := by
  classical
  obtain hFUIA := (M.ominimal A).mp hA
  obtain hFUIB := (M.ominimal B).mp hB
  obtain ⟨EA, hEA⟩ := Monotonicity_Theorem.exception_list D hFUIA
  obtain ⟨EB, hEB⟩ := Monotonicity_Theorem.exception_list D hFUIB
  set E : List R := (EA ++ EB).filter (fun c => decide (D.lt p c)) with hEdef
  have hne : E ++ [c2] ≠ [] := by
    intro h
    have hm : c2 ∈ E ++ [c2] :=
      List.mem_append.mpr (Or.inr (List.Mem.head _))
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨m, hMem, hMin⟩ :=
    Monotonicity_Theorem.exists_least_of_list D (E ++ [c2]) hne
  have hle : ∀ r : R, r ∈ EA ++ EB → D.lt p r → (D.lt m r ∨ m = r) := by
    intro r hr hlt
    exact hMin _ (List.mem_append.mpr (Or.inl (List.mem_filter.mpr
      ⟨hr, by rw [decide_eq_true_eq]; exact hlt⟩)))
  have hMp : D.lt p m := by
    cases List.mem_append.mp hMem with
    | inl hE =>
      rw [List.mem_filter] at hE
      exact of_decide_eq_true hE.right
    | inr hS =>
      cases hS with
      | head => exact hlt
      | tail _ h => cases h
  have hMc2 : D.lt m c2 ∨ m = c2 :=
    hMin _ (List.mem_append.mpr (Or.inr (List.Mem.head _)))
  have hsub : ∀ x : Power R 1,
      openInterval D (Endpoint.finite p) (Endpoint.finite m) x →
      openInterval D (Endpoint.finite p) (Endpoint.finite c2) x := by
    intro x hx
    have hx1 : D.lt p (Power.coord1 x) := hx.left
    have hx2 : D.lt (Power.coord1 x) m := hx.right
    show Endpoint.lt D (Endpoint.finite p) (Endpoint.finite (x 0)) ∧
      Endpoint.lt D (Endpoint.finite (x 0)) (Endpoint.finite c2)
    constructor
    · exact hx1
    · cases hMc2 with
      | inl h => exact D.trans hx2 h
      | inr heq =>
        rw [heq] at hx2
        exact hx2
  by_cases hAex : ∃ x : Power R 1,
      openInterval D (Endpoint.finite p) (Endpoint.finite m) x ∧ ¬ A x
  · by_cases hBex : ∃ y : Power R 1,
        openInterval D (Endpoint.finite p) (Endpoint.finite m) y ∧ ¬ B y
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
      have hpx : D.lt p (Power.coord1 x) := hxJ.left
      have hxm : D.lt (Power.coord1 x) m := hxJ.right
      have hpy : D.lt p (Power.coord1 y) := hyJ.left
      have hym : D.lt (Power.coord1 y) m := hyJ.right
      -- x's B-piece analysis toward y ∈ B
      have hyB : B y := by
        obtain hBx := hEB x hxB
        cases hBx with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inr hmem)) hpx
          cases hleM with
          | inl h => exact False.elim (D.irrefl m (D.trans h hxm))
          | inr heq =>
            rw [heq] at hxm
            exact False.elim (D.irrefl _ hxm)
        | inr hpiece =>
          obtain ⟨α, β, hxβ, hsubB, hLcond, hRcond⟩ := hpiece
          have hleV : ∀ v : R, β = Endpoint.finite v → (D.lt m v ∨ m = v) := by
            intro v hv
            have h1 : Endpoint.lt D (Endpoint.finite (x 0)) (Endpoint.finite v) := by
              have h2 := hxβ.right
              rw [hv] at h2
              exact h2
            have hvt : D.lt (Power.coord1 x) v := h1
            have hvp : D.lt p v := D.trans hpx hvt
            exact hle _ (List.mem_append.mpr (Or.inr (hRcond v hv))) hvp
          cases α with
          | posInf =>
            have hF : False := hxβ.left
            exact False.elim hF
          | negInf =>
            have hmem : openInterval D Endpoint.negInf β y := by
              have hβ : Endpoint.lt D (Endpoint.finite (y 0)) β :=
                Monotonicity_Theorem.beta_side D hxβ.right hleV hym
              exact ⟨trivial, hβ⟩
            exact hsubB _ hmem
          | finite u =>
            rcases D.trichotomy u p with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hlt, _, _⟩
            · have hmem : openInterval D (Endpoint.finite u) β y := by
                have hα : Endpoint.lt D (Endpoint.finite u) (Endpoint.finite (y 0)) :=
                  D.trans hlt hpy
                have hβ : Endpoint.lt D (Endpoint.finite (y 0)) β :=
                  Monotonicity_Theorem.beta_side D hxβ.right hleV hym
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
            · have hmem : openInterval D (Endpoint.finite u) β y := by
                have hα : Endpoint.lt D (Endpoint.finite u) (Endpoint.finite (y 0)) := by
                  rw [heq]
                  exact hpy
                have hβ : Endpoint.lt D (Endpoint.finite (y 0)) β :=
                  Monotonicity_Theorem.beta_side D hxβ.right hleV hym
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
            · have hvE : u ∈ EB := hLcond u rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inr hvE)) hlt
              have hux : D.lt u (Power.coord1 x) := hxβ.left
              cases hleM with
              | inl h =>
                exact False.elim (D.irrefl _ (D.trans (D.trans hxm h) hux))
              | inr heq2 =>
                rw [← heq2] at hux
                exact False.elim (D.irrefl _ (D.trans hxm hux))
      -- y's A-piece analysis toward False
      have hFalse : False := by
        obtain hAy := hEA y hyA
        cases hAy with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inl hmem)) hpy
          cases hleM with
          | inl h => exact D.irrefl _ (D.trans hym h)
          | inr heq =>
            rw [heq] at hym
            exact D.irrefl _ hym
        | inr hpiece =>
          obtain ⟨α, β, hyβ, hsubA, hLcond, hRcond⟩ := hpiece
          have hleV : ∀ v : R, β = Endpoint.finite v → (D.lt m v ∨ m = v) := by
            intro v hv
            have h1 : Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite v) := by
              have h2 := hyβ.right
              rw [hv] at h2
              exact h2
            have hvt : D.lt (Power.coord1 y) v := h1
            have hvp : D.lt p v := D.trans hpy hvt
            exact hle _ (List.mem_append.mpr (Or.inl (hRcond v hv))) hvp
          cases α with
          | posInf =>
            have hF : False := hyβ.left
            exact hF
          | negInf =>
            have hmem : openInterval D Endpoint.negInf β x := by
              have hβ : Endpoint.lt D (Endpoint.finite (x 0)) β :=
                Monotonicity_Theorem.beta_side D hyβ.right hleV hxm
              exact ⟨trivial, hβ⟩
            exact absurd (hsubA _ hmem) hxNA
          | finite u =>
            rcases D.trichotomy u p with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hlt, _, _⟩
            · have hmem : openInterval D (Endpoint.finite u) β x := by
                have hα : Endpoint.lt D (Endpoint.finite u) (Endpoint.finite (x 0)) :=
                  D.trans hlt hpx
                have hβ : Endpoint.lt D (Endpoint.finite (x 0)) β :=
                  Monotonicity_Theorem.beta_side D hyβ.right hleV hxm
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
            · have hmem : openInterval D (Endpoint.finite u) β x := by
                have hα : Endpoint.lt D (Endpoint.finite u) (Endpoint.finite (x 0)) := by
                  rw [heq]
                  exact hpx
                have hβ : Endpoint.lt D (Endpoint.finite (x 0)) β :=
                  Monotonicity_Theorem.beta_side D hyβ.right hleV hxm
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
            · have hvE : u ∈ EA := hLcond u rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inl hvE)) hlt
              have huy : D.lt u (Power.coord1 y) := hyβ.left
              cases hleM with
              | inl h =>
                exact D.irrefl _ (D.trans (D.trans hym h) huy)
              | inr heq2 =>
                rw [← heq2] at huy
                exact D.irrefl _ (D.trans hym huy)
      exact False.elim hFalse
    · refine ⟨m, hMp, hMc2, Or.inr ?_⟩
      intro y hy
      by_contra hyNB
      exact hBex ⟨y, hy, hyNB⟩
  · refine ⟨m, hMp, hMc2, Or.inl ?_⟩
    intro x hx
    by_contra hxNA
    exact hAex ⟨x, hx, hxNA⟩
