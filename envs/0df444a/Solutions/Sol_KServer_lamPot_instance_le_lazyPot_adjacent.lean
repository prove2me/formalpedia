-- Prove2me | solution 1 for KServer.lamPot_instance_le_lazyPot_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T17:53:16.979123+00:00
-- url     : https://prove2.me/submissions/8eb10064-6f92-4943-a6f3-4a4a15e316f8

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex_three
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_lazyPot_ge_instance

open KServer

section Perm
variable {M : Type} [MetricSpace M]

private theorem perm3_eq (C₀ : Config 3 M) (σ : List M) (X Y : Config 3 M)
    (τ : Equiv.Perm (Fin 3)) (h : ∀ i, X i = Y (τ i)) :
    workFnU C₀ σ X = workFnU C₀ σ Y := by
  rw [show X = Y ∘ (τ : Equiv.Perm (Fin 3)) from funext h]
  exact workFnU_perm 3 M C₀ σ Y τ

private theorem swap01 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![q, p, z] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 0 1) ?_
  intro i
  match i with
  | 0 => show p = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 0); rw [Equiv.swap_apply_left]; rfl
  | 1 => show q = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 1); rw [Equiv.swap_apply_right]; rfl
  | 2 => show z = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 2)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl

private theorem rot3 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![z, p, q] := by
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have c0 : c 0 = 1 := by rw [hc]; decide
  have c1 : c 1 = 2 := by rw [hc]; decide
  have c2 : c 2 = 0 := by rw [hc]; decide
  refine perm3_eq C₀ σ _ _ c ?_
  intro i
  match i with
  | 0 => show p = ![z, p, q] (c 0); rw [c0]; rfl
  | 1 => show q = ![z, p, q] (c 1); rw [c1]; rfl
  | 2 => show z = ![z, p, q] (c 2); rw [c2]; rfl

private theorem swap12 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![p, z, q] :=
  ((rot3 C₀ σ p z q).trans (swap01 C₀ σ q p z)).symm

/-- The Lipschitz property in pinned two-point form. -/
private theorem lipP (C₀ : Config 3 M) (σ : List M) (r u v v' : M) :
    workFnU C₀ σ ![r, u, v'] ≤ workFnU C₀ σ ![r, v, v'] + dist v u := by
  have hmc : moveCost (![r, v, v'] : Config 3 M) (![r, u, v'] : Config 3 M) = dist v u := by
    unfold moveCost
    rw [Fin.sum_univ_three]
    show dist r r + dist v u + dist v' v' = dist v u
    rw [dist_self, dist_self]; ring
  have h := workFnU_lipschitz 3 (by norm_num) M C₀ σ ![r, u, v'] ![r, v, v']
  rw [hmc] at h
  exact h

end Perm

section Aux
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M)

/-- Case 3.1 with the quasiconvexity branch fixed. -/
private theorem aux31 (p q B B' C C' e e' : M)
    (h1 : dist q C + dist q B = dist C B) (h2 : dist q B' + dist q C' = dist B' C')
    (hQ : workFnU C₀ σ ![r, C, p] + workFnU C₀ σ ![r, C', q]
      ≤ workFnU C₀ σ ![r, C, C'] + workFnU C₀ σ ![r, p, q]) :
    (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
      + (-dist r q + (dist q C + dist q C' - workFnU C₀ σ ![r, C, C']))
      - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r e e' B p C B' C'
  have t1 : dist e e' ≤ dist e r + dist r e' := dist_triangle e r e'
  have t2 : dist p B' ≤ dist p q + dist q B' := dist_triangle p q B'
  have t3 : dist p q ≤ dist p r + dist r q := dist_triangle p r q
  have hc1 : dist e r = dist r e := dist_comm e r
  have hc2 : dist p r = dist r p := dist_comm p r
  have hc3 : dist B p = dist p B := dist_comm B p
  have hc4 : dist B C = dist C B := dist_comm B C
  have l1 := lipP C₀ σ r B q C'
  have s1 : workFnU C₀ σ ![r, C', q] = workFnU C₀ σ ![r, q, C'] := swap12 C₀ σ r C' q
  have s2 : workFnU C₀ σ ![r, C, p] = workFnU C₀ σ ![r, p, C] := swap12 C₀ σ r C p
  linarith

/-- Case 3.3 with the quasiconvexity branch fixed. -/
private theorem aux33 (p q B B' E : M)
    (hQ : workFnU C₀ σ ![r, E, q] + workFnU C₀ σ ![r, B, p]
      ≤ workFnU C₀ σ ![r, E, B] + workFnU C₀ σ ![r, p, q]) :
    (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
      + (-dist r q + (dist q B + dist q B' - workFnU C₀ σ ![r, B, B']))
      - workFnU C₀ σ ![r, p, q] + dist E B - workFnU C₀ σ ![r, E, B]
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r B B' B q E p B'
  have t1 : dist p B ≤ dist p r + dist r B := dist_triangle p r B
  have t2 : dist q B' ≤ dist q r + dist r B' := dist_triangle q r B'
  have hc1 : dist p r = dist r p := dist_comm p r
  have hc2 : dist q r = dist r q := dist_comm q r
  have hc3 : dist B q = dist q B := dist_comm B q
  have hc4 : dist B E = dist E B := dist_comm B E
  have s1 : workFnU C₀ σ ![r, q, E] = workFnU C₀ σ ![r, E, q] := swap12 C₀ σ r q E
  have s2 : workFnU C₀ σ ![r, B, p] = workFnU C₀ σ ![r, p, B] := swap12 C₀ σ r B p
  linarith

end Aux

/-- **The remaining cases of Lemma 5.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M) :
    (∀ p q B C E : M, dist E p + dist p B = dist E B →
      (-dist r p + (dist p B + dist p B - workFnU C₀ σ ![r, B, B]))
        + (-dist r q + (dist q C + dist q C - workFnU C₀ σ ![r, C, C]))
        - workFnU C₀ σ ![r, p, q] + dist E B - workFnU C₀ σ ![r, E, B]
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q B B' C C' e e' : M,
        dist q C + dist q B = dist C B → dist q B' + dist q C' = dist B' C' →
      (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
        + (-dist r q + (dist q C + dist q C' - workFnU C₀ σ ![r, C, C']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q B B' C' e e' : M, dist q B' + dist q C' = dist B' C' →
      (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
        + (-dist r q + (dist q B + dist q C' - workFnU C₀ σ ![r, B, C']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q B B' E : M,
      (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
        + (-dist r q + (dist q B + dist q B' - workFnU C₀ σ ![r, B, B']))
        - workFnU C₀ σ ![r, p, q] + dist E B - workFnU C₀ σ ![r, E, B]
        ≤ lazyPot C₀ σ r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Case 2.3
    intro p q B C E hcol
    have hq := workFnU_quasiconvex_three M C₀ σ r B E C C
    rw [min_self] at hq
    have t1 : dist p B ≤ dist p r + dist r B := dist_triangle p r B
    have t2 : dist q C ≤ dist q r + dist r C := dist_triangle q r C
    have hc1 : dist p r = dist r p := dist_comm p r
    have hc2 : dist q r = dist r q := dist_comm q r
    have hc3 : dist E p = dist p E := dist_comm E p
    have sBE : workFnU C₀ σ ![r, B, E] = workFnU C₀ σ ![r, E, B] := swap12 C₀ σ r B E
    have hI := lazyPot_ge_instance M C₀ σ r B C E B B q C
    have l1 := lipP C₀ σ r E p q
    linarith
  · -- Case 3.1
    intro p q B B' C C' e e' h1 h2
    have hq := workFnU_quasiconvex_three M C₀ σ r C C' p q
    have h1' : dist q B + dist q C = dist B C := by
      rw [dist_comm B C, ← h1]; ring
    have h2' : dist q C' + dist q B' = dist C' B' := by
      rw [dist_comm C' B', ← h2]; ring
    have sy : workFnU C₀ σ ![r, C, C'] = workFnU C₀ σ ![r, C', C] := swap12 C₀ σ r C C'
    have sy2 : workFnU C₀ σ ![r, B, B'] = workFnU C₀ σ ![r, B', B] := swap12 C₀ σ r B B'
    have sy3 : workFnU C₀ σ ![r, p, q] = workFnU C₀ σ ![r, q, p] := swap12 C₀ σ r p q
    rcases min_cases (workFnU C₀ σ ![r, C, p] + workFnU C₀ σ ![r, C', q])
        (workFnU C₀ σ ![r, C, q] + workFnU C₀ σ ![r, C', p]) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hq
    · exact aux31 C₀ σ r p q B B' C C' e e' h1 h2 hq
    · have := aux31 C₀ σ r p q B' B C' C e e' h2' h1' (by rw [← sy]; linarith)
      linarith
  · -- Case 3.2
    intro p q B B' C' e e' h2
    have hI := lazyPot_ge_instance M C₀ σ r e e' B p q B' C'
    have t1 : dist e e' ≤ dist e r + dist r e' := dist_triangle e r e'
    have t2 : dist p B' ≤ dist p q + dist q B' := dist_triangle p q B'
    have t3 : dist p q ≤ dist p r + dist r q := dist_triangle p r q
    have hc1 : dist e r = dist r e := dist_comm e r
    have hc2 : dist p r = dist r p := dist_comm p r
    have hc3 : dist B p = dist p B := dist_comm B p
    have hc4 : dist B q = dist q B := dist_comm B q
    linarith
  · -- Case 3.3
    intro p q B B' E
    have hq := workFnU_quasiconvex_three M C₀ σ r E B p q
    have sy3 : workFnU C₀ σ ![r, p, q] = workFnU C₀ σ ![r, q, p] := swap12 C₀ σ r p q
    rcases min_cases (workFnU C₀ σ ![r, E, p] + workFnU C₀ σ ![r, B, q])
        (workFnU C₀ σ ![r, E, q] + workFnU C₀ σ ![r, B, p]) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hq
    · have := aux33 C₀ σ r q p B B' E (by rw [← sy3]; linarith)
      linarith
    · exact aux33 C₀ σ r p q B B' E hq
