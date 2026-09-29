-- Prove2me | solution 1 for KServer.lamPot_instance_le_lazyPot_special
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T17:41:29.051215+00:00
-- url     : https://prove2.me/submissions/5da7ee37-f22b-4594-aaa5-2fa42765fef5

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

/-- **The three configurations of Lemma 5 that need no rectangle.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M) :
    (∀ p q b b' c c' e e' : M, dist p b + dist p b' = dist b b' →
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + (-dist r q + (dist q c + dist q c' - workFnU C₀ σ ![r, c, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b c' e e' : M,
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + (-dist r q + (dist q b + dist q c' - workFnU C₀ σ ![r, b, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b c c' e e' : M, dist p c + dist p b = dist c b →
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + (-dist r q + (dist q c + dist q c' - workFnU C₀ σ ![r, c, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Case 1: `p` lies on a geodesic between `b` and `b'`
    intro p q b b' c c' e e' hcol
    have hq := workFnU_quasiconvex_three M C₀ σ r b b' p q
    have t1 : dist p q ≤ dist p r + dist r q := dist_triangle p r q
    have t2 : dist e e' ≤ dist e r + dist r e' := dist_triangle e r e'
    have hc1 : dist p r = dist r p := dist_comm p r
    have hc2 : dist e r = dist r e := dist_comm e r
    have hI := lazyPot_ge_instance M C₀ σ r e e' q c c' b b'
    have s1 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
    have s2 : workFnU C₀ σ ![r, b', q] = workFnU C₀ σ ![r, q, b'] := swap12 C₀ σ r b' q
    have s3 : workFnU C₀ σ ![r, b', p] = workFnU C₀ σ ![r, p, b'] := swap12 C₀ σ r b' p
    have s4 : workFnU C₀ σ ![r, b, p] = workFnU C₀ σ ![r, p, b] := swap12 C₀ σ r b p
    have l1 := lipP C₀ σ r q p b'
    have l2 := lipP C₀ σ r q p b
    rcases min_cases (workFnU C₀ σ ![r, b, p] + workFnU C₀ σ ![r, b', q])
        (workFnU C₀ σ ![r, b, q] + workFnU C₀ σ ![r, b', p]) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hq
    · linarith
    · linarith
  · -- Case 2.1: `b = b'` and `c = b`
    intro p q b c' e e'
    have hq := workFnU_quasiconvex_three M C₀ σ r b b e e'
    have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
    have t2 : dist q c' ≤ dist q r + dist r c' := dist_triangle q r c'
    have hc1 : dist p r = dist r p := dist_comm p r
    have hc2 : dist q r = dist r q := dist_comm q r
    have hc3 : dist b p = dist p b := dist_comm b p
    have hc4 : dist b q = dist q b := dist_comm b q
    have hI := lazyPot_ge_instance M C₀ σ r b c' b p q e e'
    rcases min_cases (workFnU C₀ σ ![r, b, e] + workFnU C₀ σ ![r, b, e'])
        (workFnU C₀ σ ![r, b, e'] + workFnU C₀ σ ![r, b, e]) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hq
    · linarith
    · linarith
  · -- Case 2.2: `b = b'` and `p` lies on a geodesic between `c` and `b`
    intro p q b c c' e e' hcol
    have t1 : dist e e' ≤ dist e r + dist r e' := dist_triangle e r e'
    have t2 : dist q c ≤ dist q p + dist p c := dist_triangle q p c
    have t3 : dist q p ≤ dist q r + dist r p := dist_triangle q r p
    have hc2 : dist e r = dist r e := dist_comm e r
    have hc3 : dist q r = dist r q := dist_comm q r
    have hc4 : dist c b = dist b c := dist_comm c b
    have hI := lazyPot_ge_instance M C₀ σ r e e' c b b q c'
    have l1 := lipP C₀ σ r c p q
    have s1 : workFnU C₀ σ ![r, c, q] = workFnU C₀ σ ![r, q, c] := swap12 C₀ σ r c q
    have s2 : workFnU C₀ σ ![r, p, q] = workFnU C₀ σ ![r, q, p] := swap12 C₀ σ r p q
    linarith
