-- Prove2me | solution 1 for KServer.lazyPot_le_semiLazyPot
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T16:55:10.507048+00:00
-- url     : https://prove2.me/submissions/c86e336a-a2b6-44a3-9944-0f763072a182

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_update_three
import Theorems.Thm_KServer_workFnU_quasiconvex_three
import Theorems.Thm_KServer_lazyPot_ge_instance
import Theorems.Thm_KServer_lamPot_gamPot_ge_instance
import Theorems.Thm_KServer_lazyPot_le_of_pointwise

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

/-- The unified work function of a three-point configuration is symmetric in its
last two coordinates. -/
private theorem swap12 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![p, z, q] :=
  ((rot3 C₀ σ p z q).trans (swap01 C₀ σ q p z)).symm

end Perm

section Tools
variable {M : Type} [MetricSpace M]

/-- The three branches of the update formula (5). -/
private theorem split3 (C₀ : Config 3 M) (σ : List M) (r s x y : M) :
    workFnU C₀ (σ ++ [r]) ![s, x, y] = workFnU C₀ (σ ++ [r]) ![r, x, y] + dist r s
      ∨ workFnU C₀ (σ ++ [r]) ![s, x, y] = workFnU C₀ (σ ++ [r]) ![r, s, y] + dist r x
      ∨ workFnU C₀ (σ ++ [r]) ![s, x, y] = workFnU C₀ (σ ++ [r]) ![r, s, x] + dist r y := by
  have h := workFnU_update_three M C₀ σ r s x y
  rw [swap01 C₀ (σ ++ [r]) s r y, rot3 C₀ (σ ++ [r]) s x r] at h
  rcases min_choice (workFnU C₀ (σ ++ [r]) ![r, x, y] + dist r s)
      (min (workFnU C₀ (σ ++ [r]) ![r, s, y] + dist r x)
           (workFnU C₀ (σ ++ [r]) ![r, s, x] + dist r y)) with hm | hm
  · exact Or.inl (by rw [h, hm])
  · rcases min_choice (workFnU C₀ (σ ++ [r]) ![r, s, y] + dist r x)
        (workFnU C₀ (σ ++ [r]) ![r, s, x] + dist r y) with hm2 | hm2
    · exact Or.inr (Or.inl (by rw [h, hm, hm2]))
    · exact Or.inr (Or.inr (by rw [h, hm, hm2]))

/-- Every instance of the lazy potential is below the semi-lazy potential. -/
private theorem psiI (C₀ : Config 3 M) (σ : List M) (r A A' P B B' D D' : M) :
    (dist r A + dist r A' - workFnU C₀ (σ ++ [r]) ![r, A, A'])
      + ((dist P B + dist P B' - workFnU C₀ (σ ++ [r]) ![r, B, B'])
          + (dist D D' - workFnU C₀ (σ ++ [r]) ![r, P, D]
              - workFnU C₀ (σ ++ [r]) ![r, P, D']))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  refine le_trans (lazyPot_ge_instance M C₀ (σ ++ [r]) r A A' P B B' D D') ?_
  unfold semiLazyPot
  exact le_max_left _ _

/-- Every instance of `Λ` is below the semi-lazy potential. -/
private theorem lamI (C₀ : Config 3 M) (σ : List M) (r p q b b' c c' e e' : M) :
    (-dist r p + (dist p b + dist p b' - workFnU C₀ (σ ++ [r]) ![r, b, b']))
      + (-dist r q + (dist q c + dist q c' - workFnU C₀ (σ ++ [r]) ![r, c, c']))
      - workFnU C₀ (σ ++ [r]) ![r, p, q] + dist e e'
      - workFnU C₀ (σ ++ [r]) ![r, e, e']
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  refine le_trans ((lamPot_gamPot_ge_instance M C₀ (σ ++ [r]) r).1 p q b b' c c' e e') ?_
  unfold semiLazyPot
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- Every instance of `Γ` is below the semi-lazy potential. -/
private theorem gamI (C₀ : Config 3 M) (σ : List M) (r p q d d' f b b' : M) :
    (-dist r p + (dist p b + dist p b' - workFnU C₀ (σ ++ [r]) ![r, b, b']))
      + dist r q + dist d d' - workFnU C₀ (σ ++ [r]) ![r, q, d]
      - workFnU C₀ (σ ++ [r]) ![r, q, d'] + dist q f
      - workFnU C₀ (σ ++ [r]) ![r, p, f]
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  refine le_trans ((lamPot_gamPot_ge_instance M C₀ (σ ++ [r]) r).2 p q d d' f b b') ?_
  unfold semiLazyPot
  exact le_trans (le_max_right _ _) (le_max_right _ _)

end Tools

section Cases
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r s a a' p b b' d d' : M)

private theorem c1 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, b, b'] + dist r s))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, p, d] + dist r s) - (workFnU C₀ (σ ++ [r]) ![r, p, d'] + dist r s)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have t1 : dist s a ≤ dist s r + dist r a := dist_triangle s r a
  have t2 : dist s a' ≤ dist s r + dist r a' := dist_triangle s r a'
  have hc : dist s r = dist r s := dist_comm s r
  linarith [psiI C₀ σ r a a' p b b' d d']

private theorem c2 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, b, b'] + dist r s))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, p, d] + dist r s) - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d')))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have hq := workFnU_quasiconvex_three M C₀ (σ ++ [r]) r a a' p d
  have t1 : dist s a ≤ dist s r + dist r a := dist_triangle s r a
  have t1' : dist s a' ≤ dist s r + dist r a' := dist_triangle s r a'
  have t2 : dist d d' ≤ dist d r + dist r d' := dist_triangle d r d'
  have hc : dist s r = dist r s := dist_comm s r
  have hc2 : dist d r = dist r d := dist_comm d r
  have e1 : workFnU C₀ (σ ++ [r]) ![r, p, s] = workFnU C₀ (σ ++ [r]) ![r, s, p] := swap12 C₀ (σ ++ [r]) r p s
  have e2 : workFnU C₀ (σ ++ [r]) ![r, p, a'] = workFnU C₀ (σ ++ [r]) ![r, a', p] := swap12 C₀ (σ ++ [r]) r p a'
  have e3 : workFnU C₀ (σ ++ [r]) ![r, p, a] = workFnU C₀ (σ ++ [r]) ![r, a, p] := swap12 C₀ (σ ++ [r]) r p a
  rcases min_cases (workFnU C₀ (σ ++ [r]) ![r, a, p] + workFnU C₀ (σ ++ [r]) ![r, a', d])
      (workFnU C₀ (σ ++ [r]) ![r, a, d] + workFnU C₀ (σ ++ [r]) ![r, a', p]) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hq
  · linarith [psiI C₀ σ r a' d p b b' s a]
  · linarith [psiI C₀ σ r a d p b b' s a']

private theorem c3 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, b, b'] + dist r s))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d) - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d')))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have hq := workFnU_quasiconvex_three M C₀ (σ ++ [r]) r a a' s p
  have t1 : dist s a ≤ dist s r + dist r a := dist_triangle s r a
  have t1' : dist s a' ≤ dist s r + dist r a' := dist_triangle s r a'
  have t2 : dist d d' ≤ dist d r + dist r d' := dist_triangle d r d'
  have hc : dist s r = dist r s := dist_comm s r
  have hc2 : dist d r = dist r d := dist_comm d r
  have e1 : workFnU C₀ (σ ++ [r]) ![r, p, s] = workFnU C₀ (σ ++ [r]) ![r, s, p] := swap12 C₀ (σ ++ [r]) r p s
  have e2 : workFnU C₀ (σ ++ [r]) ![r, p, a'] = workFnU C₀ (σ ++ [r]) ![r, a', p] := swap12 C₀ (σ ++ [r]) r p a'
  have e3 : workFnU C₀ (σ ++ [r]) ![r, p, a] = workFnU C₀ (σ ++ [r]) ![r, a, p] := swap12 C₀ (σ ++ [r]) r p a
  have e4 : workFnU C₀ (σ ++ [r]) ![r, a, s] = workFnU C₀ (σ ++ [r]) ![r, s, a] := swap12 C₀ (σ ++ [r]) r a s
  have e5 : workFnU C₀ (σ ++ [r]) ![r, a', s] = workFnU C₀ (σ ++ [r]) ![r, s, a'] := swap12 C₀ (σ ++ [r]) r a' s
  rcases min_cases (workFnU C₀ (σ ++ [r]) ![r, a, s] + workFnU C₀ (σ ++ [r]) ![r, a', p])
      (workFnU C₀ (σ ++ [r]) ![r, a, p] + workFnU C₀ (σ ++ [r]) ![r, a', s]) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hq
  · linarith [psiI C₀ σ r s a p b b' s a']
  · linarith [psiI C₀ σ r s a' p b b' s a]

private theorem c4 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, b, b'] + dist r s))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d) - (workFnU C₀ (σ ++ [r]) ![r, s, d'] + dist r p)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have hcsr : dist s r = dist r s := dist_comm s r
  have hq := workFnU_quasiconvex_three M C₀ (σ ++ [r]) r b b' s d'
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have t1' : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have t2 : dist d d' ≤ dist d r + dist r d' := dist_triangle d r d'
  have hc : dist p r = dist r p := dist_comm p r
  have hc2 : dist d r = dist r d := dist_comm d r
  have e1 : workFnU C₀ (σ ++ [r]) ![r, b, s] = workFnU C₀ (σ ++ [r]) ![r, s, b] := swap12 C₀ (σ ++ [r]) r b s
  have e2 : workFnU C₀ (σ ++ [r]) ![r, b', s] = workFnU C₀ (σ ++ [r]) ![r, s, b'] := swap12 C₀ (σ ++ [r]) r b' s
  rcases min_cases (workFnU C₀ (σ ++ [r]) ![r, b, s] + workFnU C₀ (σ ++ [r]) ![r, b', d'])
      (workFnU C₀ (σ ++ [r]) ![r, b, d'] + workFnU C₀ (σ ++ [r]) ![r, b', s]) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hq
  · linarith [psiI C₀ σ r b' d' s a a' p b]
  · linarith [psiI C₀ σ r b d' s a a' p b']

private theorem c5 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, b, b'] + dist r s))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, s, d] + dist r p) - (workFnU C₀ (σ ++ [r]) ![r, s, d'] + dist r p)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have t2 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have hc : dist p r = dist r p := dist_comm p r
  have hc2 : dist s r = dist r s := dist_comm s r
  linarith [psiI C₀ σ r b b' s a a' d d']

private theorem c6 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, s, b] + dist r b'))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, p, d] + dist r s) - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d')))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have t2 : dist d d' ≤ dist d r + dist r d' := dist_triangle d r d'
  have hc : dist p r = dist r p := dist_comm p r
  have hc2 : dist d r = dist r d := dist_comm d r
  have hc3 : dist s r = dist r s := dist_comm s r
  linarith [psiI C₀ σ r p d s a a' p b]

private theorem c7 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, s, b] + dist r b'))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d) - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d')))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have t2 : dist d d' ≤ dist d r + dist r d' := dist_triangle d r d'
  have hc : dist p r = dist r p := dist_comm p r
  have hc2 : dist d r = dist r d := dist_comm d r
  have hc3 : dist s r = dist r s := dist_comm s r
  linarith [psiI C₀ σ r s p s a a' p b]

private theorem c8 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, s, b] + dist r b'))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, s, p] + dist r d) - (workFnU C₀ (σ ++ [r]) ![r, s, d'] + dist r p)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have t2 : dist d d' ≤ dist d r + dist r d' := dist_triangle d r d'
  have hc : dist p r = dist r p := dist_comm p r
  have hc2 : dist d r = dist r d := dist_comm d r
  have hc3 : dist s r = dist r s := dist_comm s r
  linarith [psiI C₀ σ r s d' s a a' p b]

private theorem c9 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, s, b] + dist r b'))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, s, d] + dist r p) - (workFnU C₀ (σ ++ [r]) ![r, s, d'] + dist r p)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have t2 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc : dist p r = dist r p := dist_comm p r
  have hc3 : dist s r = dist r s := dist_comm s r
  linarith [psiI C₀ σ r s b s a a' d d']

private theorem c10 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, s, b] + dist r b'))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, p, d] + dist r s) - (workFnU C₀ (σ ++ [r]) ![r, s, d'] + dist r p)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have hq := workFnU_quasiconvex_three M C₀ (σ ++ [r]) r s b p d
  have hq2 := workFnU_quasiconvex_three M C₀ (σ ++ [r]) r p d s d'
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have t2 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have t3 : dist d d' ≤ dist d r + dist r d' := dist_triangle d r d'
  have hc : dist p r = dist r p := dist_comm p r
  have hc2 : dist d r = dist r d := dist_comm d r
  have hc3 : dist s r = dist r s := dist_comm s r
  have e1 : workFnU C₀ (σ ++ [r]) ![r, b, p] = workFnU C₀ (σ ++ [r]) ![r, p, b] := swap12 C₀ (σ ++ [r]) r b p
  have e2 : workFnU C₀ (σ ++ [r]) ![r, p, s] = workFnU C₀ (σ ++ [r]) ![r, s, p] := swap12 C₀ (σ ++ [r]) r p s
  have e3 : workFnU C₀ (σ ++ [r]) ![r, d, s] = workFnU C₀ (σ ++ [r]) ![r, s, d] := swap12 C₀ (σ ++ [r]) r d s
  rcases min_cases (workFnU C₀ (σ ++ [r]) ![r, s, p] + workFnU C₀ (σ ++ [r]) ![r, b, d])
      (workFnU C₀ (σ ++ [r]) ![r, s, d] + workFnU C₀ (σ ++ [r]) ![r, b, p]) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hq
  · rcases min_cases (workFnU C₀ (σ ++ [r]) ![r, p, s] + workFnU C₀ (σ ++ [r]) ![r, d, d'])
        (workFnU C₀ (σ ++ [r]) ![r, p, d'] + workFnU C₀ (σ ++ [r]) ![r, d, s])
        with ⟨he2, _⟩ | ⟨he2, _⟩ <;> rw [he2] at hq2
    · linarith [psiI C₀ σ r d d' s a a' p b]
    · linarith [psiI C₀ σ r b d s a a' p b, psiI C₀ σ r p d' s a a' d d']
  · linarith [psiI C₀ σ r p b s a a' d d']

private theorem c11 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, s, b] + dist r b'))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, p, d] + dist r s) - (workFnU C₀ (σ ++ [r]) ![r, p, d'] + dist r s)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have hc : dist p r = dist r p := dist_comm p r
  have hc3 : dist s r = dist r s := dist_comm s r
  linarith [gamI C₀ σ r s p d d' b a a']

private theorem c12 :
    (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
      + ((dist p b + dist p b' - (workFnU C₀ (σ ++ [r]) ![r, b, b'] + dist r s))
          + (dist d d' - (workFnU C₀ (σ ++ [r]) ![r, p, d] + dist r s) - (workFnU C₀ (σ ++ [r]) ![r, s, d'] + dist r p)))
      ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  have hq := workFnU_quasiconvex_three M C₀ (σ ++ [r]) r s d' p d
  have t1 : dist s a ≤ dist s r + dist r a := dist_triangle s r a
  have t2 : dist s a' ≤ dist s r + dist r a' := dist_triangle s r a'
  have t3 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have t4 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have hc : dist s r = dist r s := dist_comm s r
  have hc2 : dist p r = dist r p := dist_comm p r
  have e1 : workFnU C₀ (σ ++ [r]) ![r, s, p] = workFnU C₀ (σ ++ [r]) ![r, p, s] := swap12 C₀ (σ ++ [r]) r s p
  have e2 : workFnU C₀ (σ ++ [r]) ![r, d', d] = workFnU C₀ (σ ++ [r]) ![r, d, d'] := swap12 C₀ (σ ++ [r]) r d' d
  have e3 : workFnU C₀ (σ ++ [r]) ![r, d', p] = workFnU C₀ (σ ++ [r]) ![r, p, d'] := swap12 C₀ (σ ++ [r]) r d' p
  rcases min_cases (workFnU C₀ (σ ++ [r]) ![r, s, p] + workFnU C₀ (σ ++ [r]) ![r, d', d])
      (workFnU C₀ (σ ++ [r]) ![r, s, d] + workFnU C₀ (σ ++ [r]) ![r, d', p]) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hq
  · linarith [lamI C₀ σ r p s b b' a a' d d']
  · linarith [psiI C₀ σ r a a' p b b' d d', psiI C₀ σ r b b' s a a' d d']

end Cases

/-- **Lemma 4 of Bein, Chrobak and Larmore.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r s : M) :
    lazyPot C₀ (σ ++ [r]) s ≤ semiLazyPot C₀ (σ ++ [r]) r := by
  refine lazyPot_le_of_pointwise M C₀ σ r s ?_
  intro a a' p b b' d d'
  have hdd : dist d' d = dist d d' := dist_comm d' d
  rcases split3 C₀ σ r s b b' with h1 | h1 | h1 <;>
    rcases split3 C₀ σ r s p d with h2 | h2 | h2 <;>
      rcases split3 C₀ σ r s p d' with h3 | h3 | h3 <;>
        rw [h1, h2, h3]
  · linarith [c1 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c12 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c2 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c12 C₀ σ r s a a' p b b' d' d, hdd]
  · linarith [c5 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c4 C₀ σ r s a a' p b b' d' d, hdd]
  · linarith [c2 C₀ σ r s a a' p b b' d' d, hdd]
  · linarith [c4 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c3 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c11 C₀ σ r s a a' p b' b d d', hdd]
  · linarith [c10 C₀ σ r s a a' p b' b d d', hdd]
  · linarith [c6 C₀ σ r s a a' p b' b d d', hdd]
  · linarith [c10 C₀ σ r s a a' p b' b d' d, hdd]
  · linarith [c9 C₀ σ r s a a' p b' b d d', hdd]
  · linarith [c8 C₀ σ r s a a' p b' b d' d, hdd]
  · linarith [c6 C₀ σ r s a a' p b' b d' d, hdd]
  · linarith [c8 C₀ σ r s a a' p b' b d d', hdd]
  · linarith [c7 C₀ σ r s a a' p b' b d d', hdd]
  · linarith [c11 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c10 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c6 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c10 C₀ σ r s a a' p b b' d' d, hdd]
  · linarith [c9 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c8 C₀ σ r s a a' p b b' d' d, hdd]
  · linarith [c6 C₀ σ r s a a' p b b' d' d, hdd]
  · linarith [c8 C₀ σ r s a a' p b b' d d', hdd]
  · linarith [c7 C₀ σ r s a a' p b b' d d', hdd]
