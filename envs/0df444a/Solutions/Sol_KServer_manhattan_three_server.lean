-- Prove2me | solution 1 for KServer.manhattan_three_server
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T18:57:08.428254+00:00
-- url     : https://prove2.me/submissions/26e37b24-bcae-4514-82c3-735f5e7efc53

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_three_server_of_semiLazy_le_lazy
import Theorems.Thm_KServer_lamPot_le_lazyPot_manhattan
import Theorems.Thm_KServer_gamPot_le_lazyPot_manhattan

open KServer

private abbrev E2 := PiLp 1 fun _ : Fin 2 => ℝ

private noncomputable def pt (u : ℝ) : E2 := (WithLp.toLp 1 ![u, 0] : E2)

private noncomputable def X0 : Config 3 E2 := ![pt 0, pt 1, pt 2]

private theorem X0_coord : ∀ i : Fin 3, (X0 i).ofLp 0 = (i.val : ℝ) := by
  intro i
  match i with
  | 0 => show (0:ℝ) = ((0:Fin 3).val : ℝ); norm_num
  | 1 => show (1:ℝ) = ((1:Fin 3).val : ℝ); norm_num
  | 2 => show (2:ℝ) = ((2:Fin 3).val : ℝ); norm_num

private theorem X0_inj : Function.Injective X0 := by
  intro i j h
  have hc : ((i.val : ℝ)) = (j.val : ℝ) := by
    rw [← X0_coord i, ← X0_coord j, h]
  exact Fin.ext (Nat.cast_injective hc)

/-- **Theorem 2 of Bein, Chrobak and Larmore.** -/
theorem solution (C₀ : Config 3 (PiLp 1 fun _ : Fin 2 => ℝ)) :
    ∃ A : OnlineAlgorithm 3 (PiLp 1 fun _ : Fin 2 => ℝ),
      A.conf [] = C₀ ∧ IsCompetitive A 3 := by
  refine three_server_of_semiLazy_le_lazy _ C₀ X0 X0_inj ?_
  intro σ r
  unfold semiLazyPot
  exact max_le (le_refl _)
    (max_le (lamPot_le_lazyPot_manhattan C₀ (σ ++ [r]) r)
      (gamPot_le_lazyPot_manhattan C₀ (σ ++ [r]) r))
