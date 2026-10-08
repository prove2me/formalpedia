-- Prove2me | solution 1 for MondererShapley.ClosedPath.closed_path_I_eq_zero_of_potential
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:13:20.775974+00:00
-- url     : https://prove2.me/submissions/c02fca5b-4ac1-4315-bb00-2005573deb98

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential
import Definitions.Def_MondererShapley_ClosedPath_FinPath

open MondererShapley.ClosedPath

theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ)
    (hP : IsPotential u P) (γ : FinPath Y) (hγ : γ.IsClosed) : γ.I u = 0 := by
  have hs (k : Fin γ.len) :
      u (γ.dev k) (γ.pt k.succ) - u (γ.dev k) (γ.pt k.castSucc) =
      P (γ.pt k.succ) - P (γ.pt k.castSucc) := by
    have he : Function.update (γ.pt k.castSucc) (γ.dev k) (γ.pt k.succ (γ.dev k)) =
        γ.pt k.succ := by
      funext j
      by_cases hj : j = γ.dev k
      · subst j; simp
      · simpa [hj] using (γ.step k).2 j hj |>.symm
    simpa [he] using hP (γ.dev k) (γ.pt k.castSucc)
      (γ.pt k.succ (γ.dev k)) (γ.pt k.castSucc (γ.dev k))
  unfold FinPath.I
  simp_rw [hs]
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ (fun k => P (γ.pt k))
  have h₂ := Fin.sum_univ_castSucc (fun k => P (γ.pt k))
  have he : P (γ.pt 0) = P (γ.pt (Fin.last γ.len)) := congrArg P hγ
  linarith

#print axioms solution
