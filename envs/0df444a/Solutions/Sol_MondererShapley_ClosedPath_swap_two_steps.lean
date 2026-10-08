-- Prove2me | solution 1 for MondererShapley.ClosedPath.swap_two_steps
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:20:29.837003+00:00
-- url     : https://prove2.me/submissions/1e023e66-48a9-4e3c-b44a-a5f344cfe9c0

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_FinPath

namespace MondererShapley.ClosedPath
variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

theorem exchange (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0)
    (a b c : ∀ i, Y i) (i k : ι) (hik : i ≠ k)
    (hab : IsStep a b i) (hbc : IsStep b c k) :
    let z := Function.update a k (c k)
    IsStep a z k ∧ IsStep z c i ∧
      (u i b - u i a) + (u k c - u k b) =
        (u k z - u k a) + (u i c - u i z) := by
  classical
  let z := Function.update a k (c k)
  have hki := hik.symm
  have hbi : b i ≠ a i := hab.1
  have hbk : b k = a k := hab.2 k hki
  have hci : c i = b i := hbc.2 i hik
  have hck : c k ≠ a k := by simpa [hbk] using hbc.1
  have haz : IsStep a z k := ⟨by simpa [z] using hck, fun j hj => by simp [z, hj]⟩
  have hzc : IsStep z c i := by
    refine ⟨by simpa [z, hik, hci] using hbi, ?_⟩
    intro j hj
    by_cases hjk : j = k
    · subst j; simp [z]
    · simpa [z, hjk] using (hbc.2 j hjk).trans (hab.2 j hj)
  have hab' : a ≠ b := fun he => hbi (congrFun he.symm i)
  have hbc' : b ≠ c := fun he => hbc.1 (congrFun he.symm k)
  have haz' : a ≠ z := fun he => haz.1 (congrFun he.symm k)
  have hzc' : z ≠ c := fun he => hzc.1 (congrFun he.symm i)
  have hac' : a ≠ c := by
    intro he; apply hck; exact congrFun he.symm k
  have hbz' : b ≠ z := by
    intro he; apply hbi
    have hh := congrFun he i
    simpa [z, hik] using hh
  let γ : FinPath Y :=
    { len := 4
      pt := ![a, b, c, z, a]
      dev := ![i, k, i, k]
      step := by
        intro j; fin_cases j
        · exact hab
        · exact hbc
        · exact ⟨hzc.1.symm, fun j hj => (hzc.2 j hj).symm⟩
        · exact ⟨haz.1.symm, fun j hj => (haz.2 j hj).symm⟩ }
  have hs : γ.IsSimpleClosed := by
    refine ⟨rfl, ?_⟩
    intro l j hl hj hlj
    fin_cases l <;> fin_cases j <;>
      simp_all [γ, ne_comm]
  have hz := hfour γ hs rfl
  norm_num [γ, FinPath.I, Fin.sum_univ_succ] at hz
  exact ⟨haz, hzc, by dsimp [z] at hz; linarith⟩

end MondererShapley.ClosedPath
open MondererShapley.ClosedPath

theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0)
    (a b c : ∀ i, Y i) (i k : ι) (hik : i ≠ k)
    (hab : IsStep a b i) (hbc : IsStep b c k) :
    let z := Function.update a k (c k)
    IsStep a z k ∧ IsStep z c i ∧
      (u i b - u i a) + (u k c - u k b) =
        (u k z - u k a) + (u i c - u i z) := exchange u hfour a b c i k hik hab hbc
#print axioms solution
