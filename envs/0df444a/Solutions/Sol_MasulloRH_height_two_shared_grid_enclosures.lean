-- Prove2me | solution 1 for MasulloRH.height_two_shared_grid_enclosures
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:51:08.25946+00:00
-- url     : https://prove2.me/submissions/1b82b089-b4c9-4616-a9ea-df2041301372
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_height_two_central_grid_enclosures
import Theorems.Thm_MasulloRH_theta_norm_le_dyadic_on_tails
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation
open scoped BigOperators
set_option autoImplicit false

theorem solution :
    let h : ℝ := 1/8192
    let e (k : ℤ) := -4 + (k : ℝ) * h
    let s : Fin 11 → ℤ := ![-3072,-2048,1024,3072,6144,8192,11264,14336,16384,18432,19456]
    ∃ (P R W : ℕ → ℚ) (T U : ℤ → ℚ),
      (∀ (j : ℕ), j < 65536 → 0 ≤ (W j : ℝ) ∧ ∀ x ∈ Icc (e j) (e ((j : ℤ)+1)),
        ‖pulse 2 x - (P j : ℂ)‖ ≤ (R j : ℝ) ∧
          Real.exp (2*(3/4)*x + 2*(11/48)*|x|) ≤ (W j : ℝ)) ∧
      (∀ (j : ℕ), j < 65536 → ∀ i : Fin 11, ∀ z ∈ Icc (e ((j : ℤ)-s i)) (e ((j : ℤ)-s i+1)),
        ‖theta z - (T ((j : ℤ)-s i) : ℂ)‖ ≤ (U ((j : ℤ)-s i) : ℝ)) ∧
      (let A (j : ℕ) := ‖(P j : ℂ) - ∑ i, HeightTwoWitness.coeffs i * (T ((j : ℤ)-s i) : ℂ)‖ +
          ((R j : ℝ) + ∑ i, ‖HeightTwoWitness.coeffs i‖ * (U ((j : ℤ)-s i) : ℝ))
       ∑ j ∈ Finset.range 65536, h * ((W j : ℝ) * A j ^ 2) ≤ 1/100) := by
  intro h e s
  obtain ⟨P,R,W,C,D,hp,ht,hs⟩ := MasulloRH.height_two_central_grid_enclosures
  let T (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 0 else C k
  let U (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 1/(2:ℚ)^64 else D k
  refine ⟨P,R,W,T,U,hp,?_,hs⟩
  intro j _ i z hz
  let k := (j : ℤ) - s i
  change e k ≤ z ∧ z ≤ e (k+1) at hz
  change ‖theta z - (T k : ℂ)‖ ≤ (U k : ℝ)
  by_cases hk : k < 8192 ∨ 45056 ≤ k
  · have htail : z ≤ -3 ∨ 3/2 ≤ z := by
      rcases hk with hl | hr
      · left
        have hidx : (k:ℝ)+1 ≤ 8192 := by exact_mod_cast (show k+1 ≤ 8192 by omega)
        have hb := hz.2
        dsimp [e,h] at hb
        push_cast at hb
        linarith
      · right
        have hidx : 45056 ≤ (k:ℝ) := by exact_mod_cast hr
        have hb := hz.1
        dsimp [e,h] at hb
        linarith
    simpa [T,U,hk] using MasulloRH.theta_norm_le_dyadic_on_tails z htail
  · simpa [T,U,hk] using ht k (by omega) (by omega) z hz
