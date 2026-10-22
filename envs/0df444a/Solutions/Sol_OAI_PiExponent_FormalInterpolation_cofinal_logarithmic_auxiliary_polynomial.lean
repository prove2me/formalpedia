-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.cofinal_logarithmic_auxiliary_polynomial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T13:39:08.146985+00:00
-- url     : https://prove2.me/submissions/f5efcce6-9098-482d-8150-b9efdc9a2ac3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_simplex_cofinal_cardinality_gap
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_logarithmic_jet_kernel
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hvolume :
      (K : Real) * (1 + 3 * (sigma : Real)) ^ (m + 1) *
        (∏ i, (w i : Real)) / (∏ i, (v i : Real)) < 1) :
    ∀ N₀ : Nat, ∃ N : Nat, N₀ ≤ N ∧ 0 < N ∧
      ∃ F : MvPolynomial (Fin (m + 1)) Complex, F ≠ 0 ∧
        logarithmicDegreeBound w (N : Real) F ∧
        logarithmicJetBound c v ((1 + 3 * (sigma : Real)) * (N : Real)) F := by
  intro N₀
  have halpha : 0 < 1 + 3 * (sigma : Real) := by linarith
  obtain ⟨N, hN₀, hN, S, T, hS, hT, hcard⟩ :=
    weighted_simplex_cofinal_cardinality_gap (K := K) w v
      (1 + 3 * (sigma : Real)) (Nat.succ_pos m) halpha hw hv hvolume N₀
  obtain ⟨F, hF, hFS, hjet⟩ := finite_logarithmic_jet_kernel c S T hcard
  refine ⟨N, hN₀, hN, F, hF, ?_, ?_⟩
  · intro a ha
    exact (hS a).mp (hFS ha)
  · intro j a ha
    exact hjet j a ((hT a).mpr ha)
