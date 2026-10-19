-- Prove2me | solution 1 for OAI.C0Absorption.completedPairing_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:25:18.467439+00:00
-- url     : https://prove2.me/submissions/088b4e34-b642-4f76-b264-19f2ec83c824

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)


theorem solution (f g : S → ℝ) (hf : BoundedTest L o f) (hg : BoundedTest L o g)
    (z : TestSpace L o) : completedPairing L o (fun s => f s+g s) z =
      completedPairing L o f z+completedPairing L o g z := by
  obtain ⟨Kf, hKf⟩ := hf
  obtain ⟨Kg, hKg⟩ := hg
  have hfg : ∀ m : PreSpace L o, |pairing S (fun s => f s + g s) m| ≤ (Kf + Kg) * ‖m‖ := by
    intro m
    have e : pairing S (fun s => f s + g s) m = pairing S f m + pairing S g m := by
      show (Finsupp.linearCombination ℝ (fun s => f s + g s)) (show Molecule S from m).val =
        Finsupp.linearCombination ℝ f (show Molecule S from m).val +
          Finsupp.linearCombination ℝ g (show Molecule S from m).val
      simp only [Finsupp.linearCombination_apply, smul_eq_mul, mul_add, Finsupp.sum_add]
    rw [e]
    calc |pairing S f m + pairing S g m| ≤ |pairing S f m| + |pairing S g m| := abs_add_le _ _
      _ ≤ Kf * ‖m‖ + Kg * ‖m‖ := add_le_add (hKf m) (hKg m)
      _ = ((Kf + Kg : ℝ≥0) : ℝ) * ‖m‖ := by push_cast; ring
  have e : ∀ m : PreSpace L o, pairing S (fun s => f s + g s) m = pairing S f m + pairing S g m := by
    intro m
    show (Finsupp.linearCombination ℝ (fun s => f s + g s)) (show Molecule S from m).val =
      Finsupp.linearCombination ℝ f (show Molecule S from m).val +
        Finsupp.linearCombination ℝ g (show Molecule S from m).val
    simp only [Finsupp.linearCombination_apply, smul_eq_mul, mul_add, Finsupp.sum_add]
  refine UniformSpace.Completion.induction_on (p := fun z : UniformSpace.Completion (PreSpace L o) =>
      completedPairing L o (fun s => f s + g s) z = completedPairing L o f z + completedPairing L o g z) z ?_ ?_
  · exact isClosed_eq UniformSpace.Completion.continuous_extension
      (UniformSpace.Completion.continuous_extension.add UniformSpace.Completion.continuous_extension)
  · intro m
    have h1 := completedPairing_coe L o f Kf hKf m
    have h2 := completedPairing_coe L o g Kg hKg m
    have h3 := completedPairing_coe L o (fun s => f s + g s) (Kf + Kg) hfg m
    change completedPairing L o (fun s => f s + g s) (toTestSpace L o m) =
      completedPairing L o f (toTestSpace L o m) + completedPairing L o g (toTestSpace L o m)
    rw [h1, h2, h3, e]

