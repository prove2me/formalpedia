-- Prove2me | solution 2 for OAI.C0Absorption.completedPairing_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:07:46.670982+00:00
-- url     : https://prove2.me/submissions/6c9fc7fb-0ce2-4647-a643-4af7df575449

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Duality.lean:L77-L91
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.completedPairing_add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.C0Absorption.Completion ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedSeminorms

open UniformSpace Completion

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

theorem completion_lipschitz {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {f : X → Y} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (Completion.extension f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x y =>
    simpa only [Completion.extension_coe hf.uniformContinuous, Completion.dist_eq] using hf.dist_le_mul x y

end CompletedSeminorms

section SelectedCompletion

open UniformSpace Completion

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end SelectedCompletion

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Pairings ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedPairing_lipschitz (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) :
    LipschitzWith K (completedPairing L o f) :=
  completion_lipschitz (initialPairing_lipschitz L o f K h)

end CompletedPairings

section FurtherDetectors

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end FurtherDetectors

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Duality ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section ClassDuality
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem pairing_add {S : Type*} [MetricSpace S]
    (f g : S → ℝ) (m : Molecule S) :
    pairing S (fun s => f s+g s) m = pairing S f m+pairing S g m := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, mul_add, Finsupp.sum, Finset.sum_add_distrib]

theorem BoundedTest.add {f g : S → ℝ} (hf : BoundedTest L o f) (hg : BoundedTest L o g) :
    BoundedTest L o (fun s => f s+g s) := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  refine ⟨K+A,fun m => ?_⟩
  erw [pairing_add]
  exact (abs_add_le _ _).trans ((add_le_add (hK m) (hA m)).trans_eq (by push_cast; ring))

theorem completedPairing_add (f g : S → ℝ) (hf : BoundedTest L o f) (hg : BoundedTest L o g)
    (z : TestSpace L o) : completedPairing L o (fun s => f s+g s) z =
      completedPairing L o f z+completedPairing L o g z := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  obtain ⟨B,hB⟩ := (BoundedTest.add L o ⟨K,hK⟩ ⟨A,hA⟩)
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (completedPairing_lipschitz L o _ B hB).continuous
      ((completedPairing_lipschitz L o _ K hK).continuous.add (completedPairing_lipschitz L o _ A hA).continuous)
  | ih m =>
    change completedPairing L o _ (toTestSpace L o m) = _
    erw [completedPairing_coe L o _ B hB, completedPairing_coe L o _ K hK,
      completedPairing_coe L o _ A hA]
    exact pairing_add f g m

end ClassDuality

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation
end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.completedPairing_add := @_root_.OAI.C0Absorption.completedPairing_add
