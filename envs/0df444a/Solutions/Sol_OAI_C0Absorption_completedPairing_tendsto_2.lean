-- Prove2me | solution 2 for OAI.C0Absorption.completedPairing_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:40:46.401105+00:00
-- url     : https://prove2.me/submissions/2dd5cd3b-aa39-4bde-9273-4ac1de9a9255

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Pairings.lean:L121-L143
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.completedPairing_tendsto. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_tendsto_of_dense_lipschitz

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

theorem pairing_tendsto {S : Type*} [MetricSpace S]
    (f : ℕ → S → ℝ) (g : S → ℝ)
    (h : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s)))
    (m : Molecule S) :
    Filter.Tendsto (fun n => pairing S (f n) m) Filter.atTop (nhds (pairing S g m)) := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum]
  exact tendsto_finsetSum _ (fun s _ => (h s).const_mul (m.val s))

theorem completedPairing_tendsto (f : ℕ → S → ℝ) (g : S → ℝ) (K : ℝ≥0)
    (hbound : ∀ n (m : PreSpace L o), |pairing S (f n) m| ≤ K * ‖m‖)
    (hpoint : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s))) :
    (∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖) ∧
    ∀ z : TestSpace L o,
      Filter.Tendsto (fun n => completedPairing L o (f n) z) Filter.atTop
        (nhds (completedPairing L o g z)) := by
  have hg : ∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖ := by
    intro m
    exact le_of_tendsto (pairing_tendsto f g hpoint (show Molecule S from m)).abs
      (Filter.Eventually.of_forall fun n => hbound n m)
  refine ⟨hg, ?_⟩
  intro z
  apply tendsto_of_dense_lipschitz (toTestSpace L o) Completion.denseRange_coe
    (fun n => completedPairing L o (f n)) (completedPairing L o g) K
    (fun n => completedPairing_lipschitz L o (f n) K (hbound n))
    (completedPairing_lipschitz L o g K hg) _ z
  intro m
  have heq : (fun n => completedPairing L o (f n) (toTestSpace L o m)) =
      (fun n => pairing S (f n) m) :=
    funext (fun n => completedPairing_coe L o (f n) K (hbound n) m)
  rw [heq, completedPairing_coe L o g K hg]
  exact pairing_tendsto f g hpoint m

end CompletedPairings

section FurtherDetectors

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end FurtherDetectors

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open UniformSpace Completion


theorem solution : type_of% @_root_.OAI.C0Absorption.completedPairing_tendsto := @_root_.OAI.C0Absorption.completedPairing_tendsto
