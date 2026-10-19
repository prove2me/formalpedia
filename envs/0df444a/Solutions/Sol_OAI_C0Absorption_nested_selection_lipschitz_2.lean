-- Prove2me | solution 2 for OAI.C0Absorption.nested_selection_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:16:36.55286+00:00
-- url     : https://prove2.me/submissions/2e69cea5-df67-4c90-af28-6963c22426c1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Selection.lean:L108-L143
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.nested_selection_lipschitz. The node keeps its source
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
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Theorems.Thm_OAI_C0Absorption_nested_supports_signed_lipschitz

-- ---- from OAI.Analysis.C0Absorption.Selection ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology

theorem thin_sequence {r : ℕ → ℕ → Prop} (hr : ∀ i, ∀ᶠ j in atTop, r i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j, i < j → r (φ i) (φ j) := by
  have he (t : Set ℕ) (ht : t.Finite) : ∀ᶠ j in atTop, ∀ i ∈ t, i<j ∧ r i j :=
    (eventually_all_finite ht).mpr (fun i _ => (eventually_gt_atTop i).and (hr i))
  obtain ⟨φ,hφ⟩ := seq_of_forall_finite_exists (fun t ht => (he t ht).exists)
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_comm.mp hφ.1, forall_comm.mp hφ.2⟩

theorem choose_mono_sequence {P : ℕ → ℕ → Prop} (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, P i (φ i) := by
  have he (i j : ℕ) : ∃ k, j<k ∧ P i k := ((eventually_gt_atTop j).and (hP i)).exists
  choose next hn using he
  let φ : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun n prev => next (n+1) prev) n
  have hφs (n : ℕ) : φ (n+1) = next (n+1) (φ n) := rfl
  refine ⟨φ,strictMono_nat_of_lt_succ (fun n => ?_),?_⟩
  · rw [hφs]; exact (hn (n+1) (φ n)).1
  · intro i
    cases i with
    | zero => exact (hn 0 0).2
    | succ i => exact (hn (i+1) (φ i)).2

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem nested_selection_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (u b : ℕ → S → ℝ) (C : ℕ → Set S) (e : ℕ → ℝ)
    (K Kb : ℝ≥0) (hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith Kb (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x*b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x=e i)
    (hnest : ∀ i, ∀ᶠ j in atTop, tsupport (u j) ⊆ C i)
    (hsmall : Tendsto (fun i => |e i| *(Kb : ℝ)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (K+1) (fun x => ∑ i, ε i * (u (φ i) x*b (φ i) x)) := by
  have he (i : ℕ) : ∀ᶠ j in atTop, |e j| *(Kb : ℝ) ≤ (1/2 : ℝ)^(i+1) :=
    hsmall.eventually (eventually_le_nhds (by positivity))
  obtain ⟨ψ,hψ,heψ⟩ := choose_mono_sequence he
  obtain ⟨η,hη,hrel⟩ := thin_sequence (r := fun i j => tsupport (u (ψ j)) ⊆ C (ψ i))
    (fun i => hψ.tendsto_atTop.eventually (hnest (ψ i)))
  let φ := ψ ∘ η
  refine ⟨φ,hψ.comp hη,?_⟩
  have hprod (i : ℕ) : |e (φ i)| *(Kb : ℝ) ≤ (1/2 : ℝ)^(i+1) := by
    exact (heψ (η i)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.add_le_add_right (hη.id_le i) 1))
  intro n ε hε
  have hh := nested_supports_signed_lipschitz hS n
    (fun i : Fin n => u (φ i)) (fun i : Fin n => b (φ i))
    (fun i : Fin n => e (φ i)) (fun i : Fin n => C (φ i)) K
    (fun _ : Fin n => Kb) (fun i => hu _) (fun i => hb _) (fun i => hF _)
    (fun i => hC _) (fun i => hc _) (fun i j hij => hrel i j hij) ε hε
  apply hh.weaken
  refine add_le_add le_rfl ?_
  have hsum : (∑ i : Fin n, |e (φ i)| *(Kb : ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin n, (1/2 : ℝ)^(i.val+1) := Finset.sum_le_sum (fun i _ => hprod i)
      _ = ∑ i ∈ Finset.range n, (1/2 : ℝ)^(i+1) := (Finset.sum_range (fun i : ℕ => (1/2 : ℝ)^(i+1))).symm
      _ ≤ ∑' i : ℕ, (1/2 : ℝ)^(i+1) := Summable.sum_le_tsum _ (fun _ _ => by positivity) geometric_summable
      _ = 1 := geometric_tsum
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using hsum

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TagLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

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


theorem solution : type_of% @_root_.OAI.C0Absorption.nested_selection_lipschitz := @_root_.OAI.C0Absorption.nested_selection_lipschitz
