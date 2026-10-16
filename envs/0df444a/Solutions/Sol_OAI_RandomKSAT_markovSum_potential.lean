-- Prove2me | solution 1 for OAI.RandomKSAT.markovSum_potential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:04:27.435279+00:00
-- url     : https://prove2.me/submissions/888d9e02-a566-4722-944b-28086471bffd

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/LifetimePotential.lean:L60-L78
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.markovSum_potential. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential

-- ---- from OAI.Probability.SATVariance.LifetimePotential ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma markovSum_potential.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i, Monotone (P i))
    (hPc : ∀ i f c, P i (fun x => f x+c) = fun x => P i f x+c)
    (f τ : X → ℝ) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ)
    (hdrift : ∀ i x, f x + P i τ x ≤ τ x + z i) (m : ℕ) (x : X) :
    markovSum P f m x ≤ τ x + ∑ i ∈ Finset.range m, z i := by
  induction m generalizing P z x with
  | zero => simpa [markovSum] using hτ x
  | succ m ih =>
    have hi := hP 0 (fun y => ih (fun i => P (i+1)) (fun i => hP (i+1))
      (fun i => hPc (i+1)) (fun i => z (i+1)) (fun i => hdrift (i+1)) y)
    rw [hPc] at hi
    calc
      markovSum P f (m+1) x ≤ f x +
          (P 0 τ x + ∑ i ∈ Finset.range m, z (i+1)) := by
        change f x + P 0 (markovSum (fun i => P (i+1)) f m) x ≤ _
        linarith [hi x]
      _ ≤ τ x + z 0 + ∑ i ∈ Finset.range m, z (i+1) := by linarith [hdrift 0 x]
      _ = _ := by rw [Finset.sum_range_succ']; ring

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.markovSum_potential := @_root_.OAI.RandomKSAT.markovSum_potential
