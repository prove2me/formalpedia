-- Prove2me | solution 1 for OAI.MatchingEntropy.jointLaw_first
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:09.540587+00:00
-- url     : https://prove2.me/submissions/76e38b26-b842-4cce-864b-2538fe0da7be

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Coupling.lean:L48-L66
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.jointLaw_first. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling

-- ---- from OAI.Combinatorics.PerfectMatching.Coupling ----
namespace OAI

/-!
Finite pushforwards and couplings with a prescribed common marginal.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

theorem le_fiberMass_self {A C : Type*} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (a : A) :
    p a ≤ fiberMass p f (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b => if f b = f a then p b else 0)
    (by intro b _; split <;> simp_all) (Finset.mem_univ a)
  simpa only [fiberMass, ite_true] using h

theorem jointLaw_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (a : A) : (∑ b, jointLaw p q f g (a,b)) = p a := by
  have heq : ∀ b, jointLaw p q f g (a,b) =
      (p a / fiberMass p f (f a)) * (if g b=f a then q b else 0) := by
    intro b
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true]
      ring
    · simp [jointLaw, h, Ne.symm h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change p a / fiberMass p f (f a) * fiberMass q g (f a) = p a
  rw [← hcompat]
  by_cases hz : fiberMass p f (f a) = 0
  · have ha : p a = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hp f a) (hp a)
    simp [ha]
  · exact div_mul_cancel₀ _ hz

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter

theorem solution {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (a : A) : (∑ b, jointLaw p q f g (a,b)) = p a := by
  first
    | exact OAI.MatchingEntropy.jointLaw_first hp f g hcompat a
    | exact OAI.MatchingEntropy.jointLaw_first
    | (apply OAI.MatchingEntropy.jointLaw_first <;> assumption)
    | (intros; apply OAI.MatchingEntropy.jointLaw_first <;> assumption)
