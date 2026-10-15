-- Prove2me | solution 1 for OAI.BufferedIsing.pairTable_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:47:39.007105+00:00
-- url     : https://prove2.me/submissions/d1f47792-6ff1-4a4c-8bfc-b2d2db42112f

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Contraction.lean:L134-L152
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.pairTable_quotient. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction

-- ---- from OAI.Probability.Ising.Colorings ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma sum_if_respects {V : Type*} [Fintype V] [DecidableEq V] (S : Setoid V) (f : (V → Bool) → ℝ) :
    (∑ σ, if Respects S σ then f σ else 0) = ∑ σ : Colorings S, f σ.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma pairTable_quotient {V : Type*} [Fintype V] [DecidableEq V]
    (S : Setoid V) (W : (V → Bool) → ℝ) (u v : V) (s t : Bool) :
    pairTable (fun σ => if Respects S σ then W σ else 0) u v s t =
      pairTable (fun c : Quotient S → Bool => W (fun x => c (Quotient.mk S x)))
        (Quotient.mk S u) (Quotient.mk S v) s t := by
  classical
  unfold pairTable
  calc
    _ = ∑ σ, if Respects S σ then
        (if σ u = s ∧ σ v = t then W σ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hR : Respects S σ <;> by_cases hT : σ u = s ∧ σ v = t <;> simp [hR, hT]
    _ = ∑ σ : Colorings S, if σ.val u = s ∧ σ.val v = t then W σ.val else 0 :=
      sum_if_respects S _
    _ = _ := by
      rw [Fintype.sum_equiv (componentColoringEquiv S)]
      · intro σ
        rfl

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (S : Setoid V) (W : (V → Bool) → ℝ) (u v : V) (s t : Bool) :
    pairTable (fun σ => if Respects S σ then W σ else 0) u v s t =
      pairTable (fun c : Quotient S → Bool => W (fun x => c (Quotient.mk S x)))
        (Quotient.mk S u) (Quotient.mk S v) s t := by
  first
    | exact OAI.BufferedIsing.pairTable_quotient S W u v s t
    | exact OAI.BufferedIsing.pairTable_quotient
    | (apply OAI.BufferedIsing.pairTable_quotient <;> assumption)
    | (intros; apply OAI.BufferedIsing.pairTable_quotient <;> assumption)
