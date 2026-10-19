-- Prove2me | solution 1 for OAI.Release075.exists_alteration_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:27:57.677341+00:00
-- url     : https://prove2.me/submissions/a8795697-cd6f-485d-a5cc-6d2a4f0502ba

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L687-L728
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.exists_alteration_budget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_expect_lowDegree_le

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Existence from a strict finite average bound, without measure-theoretic null sets. -/
theorem exists_of_expect_lt {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (a : ℝ) (h : (𝔼 ω, X ω) < a) : ∃ ω, X ω < a := by
  obtain ⟨ω,_,hω⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty h
  exact ⟨ω,hω⟩

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Each geometric line contains exactly |K| points. -/
theorem lineMap_injective (a : V) (d : Projectivization K V) :
    Function.Injective (fun t : K => a + t • d.rep) := by
  intro t u h
  exact smul_left_injective K d.rep_nonzero (add_left_cancel h)

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

omit [Fintype V] in
theorem chosenLinePoints_card (a : V) (d : Projectivization K V) :
    (chosenLinePoints a d).card = Fintype.card K := by
  exact (Finset.card_image_iff.mpr (lineMap_injective a d).injOn).trans (Finset.card_univ)

theorem deletedPoints_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedPoints S ω).card ≤ Fintype.card K * (deletedMarks S ω).card := by
  apply Finset.card_biUnion_le.trans
  simp only [chosenLinePoints_card,Finset.sum_const,nsmul_eq_mul, Nat.cast_id]
  exact le_of_eq (Nat.mul_comm _ _)

theorem exceptionalPoints_card_le (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) :
    (exceptionalPoints S ω T).card ≤
      (Finset.univ.filter (fun z => pointDegree S ω z < T)).card +
        Fintype.card K * (deletedMarks S ω).card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (deletedPoints_card_le S ω) _)

theorem retained_card (S : Finset V) (ω : S → Projectivization K V) :
    Fintype.card (Retained S ω) = S.card - (deletedMarks S ω).card := by
  change Fintype.card {a : S // ¬ a ∈ deletedMarks S ω} = _
  rw [Fintype.card_subtype_compl]
  simp
end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

/-- One finite averaging step obtains simultaneously the strict rank budget,
the degree bound, and the cycle-free alteration; no asymptotic or external
probabilistic result is being assumed. -/
theorem exists_alteration_budget (S : Finset V) (r T : ℕ) (μ B : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z)
    (hdel : (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ B)
    (hbudget : 8 * (Fintype.card V : ℝ) + 16*r*(Fintype.card V : ℝ)/μ +
        r*(4*(Fintype.card K : ℝ)+1)*B < (S.card : ℝ)*r) :
    ∃ ω : S → Projectivization K V,
      4 * (2 * Fintype.card V + r * (exceptionalPoints S ω T).card) <
        Fintype.card (Retained S ω) * r := by
  let cost : (S → Projectivization K V) → ℝ := fun ω =>
    4*r*((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ) +
    r*(4*(Fintype.card K : ℝ)+1)*((deletedMarks S ω).card : ℝ)
  have hexp : (𝔼 ω, cost ω) ≤ 16*r*(Fintype.card V : ℝ)/μ +
      r*(4*(Fintype.card K : ℝ)+1)*B := by
    simp only [cost, Finset.expect_add_distrib, ← Finset.mul_expect]
    have hlow := expect_lowDegree_le (K := K) S T μ hμ hT hlower
    have h₁ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4*(r : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hdel
      (show 0 ≤ (r : ℝ)*(4*(Fintype.card K : ℝ)+1) by positivity)
    convert add_le_add h₁ h₂ using 2 <;> first | rfl | ring
  obtain ⟨ω,hω⟩ := exists_of_expect_lt cost ((S.card : ℝ)*r - 8*Fintype.card V)
    (hexp.trans_lt (by linarith))
  refine ⟨ω,?_⟩
  have hE := exceptionalPoints_card_le S ω T
  have hD : (deletedMarks S ω).card ≤ S.card :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
  have hN := retained_card S ω
  have hN' : (Fintype.card (Retained S ω) : ℝ) = S.card - (deletedMarks S ω).card := by
    rw [hN, Nat.cast_sub hD]
  have hE' : ((exceptionalPoints S ω T).card : ℝ) ≤
      (Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card +
      (Fintype.card K : ℝ) * (deletedMarks S ω).card := by exact_mod_cast hE
  have hEm := mul_le_mul_of_nonneg_left hE' (show 0 ≤ 4*(r : ℝ) by positivity)
  have hh : 4 * (2 * (Fintype.card V : ℝ) + r*(exceptionalPoints S ω T).card) <
      (Fintype.card (Retained S ω) : ℝ) * r := by
    dsimp [cost] at hω
    rw [hN']
    nlinarith
  exact_mod_cast hh
end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.exists_alteration_budget := @_root_.OAI.Release075.exists_alteration_budget
