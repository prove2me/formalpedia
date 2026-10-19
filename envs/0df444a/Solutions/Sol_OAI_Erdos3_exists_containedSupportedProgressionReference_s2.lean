-- Prove2me | solution 1 for OAI.Erdos3.exists_containedSupportedProgressionReference_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:54:11.341983+00:00
-- url     : https://prove2.me/submissions/6bd409c8-0a5b-4ec7-909f-f8c338345bcb

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_residue_eq_s2
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_restrict_weight_pos_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

theorem containedProgressionCubeMap_cube (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) :
    IntegerScalarCube L (fun i => (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ)) := by
  by_cases hz : IntegerScalarCube H (fun i => (z i : ℤ))
  · simp_rw [containedProgressionCubeMap_value I L H step c hL hsubset z hz]
    exact integerScalarCube_progression c hsubset _ hz
  · simp only [containedProgressionCubeMap, dif_neg hz]
    intro t
    simp only [integerScalarCubeValue, Finset.sum_const_zero, add_zero]
    exact ⟨le_rfl, Nat.cast_pos.mpr hL⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteGoodSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem mean_congr_on_support {f g : X → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.mean f = p.mean g :=
  le_antisymm (p.mean_mono_on_support (fun x hx => (h x hx).le))
    (p.mean_mono_on_support (fun x hx => (h x hx).ge))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteFiberLawSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem fiberLaw_support {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (P : Y → Prop)
    (hP : ∀ x, p.weight x ≠ 0 → P (F x))
    (y : Y) (hy : (p.fiberLaw F).weight y ≠ 0) : P y := by
  classical
  by_contra hn
  apply hy
  change p.mean (fun x => if F x = y then (1 : ℝ) else 0) = 0
  calc
    _ = p.mean (fun _ => 0) := by
      apply p.mean_congr_on_support
      intro x hx
      apply if_neg
      intro he
      exact hn (he ▸ hP x hx)
    _ = 0 := p.mean_const 0

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ContainedSupportedProgressionReference
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_cube_support
    (y : PrincipalIntegerTuples B h α L) (hy : (law).weight y ≠ 0)
    (j : PrincipalTupleIndex B h) : IntegerScalarCube (L j) (fun a => (y j a : ℤ)) := by
  apply FiniteProbabilityWeights.fiberLaw_support _
    (containedProgressionTupleMap B h L H step c hL hsubset)
    (fun y => IntegerScalarCube (L j) (fun a => (y j a : ℤ))) _ y hy
  intro z _
  exact containedProgressionCubeMap_cube α _ _ _ _ _ _ (z j)

theorem exists_containedSupportedProgressionReference_s2_oai :
    ∃ y₀ : PrincipalIntegerTuples B h α L,
      0 < (law).weight y₀ ∧
      (∀ j, IntegerScalarCube (L j) (fun a => (y₀ j a : ℤ))) ∧
      (∀ P : D → Prop,
        0 < (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight
          (principalAxisRestrict P y₀)) ∧
      (∀ y, (law).weight y ≠ 0 → principalResidueLabel q y = principalResidueLabel q y₀) := by
  obtain ⟨y₀, hy₀⟩ := (law).exists_weight_pos
  refine ⟨y₀, hy₀, ?_, ?_, ?_⟩
  · exact containedSupportedProgressionLaw_cube_support B h L H step c hL hH hsubset q r hcell y₀ hy₀.ne'
  · exact containedSupportedProgressionLaw_restrict_weight_pos_s2 B h L H step c hL hH hsubset q r hcell y₀ hy₀
  · intro y hy
    exact containedSupportedProgressionLaw_residue_eq_s2 B h L H step c hL hH hsubset q r hcell y y₀ hy hy₀.ne'

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.exists_containedSupportedProgressionReference_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.exists_containedSupportedProgressionReference_s2_oai.{u_1, u_2, u_3}
