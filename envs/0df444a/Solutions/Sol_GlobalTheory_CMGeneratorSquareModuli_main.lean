-- Prove2me | solution 1 for GlobalTheory.CMGeneratorSquareModuli.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:44.581267+00:00
-- url     : https://prove2.me/submissions/6d0cf98b-176d-43d8-8982-7909a4cd85c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmGeneratorSqQuadraticEq
import Theorems.Thm_GlobalTheory_CMGeneratorSquareModuli_cm_generator_sq_quadratic_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMGeneratorSquareModuli
open NumberField
namespace GlobalTheory.CMGeneratorSquareModuli
theorem _root_.solution : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E},
    a ∈ Algebra.adjoin ℤ ({ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H} : Set (NumberField.RingOfIntegers E)) →
    ∃ u v : ℤ, a = (u : NumberField.RingOfIntegers E) + (v : NumberField.RingOfIntegers E) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  obtain ⟨k, hk⟩ := cm_generator_sq_quadratic_eq H
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    exact ⟨u1 + u2, v1 + v2, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    refine ⟨u1 * u2 - v1 * v2 * k, u1 * v2 + u2 * v1 + v1 * v2, ?_⟩
    push_cast
    linear_combination ((v1 : NumberField.RingOfIntegers E) * v2) * hk
end GlobalTheory.CMGeneratorSquareModuli
