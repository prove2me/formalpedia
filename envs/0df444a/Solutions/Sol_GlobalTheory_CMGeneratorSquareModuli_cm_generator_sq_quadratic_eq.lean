-- Prove2me | solution 1 for GlobalTheory.CMGeneratorSquareModuli.cm_generator_sq_quadratic_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:04:01.48233+00:00
-- url     : https://prove2.me/submissions/6e6e52b7-a6d2-4610-9918-78cf3fe9cf7d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmGeneratorSqQuadraticEq

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ k : ℤ, H.w0 * H.w0 = H.w0 - (k : NumberField.RingOfIntegers E) := by
  have hm := H.d_mod
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (H.d : ℤ) + 1 = 4 * k := ⟨((H.d : ℤ) + 1) / 4, by omega⟩
  refine ⟨k, ?_⟩
  have hkc : (H.d : NumberField.RingOfIntegers E) + 1 = 4 * (k : NumberField.RingOfIntegers E) := by
    have := congrArg (fun z : ℤ => (z : NumberField.RingOfIntegers E)) hk
    push_cast at this
    exact this
  have h4 : (4 : NumberField.RingOfIntegers E) * (H.w0 * H.w0 - (H.w0 - (k : NumberField.RingOfIntegers E))) = 0 := by
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hkc
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · exact sub_eq_zero.mp h
end GlobalTheory.CMGeneratorSquareModuli
