-- Prove2me | solution 1 for GlobalTheory.PelPrim.cmHostUnit_add_conj_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:17:29.781867+00:00
-- url     : https://prove2.me/submissions/76b10a44-d8f6-439f-89a5-d07cbb2ff720

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PelObjectClassPrimAndIsoClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.PelPrim
namespace GlobalTheory.PelPrim
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : 0 < H.d := H.d_prime.pos
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have h2 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have e := H.bar_eq H.rt
      rw [h] at e
      have e2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj, ← e]
      have e3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
      rw [hr] at e3
      have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
      have : (0 : ℝ) < H.d := by exact_mod_cast hd
      nlinarith [sq_nonneg r]
    · exact h
  have h3 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, h2, map_ofNat] at this
    rw [this]; ring
  have h4 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, h3, H.two_weight_eq_one_add_root]; ring
  exact mul_left_cancel₀ two_ne_zero h4
end GlobalTheory.PelPrim
