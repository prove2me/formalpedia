-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_norm_finiteField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:10.422916+00:00
-- url     : https://prove2.me/submissions/a768caf2-30eb-4ad9-a3d2-540c7a087afe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
namespace GlobalTheory.SimMult
theorem _root_.solution {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ t, σ t ≠ t) (ν : ℤ) (hν : (ν : k) ≠ 0) :
    ∃ c, c * σ c = ν := by
  classical
  by_cases h2 : (2 : k) = 0
  · refine ⟨1, ?_⟩
    rcases Int.even_or_odd' ν with ⟨m, rfl | rfl⟩
    · exact absurd (by push_cast; rw [h2, zero_mul]) hν
    · push_cast; rw [h2]; simp
  obtain ⟨t, ht⟩ := hne
  set s := t - σ t with hs
  have hs0 : s ≠ 0 := sub_ne_zero.2 ht.symm
  have hσs : σ s = -s := by rw [hs, map_sub, hσ]; ring
  let F : Subfield k := σ.eqLocusField (RingHom.id k)
  let : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := by
    intro h
    apply h2
    have h3 : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h])
    have := congrArg F.subtype h3
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  let D : F := ⟨s * s, by
    change σ (s * s) = s * s
    rw [map_mul, hσs]; ring⟩
  have hD : D ≠ 0 := fun h => mul_ne_zero hs0 hs0 (congrArg Subtype.val h)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2 - Polynomial.C (ν : F))
    (g := Polynomial.C (-D) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) _)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hD)) (FiniteField.odd_card_of_char_ne_two hF)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul] at hab
  have h4 := congrArg F.subtype hab
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_intCast, map_zero,
    Subfield.coe_subtype, D] at h4
  have ha : σ (a : k) = a := a.2
  have hb : σ (b : k) = b := b.2
  refine ⟨a + b * s, ?_⟩
  rw [map_add, map_mul, ha, hb, hσs]
  linear_combination h4
end GlobalTheory.SimMult
