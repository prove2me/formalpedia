-- Prove2me | solution 1 for GlobalTheory.JointModelGuards.exists_root_and_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:58.453832+00:00
-- url     : https://prove2.me/submissions/e6e7374e-3fc7-4b85-a103-da1e52927082

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfEqMulInvPow
import Theorems.Thm_GlobalTheory_JointModelGuards_mem_of_eq_mul_inv_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.JointModelGuards
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.JointModelGuards
theorem _root_.solution (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by simpa using this)
  have hrW : H.rt0 ∈ W := mem_of_eq_mul_inv_pow W (a := -(H.d : ℂ)) (neg_mem (natCast_mem W _)) 1 (by
    rw [← H.sqrt_neg_disc_sq]; field_simp)
  have hp : IsPrimitiveRoot (zeta l.A) l.A := Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
  have hz0 : zeta l.A ≠ 0 := hp.ne_zero l.A_pos.ne'
  have hzW : zeta l.A ∈ W := mem_of_eq_mul_inv_pow W (a := 1) (one_mem W) (l.A - 1) (by
    have h1 : zeta l.A * zeta l.A ^ (l.A - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel l.A_pos]; exact hp.pow_eq_one
    rw [one_mul, inv_pow]
    exact eq_inv_of_mul_eq_one_left h1)
  exact ⟨⟨⟨_, hr⟩, hrW⟩, ⟨⟨_, hz⟩, hzW⟩, rfl, rfl⟩
end GlobalTheory.JointModelGuards
