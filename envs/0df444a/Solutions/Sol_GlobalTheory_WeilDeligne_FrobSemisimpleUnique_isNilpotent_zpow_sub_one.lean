-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.FrobSemisimpleUnique.isNilpotent_zpow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:14:18.634885+00:00
-- url     : https://prove2.me/submissions/9bd43217-4054-4226-9a64-dfc9b9e92690

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.FrobSemisimpleUnique
namespace GlobalTheory.WeilDeligne.FrobSemisimpleUnique
theorem _root_.solution {R : Type*} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (d : ℤ) : IsNilpotent (((u ^ d : Rˣ) : R) - 1) := by
  have hnat : ∀ n : ℕ, IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
    intro n
    rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  obtain ⟨n, rfl | rfl⟩ := d.eq_nat_or_neg
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    have h1 := hnat n
    generalize u ^ n = v at h1
    have h2 : ((v⁻¹ : Rˣ) : R) - 1 = -(((v⁻¹ : Rˣ) : R) * ((v : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [h2]
    refine (Commute.isNilpotent_mul_left ?_ h1).neg
    exact ((Commute.refl v).inv_left.units_val).sub_right (Commute.one_right _)
end GlobalTheory.WeilDeligne.FrobSemisimpleUnique
