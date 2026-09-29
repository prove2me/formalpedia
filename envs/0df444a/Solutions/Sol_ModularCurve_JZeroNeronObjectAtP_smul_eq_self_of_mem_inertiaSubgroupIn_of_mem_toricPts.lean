-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/5687bac8-592c-5e03-b6d8-12fa5f83c532

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ToricMonodromyPart

import Theorems.Thm_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hmp : m.Coprime p) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y ∈ O.toricPts m, σ • y = y := by
  intro σ hσ y hy
  have hp : p.Prime := Fact.out
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (Nat.coprime_zero_left _ |>.mp hmp) hp.ne_one
    · exact h
  have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp).mp hmp.symm

  obtain ⟨hfix, -⟩ :=
    ValuationSubring.exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
      p hp 0 m hpm A hA
  obtain ⟨-, -, hμ⟩ := hfix σ hσ

  rw [toricPts, dif_pos hm] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨χ, rfl⟩ := hx
    have h := O.toricLift_inertia m hm σ hσ 1 (fun ζ hζ => by rw [pow_one]; exact hμ ζ hζ) χ
    simpa only [toricPoint, one_smul] using h
  | zero => exact smul_zero (A := JZero (N₀ * p)) σ
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

#print axioms solution

end S_ModularCurve_JZeroNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts (solution)
