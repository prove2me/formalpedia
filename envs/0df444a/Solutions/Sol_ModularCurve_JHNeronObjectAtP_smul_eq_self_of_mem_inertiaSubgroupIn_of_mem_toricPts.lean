-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/fb01da64-40bb-59fe-a5bf-9171525cae7e

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

import Theorems.Thm_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicCurve

open scoped MatrixGroups

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JHNeronObjectAtP

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hmp : m.Coprime p) :
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

  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨χ, rfl⟩ := hx
    have h := O.toricLift_inertia m hm σ hσ 1 (fun ζ hζ => by rw [pow_one]; exact hμ ζ hζ) χ
    simpa only [JHNeronObjectAtP.toricPoint, one_smul] using h
  | zero => exact smul_zero (A := JH M H) σ
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

end S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts (solution)
