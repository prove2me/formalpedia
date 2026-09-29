-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.smul_eq_nsmul_of_mem_toricPts_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2781dd82-d052-5f04-9411-056c1c5d36ce

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_nsmul_of_mem_toricPts_of_mem_inertiaSubgroupIn

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (c : ℕ) (hc : ∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) :
    ∀ x ∈ O.toricPts m, σ • x = c • x := by

  have key : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      σ • O.toricPoint m hm χ = c • O.toricPoint m hm χ :=
    fun χ => O.toricLift_inertia m hm σ hσ c hc χ

  intro x hx
  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx
  let f : JH M H →+ JH M H := DistribSMul.toAddMonoidHom (JH M H) σ
  let g : JH M H →+ JH M H := nsmulAddMonoidHom c
  have hle : AddSubgroup.closure (Set.range (O.toricPoint m hm)) ≤ f.eqLocus g :=
    (AddSubgroup.closure_le _).mpr (by
      rintro _ ⟨χ, rfl⟩
      exact key χ)
  exact hle hx

end S_ModularCurve_JHNeronObjectAtP_smul_eq_nsmul_of_mem_toricPts_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_nsmul_of_mem_toricPts_of_mem_inertiaSubgroupIn (solution)
