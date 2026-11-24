-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:45:28.157877+00:00
-- url     : https://prove2.me/submissions/a9cd1d0f-73d3-49d9-9a74-c52bc18a4d72

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.TorusConj
namespace GlobalTheory.CompanionTheory.Iwahori.TorusConj
theorem _root_.solution {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    {P : ι → E} (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) {J : AddSubgroup E}
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J)
    {S S' : E} {σ ρ : ι → L} (hS : ∀ i, P i * S = σ i • P i)
    (hS' : ∀ j, S' * P j = ρ j • P j) (hSS : S * S' = 1) {a : E} (ha : a - 1 ∈ J)
    (h : ∀ i j, ‖σ i * ρ j‖ ≤ 1 ∨ (i ≠ j ∧ P i * a * P j = 0)) :
    S * a * S' - 1 ∈ J := by
  have e1 : S * a * S' - 1 = ∑ i, ∑ j, P i * (S * (a - 1) * S') * P j := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hP.sum]
    simp [mul_sub, sub_mul, hSS]
  rw [e1]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have e2 : P i * (S * (a - 1) * S') * P j = (σ i * ρ j) • (P i * (a - 1) * P j) := by
    calc P i * (S * (a - 1) * S') * P j = (P i * S) * (a - 1) * (S' * P j) := by
          simp only [mul_assoc]
      _ = (σ i * ρ j) • (P i * (a - 1) * P j) := by
          rw [hS, hS']
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          rw [mul_comm]
  rw [e2]
  rcases h i j with hn | ⟨hij, hz⟩
  · exact hc _ hn _ (hJ.right_mem j _ (hJ.left_mem i _ ha))
  · have : P i * (a - 1) * P j = 0 := by
      rw [mul_sub, sub_mul, hz, mul_one, hP.orth i j hij, sub_zero]
    rw [this, smul_zero]
    exact J.zero_mem
end GlobalTheory.CompanionTheory.Iwahori.TorusConj
