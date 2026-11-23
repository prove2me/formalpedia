-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.block_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:56.282022+00:00
-- url     : https://prove2.me/submissions/60ddc01c-11ca-46b7-a92e-89ab8514160d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Gauss
open GlobalTheory.CompanionTheory.Iwahori
variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}
namespace GlobalTheory.CompanionTheory.Iwahori.Gauss
theorem _root_.solution (hP : IsPieces P) (u x y v : E) :
    u * (x * y) * v = ∑ l, (u * x * P l) * (P l * y * v) := by
  have h : ∀ l, (u * x * P l) * (P l * y * v) = u * x * (P l) * y * v := by
    intro l
    calc (u * x * P l) * (P l * y * v) = u * x * (P l * P l) * y * v := by
          simp only [mul_assoc]
      _ = _ := by rw [hP.idem]
  simp_rw [h]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hP.sum]
  simp only [mul_one, mul_assoc]
end GlobalTheory.CompanionTheory.Iwahori.Gauss
