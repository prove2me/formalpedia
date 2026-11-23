-- Prove2me | solution 1 for GlobalTheory.exists_sesquilinear_eq_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:34.148198+00:00
-- url     : https://prove2.me/submissions/461a869b-e2e8-4c61-aca8-e9a8c9b3ffce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) :
    ∃ h : (Fin r → E) →ₗ[E] (Fin r → E) →ₗ⋆[E] E, ∀ x y, h x y = herm G x y := by
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  refine ⟨LinearMap.mk₂'ₛₗ _ _ (herm G) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩
  · intro x x' y; simp [herm, add_mul, Finset.sum_add_distrib]
  · intro c x y; simp [herm, Finset.mul_sum, mul_assoc]
  · intro x y y'; simp [herm, hc, mul_add, Finset.sum_add_distrib]
  · intro c x y
    simp only [herm, hc, Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory
