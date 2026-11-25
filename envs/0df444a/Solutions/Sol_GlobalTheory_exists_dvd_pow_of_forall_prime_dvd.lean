-- Prove2me | solution 1 for GlobalTheory.exists_dvd_pow_of_forall_prime_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:59.768503+00:00
-- url     : https://prove2.me/submissions/9e638748-008b-4629-a83d-69da58c317eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowMulMemRangeOfLocalDenominators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (a y : A) :
    y ≠ 0 → (∀ q, Prime q → q ∣ y → q ∣ a) → ∃ n : ℕ, y ∣ a ^ n := by
  refine UniqueFactorizationMonoid.induction_on_prime y ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _ _; exact ⟨0, hu.dvd⟩
  · intro z p hz hp ih _ h
    obtain ⟨n, hn⟩ := ih hz fun q hq hqz => h q hq (hqz.mul_left p)
    exact ⟨n + 1, by rw [pow_succ']; exact mul_dvd_mul (h p hp (dvd_mul_right _ _)) hn⟩
end GlobalTheory
