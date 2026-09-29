-- Prove2me | solution 1 for HorizontalPadicL.horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:55:16.098379+00:00
-- url     : https://prove2.me/submissions/c285d6b1-6f6f-495c-8bc7-1b9aad0c88fb

import Definitions.Def_KN_SeededThetaConstructionV2B
import Theorems.Thm_MonoidAlgebra_isUnit_iff_augmentation_of_isPGroup_v2
import Theorems.Thm_HorizontalPadicL_horizontalFiniteGroup_isPGroup_v2
import Theorems.Thm_PadicComplexInt_natCast_prime_mem_maximalIdeal_v2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The standard unit criterion for a group algebra of a finite `p`-group over
the valuation ring of `ℂ_p`: an element is a unit if its augmentation is a unit.
For the explicit horizontal group, being a unit in the coefficient ring is
equivalent to the displayed norm-one condition. -/
theorem _root_.solution
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ)
    (x : HorizontalGroupAlgebra (𝓞_ℂ_[p]).toSubring p m A)
    (haug :
      ‖((horizontalAugmentation x : (𝓞_ℂ_[p]).toSubring) : ℂ_[p])‖ = 1) :
    IsUnit x := by
  let e := ValuationSubring.subtypeToSubringEquiv (𝓞_ℂ_[p])
  let E := MonoidAlgebra.mapRingEquiv (HorizontalFiniteGroup p m A) e
  have hhom :
      e.toRingHom.comp (MonoidAlgebra.augmentation (𝓞_ℂ_[p]).toSubring
        (HorizontalFiniteGroup p m A)) =
      (MonoidAlgebra.augmentation (𝓞_ℂ_[p])
        (HorizontalFiniteGroup p m A)).comp E.toRingHom := by
    apply MonoidAlgebra.ringHom_ext <;> intro y
    · simp only [RingHom.coe_comp, Function.comp_apply]
      dsimp only [E]
      change e (MonoidAlgebra.augmentation (𝓞_ℂ_[p]).toSubring
          (HorizontalFiniteGroup p m A) (MonoidAlgebra.single 1 y)) =
        MonoidAlgebra.augmentation (𝓞_ℂ_[p]) (HorizontalFiniteGroup p m A)
          ((MonoidAlgebra.mapRingEquiv (HorizontalFiniteGroup p m A) e)
            (MonoidAlgebra.single 1 y))
      rw [MonoidAlgebra.mapRingEquiv_single]
      simp [e, E, MonoidAlgebra.augmentation]
    · simp only [RingHom.coe_comp, Function.comp_apply]
      dsimp only [E]
      change e (MonoidAlgebra.augmentation (𝓞_ℂ_[p]).toSubring
          (HorizontalFiniteGroup p m A) (MonoidAlgebra.single y 1)) =
        MonoidAlgebra.augmentation (𝓞_ℂ_[p]) (HorizontalFiniteGroup p m A)
          ((MonoidAlgebra.mapRingEquiv (HorizontalFiniteGroup p m A) e)
            (MonoidAlgebra.single y 1))
      rw [MonoidAlgebra.mapRingEquiv_single]
      simp [e, E, MonoidAlgebra.augmentation]
  have hcomm :
      e (MonoidAlgebra.augmentation (𝓞_ℂ_[p]).toSubring
        (HorizontalFiniteGroup p m A) x) =
      MonoidAlgebra.augmentation (𝓞_ℂ_[p])
        (HorizontalFiniteGroup p m A) (E x) := by
    exact DFunLike.congr_fun hhom x
  rw [← MulEquiv.isUnit_map E]
  rw [MonoidAlgebra.isUnit_iff_augmentation_of_isPGroup_v2
    (PadicComplexInt.natCast_prime_mem_maximalIdeal_v2 p)
    (horizontalFiniteGroup_isPGroup_v2 m A)]
  rw [(PadicComplexInt.integers p).isUnit_iff_valuation_eq_one]
  rw [← hcomm]
  change Valued.v
    (((MonoidAlgebra.augmentation (𝓞_ℂ_[p]).toSubring
      (HorizontalFiniteGroup p m A) x : (𝓞_ℂ_[p]).toSubring) : ℂ_[p])) = 1
  apply NNReal.eq
  simpa [e, horizontalAugmentation, MonoidAlgebra.augmentation,
    PadicComplex.norm_eq_norm, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding] using haug

end HorizontalPadicL
