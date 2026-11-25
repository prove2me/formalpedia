-- Prove2me | solution 1 for GlobalTheory.nonempty_homology_equiv_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:58.256326+00:00
-- url     : https://prove2.me/submissions/150957f8-0917-430b-b0f1-dfcded1cda42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (S : ShortComplex (ModuleCat.{v} R))
    {W : Type*} [AddCommGroup W] [Module R W] (I : W →ₗ[R] S.X₂) (Q : S.X₂ →ₗ[R] W)
    (hI : ∀ w, S.g.hom (I w) = 0) (hQ : ∀ y, Q (S.f.hom y) = 0) (hQI : ∀ w, Q (I w) = w)
    (hex : ∀ x, S.g.hom x = 0 → Q x = 0 → ∃ y, S.f.hom y = x) :
    Nonempty (S.homology ≃ₗ[R] W) := by
  let q : LinearMap.ker S.g.hom →ₗ[R] W := Q ∘ₗ (LinearMap.ker S.g.hom).subtype
  have hs : Function.Surjective q := fun w => ⟨⟨I w, hI w⟩, hQI w⟩
  have hk : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hQ y
    · intro hx
      obtain ⟨y, hy⟩ := hex x.1 x.2 hx
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨S.moduleCatHomologyIso.toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    q.quotKerEquivOfSurjective hs⟩
end GlobalTheory
