-- Prove2me | solution 1 for GlobalTheory.exists_invariant_notMem_orbit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:14.816052+00:00
-- url     : https://prove2.me/submissions/79a91368-b70c-43ea-b676-18b8a54ab3db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_of_isBaseChange
import Theorems.Thm_GlobalTheory_exists_invariant_notMem_orbit_generator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type*) [Group G] [Finite G] {A : Type*}
    [CommRing A] [MulSemiringAction G A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (Q : Ideal A) [Q.IsPrime] :
    ∃ (s : A) (e : M), (∀ g : G, g • s = s) ∧ (∀ g : G, s ∉ g • Q) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Localization.Away s)
        (LocalizedModule (.powers s) M) (LocalizedModule.mkLinearMap (.powers s) M e)) := by
  obtain ⟨s, e, h1, h2, f, hf⟩ := exists_invariant_notMem_orbit_generator G M Q
  exact ⟨s, e, h1, h2, bijective_toSpanSingleton_of_isBaseChange f e _
    (IsLocalizedModule.isBaseChange (.powers s) _ _)
    (by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit s)⟩
end GlobalTheory
