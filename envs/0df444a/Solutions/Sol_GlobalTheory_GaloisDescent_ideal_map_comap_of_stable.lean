-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.ideal_map_comap_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:43:34.184256+00:00
-- url     : https://prove2.me/submissions/722db334-c89a-4947-b5fe-a0b97f3e9b0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Theorems.Thm_GlobalTheory_GaloisDescent_ideal_map_comap_of_span
import Theorems.Thm_GlobalTheory_GaloisDescent_span_image_comap_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I :=
  ideal_map_comap_of_span I _ (span_image_comap_eq hj s hs φ hφ (I.restrictScalars L) hI)
end GlobalTheory.GaloisDescent
