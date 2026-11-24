-- Prove2me | solution 1 for GlobalTheory.Chevalley.isArtinianRing_quotient_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:55.843794+00:00
-- url     : https://prove2.me/submissions/c9df02f5-0179-47de-9ee4-344cf49a198a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Chevalley
namespace GlobalTheory.Chevalley
theorem _root_.solution (B : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (k : ℕ) : IsArtinianRing (B ⧸ maximalIdeal B ^ k) := by
  have hdim : Ring.KrullDimLE 0 (B ⧸ maximalIdeal B ^ k) := by
    rw [Ring.krullDimLE_zero_iff]
    intro Q hQ
    have h1 : maximalIdeal B ^ k ≤ Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k)) :=
      fun x hx ↦ by simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    have h2 : maximalIdeal B = Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k)) :=
      (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h1)
    haveI h3 : (Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k))).IsMaximal :=
      h2 ▸ maximalIdeal.isMaximal B
    have h4 := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (maximalIdeal B ^ k)) Ideal.Quotient.mk_surjective
      (m := Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k))) (by simpa using h1)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h4
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
end GlobalTheory.Chevalley
