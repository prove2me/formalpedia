-- Prove2me | solution 1 for GlobalTheory.GaussPoint.vV_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:55.856235+00:00
-- url     : https://prove2.me/submissions/6ec5e130-d9a0-47fc-b9bc-ba953d8f07e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint
import Theorems.Thm_GlobalTheory_GaussPoint_valV_irreducible
import Theorems.Thm_GlobalTheory_GaussPoint_valV_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing
open GlobalTheory GlobalTheory.GaussPoint
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]
namespace GlobalTheory.GaussPoint
theorem _root_.solution {V' K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Field K'] [Algebra V' K'] [IsFractionRing V' K'] (f : V →+* V') (i : K →+* K')
    (hi : ∀ a, i (algebraMap V K a) = algebraMap V' K' (f a)) {π : V} (hπ : Irreducible π)
    (hπ' : Irreducible (f π)) (x : K) : vV V' (i x) = vV V x := by
  have key : ∀ a : V, valV V' (i (algebraMap V K a)) = valV V (algebraMap V K a) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [hi]
    simp only [map_mul, map_pow]
    rw [valV_unit u.isUnit, valV_unit (u.isUnit.map f), valV_irreducible hπ, valV_irreducible hπ']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  simp only [vV, map_div₀, key]
end GlobalTheory.GaussPoint
