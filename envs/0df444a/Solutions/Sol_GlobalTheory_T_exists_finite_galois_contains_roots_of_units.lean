-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_galois_contains_roots_of_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:06.060172+00:00
-- url     : https://prove2.me/submissions/82848d31-5a8a-462a-97a0-2e1859bfdbbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFiniteGaloisContainsRootsOfUnits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFiniteGaloisContainsRootsOfUnitsStatement
import Theorems.Thm_GlobalTheory_KummerUnits_exists_finite_galois_mem_of_pow_eq_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  first | exact @GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit | exact GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit | (intros; apply GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit <;> assumption)
end _root_.GlobalTheory.T
