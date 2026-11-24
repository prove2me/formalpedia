-- Prove2me | solution 1 for GlobalTheory.AdelicMatLat.exists_nat_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:49.3014+00:00
-- url     : https://prove2.me/submissions/723f74a8-c13f-43e6-8c7d-92bc507dedc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
import Theorems.Thm_GlobalTheory_AdelicMatLat_exists_nat_denom
import Theorems.Thm_GlobalTheory_AdLat_exists_eq_algebraMap_add_nsmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
namespace GlobalTheory.AdelicMatLat
theorem _root_.solution (a : FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ (d : FiniteAdeleRing (𝓞 E) E) * a ∈ intAdeles E := by
  obtain ⟨x, b, hb, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E 1 one_pos a
  obtain ⟨d, hd, r, hr⟩ := exists_nat_denom E x
  refine ⟨d, hd, ?_⟩
  rw [mul_add, one_smul]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) hb)
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, algebraMap_mem_iff]
  exact ⟨r, hr⟩
end GlobalTheory.AdelicMatLat
