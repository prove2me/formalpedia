-- Prove2me | solution 1 for GlobalTheory.AdelicMatLat.exists_nat_mul_mem_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:42:59.700801+00:00
-- url     : https://prove2.me/submissions/47330867-9da1-4873-848c-f45e0ad342ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
import Theorems.Thm_GlobalTheory_AdelicMatLat_exists_nat_mul_mem

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
theorem _root_.solution {ι : Type} [Fintype ι] (a : ι → FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, (d : FiniteAdeleRing (𝓞 E) E) * a i ∈ intAdeles E := by
  classical
  choose d hd h using fun i => exists_nat_mul_mem E (a i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)
end GlobalTheory.AdelicMatLat
