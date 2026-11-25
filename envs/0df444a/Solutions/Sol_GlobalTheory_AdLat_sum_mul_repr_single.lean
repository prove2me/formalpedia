-- Prove2me | solution 1 for GlobalTheory.AdLat.sum_mul_repr_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:20.892998+00:00
-- url     : https://prove2.me/submissions/b58ce750-32ff-4656-a74f-6e18b64527ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat
theorem _root_.solution (e : Module.Basis (Fin n) E (Fin n → E)) (x : Fin n → E) (b : Fin n) :
    ∑ i, x i * e.repr (Pi.single i 1) b = e.repr x b := by
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp [map_sum]
end GlobalTheory.AdLat
