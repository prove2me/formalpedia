-- Prove2me | solution 1 for GlobalTheory.AdLat.adCoord_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:41.809061+00:00
-- url     : https://prove2.me/submissions/6808c85a-07f3-4555-af63-85b4599af669

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
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat
namespace _root_.GlobalTheory.AdLat
theorem _root_.solution (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (r : _root_.GlobalTheory.AdLat.RA F E) (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (r • w) = r * _root_.GlobalTheory.AdLat.adCoord F e b w := by
  change ∑ i, (r • w) i * _ = r * ∑ i, w i * _
  simp [Finset.mul_sum, mul_assoc]
end _root_.GlobalTheory.AdLat
end GlobalTheory.AdLat
