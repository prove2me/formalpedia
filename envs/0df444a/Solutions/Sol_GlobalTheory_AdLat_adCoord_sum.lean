-- Prove2me | solution 1 for GlobalTheory.AdLat.adCoord_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:04.113796+00:00
-- url     : https://prove2.me/submissions/d4cd7504-0518-4dc0-ac7e-f6b881cd81d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Theorems.Thm_GlobalTheory_AdLat_adCoord_tmul
import Theorems.Thm_GlobalTheory_AdLat_adCoord_smul

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
theorem _root_.solution (e : Module.Basis (Fin n) E (Fin n → E))
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E) (b : Fin n) :
    _root_.GlobalTheory.AdLat.adCoord F e b (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) = z b := by
  have h1 : ∀ a, _root_.GlobalTheory.AdLat.adCoord F e b (_root_.GlobalTheory.AdLat.fv F (e a)) =
      if a = b then 1 else 0 := by
    intro a
    have := _root_.GlobalTheory.AdLat.adCoord_tmul F e b 1 (e a)
    unfold _root_.GlobalTheory.AdLat.fv
    rw [this, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp [Algebra.TensorProduct.one_def]
  simp only [map_sum, _root_.GlobalTheory.AdLat.adCoord_smul, h1, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
end _root_.GlobalTheory.AdLat
end GlobalTheory.AdLat
