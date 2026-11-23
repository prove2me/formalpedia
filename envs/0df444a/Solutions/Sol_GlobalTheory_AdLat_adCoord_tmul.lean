-- Prove2me | solution 1 for GlobalTheory.AdLat.adCoord_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:13.740434+00:00
-- url     : https://prove2.me/submissions/28eaca92-08ca-4945-94c4-a3704fd14995

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
    (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (fun i => a ⊗ₜ x i) = a ⊗ₜ e.repr x b := by
  have hx : e.repr x b = ∑ i, x i * e.repr (Pi.single i 1) b := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → E) by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h],
      map_smul, Finsupp.smul_apply, smul_eq_mul]
  change ∑ i, (a ⊗ₜ x i) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hx, TensorProduct.tmul_sum]
end _root_.GlobalTheory.AdLat
end GlobalTheory.AdLat
