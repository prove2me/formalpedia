-- Prove2me | solution 1 for GlobalTheory.UnitCocycle.isDescentDatum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:41.966767+00:00
-- url     : https://prove2.me/submissions/c015ff49-58ba-495f-ad01-63eb15289fed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
import Theorems.Thm_GlobalTheory_UnitCocycle_datum_apply
import Theorems.Thm_P2M_GlobalTheory_UnitCocycle_lmul__eq_one_7cd501a29069
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
namespace GlobalTheory.UnitCocycle
theorem _root_.solution {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : FlatDescent.IsDescentDatum (datum c) := by
  have ha : ∀ z : B ⊗[R] B, FlatDescent.act R B B z = Algebra.TensorProduct.lmul' R z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp
  have h1 : ∀ z : B ⊗[R] B,
      ((datum c).restrictScalars R).lTensor B z = m₁₂ R B z * m₂₃ R B c := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_mul]
    | tmul b m => simp [datum_apply, m₁₂, m₂₃, mul_comm]
  have h2 : ∀ z : B ⊗[R] B, (TensorProduct.mk R B B 1).lTensor B z = m₁₃ R B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [m₁₃]
  constructor
  · intro n
    rw [ha, datum_apply, map_mul, lmul'_eq_one hu h]
    simp
  · intro n
    rw [h1, h2, datum_apply, map_mul, map_mul, h, mul_right_comm]
    congr 1
end GlobalTheory.UnitCocycle
