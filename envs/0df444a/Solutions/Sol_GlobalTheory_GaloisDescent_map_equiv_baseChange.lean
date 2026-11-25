-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.map_equiv_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:55:45.281723+00:00
-- url     : https://prove2.me/submissions/e4e6a125-2a6e-4700-a5a6-87a868402fae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra
import Theorems.Thm_GlobalTheory_GaloisDescent_baseChange_eq_span_image
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_quotientEquivOfMapEq_tmul
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul
attribute [local simp] GlobalTheory.GaloisDescent.mem_rationalPart
attribute [local simp] GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange



set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L G V : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction G V] [SMulDistribClass G L V]
variable [SMulCommClass G K V]
omit [MulSemiringAction G L] [SMulDistribClass G L V] [DistribMulAction G V]
  [SMulCommClass G K V]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module K N] {f : N →ₗ[K] V}
    (hf : IsBaseChange L f) (P : Submodule K N) :
    (P.baseChange L).map hf.equiv.toLinearMap = Submodule.span L (f '' P) := by
  rw [baseChange_eq_span_image, Submodule.map_span, Set.image_image]
  simp
end GlobalTheory.GaloisDescent
