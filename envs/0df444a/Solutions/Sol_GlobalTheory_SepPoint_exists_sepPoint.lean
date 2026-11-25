-- Prove2me | solution 1 for GlobalTheory.SepPoint.exists_sepPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:39.331343+00:00
-- url     : https://prove2.me/submissions/8ccca163-f45f-4e26-beef-4ab2cc923ae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparablePointOfGeometricallyDomain
import Theorems.Thm_GlobalTheory_SepPoint_exists_sepBasis
import Theorems.Thm_GlobalTheory_SepPoint_core
import Theorems.Thm_GlobalTheory_T_linearIndepOn_frob_pow_of_isDomain_tensor_insep
import Theorems.Thm_P2M_GlobalTheory_T_exists_finite_separable_point_of_separableClosure_point__d5de76197396


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SepPoint
namespace GlobalTheory.SepPoint
theorem _root_.solution : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B],
    Algebra.FiniteType k B →
    (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B)) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB hK
  haveI : IsDomain (k ⊗[k] B) := hK k inferInstance inferInstance
  haveI : IsDomain B := (Algebra.TensorProduct.lid k B).symm.toMulEquiv.isDomain
  obtain ⟨s, hs, hsep⟩ := exists_sepBasis k B hB
    (fun p hp hpk => GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep k B p hp hpk hK)
  let g : B →ₐ[k] FractionRing B := IsScalarTower.toAlgHom k B (FractionRing B)
  have hfg : g.range.FG := by
    rw [← Algebra.map_top]
    exact hB.out.map g
  obtain ⟨ψ⟩ := core k (FractionRing B) s hs hsep g.range hfg
  exact GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' k B hB ⟨ψ.comp g.rangeRestrict⟩
end GlobalTheory.SepPoint
