-- Prove2me | solution 1 for GlobalTheory.SepPoint.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:07:28.330925+00:00
-- url     : https://prove2.me/submissions/14df714f-e1e7-4dbf-bc68-4f632f2222ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparablePointOfGeometricallyDomain
import Theorems.Thm_GlobalTheory_SepPoint_exists_ev
import Theorems.Thm_GlobalTheory_SepPoint_isIntegrallyClosed_adjoin
import Theorems.Thm_GlobalTheory_T_exists_algHom_adjoin_extend_of_isIntegral_root
import Theorems.Thm_GlobalTheory_T_exists_primitive_element_separability_certificate
import Theorems.Thm_GlobalTheory_T_nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero


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
theorem _root_.solution (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F)
    (B : Subalgebra k F) (hB : B.FG) : Nonempty (B →ₐ[k] SeparableClosure k) := by
  obtain ⟨T, rfl⟩ := hB
  haveI : IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := isIntegrallyClosed_adjoin k F s hs.1
  obtain ⟨θ, hθ, H, hH0, U, V, hUV, hT⟩ := GlobalTheory.T.exists_primitive_element_separability_certificate k F s hs hsep T
  obtain ⟨ev, hev⟩ := exists_ev k F s hs.1 H hH0
  let R := Algebra.adjoin k (s : Set F)
  let f := minpoly R θ
  let e : R →+* SeparableClosure k := (ev : R →+* SeparableClosure k)
  have hmon : f.Monic := minpoly.monic hθ
  have hsepa : (f.map e).Separable := by
    have h1 := congrArg (Polynomial.map e) hUV
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h1
    refine ⟨Polynomial.C (e H)⁻¹ * U.map e, Polynomial.C (e H)⁻¹ * V.map e, ?_⟩
    rw [Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul,
      inv_mul_cancel₀ (show e H ≠ 0 from hev), Polynomial.C_1]
  have hdeg : (f.map e).degree ≠ 0 := by
    rw [hmon.degree_map]
    exact (minpoly.degree_pos hθ).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg hsepa
  have hr' : Polynomial.eval₂ (ev : R →+* SeparableClosure k) r f = 0 := by
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hr
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root k F (SeparableClosure k) R θ hθ ev r hr'
  have hHS : (H : F) ∈ Algebra.adjoin k (insert θ (R : Set F)) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ H.2)
  exact GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero k F (SeparableClosure k) _ ψ ⟨H, hHS⟩
    (by rw [hψ _ H.2 hHS]; exact hev) (T : Set F) hT
end GlobalTheory.SepPoint
