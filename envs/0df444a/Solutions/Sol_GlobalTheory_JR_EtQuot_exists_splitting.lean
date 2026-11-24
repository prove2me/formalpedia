-- Prove2me | solution 1 for GlobalTheory.JR.EtQuot.exists_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:32:29.822974+00:00
-- url     : https://prove2.me/submissions/2ba0915f-d35f-4c93-9667-983d7b0a5045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
import Theorems.Thm_GlobalTheory_JR_EtQuot_exists_idem
import Theorems.Thm_GlobalTheory_JR_EtQuot_nontrivial_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtQuot
namespace GlobalTheory.JR.EtQuot
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K →
    ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
      IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧
        Module.finrank F A₂.K < Module.finrank F A.K := by
  intro F E _ _ _ _ _ A hnt hf
  haveI : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  obtain ⟨e, he, h0, h1⟩ := exists_idem A.K hf
  let A₁ := quotEt A e he
  let A₂ := quotEt A (1 - e) he.one_sub
  let eK : A.K ≃ₐ[F] A₁.K × A₂.K :=
    AlgEquiv.prodQuotientOfIsIdempotentElem F he he.one_sub (by ring) he.mul_one_sub_self
  let e' := algebraMap A.K A.L e
  have he' : IsIdempotentElem e' := he.map _
  have hJ1 : (Ideal.span {e}).map (algebraMap A.K A.L) = Ideal.span {e'} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hJ2 : (Ideal.span {1 - e}).map (algebraMap A.K A.L) = Ideal.span {1 - e'} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  let eL : A.L ≃ₐ[F] A₁.L × A₂.L :=
    (AlgEquiv.prodQuotientOfIsIdempotentElem F he' he'.one_sub (by ring) he'.mul_one_sub_self).trans
      (AlgEquiv.prodCongr (Ideal.quotientEquivAlgOfEq F hJ1.symm) (Ideal.quotientEquivAlgOfEq F hJ2.symm))
  have hsum : Module.finrank F A.K = Module.finrank F A₁.K + Module.finrank F A₂.K := by
    rw [eK.toLinearEquiv.finrank_eq, Module.finrank_prod]
  haveI : Nontrivial A₁.K := nontrivial_quot he h1
  haveI : Nontrivial A₂.K := nontrivial_quot he.one_sub (fun h => h0 (by linear_combination -h))
  have p1 : 0 < Module.finrank F A₁.K := Module.finrank_pos
  have p2 : 0 < Module.finrank F A₂.K := Module.finrank_pos
  refine ⟨A₁, A₂, eK, eL, ⟨fun k => ?_, fun y => ?_, fun y => ?_⟩, by omega, by omega⟩
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A e) (QL A e) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A (1 - e)) (QL A (1 - e)) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A e)).star (Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A (1 - e))).star (Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl
end GlobalTheory.JR.EtQuot
