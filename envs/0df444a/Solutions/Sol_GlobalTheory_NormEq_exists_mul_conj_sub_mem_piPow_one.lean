-- Prove2me | solution 1 for GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:44.201216+00:00
-- url     : https://prove2.me/submissions/2f1dd97d-5bde-4c1b-bf6f-53d1b008098c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_NormEq_exists_mul_invol_eq_of_fixed_unit
import Theorems.Thm_GlobalTheory_NormEq_isUnit_of_v_eq_one
import Theorems.Thm_GlobalTheory_NormEq_span_piO_isMaximal
import Theorems.Thm_GlobalTheory_NormEq_finite_quot_span_piO
import Theorems.Thm_GlobalTheory_NormEq_isReduced_adjoinRoot_of_separable
import Theorems.Thm_GlobalTheory_NormEq_isUnit_of_sub_one_mem
import Theorems.Thm_GlobalTheory_ReducedAdjoinRootSeparable_isReduced_adjoinRoot_of_separable
import Theorems.Thm_GlobalTheory_UTr_IsCyc_map
import Theorems.Thm_GlobalTheory_UTr_conj_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    P.1.Separable → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → ∃ u : (GlobalTheory.UTr.Alg P)ˣ,
      (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P 1 := by
  intro L _ _ σ ϖ q h P hP x hx
  classical
  let I0 : Ideal (intL L) := Ideal.span {piO h}
  haveI : I0.IsMaximal := span_piO_isMaximal h
  letI : Field (intL L ⧸ I0) := Ideal.Quotient.field I0
  haveI : Finite (intL L ⧸ I0) := finite_quot_span_piO h
  let J := piPow h P 1
  have hJ : J = (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P)) := by
    change Ideal.span {algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) ^ 1} =
      Ideal.map (AdjoinRoot.of P.1) (Ideal.span {piO h})
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact pow_one _
  let e1 : (GlobalTheory.UTr.Alg P ⧸ J) ≃+* (GlobalTheory.UTr.Alg P ⧸ (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P))) :=
    Ideal.quotEquivOfEq hJ
  let e2 : (GlobalTheory.UTr.Alg P ⧸ (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P))) ≃+*
      AdjoinRoot (P.1.map (Ideal.Quotient.mk I0)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I0 P.1
  let e := e1.trans e2
  haveI : IsReduced (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) :=
    isReduced_adjoinRoot_of_separable (hP.map)
  haveI : IsReduced (GlobalTheory.UTr.Alg P ⧸ J) := isReduced_of_injective e.toRingHom e.injective
  haveI : Module.Finite (intL L ⧸ I0) (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) :=
    (AdjoinRoot.powerBasis' (P.2.1.map (Ideal.Quotient.mk I0))).finite
  haveI : Finite (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) := Module.finite_of_finite (intL L ⧸ I0)
  haveI : Finite (GlobalTheory.UTr.Alg P ⧸ J) := Finite.of_equiv _ e.symm.toEquiv

  have hsig : ∀ b, sigO σ h.2.1 (sigO σ h.2.1 b) = b := fun b => Subtype.ext (h.1 b)
  have hsp : sigO σ h.2.1 (piO h) = piO h := Subtype.ext h.2.2.1
  have hle : J ≤ J.comap (GlobalTheory.UTr.conj P) := Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    change GlobalTheory.UTr.conj P _ ∈ J
    rw [map_pow, GlobalTheory.UTr.conj_algebraMap, hsp]
    exact Ideal.subset_span rfl))
  let τ := Ideal.quotientMap J (GlobalTheory.UTr.conj P) hle
  have hτ' : ∀ y, τ (Ideal.Quotient.mk J y) = Ideal.Quotient.mk J (GlobalTheory.UTr.conj P y) :=
    fun y => Ideal.quotientMap_mk
  have hτ : ∀ a, τ (τ a) = a := fun a => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hτ', hτ', GlobalTheory.UTr.conj_conj P hsig]

  obtain ⟨x0, hx0, hv⟩ := h.2.2.2.2.1
  let d : intL L := sigO σ h.2.1 ⟨x0, hx0⟩ - ⟨x0, hx0⟩
  have hd : IsUnit d := isUnit_of_v_eq_one d (by simpa [d] using hv)
  let b : GlobalTheory.UTr.Alg P ⧸ J := Ideal.Quotient.mk J (algebraMap (intL L) _ ⟨x0, hx0⟩)
  have hb : IsUnit (τ b - b) := by
    have : τ b - b = Ideal.Quotient.mk J (algebraMap (intL L) (GlobalTheory.UTr.Alg P) d) := by
      simp only [b, hτ', GlobalTheory.UTr.conj_algebraMap, d, map_sub]
    rw [this]
    exact (hd.map _).map _
  have hxu : IsUnit (Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P)) := x.isUnit.map _
  have hxτ : τ (Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P)) = Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P) := by
    rw [hτ', GlobalTheory.UTr.mem_plus.1 hx]
  obtain ⟨zb, hzb, hzz⟩ := exists_mul_invol_eq_of_fixed_unit τ hτ hb hxu hxτ
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zb
  obtain ⟨wb, hw⟩ := hzb.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective wb
  have hzw : IsUnit (z * w) := isUnit_of_sub_one_mem h P le_rfl (by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, map_one, sub_self])
  have hz : IsUnit z := isUnit_of_mul_isUnit_left hzw
  refine ⟨hz.unit, ?_⟩
  rw [IsUnit.unit_spec]
  change _ ∈ J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hτ', hzz, sub_self]
end GlobalTheory.NormEq
