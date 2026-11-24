-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TorusPts.isIntegral_of_mul_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:13.537362+00:00
-- url     : https://prove2.me/submissions/ce3703dd-8087-4f2b-a410-2e470b60d3bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TorusPts
namespace GlobalTheory.UnitLemma.TorusPts
theorem _root_.solution {K : UQ} (B : InvAlg K) {f : B.A} (hf : f * f = f) (h0 : f ≠ 0) (x : K.E)
    (hx : IsIntegral K.O (algebraMap K.E B.A x * f)) : IsIntegral K.O x := by
  let J : Ideal B.A := Ideal.span {1 - f}
  have hJ : J ≠ ⊤ := by
    intro h
    have : (1 : B.A) ∈ J := h ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 this
    apply h0
    linear_combination (-f) * hr - r * hf
  haveI : Nontrivial (B.A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  let φ : K.E →ₐ[K.O] B.A ⧸ J := (Ideal.Quotient.mkₐ K.O J).comp (IsScalarTower.toAlgHom K.O K.E B.A)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  rw [← isIntegral_algHom_iff φ hinj]
  have h1 := hx.map (Ideal.Quotient.mkₐ K.O J)
  have h2 : Ideal.Quotient.mkₐ K.O J (algebraMap K.E B.A x * f) = φ x := by
    show Ideal.Quotient.mk J _ = Ideal.Quotient.mk J (algebraMap K.E B.A x)
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-algebraMap K.E B.A x, by ring⟩
  rwa [h2] at h1
end GlobalTheory.UnitLemma.TorusPts
