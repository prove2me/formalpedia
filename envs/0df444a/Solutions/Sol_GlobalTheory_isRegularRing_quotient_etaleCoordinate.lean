-- Prove2me | solution 1 for GlobalTheory.isRegularRing_quotient_etaleCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:16.833579+00:00
-- url     : https://prove2.me/submissions/997d9614-707b-4dc5-b0ef-54ebc5b2894e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinateQuotientRegular
import Theorems.Thm_GlobalTheory_isRegularRing_of_etale
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale →
    ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  intro p _ A _ _ n t het j
  let B := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra B A := (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
  have : Algebra.Etale B A := het
  let I : Ideal B := Ideal.span (X '' ({j} : Set (Fin n)))
  have hQ : IsRegularRing (B ⧸ I) :=
    IsRegularRing.of_ringEquiv (quotientSpanXEquiv (ZMod p) ({j} : Set (Fin n))).symm.toRingEquiv
  have : IsRegularRing (TensorProduct B (B ⧸ I) A) := isRegularRing_of_etale (B ⧸ I) _
  have hI : I.map (algebraMap B A) = Ideal.span {t j} := by
    simp only [I, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    show MvPolynomial.aeval t (X j) = t j
    simp
  have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv.trans
    (Algebra.TensorProduct.comm B A (B ⧸ I)).toRingEquiv
  rw [hI] at e
  exact IsRegularRing.of_ringEquiv e.symm
end GlobalTheory
