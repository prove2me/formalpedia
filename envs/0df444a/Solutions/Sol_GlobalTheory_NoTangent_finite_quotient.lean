-- Prove2me | solution 1 for GlobalTheory.NoTangent.finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:13.493071+00:00
-- url     : https://prove2.me/submissions/640a23ef-6285-450d-afec-57c4d6c7ccf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AlgHomDualNumberExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.NoTangent
open MvPowerSeries
namespace GlobalTheory.NoTangent
theorem _root_.solution {O σ : Type} [CommRing O] [Finite σ] (I : Ideal (MvPowerSeries σ O))
    (M : ℕ) (h : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O, P.totalDegree ≤ M ∧
      g - (P : MvPowerSeries σ O) ∈ I) : Module.Finite O (MvPowerSeries σ O ⧸ I) := by
  let L : MvPolynomial.restrictTotalDegree σ O M →ₗ[O] (MvPowerSeries σ O ⧸ I) :=
    (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) (R := O) O).toLinearMap ∘ₗ
      (MvPolynomial.restrictTotalDegree σ O M).subtype
  refine Module.Finite.of_surjective L ?_
  intro q
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨P, hP, hg⟩ := h g
  refine ⟨⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩, ?_⟩
  have : L ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩ =
      Ideal.Quotient.mk I (P : MvPowerSeries σ O) := by
    simp [L]
  rw [this]
  exact (Ideal.Quotient.eq.2 hg).symm
end GlobalTheory.NoTangent
