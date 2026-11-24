-- Prove2me | solution 1 for GlobalTheory.EuclidTransport.exists_schwartz_L2_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:47.189949+00:00
-- url     : https://prove2.me/submissions/f46498b6-5957-4c6d-b825-702eb8e63083

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzL2EuclideanIdentification
import Theorems.Thm_GlobalTheory_EuclidTransport_schwartzTransport_apply
import Theorems.Thm_GlobalTheory_EuclidTransport_l2Transport_toLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.EuclidTransport
variable (l : Type) [Fintype l]
variable {l}
variable (l)
variable {l}
namespace GlobalTheory.EuclidTransport
theorem _root_.solution (l : Type) [Fintype l] [DecidableEq l] :
    ∃ (e : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l) (u : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l),
      (∀ φ (x : EuclideanSpace ℝ l), e φ x = φ x.ofLp) ∧ ∀ φ : 𝓢(l → ℝ, ℂ), u (φ.toLp 2) = (e φ).toLp 2 :=
  ⟨schwartzTransport l, l2Transport l, schwartzTransport_apply, l2Transport_toLp⟩
end GlobalTheory.EuclidTransport
