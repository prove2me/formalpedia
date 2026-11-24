-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.Dual.herm_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:33.592095+00:00
-- url     : https://prove2.me/submissions/359d98d2-7926-4c87-abe4-988ce9a1be18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_Dual_deg_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
namespace GlobalTheory.UnitLemma.Unr.Dual
theorem _root_.solution {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) :
    B.herm x y z = @Algebra.trace K.E K'.E _ _ φ.toAlgebra ((overExt φ B ψ hψ hσ).herm x y z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos
    (by rw [show Module.finrank K.E K'.E = d from hU.2.2.2.2]; exact deg_pos hU)
  haveI : Module.Finite K'.E B.A := Module.Finite.of_restrictScalars_finite K.E K'.E B.A
  show Algebra.trace K.E B.A (x * y * B.σ z) = Algebra.trace K.E K'.E (Algebra.trace K'.E B.A (x * y * B.σ z))
  exact (Algebra.trace_trace _).symm
end GlobalTheory.UnitLemma.Unr.Dual
