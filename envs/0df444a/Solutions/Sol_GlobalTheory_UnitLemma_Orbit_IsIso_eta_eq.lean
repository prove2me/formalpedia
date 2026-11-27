-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.IsIso.eta_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:30.00512+00:00
-- url     : https://prove2.me/submissions/6202fdb6-87d1-4471-977e-242b2e2d5260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_eta_gram
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_IsIso_herm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
open GlobalTheory.UnitLemma.Orbit.IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}
namespace GlobalTheory.UnitLemma.Orbit.IsIso
theorem _root_.solution (h : IsIso φ) (x : B.A) : K.eta (C.gramDet (φ x)) = K.eta (B.gramDet x) := by
  have hr : Module.finrank K.E B.A = Module.finrank K.E C.A := φ.toLinearEquiv.finrank_eq
  rw [← eta_gram C (φ x) (((Module.finBasis K.E B.A).map φ.toLinearEquiv).reindex (finCongr hr))]
  congr 1
  unfold InvAlg.gramDet
  rw [← Matrix.det_submatrix_equiv_self (finCongr hr)]
  congr 1
  ext i j
  simp [h.herm_eq]
end GlobalTheory.UnitLemma.Orbit.IsIso
