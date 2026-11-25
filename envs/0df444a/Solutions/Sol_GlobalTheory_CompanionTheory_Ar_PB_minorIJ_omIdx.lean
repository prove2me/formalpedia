-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.minorIJ_omIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:04.436902+00:00
-- url     : https://prove2.me/submissions/472afb27-78f9-4397-ba4d-b96a6d3970bd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_mem_omIdx_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_omEmb_strictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {R : Type} [CommRing R] {p q : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (T : Matrix (Fin (p + q)) (Fin (p + q)) R) :
    minorIJ T (omIdx (p + q) p) (omIdx (p + q) p) = (omBlock T).det := by
  rw [minorIJ, dif_pos rfl]
  let e : Fin q ≃ omIdx (p + q) p := Equiv.ofBijective (fun a => ⟨omEmb p q a, (mem_omIdx_iff p q _).2 ⟨a, rfl⟩⟩)
    ⟨fun a b h => (omEmb_strictMono p q).injective (congrArg Subtype.val h),
      fun i => let ⟨a, ha⟩ := (mem_omIdx_iff p q _).1 i.2; ⟨a, Subtype.ext ha⟩⟩
  rw [← Matrix.det_submatrix_equiv_self (e.trans ((omIdx (p + q) p).orderIsoOfFin rfl).symm.toEquiv)]
  congr 1
  ext a b
  simp [omBlock, ← Finset.coe_orderIsoOfFin_apply, e]
  rfl
end GlobalTheory.CompanionTheory.Ar.PB
