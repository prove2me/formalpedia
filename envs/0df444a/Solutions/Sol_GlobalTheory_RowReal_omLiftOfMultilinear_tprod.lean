-- Prove2me | solution 1 for GlobalTheory.RowReal.omLiftOfMultilinear_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:27.385677+00:00
-- url     : https://prove2.me/submissions/6a987569-5fe1-46a7-ba87-747242fe8d65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OmLiftOfMultilinearTprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.RowReal
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
namespace GlobalTheory.RowReal
theorem _root_.solution
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) (x y v φ) :
    omLiftOfMultilinear P Φ (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) =
      Φ x y v φ := by
  simp only [omLiftOfMultilinear, TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.uncurry_apply,
    LinearMap.llcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
end GlobalTheory.RowReal
