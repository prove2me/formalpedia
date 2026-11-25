-- Prove2me | solution 1 for GlobalTheory.RowReal.invFun_of_multilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:47.950421+00:00
-- url     : https://prove2.me/submissions/1e3753d3-1453-48d4-8151-f9d6ed7905d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OmLiftOfMultilinearTprod
import Theorems.Thm_GlobalTheory_RowReal_omLiftOfMultilinear_tprod

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
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ)))
    (hΦ : ∀ g x y v φ, Φ (fun j => rowFock P j g (x j)) (fun i => colFock P i g (y i)) (psiRep P g v)
      ((baseRep P).dual g φ) = Φ x y v φ), ∃ l ∈ invFun (omRep P), ∀ x y v φ,
      l (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) = Φ x y v φ := by
  intro ι _ _ S P Φ hΦ
  refine ⟨omLiftOfMultilinear P Φ, ?_, omLiftOfMultilinear_tprod P Φ⟩
  intro g z
  have key : (omLiftOfMultilinear P Φ).comp (omRep P g) = omLiftOfMultilinear P Φ := by
    ext x y v φ
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.restrictScalars_apply]
    rw [omRep, Representation.tprod_apply, TensorProduct.map_tmul, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
    simp only [piTprod, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod,
      Pi.monoidHom_apply, omLiftOfMultilinear_tprod]
    exact hΦ g x y v φ
  exact LinearMap.congr_fun key z
end GlobalTheory.RowReal
