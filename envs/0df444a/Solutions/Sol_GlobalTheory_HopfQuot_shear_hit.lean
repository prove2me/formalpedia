-- Prove2me | solution 1 for GlobalTheory.HopfQuot.shear_hit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:22.708287+00:00
-- url     : https://prove2.me/submissions/31998e54-d4c0-4a69-bfb7-e5dedb1d94aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_hit_apply
import Theorems.Thm_GlobalTheory_HopfQuot_shear_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (f : Λ →ₗ[R] R) (z : Λ ⊗[R] Λ) :
    shear R Λ ((hit f).baseChange Λ z) = (hit f).baseChange Λ (shear R Λ z) := by
  have key : ∀ y : Λ, Coalgebra.comul (R := R) (hit f y) =
      (hit f).baseChange Λ (Coalgebra.comul y) := by
    intro y
    let F : Λ ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] Λ ⊗[R] Λ := ((ev Λ f).restrictScalars R).lTensor Λ
    have h1 : ∀ w : Λ ⊗[R] Λ, Coalgebra.comul (R := R) (ev Λ f w) =
        F (TensorProduct.assoc R Λ Λ Λ ((Coalgebra.comul (R := R)).rTensor Λ w)) := by
      intro w
      induction w with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b =>
        rw [ev_tmul, map_smul, LinearMap.rTensor_tmul]
        generalize Coalgebra.comul (R := R) a = w
        induction w with
        | zero => simp
        | add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]
        | tmul u v => simp [F]
    have h2 : ∀ w : Λ ⊗[R] Λ, (hit f).baseChange Λ w =
        F ((Coalgebra.comul (R := R)).lTensor Λ w) := by
      intro w
      induction w with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b => simp [F, hit_apply]
    rw [hit_apply, h1, h2, Coalgebra.coassoc_apply]
  induction z with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    rw [LinearMap.baseChange_tmul, shear_tmul, shear_tmul, map_smul, key]
end GlobalTheory.HopfQuot
