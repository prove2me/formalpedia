-- Prove2me | solution 1 for GlobalTheory.HopfQuot.ev_mem_equalizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:22:50.920806+00:00
-- url     : https://prove2.me/submissions/d42ff95d-f1ee-4bca-969f-451b5919b02f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
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
variable {R Λ B : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
  (ρ : B →ₐ[R] B ⊗[R] Λ)
namespace GlobalTheory.HopfQuot
theorem _root_.solution
    (hassoc : ∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b))
    (l : Λ →ₗ[R] R) (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : B) :
    ev B l (ρ b) ∈ AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) := by
  let F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ := ((ev Λ l).restrictScalars R).lTensor B
  have h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l w) =
      F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w)) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      rw [ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      generalize ρ a = w
      induction w with
      | zero => simp
      | add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R := R)).lTensor B w) =
      ev B l w ⊗ₜ 1 := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_tmul, ha, hb]
    | tmul a b => simp [F, hl, Algebra.algebraMap_eq_smul_one, smul_tmul]
  rw [AlgHom.mem_equalizer, h1, hassoc, h2]
  rfl
end GlobalTheory.HopfQuot
