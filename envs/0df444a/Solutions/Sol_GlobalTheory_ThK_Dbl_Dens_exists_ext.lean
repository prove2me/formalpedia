-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Dens.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:42.921124+00:00
-- url     : https://prove2.me/submissions/187f6a65-ad89-43d0-b367-927a2225017c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal
section Schur
variable {R V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V] [Module R V]
  [IsScalarTower ℂ R V] [IsSimpleModule R V]
end Schur
private theorem dite_update_eq_update_dite {ι : Type} [DecidableEq ι] {X : ι → Type} (T T₁ : Finset ι) (hT : T ⊆ T₁)
    (s : ∀ i, X i) [DecidableEq T] (m : ∀ v : T, X v) (i : T) (z : X i) :
    (fun v : T₁ => if h : (v : ι) ∈ T then Function.update m i z ⟨v, h⟩ else s v) =
      Function.update (fun v : T₁ => if h : (v : ι) ∈ T then m ⟨v, h⟩ else s v) ⟨i, hT i.2⟩ z := by
  funext v
  by_cases hv : (v : ι) ∈ T
  · by_cases hvi : (v : ι) = i
    · have hv' : v = ⟨i, hT i.2⟩ := Subtype.ext hvi
      subst hv'
      simp
    · have h1 : (⟨v, hv⟩ : T) ≠ i := fun h => hvi (by rw [← h])
      have h2 : v ≠ ⟨i, hT i.2⟩ := fun h => hvi (by rw [h])
      rw [dif_pos hv, Function.update_of_ne h1, Function.update_of_ne h2, dif_pos hv]
  · have h2 : v ≠ ⟨i, hT i.2⟩ := fun h => hv (by rw [h]; exact i.2)
    rw [dif_neg hv, Function.update_of_ne h2, dif_neg hv]
end GlobalTheory.ThK.Dbl.Dens
end
end

set_option autoImplicit false
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal
namespace GlobalTheory.ThK.Dbl.Dens
theorem _root_.solution {ι : Type} [DecidableEq ι] {X : ι → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (T T₁ : Finset ι) (hT : T ⊆ T₁) (s : ∀ i, X i) :
    ∃ e : (PiTensorProduct ℂ fun v : T => X v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => X v,
      ∀ u : ∀ i, X i, (∀ i ∉ T, u i = s i) →
        e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v := by
  classical
  let f : MultilinearMap ℂ (fun v : T => X v) (PiTensorProduct ℂ fun v : T₁ => X v) :=
    { toFun := fun m => PiTensorProduct.tprod ℂ fun v : T₁ => if h : (v : ι) ∈ T then m ⟨v, h⟩ else s v
      map_update_add' := fun m i x y => by
        simp only [dite_update_eq_update_dite T T₁ hT s]
        exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun m i c x => by
        simp only [dite_update_eq_update_dite T T₁ hT s]
        exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }
  refine ⟨PiTensorProduct.lift f, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ _ = _
  congr 1
  funext v
  by_cases hv : (v : ι) ∈ T
  · rw [dif_pos hv]
  · rw [dif_neg hv, hu v hv]
end GlobalTheory.ThK.Dbl.Dens
