-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:10.739475+00:00
-- url     : https://prove2.me/submissions/86a554be-4dcf-401d-aa42-691e4bbc00c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabiliser
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (s : A →+* A) (J : Matrix n n A)
namespace GlobalTheory.UnitVectorStabiliser
theorem _root_.solution (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) :
    ∃ (c : (n → A) →ₗ[A] A) (p : (n → A) →ₗ[A] P), (∀ y, y = c y • x + (p y : n → A)) ∧
      c x = 1 ∧ ∀ y : P, c y = 0 := by
  obtain ⟨b, hb⟩ := hx.exists_left_inv
  refine ⟨b • hfLin s J x,
    LinearMap.codRestrict P (LinearMap.id - (b • hfLin s J x).smulRight x) fun y => ?_,
    fun y => ?_, hb, fun y => ?_⟩
  · rw [hP]
    show hfLin s J x (y - (b * hfLin s J x y) • x) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    have : b * hfLin s J x x = 1 := hb
    linear_combination (- hfLin s J x y) * this
  · show y = (b * hfLin s J x y) • x + (y - (b * hfLin s J x y) • x)
    abel
  · show b * hform s J x y = 0
    rw [(hP y).1 y.2, mul_zero]
end GlobalTheory.UnitVectorStabiliser
