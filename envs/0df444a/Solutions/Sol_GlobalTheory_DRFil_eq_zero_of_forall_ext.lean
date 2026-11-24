-- Prove2me | solution 1 for GlobalTheory.DRFil.eq_zero_of_forall_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:22.226963+00:00
-- url     : https://prove2.me/submissions/bd85df9d-4ee8-4c16-b2c2-be394cadf373

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {Qp : Type} [Field Qp] (F : Type) [CommRing F] [Algebra Qp F]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
variable {F}
namespace GlobalTheory.DRFil
theorem _root_.solution (x : V ⊗[Qp] F) (h : ∀ φ : V →ₗ[LL] LL, ext Qp F φ x = 0) : x = 0 := by
  classical
  let bV := Basis.ofVectorSpace LL V
  have key : ∀ x : V ⊗[Qp] F, ∃ s : Finset _, ∀ t : Finset _, s ⊆ t →
      x = ∑ i ∈ t, sm Qp F LL V (ext Qp F (bV.coord i) x) (bV i ⊗ₜ[Qp] (1 : F)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨∅, fun t _ => by simp⟩
    | add x y hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨s', hs'⟩ := hy
      refine ⟨s ∪ s', fun t ht => ?_⟩
      simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      rw [← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]
    | tmul v b =>
      refine ⟨(bV.repr v).support, fun t ht => ?_⟩
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, sm_tmul, mul_one,
        Basis.coord_apply, ← TensorProduct.sum_tmul]
      congr 1
      conv_lhs => rw [← bV.linearCombination_repr v]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ ht _ (by simp)]
  obtain ⟨s, hs⟩ := key x
  rw [hs s le_rfl]
  simp [h]
end GlobalTheory.DRFil
