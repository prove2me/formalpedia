-- Prove2me | solution 1 for GlobalTheory.FinEt.exists_algClosed_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:55.952001+00:00
-- url     : https://prove2.me/submissions/0f164d72-8d5a-4a14-8995-8dca612b5958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
namespace GlobalTheory.FinEt
theorem _root_.solution (X : Scheme.{u}) (x : X) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (a : Spec (.of k) ⟶ X),
      Set.range a = {x} := by
  refine ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫ X.fromSpecResidueField x, ?_⟩
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · rintro rfl
    obtain ⟨z⟩ : Nonempty (Spec (.of (AlgebraicClosure (X.residueField y)))) := inferInstance
    refine ⟨z, ?_⟩
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
end GlobalTheory.FinEt
