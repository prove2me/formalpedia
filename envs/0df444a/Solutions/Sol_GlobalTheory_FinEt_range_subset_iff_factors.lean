-- Prove2me | solution 1 for GlobalTheory.FinEt.range_subset_iff_factors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:11.697797+00:00
-- url     : https://prove2.me/submissions/04627a76-58a2-4a69-91df-c662103373af

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
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution {T : Scheme.{u}} (t : T ⟶ S) (U : S.Opens) :
    Set.range t ⊆ U ↔ ∃ t' : T ⟶ U, t' ≫ U.ι = t := by
  constructor
  · intro h
    exact ⟨IsOpenImmersion.lift U.ι t (by simpa using h), IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨t', rfl⟩ _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
end GlobalTheory.FinEt
