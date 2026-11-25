-- Prove2me | solution 1 for GlobalTheory.hom_ext_of_isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:17:36.074304+00:00
-- url     : https://prove2.me/submissions/faddd483-36a8-43ea-afe7-aefc9d8997a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_existsUnique_factor_stalk
import Theorems.Thm_GlobalTheory_ne_top_of_isHausdorff
import Theorems.Thm_P2M_GlobalTheory_adicLevel__closedPoint_ce2e53ef22fe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution (I : Ideal R) [IsHausdorff I R] {X : Scheme.{u}}
    {g g' : Spec (.of R) ⟶ X}
    (h : ∀ n, adicLevelι I (n + 1) ≫ g = adicLevelι I (n + 1) ≫ g') : g = g' := by
  have hI := ne_top_of_isHausdorff I
  have hx : g' (closedPoint R) = g (closedPoint R) := by
    rw [← adicLevelι_closedPoint hI 0]
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _))
    rw [h]
  obtain ⟨φ, hφ, -⟩ := existsUnique_factor_stalk g rfl
  obtain ⟨φ', hφ', -⟩ := existsUnique_factor_stalk g' hx
  have : φ = φ' := by
    ext1
    apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    intro n a
    have h1 : adicLevelι I (n + 1) ≫ Spec.map φ = adicLevelι I (n + 1) ≫ Spec.map φ' := by
      rw [← cancel_mono (X.fromSpecStalk _), Category.assoc, Category.assoc, hφ, hφ', h]
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom a)
  rw [← hφ', ← this, hφ]
end GlobalTheory
