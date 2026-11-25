-- Prove2me | solution 1 for GlobalTheory.existsUnique_of_isAdicFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:44.729001+00:00
-- url     : https://prove2.me/submissions/044a949e-a86f-4b93-9896-97f4ce2c397d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_existsUnique_factor_stalk
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_ne_top_of_isHausdorff
import Theorems.Thm_GlobalTheory_IsAdicFamily_closedPoint_eq
import Theorems.Thm_GlobalTheory_hom_ext_of_isHausdorff

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
theorem _root_.solution [IsAdicComplete I R] {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) :
    ∃! g : Spec (.of R) ⟶ X, ∀ n, adicLevelι I (n + 1) ≫ g = f n := by
  have hI := ne_top_of_isHausdorff I
  refine existsUnique_of_exists_of_unique ?_ fun g g' hg hg' =>
    hom_ext_of_isHausdorff I fun n => (hg n).trans (hg' n).symm
  have hloc := isLocalRing_quotient_pow hI
  let x : X := f 0 (closedPoint (R ⧸ I ^ (0 + 1)))
  have hφ := fun n => (existsUnique_factor_stalk (f n) (x := x) (hf.closedPoint_eq hI n)).exists
  choose φ hφ using hφ
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp
      (φ (m + 1)).hom = (φ m).hom := by
    intro m
    have h1 : adicLevelMap I (Nat.le_succ (m + 1)) ≫ Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono (X.fromSpecStalk _), Category.assoc, hφ, hφ, hf m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom I ha (fun n => (φ n).hom) hc)) ≫ X.fromSpecStalk x,
    fun n => ?_⟩
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    IsAdicComplete.StrictMono.mk_comp_liftRingHom I ha (fun n => (φ n).hom) hc (n := n)]
  exact hφ n
end GlobalTheory
