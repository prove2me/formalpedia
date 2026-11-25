-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechAcyclic_of_bijective_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:35.093735+00:00
-- url     : https://prove2.me/submissions/ec0575a2-602c-4a9e-b4b2-0208f43d0082

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe w w' u
noncomputable section
variable {X : TopCat.{u}} {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {D : Opens X}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (φ : ∀ W : Opens X, W ≤ D → Q.obj (op W) →+ P.obj (op W))
    (hφ : ∀ W hW, Function.Bijective (φ W hW))
    (hnat : ∀ {W W' : Opens X} (h : W' ≤ W) (hW : W ≤ D) (x : Q.obj (op W)),
      φ W' (h.trans hW) (res Q h x) = res P h (φ W hW x))
    {ι : Type w} (U : ι → Opens X) (hU : ∀ a, U a ≤ D) (hQ : CechAcyclic Q U) :
    CechAcyclic P U := by
  have hI : ∀ {m : ℕ} (i : Fin (m + 1) → ι), inter U i ≤ D := fun i =>
    (inter_le U i 0).trans (hU _)
  let push' (m : ℕ) : Cochain Q U m →+ Cochain P U m :=
    { toFun σ i := φ _ (hI i) (σ i)
      map_zero' := by funext i; exact map_zero _
      map_add' σ τ := by funext i; exact map_add _ _ _ }
  have hd : ∀ m σ, d P U m (push' m σ) = push' (m + 1) (d Q U m σ) := by
    intro m σ
    funext i
    rw [d_apply]
    change _ = φ _ (hI i) (d Q U m σ i)
    rw [d_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul]
    congr 1
    exact (hnat _ (hI (i ∘ a.succAbove)) _).symm
  have hinj : ∀ m, Function.Injective (push' m) := fun m σ τ h => by
    funext i
    exact (hφ _ (hI i)).1 (congrFun h i)
  have hsurj : ∀ m, Function.Surjective (push' m) := fun m σ =>
    ⟨fun i => ((hφ _ (hI i)).2 (σ i)).choose, funext fun i => ((hφ _ (hI i)).2 (σ i)).choose_spec⟩
  intro m σ hσ
  obtain ⟨σQ, rfl⟩ := hsurj _ σ
  have h0 : d Q U (m + 1) σQ = 0 := hinj _ (by rw [← hd, hσ, map_zero])
  obtain ⟨τ, hτ⟩ := hQ m σQ h0
  exact ⟨push' m τ, by rw [hd, hτ]⟩
end GroundTheory.Arith.SchemeCoh
