-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.triv_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:17.94872+00:00
-- url     : https://prove2.me/submissions/658b4b0e-22d3-4b99-9ecb-b54ce4ff5306

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_mem_basicOpen_rs
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_isUnit_of_basicOpen
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_sec_basicOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
variable {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M)
variable {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
  (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
include h
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution (v : Fin P.a → R') (hv : (P.D₀.map g).mulVec v = 0)
    (H : ∀ y : X', ∃ i, y ∈ X'.basicOpen (loc P π f' v i)) : Triv (M.pull π) := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  have hu : ∀ j, IsUnit ((E ⟨v, hv⟩).f j) := fun j => isUnit_of_basicOpen _ fun y hy => by
    obtain ⟨i, hi⟩ := H y
    refine sec_basicOpen (E ⟨v, hv⟩) (j := fun _ => P.ch i) hy ?_
    rw [← mem_basicOpen_rs (le_pull M π (P.le i)) _ (X'.basicOpen_le _ hi), hE]
    exact hi
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext ((E ⟨v, hv⟩).compat i j)⟩
end GlobalTheory.AbLaw.Seesaw
