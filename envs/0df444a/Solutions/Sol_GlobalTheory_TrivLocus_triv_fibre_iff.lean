-- Prove2me | solution 1 for GlobalTheory.TrivLocus.triv_fibre_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:49.890803+00:00
-- url     : https://prove2.me/submissions/dd75a5b7-c334-41fa-bb65-a51c175860e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors
import Theorems.Thm_GlobalTheory_TrivLocus_nontrivial_ker_iff
import Theorems.Thm_GlobalTheory_TrivLocus_pull_pw
import Theorems.Thm_GlobalTheory_TrivLocus_triv_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb


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
open GlobalTheory GlobalTheory.TrivLocus
variable {X Y : Scheme.{0}}
namespace GlobalTheory.TrivLocus
theorem _root_.solution {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (hM : M.IsLB)
    (P : Perf f M) (Q : Perf f (pw M (-1))) [IsProper f] [GeometricallyIntegral f]
    {K : Type} [Field K] (g : R →+* K) {X' : Scheme.{0}} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    Triv (M.pull π) ↔ (∀ σ : Fin P.a → Fin P.b, (P.D₀.submatrix σ id).det ∈ RingHom.ker g) ∧
      ∀ σ : Fin Q.a → Fin Q.b, (Q.D₀.submatrix σ id).det ∈ RingHom.ker g := by
  have : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ h
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  obtain ⟨E, -⟩ := P.sec K g X' π f' h
  obtain ⟨E', -⟩ := Q.sec K g X' π f' h
  rw [triv_iff (isField_of_universallyClosed K f') _ (LB.isLB_linComb hM _ _).cover, ← pull_pw,
    ← nontrivial_ker_iff, ← nontrivial_ker_iff, E.nontrivial_congr, E'.nontrivial_congr]
end GlobalTheory.TrivLocus
