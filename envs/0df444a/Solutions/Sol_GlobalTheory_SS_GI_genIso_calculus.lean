-- Prove2me | solution 1 for GlobalTheory.SS.GI.genIso_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:42.027987+00:00
-- url     : https://prove2.me/submissions/e9fa569e-7b58-4229-ad0c-d3c463508627

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_isoAt_assoc
import Theorems.Thm_GlobalTheory_SS_GI_isoAt_braiding
import Theorems.Thm_GlobalTheory_SS_GI_exists_mem_sp_prod
import Theorems.Thm_GlobalTheory_SS_GI_genIso_of_le
import Theorems.Thm_GlobalTheory_SS_GI_genIso_comp
import Theorems.Thm_GlobalTheory_SS_GI_genIso_inv
import Theorems.Thm_GlobalTheory_SS_GI_genIso_twist
import Theorems.Thm_GlobalTheory_SS_GI_genIso_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}
namespace GlobalTheory.SS.GI
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → (∀ (A : Over (Sp K)) (M N : Model R A), M.Irr → M.Le N → GenIso M N (𝟙 A)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A'') (f : A ⟶ A') (g : A' ⟶ A''), N.Irr → GenIso M N f → GenIso N P g → GenIso M P (f ≫ g)) ∧ (∀ (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ≅ A'), (GenIso M N f.hom → GenIso N M f.inv) ∧ (GenIso M N f.hom ↔ GenIso (M.twist f) N (𝟙 A')) ∧ (M.Irr → (M.twist f).Irr)) ∧ (∀ (A A' B B' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R B) (Q : Model R B') (f : A ⟶ B) (g : A' ⟶ B'), GenIso M P f → GenIso N Q g → GenIso (M.prod N) (P.prod Q) (f ⊗ₘ g)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A''), M.Irr → N.Irr → P.Irr → GenIso ((M.prod N).prod P) (M.prod (N.prod P)) (α_ A A' A'').hom ∧ GenIso (M.prod N) (N.prod M) (β_ A A').hom) := by
  intro R K _ _ _ _ _ _
  refine ⟨fun A M N hM h => genIso_of_le hM.1 h, fun _ _ _ _ _ _ _ _ hN h h' => genIso_comp hN h h',
    fun A A' M N f => ⟨genIso_inv, ?_, id⟩, fun _ _ _ _ _ _ _ _ _ _ h h' => genIso_prod h h',
    fun A A' A'' M N P ⟨⟨x, hx⟩, _⟩ ⟨⟨y, hy⟩, _⟩ ⟨⟨t, ht⟩, _⟩ => ?_⟩
  · rw [genIso_twist, Category.comp_id]
  · obtain ⟨z, hz, -⟩ := exists_mem_sp_prod hx hy
    obtain ⟨z', hz', -⟩ := exists_mem_sp_prod hz ht
    exact ⟨⟨z', hz', isoAt_assoc M N P z'⟩, ⟨z, hz, isoAt_braiding M N z⟩⟩
end GlobalTheory.SS.GI
