-- Prove2me | solution 1 for GlobalTheory.Twist.mateHom_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:38.54385+00:00
-- url     : https://prove2.me/submissions/01691d3f-7c40-4d59-8ce1-785c601e6648

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod)
open GlobalTheory
open GlobalTheory.Twist
variable {X Y : Scheme.{0}}
variable {F G : X.Modules}
variable {C D : Type*} [Category C] [Category D] {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q)
  (S : C ⥤ C) (T : D ⥤ D) (e : Q ⋙ S ≅ T ⋙ Q)
namespace GlobalTheory.Twist
theorem _root_.solution {A B : C} (f : A ⟶ B) :
    P.map (S.map f) ≫ mateHom adj S T e B = mateHom adj S T e A ≫ T.map (P.map f) := by
  rw [mateHom, mateHom, ← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm, ← S.map_comp_assoc, Category.assoc]
  congr 1
  have h₁ := adj.unit.naturality f
  have h₂ := e.hom.naturality (P.map f)
  dsimp at h₁ h₂ ⊢
  rw [h₁, S.map_comp_assoc, h₂]
end GlobalTheory.Twist
