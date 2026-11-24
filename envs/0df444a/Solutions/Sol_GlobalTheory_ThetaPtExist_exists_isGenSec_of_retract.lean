-- Prove2me | solution 1 for GlobalTheory.ThetaPtExist.exists_isGenSec_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:11.510234+00:00
-- url     : https://prove2.me/submissions/f469c27c-9125-46fa-872c-dcadafd88819

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Theorems.Thm_GlobalTheory_ThetaPtExist_exists_pullSec
import Theorems.Thm_GlobalTheory_ThetaAct_sv_ext
import Theorems.Thm_GlobalTheory_ThetaAct_sv_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtExist
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
open ThetaAct
namespace GlobalTheory.ThetaPtExist
theorem _root_.solution (hL : L.IsLB) {a : ℤ} {T' : Over S} (i : T' ⟶ T) (h : T ⟶ T')
    (hi : i ≫ h = 𝟙 T') (t : SecM A L a T) (ht : ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s) :
    ∃ th, IsGenSec A L a (T := T') th := by
  obtain ⟨t', ht'⟩ := exists_pullSec hL i t
  refine ⟨SecM.toSec A t', fun s => ?_⟩
  obtain ⟨s₀, hs₀⟩ := exists_pullSec hL h (SecM.ofSec A s)
  obtain ⟨r, hr⟩ := ht s₀
  have key : SecM.ofSec A s = i.left.appTop.hom r • t' := sv_ext hL fun y J hJ => by
    have e₁ : (𝟙 _ ≫ (i ▷ A).left) ≫ (h ▷ A).left = 𝟙 _ := by
      rw [Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, id_whiskerRight, Category.id_comp]; rfl
    have e₂ : (𝟙 _ ≫ (i ▷ A).left) ≫ (fst T A).left = (𝟙 _ ≫ (fst T' A).left) ≫ i.left := by
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
    have q := hs₀ _ (𝟙 _ ≫ (i ▷ A).left) y J hJ
    rw [e₁, ← hr, sv_smul _ _ _ _ hJ, e₂] at q
    rw [sv_smul _ _ _ _ hJ, ht' _ _ _ _ hJ, ← q]
    exact congrArg (· * _) (gs_pull (𝟙 _ ≫ (fst T' A).left) i.left y ⊤ trivial r).symm
  exact ⟨i.left.appTop.hom r, fun j => congrArg (fun q => q.1 j) key⟩
end GlobalTheory.ThetaPtExist
