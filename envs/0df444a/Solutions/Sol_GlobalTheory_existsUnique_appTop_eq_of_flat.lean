-- Prove2me | solution 1 for GlobalTheory.existsUnique_appTop_eq_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:08.140804+00:00
-- url     : https://prove2.me/submissions/e6d0847b-f8e6-43fa-829d-f69e5ed64f90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_mOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_fnOf_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_fnOf_mOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (m : X ⟶ Y) [QuasiCompact m]
    [Surjective m] [Flat m] (f : Γ(X, ⊤))
    (h : ∀ {Z : Scheme.{0}} (a b : Z ⟶ X), a ≫ m = b ≫ m → a ≫ TLinPf.mOf f = b ≫ TLinPf.mOf f) :
    ∃! g : Γ(Y, ⊤), m.appTop.hom g = f := by
  refine ⟨TLinPf.fnOf (EffectiveEpi.desc m (TLinPf.mOf f) h), ?_, ?_⟩
  · beta_reduce
    rw [← TLinPf.fnOf_comp, EffectiveEpi.fac, TLinPf.fnOf_mOf]
  · intro g hg
    rw [← TLinPf.fnOf_mOf g]
    congr 1
    apply EffectiveEpi.uniq
    rw [TLinPf.comp_mOf, hg]
end GlobalTheory
