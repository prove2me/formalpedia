-- Prove2me | solution 1 for GlobalTheory.ExpUniq.sval_term_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:01.074091+00:00
-- url     : https://prove2.me/submissions/ed2dfc2e-f9e3-4c1c-953c-503685a2f042

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
import Theorems.Thm_GlobalTheory_ExpUniq_sval_eq_zero_of_group
import Theorems.Thm_GlobalTheory_ExpUniq_sval_eq_zero_of_weight_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {σ σ' : U.SecGT T k} {f f' : ∀ α, SecBT D T k α}
namespace GlobalTheory.ExpUniq
theorem _root_.solution (h : U.ExpT T k σ f)
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ _) z J, Good U.P.L.L z J → sval σ r z J = 0) (α : D.X) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ D.P.A).left) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (ha : (r ≫ (snd T D.P.A).left) ≫ D.P.A.hom = a ≫ thick R I e) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f α) r z J = 0 := by
  obtain ⟨s, hs⟩ := h e
  have hb : (U.gt e).pG.left ≫ D.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left),
      r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ z J, Good D.P.L z J →
      (∀ α ∉ s, sval (f α) r z J = 0) ∧ ∑ χ ∈ s, sval (f χ) r z J * (val ((U.gt e).t χ) x z J).val = 0 := by
    intro Z x r hr z J hJ
    have w : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
      rw [Category.assoc, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, ← hr, Category.assoc,
        Category.assoc, Over.w, Over.w]
    obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
    obtain ⟨E₁, E₂⟩ := hs Z x (pullback.lift _ _ w) r (pullback.lift_snd _ _ _) hr (pullback.lift_fst _ _ _).symm
      z JG J hJG hJ
    exact ⟨E₁, E₂.symm.trans ((congrArg _ (hσ _ _ z JG hJG)).trans (mul_zero _))⟩
  refine sval_eq_zero_of_group (U.gt e) (snd T D.P.A).left (f α) (fun Z x r hr z J hJ => ?_) r a ha z J hJ
  by_cases hα : α ∈ s
  · exact sval_eq_zero_of_weight_sum (U.gt e) (snd T D.P.A).left f s
      (fun Z x r hr z J hJ => (H Z x r hr z J hJ).2) α hα Z x r hr z J hJ
  · exact (H Z x r hr z J hJ).1 α hα
end GlobalTheory.ExpUniq
