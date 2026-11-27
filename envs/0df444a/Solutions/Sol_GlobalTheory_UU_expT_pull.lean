-- Prove2me | solution 1 for GlobalTheory.UU.expT_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:35:45.455551+00:00
-- url     : https://prove2.me/submissions/479235ea-7539-48aa-b270-64284ff876c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPullSecSval
import Theorems.Thm_GlobalTheory_UU_exists_pullSec_sval
import Theorems.Thm_P2M_GlobalTheory_UU_whisker_fam_T_e5d72d444ec4
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
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → ∃ (σ' : U.SecGT T' k) (f' : ∀ α, SecBT D T' k α), U.ExpT T' k σ' f' ∧ PullT ρ f f' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T') (s : Raw D F k), PullB D F φ k f' s ↔ PullB D F (φ ≫ ρ) k f s := by
  intro R _ _ I D A G _ _ U T T' ρ k σ f H
  obtain ⟨σ', hσ⟩ := exists_pullSec_sval σ (ρ ▷ G).left (fun _ => (snd T' G).left) (fun _ => by
    show (ρ ▷ G ≫ snd T G).left = _
    rw [whiskerRight_snd])
  choose f' hf using fun α => exists_pullSec_sval (f α) (ρ ▷ D.P.A).left (famφT D T' α) (whisker_famφT D ρ α)
  have s1 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (snd T B).left = (snd T' B).left := fun B => by
    show (ρ ▷ B ≫ snd T B).left = _
    rw [whiskerRight_snd]
  have s2 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (fst T B).left = (fst T' B).left ≫ ρ.left := fun B => by
    show (ρ ▷ B ≫ fst T B).left = (fst T' B ≫ ρ).left
    rw [whiskerRight_fst]
  refine ⟨σ', f', fun e => ?_, fun α Z r z J hJ => hf α Z r z J hJ, fun F _ _ φ s => ?_⟩
  · obtain ⟨s, hs⟩ := H e
    refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hJ => ?_⟩
    have := hs Z x (rG ≫ (ρ ▷ G).left) (rB ≫ (ρ ▷ D.P.A).left) (by rw [Category.assoc, s1, h1])
      (by rw [Category.assoc, s1, h2])
      (by rw [Category.assoc, s2, Category.assoc, s2, ← Category.assoc, h3, Category.assoc]) z JG J hG hJ
    refine ⟨fun α hα => (hf α Z rB z J hJ).trans (this.1 α hα), ?_⟩
    rw [hσ Z rG z JG hG, this.2]
    exact Finset.sum_congr rfl fun α _ => by rw [hf α Z rB z J hJ]
  · have e : (φ ▷ D.P.A).left ≫ (ρ ▷ D.P.A).left = ((φ ≫ ρ) ▷ D.P.A).left := by
      rw [comp_whiskerRight]; rfl
    have key : ∀ α (z : (DegPre.BF D F).left) J, Good D.P.L z J →
        sval (f' α) (φ ▷ D.P.A).left z J = sval (f α) ((φ ≫ ρ) ▷ D.P.A).left z J := fun α z J hJ =>
      (hf α _ (φ ▷ D.P.A).left z J hJ).trans (congrArg (fun q => sval (f α) q z J) e)
    exact ⟨fun h α z J hJ => (h α z J hJ).trans (key α z J hJ), fun h α z J hJ => (h α z J hJ).trans (key α z J hJ).symm⟩
end GlobalTheory.UU
