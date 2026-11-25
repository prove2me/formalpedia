-- Prove2me | solution 1 for GlobalTheory.exists_sec_of_generic_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:07.057869+00:00
-- url     : https://prove2.me/submissions/6f70d223-3eda-40b7-8c74-553eb3d9f21e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecOfGenericFibre
import Theorems.Thm_GlobalTheory_TwistLoc_exists_clear_denominator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y : Over (Spec (CommRingCat.of V))) [QuasiCompact Y.hom] [IsSeparated Y.hom] (K : Type) [Fintype K] (φ : K → (Y.left ⟶ Z)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L (fun k => (snd (TK V) Y).left ≫ φ k) ε)), ∃ (r : V) (_ : r ≠ 0) (σ : LB.Sec (LB.LinComb L φ ε)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (TK V ⊗ Y).left) (z : T) (J), Good L z J → sval σ (ρ ≫ (snd (TK V) Y).left) z J = gs ρ z ⊤ (scal (TK V ⊗ Y).hom r) * sval s ρ z J := by
  intro V _ _ Z L hL Y _ _ K _ φ ε s
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have H : IsPullback (snd (TK V) Y).left (fst (TK V) Y).left Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :=
    (IsPullback.of_hasPullback (TK V).hom Y.hom).flip
  obtain ⟨t, ht, σ, hσ⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors V) H hL φ ε s
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun T ρ z J hJ => ?_⟩
  rw [sval_of σ (ρ ≫ (snd (TK V) Y).left) z J (fun k => J (ρ ≫ (snd (TK V) Y).left ≫ φ k))
    (fun k => by rw [Category.assoc])]
  refine (hσ T ρ z _ (hJ.mem (fun k => (snd (TK V) Y).left ≫ φ k) ρ)).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [Over.w (snd (TK V) Y)]
  exact (gs_pull ρ (TK V ⊗ Y).hom z ⊤ trivial _).symm
end GlobalTheory
