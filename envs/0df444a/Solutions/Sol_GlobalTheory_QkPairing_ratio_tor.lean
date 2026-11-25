-- Prove2me | solution 1 for GlobalTheory.QkPairing.ratio_tor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:24.336955+00:00
-- url     : https://prove2.me/submissions/3cc9928e-096b-444d-a35b-c61dcd6dff5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_WeilQkPairingExistsUniqueTorus
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.QkPairing
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
namespace GlobalTheory.QkPairing
theorem _root_.solution (p p' : QkPt D F k) (t : Multiplicative D.X →* Fˣ) (hy : p.y = 0) (ht : IsTor t p.g) {ζ : F}
    (H : IsRatio p p' ζ) : ζ = (t (Multiplicative.ofAdd p'.y)).val := by
  let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
  choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := H _ (𝟙 _) z J hJ
  have e₀ : val (p'.g.s p.y) (𝟙 _) z J = 1 := by
    rw [hy]; exact (val_corr hJ p'.g.s_zero _).trans (val_one _)
  have e₁ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p'.g.b) (𝟙 _ ≫ p.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact C.N_one _ _ _
  have e₂ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p.g.b) (𝟙 _ ≫ p'.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  rw [e₁, e₂, Over.id_left, e₀, _root_.mul_one, _root_.mul_one, Units.val_one, _root_.mul_one, ht.2 _ z J hJ, cst,
    gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at e
  exact ((((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙 (TF (R := R) F).left :
    (TF (R := R) F).left ⟶ _).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)).injective e).symm
end GlobalTheory.QkPairing
