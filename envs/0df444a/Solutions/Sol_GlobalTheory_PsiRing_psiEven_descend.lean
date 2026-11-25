-- Prove2me | solution 1 for GlobalTheory.PsiRing.psiEven_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:00.761205+00:00
-- url     : https://prove2.me/submissions/eb27075b-a66b-4821-8371-78a514f6f2a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiEvenDescendBaseChange
import Theorems.Thm_GlobalTheory_PsiRing_val_sym_comp
import Theorems.Thm_GlobalTheory_CubTransport_val_pmaps
import Theorems.Thm_GlobalTheory_PsiEvenPull_c_neg
import Theorems.Thm_GlobalTheory_TauPull_corr_of_dense
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
noncomputable section
open GlobalTheory GlobalTheory.PsiRing
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
  {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)}
namespace GlobalTheory.PsiRing
theorem _root_.solution : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.PsiEven → D.PsiEven := by
  intro hG R V _ _ _ _ φ D D' β v xe gp hv hc gam hgam hψ h χ
  obtain ⟨x, rfl⟩ := xe.surjective χ
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  have red : IsReduced (TK R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  have cx : ∀ a, D'.xK a ≫ β = gam ≫ D.xK (xe a) := fun a => by
    show (jK V ≫ (D'.c a).left) ≫ β = gam ≫ jK R ≫ (D.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam, Category.assoc]
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  refine TauPull.corr_of_dense D.P.isLB gam z (fun U ⟨y, hy⟩ => Subsingleton.elim y (gam z) ▸ hy) fun J hJ => ?_
  choose J' hJ₀ using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have hJ' : Good D'.P.L z J' := hJ₀
  have vψ : ∀ a, val (D.psi (xe a)) gam z J =
      (gw v (D'.xK a) z (J (D'.xK a ≫ β)) (J' (D'.xK a)))⁻¹ * val (D'.psi a) (𝟙 _) z J' := fun a => by
    have := CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ hJ'
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have e := val_corr hJ' (h x) (𝟙 _)
  rw [val_mul hJ', val_pull hJ', Category.id_comp] at e
  rw [val_mul hJ, val_pull hJ, ← map_neg, vψ, vψ, ← cx, val_sym_comp hG gp hv _ z hJ hJ', ← cn]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'
end GlobalTheory.PsiRing
