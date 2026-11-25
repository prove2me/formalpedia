-- Prove2me | solution 1 for GlobalTheory.psiScal_eq_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:53:12.392135+00:00
-- url     : https://prove2.me/submissions/5e938cee-e9c0-47ed-9193-7e3a786fa891

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiScalarEqExpansionCoefRatio
import Theorems.Thm_GlobalTheory_PsiRatio_exists_cstHom
import Theorems.Thm_GlobalTheory_PsiRatio_cst_eq_scal
import Theorems.Thm_GlobalTheory_MulPullSec_mem_nonzeroLocus_iff
import Theorems.Thm_GlobalTheory_PsiInt_scal_jK
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  intro R _ _ D ga a f th hS hR hN χ q p hq hp
  let B : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let T : Over (Spec (CommRingCat.of R)) := TK R ⊗ B
  let pt : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨z₀, hz₀, hth⟩ := hN (jK R pt)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := jK R) (g := B.hom) pt z₀ hz₀.symm
  let z' : T.left := z
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z'
  let x : T ⟶ D.P.A := snd (TK R) B ≫ snd _ _
  have ex : lift (toUnit T) x = snd (TK R) B := by
    ext1
    · exact toUnit_unique _ _
    · exact lift_snd _ _
  have ey : x * (cT D T χ)⁻¹ * cT D T χ = x := inv_mul_cancel_right _ _
  have hu : IsUnit (sval th (snd (TK R) B).left z' J) := by
    refine (MulPullSec.mem_nonzeroLocus_iff th (snd (TK R) B).left z' hJ).1 ?_
    have : (snd (TK R) B).left z' = z₀ := hz
    rw [this]
    exact hth
  have e₁ := hR χ T (toUnit _) (fst (TK R) B) (x * (cT D T χ)⁻¹) z' J hJ
  have e₂ := (hS χ).2 T (fst (TK R) B) z' J hJ
  have e₃ := hq _ (snd (TK R) B).left z' J hJ
  have e₄ := hp T (x * (cT D T χ)⁻¹) z' J hJ
  rw [ey, ex] at e₁ e₄
  have e' : T.hom = (fst (TK R) B).left ≫ jK R := (Over.w (fst (TK R) B)).symm
  have e'' : (snd (TK R) B).left ≫ B.hom = (fst (TK R) B).left ≫ jK R := (Over.w (snd (TK R) B)).trans e'
  obtain ⟨φ, -, hφ⟩ := PsiRatio.exists_cstHom (F := FractionRing R) (fst (TK R) B).left z'
  have hc : ∀ c : R, cst ((fst (TK R) B).left ≫ jK R) z' c = φ (algebraMap R (FractionRing R) c) := fun c =>
    (PsiRatio.cst_eq_scal _ _ _).trans ((congrArg (gs (𝟙 _) z' ⊤) (PsiInt.scal_jK _ c)).trans (hφ _))
  have c₃ := (congrArg (fun s => cst s z' q) e'').trans (hc q)
  have c₄ := (congrArg (fun s => cst s z' p) e').trans (hc p)
  have alg : ∀ (A : Type) [CommRing A] (s s₀ t cq cp ca cq' cp' ca' : A) (u g r : Aˣ), IsUnit t →
      s = (u * r).val * s₀ → u.val = ca * g.val → s₀ = cq * t → s = cp * ((g * r).val * t) →
      cq = cq' → cp = cp' → ca = ca' → cq' * ca' = cp' := by
    intro A _ s s₀ t cq cp ca cq' cp' ca' u g r ht h₁ h₂ h₃ h₄ h₅ h₆ h₇
    subst h₅ h₆ h₇
    refine (((g * r).isUnit.mul ht).mul_left_inj).1 ?_
    rw [← h₄, h₁, h₃, Units.val_mul, Units.val_mul, h₂]
    ring
  apply φ.injective
  rw [map_mul]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ hu e₁ e₂ e₃ e₄ c₃ c₄ (hφ _)
end GlobalTheory
