-- Prove2me | solution 1 for GlobalTheory.WitnessData.exists_psi_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:03.95419+00:00
-- url     : https://prove2.me/submissions/357cd6b2-fadc-4ddd-9a8e-d9182fb3baef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
import Theorems.Thm_GlobalTheory_WitnessData_unit_ext_field
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
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
noncomputable section
open GlobalTheory GlobalTheory.WitnessData
namespace GlobalTheory.WitnessData
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {Φ : D'.P.A.left ⟶ D.P.A.left}
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W)
    {g : (TK R).left ⟶ (TW W).left} (hg : g ≫ W.ι = jK R) {x : D'.X} {y : D.X} (hx : D'.xK x ≫ Φ = D.xK y)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ (z : Sp F) (p : D.P.L.ι) (q : D'.P.L.ι), Φ (D'.xK x (jFK (R := R) F z)) ∈ D.P.L.U p →
      D'.xK x (jFK (R := R) F z) ∈ D'.P.L.U q →
      gm (jFK (R := R) F) z (LB.wchart D.P.L (fun _ : PUnit => D.xK y) (fun _ => p)) ((D.psi y).s (fun _ => p)) =
        gw w (jFK (R := R) F ≫ D'.xK x) z p q ^ (-1 : ℤ) *
          gm (jFK (R := R) F) z (LB.wchart D'.P.L (fun _ : PUnit => D'.xK x) (fun _ => q)) ((D'.psi x).s (fun _ => q))) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) w (D'.xK x) (-1) (D'.psi x) b ∧
      LB.Gen.Corr D.P.L _ _ _ _ b (LB.pullGen D.P.L _ _ (ψW.psi y) g) := by
  have hc : g ≫ (toUnit (TW W) ≫ D.c y).left = D'.xK x ≫ Φ := by
    rw [hx]
    show g ≫ W.ι ≫ (D.c y).left = jK R ≫ (D.c y).left
    rw [← Category.assoc, hg]
  obtain ⟨b, -, vb⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ Φ) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) hc)
    (LB.pullGen D.P.L _ _ (ψW.psi y) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen y) g)
  refine ⟨b, fun jN jL => ?_, corr_of_val D.P.isLB fun z J hJ => vb _ _ z J hJ⟩
  have hW : jFK (R := R) F ≫ jK R = (jFK (R := R) F ≫ g) ≫ W.ι := by rw [Category.assoc, hg]
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : Sp F ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = jFK (R := R) F ∧
      lam ≫ (jK R ∣_ W) = jFK (R := R) F ≫ g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW.symm,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine unit_ext_field (algebraMap (FractionRing R) F) fun z hz => ?_
  have hp : Φ (D'.xK x (jFK (R := R) F z)) ∈ D.P.L.U (jN PUnit.unit) := mem_pull.1 hz.1
  have hq : D'.xK x (jFK (R := R) F z) ∈ D'.P.L.U jL := hz.2
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : PUnit => jFK (R := R) F ≫ D'.xK x ≫ Φ) jN
    (fun _ _ _ => rfl) (fun _ => hp)
  have v : val b (jFK (R := R) F) z J = val (D.psi y) (jFK (R := R) F) z J := by
    have e := val_corr hJ (ψW.psi_eq y) lam
    rw [val_pull hJ, val_pull hJ, l₁, l₂] at e
    exact (vb _ _ z J hJ).trans ((val_pull hJ _ _ _).trans e)
  rw [val_of b _ z J jN eJ, val_of (D.psi y) _ z J jN (fun k => by rw [← eJ k, hx])] at v
  refine (gm_res _ z _ hz _).trans (v.trans ((H z (jN PUnit.unit) jL hp hq).trans (Eq.symm
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res _ z _ hz _))))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ z _ hz _))
end GlobalTheory.WitnessData
