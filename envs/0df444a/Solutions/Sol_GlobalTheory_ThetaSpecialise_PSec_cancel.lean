-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.PSec.cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:48:49.025686+00:00
-- url     : https://prove2.me/submissions/2f11d257-038c-4243-b5ec-f25167f9e94c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {X X' X'' Y Y' Y'' Y₁ Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'}
  {K : Type} [Fintype K] {ε : K → ℤ}
variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₁' ⟶ X)} {a : Y₁ ⟶ Y} {b : Y₁' ⟶ Y₁}
  {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Sec (LB.LinComb L φ₁ ε)} {v : LB.Sec (LB.LinComb L φ₂ ε)}
variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {s' : LB.Sec (LB.LinComb L' φ' ε)}
namespace GlobalTheory.ThetaSpecialise
namespace PSec
theorem _root_.solution {w' : LB.Iso L'' (L'.pull Φ')} {w'' : LB.Iso L'' (L.pull (Φ' ≫ Φ))} (T : Tri w w' w'')
    (hL : L.IsLB) {φ'' : K → (Y'' ⟶ X'')} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} (hc : ∀ k, φ'' k ≫ Φ' = h' ≫ φ' k)
    {s'' : LB.Sec (LB.LinComb L'' φ'' ε)} (H : PSec w φ' φ ε h s' s) (H'' : PSec w'' φ'' φ ε (h' ≫ h) s'' s) :
    PSec w' φ'' φ' ε h' s'' s' := by
  unfold Tri at T
  unfold PSec at H H'' ⊢
  intro Z r z p q hp hq
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  set P : K → L.ι := fun κ => J (r ≫ φ'' κ ≫ Φ' ≫ Φ)
  have hPmem : ∀ κ, Φ (Φ' (φ'' κ (r z))) ∈ L.U (P κ) := fun κ => by
    simpa only [Scheme.Hom.comp_apply] using hJ (r ≫ φ'' κ ≫ Φ' ≫ Φ)
  have pt : ∀ κ, φ' κ (h' (r z)) = Φ' (φ'' κ (r z)) := fun κ => by
    have hκ := congrArg (fun g : Y'' ⟶ X' => g (r z)) (hc κ)
    simp only [Scheme.Hom.comp_apply] at hκ
    exact hκ.symm
  have hP' : ∀ κ, Φ (φ' κ ((r ≫ h') z)) ∈ L.U (P κ) := fun κ => by
    rw [Scheme.Hom.comp_apply, pt κ]; exact hPmem κ
  have hp' : ∀ κ, φ' κ ((r ≫ h') z) ∈ L'.U (p κ) := fun κ => by
    rw [Scheme.Hom.comp_apply, pt κ]; exact hp κ
  have hP'' : ∀ κ, (Φ' ≫ Φ) (φ'' κ (r z)) ∈ L.U (P κ) := fun κ => by
    rw [Scheme.Hom.comp_apply]; exact hPmem κ
  have e : ∀ κ, (r ≫ φ'' κ) ≫ Φ' = (r ≫ h') ≫ φ' κ := fun κ => by
    rw [Category.assoc, hc κ, Category.assoc]
  have hprod : (∏ κ, gw w'' (r ≫ φ'' κ) z (P κ) (q κ) ^ ε κ) =
      (∏ κ, gw w ((r ≫ h') ≫ φ' κ) z (P κ) (p κ) ^ ε κ) * ∏ κ, gw w' (r ≫ φ'' κ) z (p κ) (q κ) ^ ε κ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun κ _ => ?_
    have m1 : Φ (Φ' ((r ≫ φ'' κ) z)) ∈ L.U (P κ) := by rw [Scheme.Hom.comp_apply]; exact hPmem κ
    have m2 : Φ' ((r ≫ φ'' κ) z) ∈ L'.U (p κ) := by rw [Scheme.Hom.comp_apply]; exact hp κ
    have m3 : (r ≫ φ'' κ) z ∈ L''.U (q κ) := by rw [Scheme.Hom.comp_apply]; exact hq κ
    rw [← mul_zpow, T Z (r ≫ φ'' κ) z (P κ) (p κ) (q κ) m1 m2 m3, e κ]
  have k1 := H Z (r ≫ h') z P p hP' hp'
  have k2 := H'' Z r z P q hP'' hq
  rw [Category.assoc] at k1
  rw [k1, hprod, Units.val_mul, _root_.mul_assoc] at k2
  exact (Units.mul_right_inj _).1 k2
end PSec
end GlobalTheory.ThetaSpecialise
