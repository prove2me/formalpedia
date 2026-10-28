-- Prove2me | solution 1 for OAI.CoulombAtom.sharp_joint_selected_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:55:42.949677+00:00
-- url     : https://prove2.me/submissions/c1b89133-b739-458c-8c66-c8336f00be16

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_sharp_cell_local_potential

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchTruncationLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchDensityCapConstant_pos : 0 < tfPatchDensityCapConstant := by
  exact Real.rpow_pos_of_pos (div_pos tfPatchCapConstant_pos (mul_pos (by norm_num) tfKinetic_pos)) _

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma thinFieldBase_collar_bound {a b m D B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m)
    (hDm : D*a ≤ m^2) (hbm : a ≤ b^2*m) (hB : 0 ≤ B)
    (hC : 1 ≤ C) (hBC : B ≤ C*m^2) :
    thinFieldBase a b D B ≤ (6+C+localizationIMSConstant*C)*(m/a)^2 := by
  have hfield := localFieldScale_linear_bound ha hm h3 hC hBC (D := D)
  have hr : Real.sqrt B ≤ C*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1)
      (le_trans zero_le_one hm) (by simpa using hBC)
  have hD : D/a ≤ (m/a)^2 := by
    have hh := div_le_div_of_nonneg_right hDm (sq_nonneg a)
    calc _ = (D*a)/a^2 := by field_simp
         _ ≤ m^2/a^2 := hh
         _ = _ := by ring
  have hcollar : m/(b^2*a) ≤ (m/a)^2 := by
    have hh := mul_le_mul_of_nonneg_left hbm (show 0 ≤ m/(b^2*a^2) by positivity)
    calc _ = m/(b^2*a^2)*a := by field_simp
         _ ≤ m/(b^2*a^2)*(b^2*m) := hh
         _ = _ := by field_simp
  have hI := localizationIMSConstant_nonneg
  have hC0 := le_trans zero_le_one hC
  have hi : localizationIMSConstant*Real.sqrt B/(b^2*a) ≤
      localizationIMSConstant*C*(m/a)^2 := by
    calc _ ≤ localizationIMSConstant*(C*m)/(b^2*a) := by gcongr
         _ = localizationIMSConstant*C*(m/(b^2*a)) := by ring
         _ ≤ _ := by gcongr
  unfold thinFieldBase
  nlinarith only [hfield,hD,hi]

lemma sharpFreshFieldConstant_one_le : 1 ≤ sharpFreshFieldConstant := by
  have hC := actualCellMomentConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold sharpFreshFieldConstant
  have h : 0 ≤ thinFieldUniversalConstant*(6+actualCellMomentConstant+
      localizationIMSConstant*actualCellMomentConstant) := by positivity
  linarith only [h]

lemma sharpFreshField_square {a b D B m : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hDm : D*a ≤ m^2) (hbm : a ≤ b^2*m)
    (hB : 0 ≤ B) (hBC : B ≤ actualCellMomentConstant*m^2) :
    thinFieldUniversalConstant*thinFieldBase a b D B ≤ (sharpFreshFieldConstant*(m/a))^2 := by
  have hh := thinFieldBase_collar_bound ha hb hm h3 hDm hbm hB actualCellMomentConstant_one_le hBC
  let K := thinFieldUniversalConstant*(6+actualCellMomentConstant+
    localizationIMSConstant*actualCellMomentConstant)
  have hK : 0 ≤ K := by
    have := thinFieldUniversalConstant_pos
    have := actualCellMomentConstant_one_le
    have := localizationIMSConstant_nonneg
    dsimp [K]; positivity
  have hKK : K ≤ sharpFreshFieldConstant^2 := by change K ≤ (1+K)^2; nlinarith only [hK]
  calc _ ≤ K*(m/a)^2 := by
          have ht := mul_le_mul_of_nonneg_left hh thinFieldUniversalConstant_pos.le
          exact ht.trans_eq (by dsimp [K]; ring)
       _ ≤ sharpFreshFieldConstant^2*(m/a)^2 := mul_le_mul_of_nonneg_right hKK (sq_nonneg _)
       _ = _ := by ring

theorem sharp_cell_fresh_field_mass {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b r Z lam : ℝ} (hb : 0 < b) (hba : b ≤ localCellRadius y)
    (hr : r ∈ Set.Icc (5*localCellRadius y) (6*localCellRadius y))
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ hr0 : 0 ≤ r,
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
        (coreFirstRadialCut_partition y hr0 hb) ψ Z lam ≤
          (sharpFreshFieldConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y/localCellRadius y))^2 ∧
      freshPatchMass (coreFirstRadialCut y hr0 hb) (coreFirstRadialCut_partition y hr0 hb)
        ψ Z lam y (r-4*b) ≤
          768*sharpFreshFieldConstant*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (16*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hr0 : 0 ≤ r := le_trans (by positivity : 0 ≤ 5*a) hr.1
  have hsep : 20*a ≤ ‖y‖ := by dsimp [a,localCellRadius]; nlinarith [norm_nonneg y]
  have hbcount : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+16*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hψ hm hZ hlam hy)
  have hsq := sharpFreshField_square ha hb (localOffsetMass_one_le D y)
    (localOffsetMass_cube_le D y) (localOffsetMass_offset (le_max_right _ _) hy) hcollar
    (rawCountMoment_nonneg ψ y (16*a)) hbcount
  refine ⟨hr0,(freshOutMaximum_thin_bound hψ hm y ha hr0 hr.2 hb hba hsep hZ hlam).trans hsq,?_⟩
  have hh := freshPatchMass_thin_bound hψ hm y ha hr0 hr.2 hb (by linarith [hr.1]) hba hsep hZ hlam
  have hQ : 0 ≤ sharpFreshFieldConstant*(m/a) := by
    have := sharpFreshFieldConstant_one_le
    have := localOffsetMass_one_le D y
    positivity
  have hroot := Real.sqrt_le_iff.mpr ⟨hQ,hsq⟩
  calc _ ≤ 768*a*Real.sqrt (thinFieldUniversalConstant*thinFieldBase a b D B) := hh
       _ ≤ 768*a*(sharpFreshFieldConstant*(m/a)) := mul_le_mul_of_nonneg_left hroot (by positivity)
       _ = _ := by dsimp [m,D]; field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SelectedMasterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann CoulombObservation

theorem selected_fresh_patch_budget_with_deletion {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hba : 7*b < 5*a) (hy : 6*a+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      let p := coreFirstRadialCut y ht hb
      let hp := coreFirstRadialCut_partition y ht hb
      let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
      (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        (outerDeletedCount y t b u)^2*
          formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤ (8*b/a)*B ∧
      (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention L y t b c s) u) ≤
        corePriceExcess Z lam ψ+
        (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ)+
        b⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+B^(1/2:ℝ))+
        (((2*Real.pi+1)/2)/b)*B^(1/2:ℝ)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*Real.sqrt ((8*b/a)*B)+
        ((packetDirichlet g/2)*b⁻¹^2)*freshPatchMass p hp ψ Z lam y (t-4*b) := by
  obtain ⟨t,ht,ht0,hd,hfirst,h43,hims⟩ :=
    radial_fresh_selected_counts hψ.sobolevVector hm y ha hb (by linarith)
  refine ⟨t,ht,ht0,hd,?_⟩
  have htb : 7*b < t := lt_of_lt_of_le hba ht.1
  have hty : t+2*b ≤ ‖y‖ := le_trans (by linarith [ht.2]) hy
  have he := radial_fresh_patch_budget hψ y hb htb (by linarith) hZ hlam hg hcg hgn hr hgs
  dsimp only at he ⊢
  rw [radial_fresh_tail_split hψ.sobolevVector y _ hb (by linarith) (by linarith)] at he
  have hdel := radial_deleted_field_budget hψ.sobolevVector y ht0 hb hty hZ hlam.le
  dsimp only at hdel
  have hds := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd)
    (Real.sqrt_nonneg (freshOutMaximumSecondMoment (coreFirstRadialCut y ht0 hb) (coreFirstRadialCut_partition y ht0 hb) ψ Z lam))
  have h43' := mul_le_mul_of_nonneg_left h43
    (mul_nonneg (sq_nonneg b⁻¹) neumannRemainderConstant_pos.le)
  have hfirst' := mul_le_mul_of_nonneg_left hfirst
    (by positivity : 0 ≤ (((2*Real.pi+1)/2)/b))
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpFreshPatchBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpFreshPatch_barrier_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma count_two_thirds_scale {B C m : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hBC : B ≤ C*m^2) : B^(2/3:ℝ) ≤ C^(2/3:ℝ)*m^(4/3:ℝ) := by
  have hh := Real.rpow_le_rpow hB hBC (by norm_num : (0:ℝ) ≤ 2/3)
  have he : (C*m^2)^(2/3:ℝ) = C^(2/3:ℝ)*m^(4/3:ℝ) := by
    rw [Real.mul_rpow hC (sq_nonneg m),←Real.rpow_natCast,←Real.rpow_mul hm]
    norm_num
  rwa [he] at hh

end CoulombAtom

end Work_SharpFreshPatch_barrier_scope

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpLocalPotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

 theorem sharp_selected_patch_energy {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b Z lam r : ℝ} (hb : 0 < b) (hba : 7*b < 5*localCellRadius y)
    (hr : r ∈ Icc (5*localCellRadius y) (6*localCellRadius y)) (hr0 : 0 ≤ r)
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    selectedPatchEnergyError ψ y (localCellRadius y) hr0 hb Z lam canonicalRealPacket ≤
      corePriceExcess Z lam ψ+sharpPatchRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (7*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hba' : b ≤ a := by linarith
  obtain ⟨hr0',hfield,hmass⟩ := sharp_cell_fresh_field_mass hψ hm hy hb hba' hr hZ hlam hcollar
  have hBC : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+7*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hψ hm hZ hlam hy)
  have hB : 0 ≤ B := rawCountMoment_nonneg ψ y (7*a)
  have hC := actualCellMomentConstant_one_le
  have hC0 := le_trans zero_le_one hC
  have hm0 : 0 ≤ m := le_trans zero_le_one (localOffsetMass_one_le D y)
  have hroot : Real.sqrt B ≤ actualCellMomentConstant*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hBC)
  have htwo := count_two_thirds_scale hB hC0 hm0 hBC
  have hsqrt : Real.sqrt ((8*b/a)*B) ≤ Real.sqrt (8*b/a)*actualCellMomentConstant*m := by
    rw [Real.sqrt_mul (show 0 ≤ 8*b/a by positivity)]
    exact (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)).trans_eq (by ring)
  have hF0 : 0 ≤ sharpFreshFieldConstant*(m/a) := by
    have := sharpFreshFieldConstant_one_le
    positivity
  have hfieldroot : Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ Z lam) ≤ sharpFreshFieldConstant*(m/a) :=
    Real.sqrt_le_iff.mpr ⟨hF0,hfield⟩
  have hims : (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2 = localizationIMSConstant/b^2 := by
    unfold localizationIMSConstant
    ring
  unfold selectedPatchEnergyError
  dsimp only
  rw [←rawCountMoment_eq_integral hψ.sobolevVector y (7*a)]
  simp only [←Real.sqrt_eq_rpow,hims]
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  change _ ≤ corePriceExcess Z lam ψ+sharpPatchRemainder a b m
  unfold sharpPatchRemainder
  simp only [←add_assoc]
  gcongr

 theorem sharp_selected_potential_error {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {b Z lam r q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hr : r ∈ Icc (5*localCellRadius y) (6*localCellRadius y)) (hr0 : 0 ≤ r)
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    selectedPotentialError ψ y (localCellRadius y) hr0 hb Z lam q canonicalRealPacket ≤
      sharpPotentialRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) (max (corePriceExcess Z lam ψ) 0) q := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (7*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  have hsf := hψ.sobolevFermion
  have h7 : 7*b < 5*a := by linarith
  have hE := sharp_selected_patch_energy hsf hm hy hb h7 hr hr0 hZ hlam hcollar
  have hE' : selectedPatchEnergyError ψ y a hr0 hb Z lam canonicalRealPacket ≤
      D+sharpPatchRemainder a b m := hE.trans (add_le_add (le_max_left _ _) le_rfl)
  have hq3 : 0 < q+Real.sqrt 3*b := by positivity
  have hb3 : 0 < Real.sqrt 3*b := by positivity
  have hqB := sharp_cell_local_potential hψ hy ha1 hZ hlam hq3 hqr
  have hbB := sharp_cell_local_potential hψ hy ha1 hZ hlam hb3 (by linarith : Real.sqrt 3*b ≤ 4*a)
  have hBC : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hsf.sobolevVector y y
      (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+7*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hsf hm hZ hlam hy)
  have hB : 0 ≤ B := rawCountMoment_nonneg ψ y (7*a)
  have hm0 : 0 ≤ m := le_trans zero_le_one (localOffsetMass_one_le D y)
  have hC := actualCellMomentConstant_one_le
  have hroot : Real.sqrt B ≤ actualCellMomentConstant*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hBC)
  have hsqrt : Real.sqrt ((8*b/a)*B) ≤ Real.sqrt (8*b/a)*actualCellMomentConstant*m := by
    rw [Real.sqrt_mul (show 0 ≤ 8*b/a by positivity)]
    exact (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)).trans_eq (by ring)
  have ht7 : a ≤ r-7*b := by linarith [hr.1]
  have ht4 : a ≤ r-4*b := by linarith [hr.1]
  have hcap : 0 ≤ 2*Real.pi*tfPatchDensityCapConstant*q^2 := by
    have := tfPatchDensityCapConstant_pos
    positivity
  have hcap' : 2*Real.pi*tfPatchDensityCapConstant*q^2/(r-4*b)^6 ≤
      2*Real.pi*tfPatchDensityCapConstant*q^2/a^6 := by gcongr
  have hdel : Real.sqrt ((8*b/a)*B)/(r-7*b) ≤
      (Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a := by gcongr
  change _ ≤ sharpPotentialRemainder a b m D q
  unfold selectedPotentialError sharpPotentialRemainder
  rw [←rawCountMoment_eq_integral hsf.sobolevVector y (7*a)]
  exact add_le_add (add_le_add (add_le_add (add_le_add
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE' (by positivity))) hqB) hcap') hbB) hdel

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_SharpJointComparisonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

theorem sharp_joint_selected_patch_oai {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {b Z lam q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ r ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ hr0 : 0 ≤ r,
      radialPatchGapMean ψ y hr0 hb Z lam ≤ corePriceExcess Z lam ψ+
        sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) ∧
      radialPotentialError ψ y hr0 hb Z lam q ≤
        sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)
          (max (corePriceExcess Z lam ψ) 0) q := by
  have ha := localCellRadius_pos hy
  have h7 : 7*b < 5*localCellRadius y := by linarith
  have hn : 6*localCellRadius y+2*b ≤ ‖y‖ := by
    unfold localCellRadius at *
    nlinarith [norm_nonneg y]
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  obtain ⟨r,hr,hr0,hd,hgap⟩ := selected_fresh_patch_budget_with_deletion
    hψ.sobolevFermion hm y ha hb h7 hn hZ hlam canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  have hgs : radialPatchGapMean ψ y hr0 hb Z lam ≤
      selectedPatchEnergyError ψ y (localCellRadius y) hr0 hb Z lam canonicalRealPacket := hgap
  refine ⟨r,hr,hr0,hgs.trans (sharp_selected_patch_energy hψ.sobolevFermion hm hy
    hb h7 hr hr0 hZ hlam hcollar),?_⟩
  have htb : 0 < r-7*b := by linarith [hr.1]
  have he := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2/q))
  have hd' := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hd) htb.le
  have hpot : radialPotentialError ψ y hr0 hb Z lam q ≤
      selectedPotentialError ψ y (localCellRadius y) hr0 hb Z lam q canonicalRealPacket := by
    simp only [radialPotentialError,hm,Real.sqrt_one,one_mul,mul_one,selectedPotentialError,
      selectedPatchEnergyError]
    exact add_le_add (add_le_add (add_le_add (add_le_add he le_rfl) le_rfl) le_rfl) hd'
  exact hpot.trans (sharp_selected_potential_error hψ hy ha1 hb hba hr hr0 hZ hlam hq hqr hcollar)

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.sharp_joint_selected_patch_oai := @OAI.CoulombAtom.sharp_joint_selected_patch_oai
