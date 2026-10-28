-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:33:59.898875+00:00
-- url     : https://prove2.me/submissions/1ec4e74f-29b1-45f8-96ed-fcf9fadf97e7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_BlowupCurveMargin_margin_of_contracted_q68
import Theorems.Thm_OAI_PiExponent_BlowupCurveMargin_margin_of_image_outside_chart_q68
import Theorems.Thm_OAI_PiExponent_BlowupCurveMargin_margin_of_nonnegative_degree_q68
import Theorems.Thm_OAI_PiExponent_CurveInequality_weighted_curve_inequality_q68
import Theorems.Thm_OAI_PiExponent_CurveNormalizationMorphism_exists_intrinsic_normalization_morphism_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightSeparationProducts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

theorem product_dominance_of_lower_indices
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A)
    (hB : ∀ j ∈ B, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by
  have hxnonneg : ∀ j, 0 ≤ x j := fun j => le_trans zero_le_one (hx j)
  have hsub : B ⊆ Finset.range i := by
    intro j hj
    exact Finset.mem_range.mpr (hB j hj)
  have hprodB : (∏ j ∈ B, x j) ≤ ∏ j ∈ Finset.range i, x j :=
    Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun j _ => hxnonneg j) (fun j _ _ => hx j)
  have hprodA : x i ≤ ∏ j ∈ A, x j := by
    have hsubA : ({i} : Finset ℕ) ⊆ A := Finset.singleton_subset_iff.mpr hiA
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_one_le hsubA
        (fun j _ => hxnonneg j) (fun j _ _ => hx j))
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hprodB hD.le) hgrowth) hprodA

theorem normalized_products_separated
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A) (hiB : i ∉ B)
    (hB : ∀ j ∈ B \ A, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by
  have hdiff : D * (∏ j ∈ B \ A, x j) < ∏ j ∈ A \ B, x j :=
    product_dominance_of_lower_indices x D hx hD (A \ B) (B \ A) i
      (Finset.mem_sdiff.mpr ⟨hiA, hiB⟩) hB hgrowth
  have hcommon : 0 < ∏ j ∈ A ∩ B, x j :=
    Finset.prod_pos (fun j _ => lt_of_lt_of_le zero_lt_one (hx j))
  calc
    D * (∏ j ∈ B, x j)
        = (∏ j ∈ A ∩ B, x j) * (D * (∏ j ∈ B \ A, x j)) := by
            rw [← Finset.prod_inter_mul_prod_sdiff B A x, Finset.inter_comm B A]
            ac_rfl
    _ < (∏ j ∈ A ∩ B, x j) * (∏ j ∈ A \ B, x j) :=
      mul_lt_mul_of_pos_left hdiff hcommon
    _ = ∏ j ∈ A, x j := Finset.prod_inter_mul_prod_sdiff A B x

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightSeparation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

theorem weightSeparationFactor_pos
    (m : ℕ) (C w0 v0 theta : ℝ) (hC : 0 < C) :
    0 < weightSeparationFactor m C w0 v0 theta := by
  unfold weightSeparationFactor
  have hbase : 0 < max 1 (max v0 (1 / theta) / min w0 1) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos hC (pow_pos hbase _)

theorem geometric_weight_products_of_normalized
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (A B : Finset ℕ) (hcard : A.card = B.card) (hbound : B.card ≤ m + 1)
    (hsep : weightSeparationFactor m C w0 v0 theta * (∏ i ∈ B, x i) <
      ∏ i ∈ A, x i) :
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) <
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by
  let L : ℝ := min w0 1
  let R : ℝ := max v0 (1 / theta)
  let T : ℝ := max 1 (R / L)
  have hL : 0 < L := lt_min hw0 zero_lt_one
  have hR : 0 < R := lt_of_lt_of_le hv0 (le_max_left _ _)
  have hT : 1 ≤ T := le_max_left _ _
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le zero_lt_one (hx i)
  have hdeg (i : ℕ) : L * x i ≤ geometricDegreeWeight w0 x i := by
    by_cases hi : i = 0
    · subst i
      simp only [geometricDegreeWeight, hx0, mul_one]
      exact min_le_left _ _
    · simp only [geometricDegreeWeight, ite_eq_right hi]
      exact mul_le_of_le_one_left (le_of_lt (hxpos i)) (min_le_right _ _)
  have hjet (i : ℕ) : geometricJetWeight v0 theta x i ≤ R * x i := by
    by_cases hi : i = 0
    · subst i
      simp only [geometricJetWeight, hx0, mul_one]
      exact le_max_left _ _
    · simp only [geometricJetWeight, ite_eq_right hi]
      calc
        x i / theta = (1 / theta) * x i := by ring
        _ ≤ R * x i := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (le_of_lt (hxpos i))
  have hdegprod : L ^ A.card * (∏ i ∈ A, x i) ≤
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by
    calc
      _ = ∏ i ∈ A, (L * x i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod (fun i _ => mul_nonneg (le_of_lt hL)
        (le_of_lt (hxpos i))) (fun i _ => hdeg i)
  have hjetnonneg (i : ℕ) : 0 ≤ geometricJetWeight v0 theta x i := by
    unfold geometricJetWeight
    split
    · exact le_of_lt hv0
    · exact div_nonneg (le_of_lt (hxpos i)) (le_of_lt htheta)
  have hjetprod : (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
      R ^ B.card * (∏ i ∈ B, x i) := by
    calc
      _ ≤ ∏ i ∈ B, (R * x i) := Finset.prod_le_prod
        (fun i _ => hjetnonneg i) (fun i _ => hjet i)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hRle : R ≤ T * L := (div_le_iff₀ hL).mp (le_max_right _ _)
  have hpowers : R ^ B.card ≤ T ^ (m + 1) * L ^ B.card := by
    calc
      R ^ B.card ≤ (T * L) ^ B.card := pow_le_pow_left₀ (le_of_lt hR) hRle _
      _ = T ^ B.card * L ^ B.card := mul_pow _ _ _
      _ ≤ T ^ (m + 1) * L ^ B.card := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hT hbound) (pow_nonneg (le_of_lt hL) _)
  have hprodB : 0 ≤ ∏ i ∈ B, x i := Finset.prod_nonneg fun i _ => le_of_lt (hxpos i)
  calc
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
        C * (R ^ B.card * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left hjetprod (le_of_lt hC)
    _ ≤ C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpowers hprodB) (le_of_lt hC)
    _ = L ^ A.card * (weightSeparationFactor m C w0 v0 theta *
          (∏ i ∈ B, x i)) := by
      rw [hcard]
      change C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) =
        L ^ B.card * ((C * T ^ (m + 1)) * (∏ i ∈ B, x i))
      ring
    _ < L ^ A.card * (∏ i ∈ A, x i) :=
      mul_lt_mul_of_pos_left hsep (pow_pos hL _)
    _ ≤ _ := hdegprod

theorem geometric_weight_products_separated
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (hgrowth : SeparatedWeightGrowth m (weightSeparationFactor m C w0 v0 theta) x)
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (m + 1)) (hB : B ⊆ Finset.range (m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    C * (∏ j ∈ B, geometricJetWeight v0 theta x j) <
      ∏ j ∈ A, geometricDegreeWeight w0 x j := by
  have hibound : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp (hA hiA))
  have hcardbound : B.card ≤ m + 1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hB
  apply geometric_weight_products_of_normalized m C w0 v0 theta x
    hC hw0 hv0 htheta hx0 hx A B hcard hcardbound
  exact PiExponent.normalized_products_separated x
    (weightSeparationFactor m C w0 v0 theta) hx
    (weightSeparationFactor_pos m C w0 v0 theta hC)
    A B i hiA hiB hbelow (hgrowth i hi hibound)

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleParameters
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

theorem interpolationSeparationConstant_pos (m : ℕ) (sigma : ℚ)
    (hsigma : 0 < (sigma : ℝ)) : 0 < interpolationSeparationConstant m sigma := by
  unfold interpolationSeparationConstant
  positivity

namespace AdmissibleParameters

variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

theorem separated_weight_products
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (d.m + 1)) (hB : B ⊆ Finset.range (d.m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    interpolationSeparationConstant d.m d.sigma *
      (∏ j ∈ B, PiExponentApprox.geometricJetWeight d.v0 d.base.theta d.x j) <
      ∏ j ∈ A, PiExponentApprox.geometricDegreeWeight d.w0 d.x j := by
  exact PiExponentApprox.geometric_weight_products_separated d.m
    (interpolationSeparationConstant d.m d.sigma) d.w0 d.v0 d.base.theta d.x
    (interpolationSeparationConstant_pos d.m d.sigma d.sigma_pos)
    d.w0_pos d.v0_pos d.base.theta_pos d.x_zero d.x_one_le d.weight_growth
    A B hcard hA hB i hi hiA hiB hbelow

end AdmissibleParameters

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHilbertDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section OrderLifting

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

theorem exists_chain_lift_last (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b)
    (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton b =>
      obtain ⟨a, ha⟩ := hs b
      exact ⟨RelSeries.singleton _ a, rfl, ha⟩
  | snoc p b hb ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      obtain ⟨a, ha, hab⟩ := hu q.last b (hlast.symm ▸ hb)
      refine ⟨q.snoc a ha, ?_, ?_⟩
      · simp only [RelSeries.snoc_length, hlen]
      · simpa only [RelSeries.last_snoc] using hab

theorem krullDim_le_of_goingUp (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b) :
    Order.krullDim β ≤ Order.krullDim α := by
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, _⟩ := exists_chain_lift_last f hs hu p
  exact hlen ▸ le_iSup (fun q : LTSeries α => (q.length : WithBot ℕ∞)) q

end OrderLifting

section IntegralDimension

variable {A B : Type*} [CommRing A] [CommRing B]

theorem ringKrullDim_eq_of_integral_injective (f : A →+* B)
    (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim B = ringKrullDim A := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hi⟩
  let c : PrimeSpectrum B → PrimeSpectrum A :=
    fun p => ⟨p.asIdeal.comap f, inferInstance⟩
  have hc : StrictMono c := by
    intro p q hpq
    obtain ⟨hpq', x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp (show p.asIdeal < q.asIdeal from hpq)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hpq' ⟨hxq, hxp⟩
      (Algebra.IsIntegral.isIntegral x)
  have hs : Function.Surjective c := by
    intro p
    obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal (⊥ : Ideal B) (by
        change RingHom.ker f ≤ p.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
        exact bot_le)
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
  have hu : ∀ a b, c a < b → ∃ a', a < a' ∧ c a' = b := by
    intro a b hab
    obtain ⟨q, haq, hq, hqb⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime b.asIdeal a.asIdeal hab.le
    refine ⟨⟨q, hq⟩, lt_of_le_of_ne haq ?_, PrimeSpectrum.ext hqb⟩
    intro heq
    have he : c a = b := by
      rw [heq]
      exact PrimeSpectrum.ext hqb
    exact hab.ne he
  exact le_antisymm (Order.krullDim_le_of_strictMono c hc)
    (krullDim_le_of_goingUp c hs hu)

end IntegralDimension

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_finite_normalization_with_dimension :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim R = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨s, g, hg, hfin, ?_⟩
  have hd := ringKrullDim_eq_of_integral_injective g.toRingHom hg hfin.to_isIntegral
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard, Nat.card_fin, zero_add, WithBot.coe_natCast] using hd

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffineTranscendenceDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section Normalization

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B]

theorem normalization_trdeg_toNat (s : ℕ)
    (g : MvPolynomial (Fin s) k →ₐ[k] B)
    (hg : Function.Injective g) (hi : g.IsIntegral) :
    (Algebra.trdeg k B).toNat = s := by
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hi⟩
  have : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  have ht := congrArg Cardinal.toNat
    (lift_trdeg_add_eq k (MvPolynomial (Fin s) k) B)
  simpa [trdeg_eq_zero] using ht.symm

theorem finiteType_domain_krullDim_eq_trdeg [Algebra.FiniteType k B] :
    ringKrullDim B = ((Algebra.trdeg k B).toNat : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin, hdim⟩ := exists_finite_normalization_with_dimension k B
  rw [hdim, normalization_trdeg_toNat k B s g hg hfin.to_isIntegral]

end Normalization

section AlgebraicTower

variable (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
  [IsScalarTower k B C] [FaithfulSMul B C]

theorem trdeg_toNat_eq_of_algebraic_tower [Algebra.IsAlgebraic B C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k B C)
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero, Cardinal.toNat_lift] using ht

theorem localization_trdeg_toNat_eq (M : Submonoid B) [IsLocalization M C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have : Algebra.IsAlgebraic B C := IsLocalization.isAlgebraic C M
  exact trdeg_toNat_eq_of_algebraic_tower k B C

end AlgebraicTower

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveWeights
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AdmissibleParameters
noncomputable section
open scoped BigOperators
variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

lemma curveDegreeWeights_cast (i : Fin (d.m + 1)) :
    (d.curveDegreeWeights i : ℝ) = PiExponentApprox.geometricDegreeWeight d.w0 d.x i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [PiExponentApprox.geometricDegreeWeight]
  · simp [PiExponentApprox.geometricDegreeWeight, d.cast_rationalWeight]

lemma curveJetWeights_cast (i : Fin (d.m + 1)) :
    (d.curveJetWeights i : ℝ) = PiExponentApprox.geometricJetWeight d.v0 d.base.theta d.x i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [PiExponentApprox.geometricJetWeight]
  · simp [PiExponentApprox.geometricJetWeight, d.cast_rationalWeight]

lemma curve_fibre_product_ratio :
    (∏ i : Fin d.m, (d.curveDegreeWeights i.succ : ℝ)) /
      (∏ i : Fin d.m, (d.curveJetWeights i.succ : ℝ)) = (d.base.theta : ℝ) ^ d.m := by
  have hp : (∏ i : Fin d.m, (d.rationalWeight (i.val + 1) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast ne_of_gt (d.rationalWeight_pos _))
  simp only [curveDegreeWeights_succ, curveJetWeights_succ, Rat.cast_div,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hp]

lemma curve_product_ratio :
    (∏ i : Fin (d.m + 1), (d.curveDegreeWeights i : ℝ)) /
      (∏ i : Fin (d.m + 1), (d.curveJetWeights i : ℝ)) =
      ((d.w0 : ℝ) / d.v0) * (d.base.theta : ℝ) ^ d.m := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_div_mul_comm, d.curve_fibre_product_ratio]
  rfl

lemma curve_volume :
    (d.K : ℝ) * (1 + 3 * (d.sigma : ℝ)) ^ (d.m + 1) *
      (∏ i, (d.curveDegreeWeights i : ℝ)) / (∏ i, (d.curveJetWeights i : ℝ)) < 1 := by
  calc
    _ = (1 + 3 * (d.sigma : ℝ)) ^ (d.m + 1) *
        ((d.K : ℝ) * ((∏ i, (d.curveDegreeWeights i : ℝ)) /
          (∏ i, (d.curveJetWeights i : ℝ)))) := by ring
    _ = (1 + 3 * (d.sigma : ℝ)) ^ (d.m + 1) *
        ((d.K : ℝ) * ((d.w0 : ℝ) / d.v0) * (d.base.theta : ℝ) ^ d.m) := by
      rw [d.curve_product_ratio]
      ring
    _ < 1 := d.sigma_volume

lemma curve_fibre_volume :
    (d.K : ℝ) * (1 + 3 * (d.sigma : ℝ)) ^ d.m *
      (∏ i : Fin d.m, (d.curveDegreeWeights i.succ : ℝ)) /
      (∏ i : Fin d.m, (d.curveJetWeights i.succ : ℝ)) < 1 := by
  calc
    _ = (1 + 3 * (d.sigma : ℝ)) ^ d.m *
        ((d.K : ℝ) * ((∏ i : Fin d.m, (d.curveDegreeWeights i.succ : ℝ)) /
          (∏ i : Fin d.m, (d.curveJetWeights i.succ : ℝ)))) := by ring
    _ = (1 + 3 * (d.sigma : ℝ)) ^ d.m *
        ((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m) := by rw [d.curve_fibre_product_ratio]
    _ < 1 := d.sigma_centers

lemma curve_coordinate_ratio (i : Fin d.m) :
    (1 + (d.sigma : ℝ)) * (d.curveDegreeWeights i.succ : ℝ) <
      (d.curveJetWeights i.succ : ℝ) := by
  simp only [curveDegreeWeights_succ, curveJetWeights_succ, Rat.cast_div]
  apply (lt_div_iff₀ d.base.theta_pos).mpr
  have hi : (0 : ℝ) < d.rationalWeight (i.val + 1) := by exact_mod_cast d.rationalWeight_pos _
  nlinarith [mul_lt_mul_of_pos_right d.sigma_theta hi]

lemma curve_separated_weight_products (A B : Finset (Fin (d.m + 1)))
    (hcard : A.card = B.card) (i : Fin (d.m + 1)) (hi : i ≠ 0)
    (hiA : i ∈ A) (hiB : i ∉ B)
    (hhigh : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) :
    PersistentWeightComparison.comparisonConstant d.m d.sigma *
      (∏ j ∈ B, (d.curveJetWeights j : ℝ)) <
      ∏ j ∈ A, (d.curveDegreeWeights j : ℝ) := by
  classical
  let e : Fin (d.m + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hbound (S : Finset (Fin (d.m + 1))) : S.map e ⊆ Finset.range (d.m + 1) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨k, hkB, rfl⟩ := Finset.mem_map.mp hjB
    by_contra hnot
    have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
    have hne : i ≠ k := fun h => hiB (h.symm ▸ hkB)
    have hkA := (hhigh k (lt_of_le_of_ne hik hne)).mpr hkB
    exact hjA (Finset.mem_map.mpr ⟨k, hkA, rfl⟩)
  have hn : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have h := d.separated_weight_products (A.map e) (B.map e)
    (by simpa using hcard) (hbound A) (hbound B) i.val hn
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩)
    (by
      intro hmem
      obtain ⟨a, haB, hai⟩ := Finset.mem_map.mp hmem
      have hai' : a = i := Fin.ext hai
      exact hiB (hai' ▸ haB))
    hbelow
  simpa only [Finset.prod_map, e, Function.Embedding.coeFn_mk,
    ← d.curveJetWeights_cast, ← d.curveDegreeWeights_cast,
    PersistentWeightComparison.comparisonConstant, interpolationSeparationConstant] using h

end
end PiExponent.AdmissibleParameters

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveInequalityIntrinsic
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkClosedPointTo_isIso _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkMap_isIso _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveInequality

open CurveValuationCenter PlaceValuationRing CurveContactFamily PersistentWeightComparison


variable {E : Type*} [Field E] [Algebra ℂ E]

variable [Algebra.EssFiniteType ℂ E]

theorem admissible_weighted_curve_inequality {nu Lambda C : ℝ}
    (d : AdmissibleParameters nu Lambda C)
    (y : E) (x : Fin d.m → E) (c : Fin d.K → Fin d.m → ℂ)
    (hc : ∀ i, Function.Injective (fun j => c j i))
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m+1) → E := Fin.cases y x
    let hz := nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
      (contact hres hfinite z c hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  weighted_curve_inequality_q68 y x c hc hgen htrdeg
    d.curveDegreeWeights d.curveJetWeights d.curveDegreeWeights_pos d.curveJetWeights_pos
    d.sigma (by exact_mod_cast d.sigma_pos) d.curve_volume d.curve_fibre_volume
    d.curve_separated_weight_products d.curve_coordinate_ratio

end PiExponent.CurveInequality
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveInequality
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkClosedPointTo_isIso _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkMap_isIso _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.AdmissibleParameters

variable {nu Lambda C : ℝ} (d : AdmissibleParameters nu Lambda C)

theorem exact_weighted_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m+1) → E := Fin.cases y x
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  CurveInequality.admissible_weighted_curve_inequality d y x d.curveCenters
    d.curveCenters_injective hgen htrdeg

end PiExponent.AdmissibleParameters
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem centerIdeal_support_subset_chart :
    ((centerIdeal d).support : Set (compactification d)) ⊆ (affineChart d).opensRange := by
  rw [centerIdeal_support]
  intro x hx
  obtain ⟨j,z,rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨CompactLogJetIdeal.point (d.curveCenters j) z,rfl⟩

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupCurveMargin
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BlowupCurveMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness
variable {B X : Scheme.{0}}

variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
variable {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

theorem actual_contact_bound (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    (1 + (d.sigma : ℝ)) * contactSum d y x hgen htrdeg ≤ poleDegree d y x htrdeg :=
  d.exact_weighted_curve_inequality y x hgen htrdeg

theorem margin_of_actual_contact_degrees
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (C : IntegralCurve B) (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) (R : ℚ) (hR : 0 < R)
    (hA : (curveDegree p A C : ℝ) = (R : ℝ) * poleDegree d y x htrdeg)
    (hJ : (curveDegree p J C : ℝ) = -(R : ℝ) * contactSum d y x hgen htrdeg) :
    marginCoefficient a d.sigma * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  apply margin_of_nonnegative_degree_q68 p A J a ha hample d.sigma d.sigma_pos C
  rw [hA, hJ]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR.le
  have h := mul_le_mul_of_nonneg_left (actual_contact_bound d y x hgen htrdeg) hR'
  nlinarith


end PiExponent.BlowupCurveMargin

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGeometricFunctionField
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveGeometricFunctionField

open CategoryTheory AlgebraicGeometry

variable (k A E : Type*) [Field k] [CommRing A] [IsDomain A] [Field E]
  [Algebra k A] [Algebra k E] [Algebra A E] [IsScalarTower k A E]
  [IsFractionRing A E]

omit [IsDomain A] in
theorem fractionField_essFiniteType [Algebra.FiniteType k A] :
    Algebra.EssFiniteType k E := by
  let : Algebra.EssFiniteType A E :=
    Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors A)
  exact Algebra.EssFiniteType.comp k A E

theorem fractionField_trdeg_eq_one [Algebra.FiniteType k A]
    (hdim : ringKrullDim A = 1) : Algebra.trdeg k E = 1 := by
  let : FaithfulSMul A E :=
    (faithfulSMul_iff_algebraMap_injective A E).mpr (IsFractionRing.injective A E)
  have hd : (Algebra.trdeg k A).toNat = 1 := by
    rw [PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg k A] at hdim
    exact_mod_cast hdim
  have he := PiExponentJets.W24.localization_trdeg_toNat_eq k A E
    (nonZeroDivisors A)
  exact Cardinal.toNat_eq_one.mp (he.symm.trans hd)

omit [IsDomain A] in
theorem adjoin_coordinates_eq_top {ι : Type*}
    (φ : MvPolynomial ι k →ₐ[k] A) (hφ : Function.Surjective φ) :
    IntermediateField.adjoin k (Set.range (coordinates k A E φ)) = ⊤ := by
  let x := coordinates k A E φ
  let K := IntermediateField.adjoin k (Set.range x)
  have hψ : (IsScalarTower.toAlgHom k A E).comp φ = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x, coordinates]
  have hmem (a : A) : algebraMap A E a ∈ K := by
    obtain ⟨p, rfl⟩ := hφ a
    apply IntermediateField.algebra_adjoin_le_adjoin k (Set.range x)
    rw [← MvPolynomial.aeval_range]
    refine ⟨p, ?_⟩
    exact (congrArg (fun f : MvPolynomial ι k →ₐ[k] E => f p) hψ).symm
  apply top_le_iff.mp
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A z
  exact K.div_mem (hmem a) (hmem b)

theorem of_surjective_coordinates {ι : Type*} [Finite ι]
    (φ : MvPolynomial ι k →ₐ[k] A) (hφ : Function.Surjective φ)
    (hdim : ringKrullDim A = 1) :
    Algebra.EssFiniteType k E ∧ Algebra.trdeg k E = 1 ∧
      IntermediateField.adjoin k (Set.range (coordinates k A E φ)) = ⊤ := by
  let : Algebra.FiniteType k A := Algebra.FiniteType.of_surjective φ hφ
  exact ⟨fractionField_essFiniteType k A E,
    fractionField_trdeg_eq_one k A E hdim, adjoin_coordinates_eq_top k A E φ hφ⟩

attribute [local instance] intrinsicSectionAlgebra

end PiExponent.CurveGeometricFunctionField

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupMargin
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open AdmissibleBlowupGeometry BlowupCurveMargin
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem uniform_margin_of_affine_curve_data
    (a : ℕ) (ha : 1 < a) (hample : (((A d).pow a).tensor (J d)).IsAmple)
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AffineCurveDegreeData d C)) :
    ∀ C : IntegralCurve (blowup d),
      marginCoefficient a d.sigma *
          (curveDegree (structureMap d) (((A d).pow a).tensor (J d)) C : ℝ) ≤
        (curveDegree (structureMap d) ((A d).tensor (J d)) C : ℝ) := by
  classical
  intro C
  by_cases hc : ∃ x : compactification d,
      Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)
  · obtain ⟨x,hx⟩ := hc
    exact margin_of_contracted_q68 (structureMap d) (projection d) (hyperplane d) (J d)
      a ha hample d.sigma d.sigma_pos C x hx
  · by_cases hm : ∃ c : C.scheme,
        (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange
    · obtain ⟨r⟩ := hdata C hc hm
      let := r.field
      let := r.algebra
      let := r.essFiniteType
      exact margin_of_actual_contact_degrees d (structureMap d) (A d) (J d)
        a ha hample C r.y r.x r.coordinates_generate r.trdeg_one
        (scale d).radius (by exact_mod_cast (scale d).radius_pos)
        r.hyperplane_degree r.exceptional_degree
    · exact margin_of_image_outside_chart_q68 (structureMap d) (centerIdeal d)
        (projection d) (A d) (J d) (exceptionalInclusion d) (exceptional_presents d)
        a ha hample d.sigma d.sigma_pos C (affineChart d).opensRange
        (centerIdeal_support_subset_chart d) (fun c hh => hm ⟨c,hh⟩)

end PiExponent.AdmissibleBlowupMargin

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupPolarization
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem ampleExponent_gt_one : 1 < ampleExponent d := (exists_ampleExponent d).choose_spec.1

theorem uniform_curve_margin_of_affine_curve_data
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AdmissibleBlowupMargin.AffineCurveDegreeData d C)) :
    ∀ C : IntegralCurve (blowup d),
      uniformMargin d * (curveDegree (structureMap d) (H d) C : ℝ) ≤
        (curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  AdmissibleBlowupMargin.uniform_margin_of_affine_curve_data d (ampleExponent d)
    (ampleExponent_gt_one d) (H_ample d) hdata

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IntegralAffineOpenDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.IntegralAffineOpenDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of k))

theorem germToFunctionField_fromSpec (U : X.affineOpens) [Nonempty U.1] :
    Spec.map (X.germToFunctionField U.1) ≫ U.2.fromSpec =
      X.fromSpecStalk (genericPoint X) :=
  U.2.fromSpecStalk_eq_fromSpecStalk _

theorem chart_functionField_scalarTower (U : X.affineOpens) [Nonempty U.1] :
    letI := chartAlgebra p U
    letI := functionFieldAlgebra p
    IsScalarTower k Γ(X, U.1) X.functionField := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  have h : Spec.preimage (U.2.fromSpec ≫ p) ≫ X.germToFunctionField U.1 =
      Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc,
      germToFunctionField_fromSpec, Spec.map_preimage]
  exact IsScalarTower.of_algebraMap_eq' (CommRingCat.hom_ext_iff.mp h).symm

omit [IsIntegral X] in
theorem chart_finiteType [LocallyOfFiniteType p] (U : X.affineOpens) :
    letI := chartAlgebra p U
    Algebra.FiniteType k Γ(X, U.1) := by
  let := chartAlgebra p U
  have h : LocallyOfFiniteType (Spec.map (Spec.preimage (U.2.fromSpec ≫ p))) := by
    rw [Spec.map_preimage]
    let hOpen : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    let : LocallyOfFiniteType U.2.fromSpec :=
      @locallyOfFiniteType_of_isOpenImmersion _ _ U.2.fromSpec hOpen
    exact locallyOfFiniteType_comp U.2.fromSpec p
  have h' : RingHom.FiniteType (chartConstants p U) := HasRingHomProperty.Spec_iff.mp h
  exact RingHom.finiteType_algebraMap.mp h'

theorem chart_ring_dimension [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    letI := functionFieldAlgebra p
    ringKrullDim Γ(X, U.1) = ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  let := chart_functionField_scalarTower p U
  let := chart_finiteType p U
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let : FaithfulSMul Γ(X, U.1) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  rw [PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg k Γ(X, U.1),
    PiExponentJets.W24.localization_trdeg_toNat_eq k Γ(X, U.1) X.functionField
      (nonZeroDivisors Γ(X, U.1))]

omit [IsIntegral X] in
theorem affine_dimension_eq_ring (U : X.affineOpens) :
    topologicalKrullDim U.1 = ringKrullDim Γ(X, U.1) := by
  have h := U.2.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  change topologicalKrullDim U.1 = topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) at h
  exact h.trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

theorem affine_open_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    topologicalKrullDim U.1 = topologicalKrullDim X := by
  let := functionFieldAlgebra p
  have hU : topologicalKrullDim U.1 =
      ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) :=
    (affine_dimension_eq_ring U).trans (chart_ring_dimension p U)
  apply le_antisymm (topologicalKrullDim_subspace_le X U.1)
  change topologicalKrullDim X ≤ topologicalKrullDim U.1
  rw [hU]
  apply PiExponent.NumericalAmpleness.dimension_le_of_local_bound
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact ⟨V, hxV, ((affine_dimension_eq_ring ⟨V, hV⟩).trans
    (chart_ring_dimension p ⟨V, hV⟩)).le⟩

theorem affine_ring_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    ringKrullDim Γ(X, U.1) = topologicalKrullDim X :=
  (affine_dimension_eq_ring U).symm.trans (affine_open_dimension_eq p U)

end PiExponent.IntegralAffineOpenDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveImageAffineCoordinates
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} [IsIntegral C]
variable {ι : Type}

theorem preimage_surjective {R S : CommRingCat}
    (q : Spec S ⟶ Spec R) [IsClosedImmersion q] :
    Function.Surjective (Spec.preimage q) := by
  have he : Spec.preimage q = (Scheme.ΓSpecIso R).inv ≫ q.appTop ≫
      (Scheme.ΓSpecIso S).hom := by
    have h : Spec.preimage q = (Scheme.ΓSpecIso R).inv ≫
        (Spec.map (Spec.preimage q)).appTop ≫ (Scheme.ΓSpecIso S).hom := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    simpa only [Spec.map_preimage] using h
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).surjective.comp
    ((q.app_surjective ⊤ (isAffineOpen_top _)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)

theorem field_properties [Finite ι] (p : C ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim C = 1) (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ))) [IsClosedImmersion q]
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra p
    Algebra.EssFiniteType ℂ C.functionField ∧ Algebra.trdeg ℂ C.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates U q)) = ⊤ := by
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.functionFieldAlgebra p
  let := IntegralAffineOpenDimension.chart_functionField_scalarTower p U
  let := functionField_isFractionRing_of_isAffineOpen C U.1 U.2
  have hdimA : ringKrullDim Γ(C,U.1) = 1 :=
    (IntegralAffineOpenDimension.affine_ring_dimension_eq p U).trans hdim
  exact CurveGeometricFunctionField.of_surjective_coordinates ℂ Γ(C,U.1) C.functionField
    (presentation p U q hq) (preimage_surjective q) hdimA

theorem coordinates_generic_map
    (p : C ⟶ Spec (.of ℂ)) (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p)
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) (i : C ⟶ X)
    (hchart : q ≫ j = U.2.fromSpec ≫ i) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra p
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (coordinates U q)).toRingHom) ≫ j =
      C.fromSpecStalk (genericPoint C) ≫ i := by
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.functionFieldAlgebra p
  let := IntegralAffineOpenDimension.chart_functionField_scalarTower p U
  have he : (MvPolynomial.aeval (coordinates U q)).toRingHom =
      (C.germToFunctionField U.1).hom.comp (Spec.preimage q).hom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (coordinates U q) =
        (IsScalarTower.toAlgHom ℂ Γ(C,U.1) C.functionField).comp (presentation p U q hq) from ?_)
    apply MvPolynomial.algHom_ext
    intro a
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, ← CommRingCat.hom_comp, CommRingCat.ofHom_hom, Spec.map_comp,
    Spec.map_preimage, Category.assoc, hchart, ← Category.assoc,
    IntegralAffineOpenDimension.germToFunctionField_fromSpec]

theorem transport_field_properties {F E : Type} [Field F] [Field E]
    [Algebra ℂ F] [Algebra ℂ E] [Algebra.EssFiniteType ℂ F]
    (e : F ≃ₐ[ℂ] E) (x : ι → F)
    (hd : Algebra.trdeg ℂ F = 1)
    (hx : IntermediateField.adjoin ℂ (Set.range x) = ⊤) :
    Algebra.EssFiniteType ℂ E ∧ Algebra.trdeg ℂ E = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (e ∘ x)) = ⊤ := by
  refine ⟨Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective,
    e.trdeg_eq.symm.trans hd, ?_⟩
  rw [Set.range_comp]
  change IntermediateField.adjoin ℂ (e.toAlgHom '' Set.range x) = ⊤
  rw [← IntermediateField.adjoin_map ℂ (Set.range x) e.toAlgHom, hx,
    ← AlgHom.fieldRange_eq_map]
  exact e.fieldRange_eq_top

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveImageAffineChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} {ι : Type}

theorem affinePresentation_over (p : X ⟶ Spec (.of ℂ))
    (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ))) :
    affinePresentation i j ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      (affinePart i j).2.fromSpec ≫ i ≫ p := by
  rw [← hj, ← Category.assoc, affinePresentation_comp, Category.assoc]

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveCoordinates
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry
open CurveImageAffineCoordinates
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
variable (C : NumericalAmpleness.IntegralCurve (blowup d))
variable (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})

variable (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange)

theorem field_properties :
    letI := sourceAlgebra d C
    Algebra.EssFiniteType ℂ C.scheme.functionField ∧
      Algebra.trdeg ℂ C.scheme.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates d C hn hm)) = ⊤ := by
  let := sourceAlgebra d C
  let := imageAlgebra d C hn
  let := chart_nonempty d C hn hm
  obtain ⟨ht,hd,hg⟩ := CurveImageAffineCoordinates.field_properties
    (imageStructure d C hn) (imageCurve d C hn).dimension
    (chart d C hn) (chartPresentation d C hn)
    (affinePresentation_over (compactificationStructureMap d) _ _ (affineChart_over d))
  let := ht
  exact transport_field_properties (fieldEquiv d C hn)
    (imageCoordinates d C hn hm) hd hg

theorem coordinates_generic_map :
    letI := sourceAlgebra d C
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm)).toRingHom) ≫
      affineChart d = C.scheme.fromSpecStalk (genericPoint C.scheme) ≫
        C.embedding ≫ projection d := by
  let := sourceAlgebra d C
  let := imageAlgebra d C hn
  let := chart_nonempty d C hn hm
  have himage := CurveImageAffineCoordinates.coordinates_generic_map
    (imageStructure d C hn) (chart d C hn) (chartPresentation d C hn)
    (affinePresentation_over (compactificationStructureMap d) _ _ (affineChart_over d))
    (affineChart d) (imageCurve d C hn).embedding (affinePresentation_comp _ _)
  have he : (MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm)).toRingHom =
      (AdmissibleCurveImage.functionFieldIso d C hn).hom.hom.comp
        (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)).toRingHom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm) =
        (fieldEquiv d C hn).toAlgHom.comp
          (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)) from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)).toRingHom) ≫ affineChart d =
      (imageCurve d C hn).scheme.fromSpecStalk (genericPoint (imageCurve d C hn).scheme) ≫
        (imageCurve d C hn).embedding from himage]
  exact AdmissibleCurveImage.functionFieldIso_generic d C hn

end PiExponent.AdmissibleCurveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveModel
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem existsModelData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ t : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {t})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (ModelData d C) := by
  let := AdmissibleCurveCoordinates.sourceAlgebra d C
  have hp := AdmissibleCurveCoordinates.field_properties d C hn hm
  let := hp.1
  let z := AdmissibleCurveCoordinates.coordinates d C hn hm
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField hp.2.1
  obtain ⟨i,hi⟩ := CurveInequality.nonconstant_coordinates z hp.2.2 hp.2.1
  let f := z i
  have hf : Transcendental ℂ f := hi
  let := hfinite f hf
  obtain ⟨g,hg,hgeneric,hgfinite,W,hW,hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism_q68
      (C.embedding ≫ structureMap d) C.dimension f hf
  let := hgfinite
  let := hWiso
  have hWne : W ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection d) =
      CurveMonomialMap.genericMonomialMap (exponents d) (constantIndex d)
        ((scale d).exponents_constant d.curveDegreeWeights_pos) (coordinateIndex d)
        ((scale d).exponents_coordinate d.curveDegreeWeights_pos) z := by
    change parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection d) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart d
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    exact (AdmissibleCurveCoordinates.coordinates_generic_map d C hn hm).symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := hp.1
           coordinates := z
           coordinates_generate := hp.2.2
           trdeg_one := hp.2.1
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

end PiExponent.AdmissibleCurveModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveDegreeData
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupMargin
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := AdmissibleCurveModel.existsModelData d C hn hm
  exact ⟨AdmissibleCurveModel.degreeData d C r⟩

end PiExponent.AdmissibleBlowupMargin

namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem uniform_curve_margin_q68_oai :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (AdmissibleBlowupMargin.affineCurveDegreeData d)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68_oai := @OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68_oai
