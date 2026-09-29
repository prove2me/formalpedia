-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.isCuspidal_of_not_isAffinePlace_reduceFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4843c78a-2c71-5e50-a431-e14b376e6d82

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_of_not_isAffinePlace_reduceFst
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace MOVHcd1

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_of_ord_sub_pos (v : Place K F) {g : F} {b : K}
    (h : 0 < v.ord (g - algebraMap K F b)) : v.HasValue g b := by
  have hne : g - algebraMap K F b ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := v.mem_of_ord_nonneg hne h.le
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (g - algebraMap K F b) = 0 at h0
    omega
  have hgmem : g ∈ v.toValuationSubring := by
    have : g = (g - algebraMap K F b) + algebraMap K F b := by ring
    rw [this]
    exact add_mem hmem (v.algebraMap_mem' b)
  refine ⟨hgmem, ?_⟩
  have hx : (⟨g, hgmem⟩ : v.toValuationSubring) =
      ⟨_, hmem⟩ + ⟨algebraMap K F b, v.algebraMap_mem' b⟩ := Subtype.ext (by push_cast; ring)
  rw [hx, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add]
  exact v.residue_algebraMap b

theorem sum_mapDomain_eq_sum_filter {α β : Type*} [DecidableEq β] (r : α → β) (D : α →₀ ℤ) (S : Finset β) :
    ∑ v ∈ S, Finsupp.mapDomain r D v = ∑ P ∈ D.support.filter (fun P => r P ∈ S), D P := by
  classical
  have happ : ∀ v, Finsupp.mapDomain r D v = ∑ P ∈ D.support, if r P = v then D P else 0 := by
    intro v
    simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp_rw [happ]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P hP => ?_
  by_cases h : r P ∈ S
  · rw [if_pos h, Finset.sum_ite_eq S (r P) (fun _ => D P), if_pos h]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro v hv
    rw [if_neg]
    rintro rfl
    exact h hv

theorem transcendental_of_coeff_neg_ne_zero [IsAlgClosed K] (E : IntermediateField K (LaurentSeries K)) (x : E)
    (hx : ((x : E) : LaurentSeries K).coeff (-1) ≠ 0) : Transcendental K x := by
  intro halg

  have hint : IsIntegral K x := halg.isIntegral
  have hirr := minpoly.irreducible hint
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K hirr
  have hmem : x ∈ (algebraMap K E).range := minpoly.mem_range_of_degree_eq_one K x hdeg
  obtain ⟨c, hc⟩ := hmem
  have : ((x : E) : LaurentSeries K) = algebraMap K (LaurentSeries K) c := by
    rw [← hc]; rfl
  rw [this, algebraMap_laurentSeries_eq_single] at hx
  simp at hx

end Generic

section Modular

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

theorem not_dvd_div' (p M : ℕ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p := fun h =>
  hpM2 (by rw [pow_two, ← Nat.mul_div_cancel' hpM]; exact Nat.mul_dvd_mul_left p h)

scoped instance finiteIndex_ΓN' : (JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))

theorem exists_carrier_down : ∃ xj : (Fbar p M H hpM (ResidueField ↥A)), ((xj : (Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) :=
  ⟨⟨jqModC (ResidueField ↥A), intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))⟩, rfl⟩

theorem exists_carrier_up : ∃ x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
  have hjQ : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))
    exact intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  have hmem := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjQ
  have hco : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  rw [hco] at hmem
  exact ⟨⟨jqModC (AlgebraicClosure ℚ), hmem⟩, rfl⟩

theorem mem_or_neg_mem_gammaH_of_mem_sup (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CohCarrier.GammaH N (H' ⊔ Subgroup.zpowers (-1))) :
    γ ∈ CohCarrier.GammaH N H' ∨ -γ ∈ CohCarrier.GammaH N H' := by
  obtain ⟨h0, hu⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hneg0 : -γ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    simp [Matrix.SpecialLinearGroup.coe_neg, h0]
  have hunits : CohCarrier.gamma0Units N ⟨-γ, hneg0⟩ = -CohCarrier.gamma0Units N ⟨γ, h0⟩ := by
    ext
    simp [CohCarrier.val_gamma0Units, CongruenceSubgroup.Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]
  rcases Int.even_or_odd k with hk | hk
  · left
    rw [hk.neg_one_zpow, mul_one] at hyz
    exact CohCarrier.mem_GammaH_iff.mpr ⟨h0, hyz ▸ hy⟩
  · right
    rw [hk.neg_one_zpow] at hyz
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hneg0, ?_⟩
    rw [hunits, ← hyz, mul_neg_one, neg_neg]
    exact hy

end Modular

end MOVHcd1
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_of_not_isAffinePlace_reduceFst.MOVHcd1"

set_option maxHeartbeats 3200000 in
open Classical in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A)
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hV : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V)) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V := by
  classical
  intro x hx a
  by_contra hle
  push Not at hle
  haveI : (JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex := MOVHcd1.finiteIndex_ΓN' p M H hpM
  have hT : ModularGroup.T ∈ (JHNeronObjectAtP.ΓN p M H hpM) := ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  have hpN : ¬ p ∣ M / p := MOVHcd1.not_dvd_div' p M hpM hpM2
  obtain ⟨x', hx'⟩ := MOVHcd1.exists_carrier_up p M H hpM
  obtain ⟨xj, hxj⟩ := MOVHcd1.exists_carrier_down p M H hpM A

  have hj1 : ∀ (K : Type) [CommRing K] [Nontrivial K], (jqModC K).coeff (-1) ≠ 0 := by
    intro K _ _; simp [ModularCurve.coeff_jqModC_neg_one]
  have htr_up : Transcendental (AlgebraicClosure ℚ) x' :=
    MOVHcd1.transcendental_of_coeff_neg_ne_zero _ x' (by rw [hx']; exact hj1 (AlgebraicClosure ℚ))
  have htr_dn : Transcendental (ResidueField ↥A) xj :=
    MOVHcd1.transcendental_of_coeff_neg_ne_zero _ xj (by rw [hxj]; exact hj1 (ResidueField ↥A))

  haveI hfin_dn : FiniteDimensional (IntermediateField.adjoin (ResidueField ↥A) ({xj} : Set (Fbar p M H hpM (ResidueField ↥A)))) (Fbar p M H hpM (ResidueField ↥A)) :=
    (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) hT (JHNeronObjectAtP.ΓN p M H hpM) le_rfl
      (fun γ h => Or.inl h) xj hxj).1
  have key : ∀ (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) (z : E), ((z : E) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      E = qExpFunctionFieldC (AlgebraicClosure ℚ) (JHNeronObjectAtP.ΓN p M H hpM) → FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({z} : Set E)) E := by
    rintro E z hz rfl
    exact (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index (AlgebraicClosure ℚ) (JHNeronObjectAtP.ΓN p M H hpM) hT (JHNeronObjectAtP.ΓN p M H hpM) le_rfl
      (fun γ h => Or.inl h) z hz).1
  haveI hfin_up : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    key _ x' hx' (ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) (JHNeronObjectAtP.ΓN p M H hpM))

  obtain ⟨Sup, hSup, hsum_up⟩ := AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed (AlgebraicClosure ℚ) x' htr_up hfin_up (a : (AlgebraicClosure ℚ))
  obtain ⟨Sdn, hSdn, hsum_dn⟩ := AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed (ResidueField ↥A) xj htr_dn hfin_dn
    (IsLocalRing.residue ↥A a)

  have hchain : (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) : ℤ) ≤
      Module.finrank (IntermediateField.adjoin (ResidueField ↥A) ({xj} : Set (Fbar p M H hpM (ResidueField ↥A)))) (Fbar p M H hpM (ResidueField ↥A)) := by
    have h1 := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index (AlgebraicClosure ℚ) (JHNeronObjectAtP.ΓN p M H hpM) hT
      (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1))) (ModularCurve.GammaH_mono le_sup_left)
      (fun γ hγ => MOVHcd1.mem_or_neg_mem_gammaH_of_mem_sup (M / p) (infSubgroup p M H hpM) γ hγ) x' hx'
    have h2 := ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField (M / p) (infSubgroup p M H hpM)
      (ℓ := p) hpN A hA xj hxj
    exact_mod_cast h1.trans h2

  set f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)) with hf
  have hαx : α x' = x := Subtype.ext (by rw [hα_coe x', hx', hx])
  have hαf : α f = x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) := by rw [hf, map_sub, hαx, AlgHom.commutes]
  set W := V.restrictAlong α hα with hWdef
  have hordW : 0 < W.ord f := by
    have h := Place.ord_restrictAlong α hα V f
    have h' : V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) =
        (Place.ramificationIndexAlong α V : ℤ) * W.ord f := by rw [← hαf]; exact h
    have hmul : 0 < (Place.ramificationIndexAlong α V : ℤ) * W.ord f := by rw [← h']; exact hle
    by_contra hn
    push Not at hn
    have : (Place.ramificationIndexAlong α V : ℤ) * W.ord f ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hn
    linarith
  have hf0 : f ≠ 0 := by
    intro h0
    have : W.ord f = 0 := by rw [h0, Place.ord_zero]
    omega

  set y : LaurentSeries ↥A := jqModC ↥A - HahnSeries.single 0 a with hy
  set g : (Fbar p M H hpM (ResidueField ↥A)) := xj - algebraMap (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A a) with hg
  have hyco : coeffMap A.subtype y = ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hy, map_sub, coeffMap_single, hf]
    have : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := map_jqModC A.subtype
    rw [this]
    push_cast
    rw [hx', algebraMap_laurentSeries_eq_single]
    rfl
  have hgco : ((g : (Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
    rw [hy, map_sub, coeffMap_single, hg]
    have : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := map_jqModC _
    rw [this]
    push_cast
    rw [hxj, algebraMap_laurentSeries_eq_single]
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 := congrArg (fun s : LaurentSeries (ResidueField ↥A) => s.coeff (-1)) hgco
    rw [h0] at h1
    simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
    rw [hy, map_sub, coeffMap_single] at h1
    have : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := map_jqModC _
    rw [this, HahnSeries.coeff_sub, HahnSeries.coeff_single_of_ne (by decide)] at h1
    exact hj1 (ResidueField ↥A) (by simpa using h1.symm)

  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := (AlgebraicClosure ℚ)) f hf0
  have hd0 : ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g := Psp.d0_qexp f y hyco g hgco hg0 D hD

  have hord_g : ∀ v' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v'.ord (xj - algebraMap (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A a)) = v'.ord g := fun v' => by rw [hg]
  have hmass : ∑ v' ∈ Sdn, v'.ord g = ∑ P ∈ D.support.filter (fun P => Psp.sp P ∈ Sdn), D P := by
    rw [← MOVHcd1.sum_mapDomain_eq_sum_filter Psp.sp D Sdn]
    exact Finset.sum_congr rfl fun v' _ => (hd0 v').symm
  set T := D.support.filter (fun P => Psp.sp P ∈ Sdn) with hTdef
  set Tpos := T.filter (fun P => 0 < D P) with hTpos
  set Pos := D.support.filter (fun P => 0 < D P) with hPos
  have hT_le : ∑ P ∈ T, D P ≤ ∑ P ∈ Tpos, D P := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun P => 0 < D P)]
    have : ∑ P ∈ T.filter (fun P => ¬ 0 < D P), D P ≤ 0 :=
      Finset.sum_nonpos fun P hP => le_of_not_gt (Finset.mem_filter.mp hP).2
    linarith
  have hsub : Tpos ⊆ Pos := by
    intro P hP
    rw [hTpos, Finset.mem_filter, hTdef, Finset.mem_filter] at hP
    exact Finset.mem_filter.mpr ⟨hP.1.1, hP.2⟩
  have hPos_eq : ∑ P ∈ Pos, D P = ∑ P ∈ Sup, P.ord f := by
    apply Finset.sum_congr
    · ext P
      rw [hPos, Finset.mem_filter, hSup, Finsupp.mem_support_iff, hD]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨h.ne', h⟩
    · intro P _; exact hD P
  have hTpos_le : ∑ P ∈ Tpos, D P ≤ ∑ P ∈ Pos, D P :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun P hP _ => le_of_lt (Finset.mem_filter.mp hP).2

  have hsum_dn' : ∑ v' ∈ Sdn, v'.ord g = (Module.finrank (IntermediateField.adjoin (ResidueField ↥A) ({xj} : Set (Fbar p M H hpM (ResidueField ↥A)))) (Fbar p M H hpM (ResidueField ↥A)) : ℤ) := by
    rw [← hsum_dn]
  have heq : ∑ P ∈ Tpos, D P = ∑ P ∈ Pos, D P := by
    have := hchain
    rw [← hsum_up, ← hsum_dn', ← hPos_eq, hmass] at this
    linarith

  have hWpos : W ∈ Pos := by
    rw [hPos, Finset.mem_filter, Finsupp.mem_support_iff, hD]
    exact ⟨hordW.ne', hordW⟩
  have hWT : W ∈ Tpos := by
    by_contra hWT
    have hsd : ∑ P ∈ Pos \ Tpos, D P + ∑ P ∈ Tpos, D P = ∑ P ∈ Pos, D P := Finset.sum_sdiff hsub
    have hzero : ∑ P ∈ Pos \ Tpos, D P = 0 := by linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun P hP => le_of_lt (Finset.mem_filter.mp (Finset.sdiff_subset hP)).2)).mp hzero
    have := hall W (Finset.mem_sdiff.mpr ⟨hWpos, hWT⟩)
    rw [hD] at this
    omega
  have hWS : Psp.sp W ∈ Sdn := (Finset.mem_filter.mp (Finset.mem_filter.mp hWT).1).2
  have hpos' : 0 < (Psp.sp W).ord (xj - algebraMap (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A a)) := (hSdn _).mp hWS

  apply hV
  refine ⟨xj, IsLocalRing.residue ↥A a, hxj, ?_⟩
  have : Psp.reduceFst α hα V = Psp.sp W := rfl
  rw [this]
  exact MOVHcd1.hasValue_of_ord_sub_pos _ hpos'

end S_ModularCurve_JHPlaceSpecialization_isCuspidal_of_not_isAffinePlace_reduceFst
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_of_not_isAffinePlace_reduceFst (solution)
