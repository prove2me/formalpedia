-- Prove2me | solution 1 for ModularCurve.FullLevel.jShadow_of_inTube
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9ae1dd3c-dc98-5a57-b643-a9d87c6f962f

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_jShadow_of_inTube
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

namespace TubeShadowSol

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  have h : v.adicValuation f ≤ 1 := by
    have h1 := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F) = f from rfl] at h1
    rw [h1]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  rcases v.adicValuation_le_one_iff.1 h with h0 | h0
  · rw [h0, Place.ord_zero]
  · exact h0

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_add_one_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : 0 ≤ v.ord (f + 1) := by
  by_cases hf : f = 0
  · rw [hf, zero_add, Place.ord_one]
  · exact ord_nonneg_of_mem v (add_mem (mem_of_ord_nonneg v hf h) (one_mem _))

theorem evalAt_add_one (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (f + 1) = v.evalAt f + 1 := by
  have hf1 : f + 1 ∈ v.toValuationSubring := add_mem hf (one_mem _)
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hf1, map_add, map_one, v.algebraMap_evalAt hv hf, ← map_one (residue ↥v.toValuationSubring),
    ← map_add]
  rfl

theorem evalAt_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) : v.evalAt f = 0 := by
  rw [Place.evalAt, dif_neg hf]

end PlaceFacts

section Core

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  {F' : Type*} [Field F'] [Algebra L F']

theorem core (R₀ : ConstantReduction A F Fbar) (j : F)
    (s : Place (ResidueField A) Fbar) (hs : s.IsRational)
    (ι : F →ₐ[L] F') (P : Place L F')
    (hP : ∀ (f : F) (hf : f ∈ R₀.integers),
      (∀ P' : Place L F, 0 ≤ P'.ord j → 0 ≤ P'.ord f) →
      R₀.residue ⟨f, hf⟩ ∈ s.toValuationSubring →
      ∀ a : A, residue A a = s.evalAt (R₀.residue ⟨f, hf⟩) →
        ∃ h : P.evalAt (ι f) - (a : L) ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (f : F) (hf : f ∈ R₀.integers)
    (hcusp : ∀ P' : Place L F, 0 ≤ P'.ord j → 0 ≤ P'.ord f)
    (hreg : R₀.residue ⟨f, hf⟩ ∈ s.toValuationSubring) :
    ι f ∈ P.toValuationSubring ∧
      ∀ a : A, residue A a = s.evalAt (R₀.residue ⟨f, hf⟩) →
        ∃ h : P.evalAt (ι f) - (a : L) ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A := by
  have hcong := hP f hf hcusp hreg
  refine ⟨?_, hcong⟩
  by_contra hnot

  have h0 : P.evalAt (ι f) = 0 := evalAt_of_not_mem P hnot

  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := ↥A) (s.evalAt (R₀.residue ⟨f, hf⟩))
  obtain ⟨hmemA, hmax⟩ := hcong a ha
  have ha𝔪 : a ∈ maximalIdeal A := by
    have e : (⟨P.evalAt (ι f) - (a : L), hmemA⟩ : A) = -a := Subtype.ext (by
      show P.evalAt (ι f) - (a : L) = ((-a : A) : L)
      rw [h0, zero_sub]; rfl)
    rw [e] at hmax
    exact neg_mem_iff.1 hmax
  have hra : residue A a = 0 := (IsLocalRing.residue_eq_zero_iff a).2 ha𝔪

  have hf1 : f + 1 ∈ R₀.integers := add_mem hf (one_mem _)
  have hres1 : R₀.residue ⟨f + 1, hf1⟩ = R₀.residue ⟨f, hf⟩ + 1 := by
    rw [← map_one R₀.residue, ← map_add]; rfl
  have hcusp1 : ∀ P' : Place L F, 0 ≤ P'.ord j → 0 ≤ P'.ord (f + 1) := fun P' hj =>
    ord_add_one_nonneg P' (hcusp P' hj)
  have hreg1 : R₀.residue ⟨f + 1, hf1⟩ ∈ s.toValuationSubring := by
    rw [hres1]; exact add_mem hreg (one_mem _)
  have hev1 : s.evalAt (R₀.residue ⟨f + 1, hf1⟩) = s.evalAt (R₀.residue ⟨f, hf⟩) + 1 := by
    rw [hres1]; exact evalAt_add_one s hs hreg
  obtain ⟨hmemA1, hmax1⟩ := hP (f + 1) hf1 hcusp1 hreg1 (a + 1) (by rw [map_add, map_one, ha, hev1])
  have hnot1 : ι (f + 1) ∉ P.toValuationSubring := fun h => hnot (by
    have := sub_mem h (one_mem P.toValuationSubring)
    rwa [map_add, map_one, add_sub_cancel_right] at this)
  have h01 : P.evalAt (ι (f + 1)) = 0 := evalAt_of_not_mem P hnot1
  have ha1𝔪 : a + 1 ∈ maximalIdeal A := by
    have e : (⟨P.evalAt (ι (f + 1)) - ((a + 1 : A) : L), hmemA1⟩ : A) = -(a + 1) := Subtype.ext (by
      show P.evalAt (ι (f + 1)) - ((a + 1 : A) : L) = ((-(a + 1) : A) : L)
      rw [h01, zero_sub]; rfl)
    rw [e] at hmax1
    exact neg_mem_iff.1 hmax1
  have h1 : residue A (a + 1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 ha1𝔪
  rw [map_add, map_one, hra, zero_add] at h1
  exact one_ne_zero h1

end Core

section Coeff

theorem coeffMap_eq_laurentMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    coeffMap f x = laurentMap f x := rfl

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S := map_jqModC f

theorem coeffMap_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, jqNModC, coeffMap_eq_laurentMap, laurentMap_qExpand, ← coeffMap_eq_laurentMap, coeffMap_jqModC]

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]; exact coeffMap_jqModC (algebraMap ℚ L)

theorem coeffEmb_qExpand_jq (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    coeffEmb L (qExpand ℚ N jq) = jqNModC L N := by
  rw [← jqModC_rat]; exact coeffMap_jqNModC (algebraMap ℚ L) N

end Coeff

section Integral

variable (M' : ℕ) [NeZero M']

noncomputable def jHat : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩

noncomputable def jNHat : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩

@[scoped simp] theorem coe_jHat : ((jHat M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffEmb (AlgebraicClosure ℚ) jq := rfl

@[scoped simp] theorem coe_jNHat : ((jNHat M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
theorem isIntegral_jNHat :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) {jHat M'}) (jNHat M') := by
  obtain ⟨Φ, hmonic, heval⟩ := ModularCurve.exists_monic_evalAtJ_jqN_eq_zero M'
  set jA : ↥(Algebra.adjoin (AlgebraicClosure ℚ) {jHat M'}) :=
    ⟨jHat M', Algebra.self_mem_adjoin_singleton (AlgebraicClosure ℚ) (jHat M')⟩ with hjA
  refine ⟨Φ.map (Polynomial.aeval jA).toRingHom, hmonic.map (Polynomial.aeval jA).toRingHom, ?_⟩
  rw [Polynomial.eval₂_map]

  apply (algebraMap ↥(modularFunctionFieldBar M') (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [map_zero, Polynomial.hom_eval₂]

  have hring : ((algebraMap ↥(modularFunctionFieldBar M') (LaurentSeries (AlgebraicClosure ℚ))).comp
      ((algebraMap ↥(Algebra.adjoin (AlgebraicClosure ℚ) {jHat M'}) ↥(modularFunctionFieldBar M')).comp
        (Polynomial.aeval jA).toRingHom)) =
      (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro n
      simp
    · show (algebraMap ↥(modularFunctionFieldBar M') (LaurentSeries (AlgebraicClosure ℚ)))
          ((algebraMap ↥(Algebra.adjoin (AlgebraicClosure ℚ) {jHat M'}) ↥(modularFunctionFieldBar M'))
            ((Polynomial.aeval jA).toRingHom Polynomial.X)) =
        coeffEmb (AlgebraicClosure ℚ) (evalAtJ Polynomial.X)
      rw [evalAtJ_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
      rfl
  rw [hring, show (algebraMap ↥(modularFunctionFieldBar M') (LaurentSeries (AlgebraicClosure ℚ))) (jNHat M') =
      coeffEmb (AlgebraicClosure ℚ) (jqN M') from rfl, ← Polynomial.hom_eval₂, heval, map_zero]

end Integral

end TubeShadowSol
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_jShadow_of_inTube.TubeShadowSol"

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open TubeShadowSol

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (hs : s ∈ ssPlaces q M' (ResidueField A))
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))
    (hP : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)) :
    (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
        ∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
          ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧
      ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
        ∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
          ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A)) := by

  have hsrat : s.IsRational := hs.1
  have haff : IsAffineGeomPlace (ResidueField A) M' s := hs.2.1

  have key : ∀ (x : ↥(modularFunctionFieldBar M')) (y : LaurentSeries ↥A),
      (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y →
      ∃ h : x ∈ R₀.integers,
        ((R₀.residue ⟨x, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y := by
    intro x y hxy
    obtain ⟨x, hx⟩ := x
    change x = _ at hxy
    subst hxy
    exact hR₀ y hx

  have hZL : A.subtype.comp (Int.castRingHom ↥A) = Int.castRingHom (AlgebraicClosure ℚ) := RingHom.ext_int _ _
  have hZκ : (IsLocalRing.residue ↥A).comp (Int.castRingHom ↥A) = Int.castRingHom (ResidueField A) := RingHom.ext_int _ _
  have hQL : (Int.castRingHom (AlgebraicClosure ℚ)) = (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) :=
    RingHom.ext_int _ _

  have hj_coe : ((jHat M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) (jqModC ℤ)) := by
    rw [coe_jHat, coeffMap_coeffMap, hZL, coeffMap_jqModC, coeffEmb_jq]
  obtain ⟨hjint, hjres⟩ := key (jHat M') _ hj_coe
  have hjres' : R₀.residue ⟨jHat M', hjint⟩ = jGeomGen (ResidueField A) M' := by
    apply Subtype.ext
    rw [hjres, coeffMap_coeffMap, hZκ, coeffMap_jqModC, coe_jGeomGen]

  have hjN_coe : ((jNHat M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) (jqNModC ℤ M')) := by
    rw [coe_jNHat, coeffMap_coeffMap, hZL, coeffMap_jqNModC, coeffEmb_qExpand_jq]
  obtain ⟨hjNint, hjNres⟩ := key (jNHat M') _ hjN_coe
  have hjNres' : R₀.residue ⟨jNHat M', hjNint⟩ = jNGeomGen (ResidueField A) M' := by
    apply Subtype.ext
    rw [hjNres, coeffMap_coeffMap, hZκ, coeffMap_jqNModC, coe_jNGeomGen]

  have hcuspN : ∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P'.ord (jHat M') → 0 ≤ P'.ord (jNHat M') := fun P' hj =>
    AlgebraicCurve.Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg P' (isIntegral_jNHat M') hj

  have hcore := core A R₀ (jHat M') s hsrat (IntermediateField.inclusion hle) P hP
  obtain ⟨h1, h2⟩ := hcore (jHat M') hjint (fun _ h => h) (by rw [hjres']; exact haff.1)
  obtain ⟨h3, h4⟩ := hcore (jNHat M') hjNint hcuspN (by rw [hjNres']; exact haff.2)
  rw [hjres'] at h2
  rw [hjNres'] at h4
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

end S_ModularCurve_FullLevel_jShadow_of_inTube
end P2MW
export P2MW.S_ModularCurve_FullLevel_jShadow_of_inTube (solution)
