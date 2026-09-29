-- Prove2me | solution 1 for ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/bbd9bd93-5ec1-5a0c-9dc5-c267644e2007

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_LaurentSeries_coeff_pow_char
import Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC qExpFunctionFieldC intFormRatiosC_subset qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_congr qExpand_qExpand coeff_jq_neg_one coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat map_jqModC jqModC_eq_map_intCast exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC jqModC_mem_intFormRatiosC map_intCast_pow_char_eq_qExpand"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar Idx levelAutBar coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd"
p2m_open "ModularCurve.FullLevel ModularCurve"

namespace K2flat

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

private theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ hk, qExpand_coeff_of_not_dvd _ _ hk, map_zero]

private theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

private theorem coeff_jqModC_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have hZ : (jqModC ℤ).coeff (-1) = 1 := by
    have h := coeff_jq_neg_one
    rw [← jqModC_rat, jqModC_eq_map_intCast ℚ, HahnSeries.map_coeff, eq_intCast] at h
    exact_mod_cast h
  rw [jqModC_eq_map_intCast K, HahnSeries.map_coeff, hZ, map_one]

private theorem jqModC_pow_sq (κ : Type*) [CommRing κ] (p : ℕ) [Fact p.Prime] [CharP κ p] :
    (jqModC κ) ^ (p ^ 2) = qExpand κ (p ^ 2) (jqModC κ) := by
  have h1 : (jqModC κ) ^ p = qExpand κ p (jqModC κ) := by
    rw [jqModC_eq_map_intCast κ]
    exact ModularCurve.map_intCast_pow_char_eq_qExpand p (jqModC ℤ)
  rw [qExpand_congr (sq p), show (jqModC κ) ^ (p ^ 2) = ((jqModC κ) ^ p) ^ p by rw [sq, pow_mul], h1,
    ← map_pow, h1, qExpand_qExpand]

private theorem coeff_neg_one_pow_sq_eq_zero (κ : Type*) [CommRing κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (s : LaurentSeries κ) : (s ^ (p ^ 2)).coeff (-1) = 0 := by
  rw [show s ^ (p ^ 2) = (s ^ p) ^ p by rw [sq, pow_mul], LaurentSeries.coeff_pow_char]
  have : ¬ ((p : ℤ) ∣ -1) := by
    intro h
    have h2 := Int.le_of_dvd one_pos (Int.dvd_neg.mp h)
    have hp := (Fact.out : p.Prime).two_le
    omega
  rw [if_neg this]

private theorem jqModC_mem_fieldBar : jqModC (AlgebraicClosure ℚ) ∈ fieldBar q M' := by
  have h1 : jqModC ℚ ∈ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) : Set (LaurentSeries ℚ)) :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  have h2 := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h1
  have h3 : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  rw [h3] at h2
  exact h2

private theorem charP_residueField (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    CharP (ResidueField A) q := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr
  have hmem : (⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ : A) ∈ maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
  have : residue A ⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ = 0 := (residue_eq_zero_iff _).mpr hmem
  rw [← map_natCast (residue A) q]
  convert this
  norm_cast

private theorem isUnit_of_isUnit_map {F : Type*} [Field F] (O : ValuationSubring F) (τ : F ≃+* F)
    (hτ : ∀ f, f ∈ O ↔ τ f ∈ O) (u : F) (hu : u ∈ O)
    (hU : IsUnit (⟨τ u, (hτ u).mp hu⟩ : O)) : IsUnit (⟨u, hu⟩ : O) := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hU
  have hb' : τ u * (b : F) = 1 := by
    have := congrArg (fun z : O => (z : F)) hb
    simpa using this
  have hbO : τ.symm (b : F) ∈ O := by rw [hτ, RingEquiv.apply_symm_apply]; exact b.2
  refine isUnit_iff_exists_inv.mpr ⟨⟨τ.symm (b : F), hbO⟩, Subtype.ext ?_⟩
  change u * τ.symm (b : F) = 1
  apply τ.injective
  rw [map_mul, RingEquiv.apply_symm_apply, map_one, hb']

private theorem isUnit_map_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) (τ : F ≃+* F)
    (hτ : ∀ f, f ∈ O ↔ τ f ∈ O) (u : F) (hu : u ∈ O)
    (hU : IsUnit (⟨u, hu⟩ : O)) : IsUnit (⟨τ u, (hτ u).mp hu⟩ : O) := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hU
  have hb' : u * (b : F) = 1 := by
    have := congrArg (fun z : O => (z : F)) hb
    simpa using this
  refine isUnit_iff_exists_inv.mpr ⟨⟨τ (b : F), (hτ _).mp b.2⟩, Subtype.ext ?_⟩
  change τ u * τ (b : F) = 1
  rw [← map_mul, hb', map_one]

private theorem mem_maximalIdeal_of_map_mem {F : Type*} [Field F] (O : ValuationSubring F) (τ : F ≃+* F)
    (hτ : ∀ f, f ∈ O ↔ τ f ∈ O) (u : F) (hu : u ∈ O)
    (hm : (⟨τ u, (hτ u).mp hu⟩ : O) ∈ maximalIdeal O) : (⟨u, hu⟩ : O) ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
  exact fun hU => hm (isUnit_map_of_isUnit O τ hτ u hu hU)

end K2flat

end ModularCurve.FullLevel

open _root_.ModularCurve.FullLevel _root_.P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two.ModularCurve.FullLevel ModularCurve.FullLevel.K2flat in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom ≠ O := by
  intro h
  haveI : CharP (ResidueField A) q := charP_residueField q A hA

  have hex : ∃ R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      (∀ f : fieldBar q M', f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
              LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
      (AlgebraicClosure ℚ) A (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))
      (ModularCurve.translation_mem_GammaH _ _)
  obtain ⟨R, hRi, hRii⟩ := hex
  have hOR : O = R.integers := SetLike.ext fun f => (hO f).trans (hRi f).symm
  subst hOR

  let τ : fieldBar q M' ≃+* fieldBar q M' := (levelAutBar q M' ζ δ).toRingEquiv
  have hτ : ∀ f : fieldBar q M', f ∈ R.integers ↔ τ f ∈ R.integers := fun f => by
    have := (SetLike.ext_iff.mp h f).symm
    rwa [ValuationSubring.mem_comap] at this
  have hτ' : ∀ f : fieldBar q M', τ.symm f ∈ R.integers ↔ f ∈ R.integers := fun f => by
    rw [hτ (τ.symm f), RingEquiv.apply_symm_apply]

  have hyA : coeffMap A.subtype (jqModC A) ∈ fieldBar q M' := by
    rw [coeffMap_jqModC]; exact jqModC_mem_fieldBar q M'
  obtain ⟨hjO, hjres⟩ := hRii (jqModC A) hyA
  have hjF_coe : ((⟨coeffMap A.subtype (jqModC A), hyA⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) := coeffMap_jqModC _

  have hlaw := coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd q M' hqM' ζ δ hδ ha _ hjF_coe
  have hy2 : coeffMap A.subtype (qExpand A (q ^ 2) (jqModC A)) ∈ fieldBar q M' := by
    rw [coeffMap_qExpand, coeffMap_jqModC, ← hlaw]; exact (levelAutBar q M' ζ δ _).2
  have hτj : τ ⟨coeffMap A.subtype (jqModC A), hyA⟩ = ⟨coeffMap A.subtype (qExpand A (q ^ 2) (jqModC A)), hy2⟩ := by
    apply Subtype.ext
    change ((levelAutBar q M' ζ δ ⟨coeffMap A.subtype (jqModC A), hyA⟩ : fieldBar q M') :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (qExpand A (q ^ 2) (jqModC A))
    rw [hlaw, coeffMap_qExpand, coeffMap_jqModC]
  obtain ⟨hτjO, hτjres⟩ := hRii (qExpand A (q ^ 2) (jqModC A)) hy2

  let jO : R.integers := ⟨⟨coeffMap A.subtype (jqModC A), hyA⟩, hjO⟩
  let tjO : R.integers := ⟨⟨coeffMap A.subtype (qExpand A (q ^ 2) (jqModC A)), hy2⟩, hτjO⟩
  have hwO : τ.symm ⟨coeffMap A.subtype (jqModC A), hyA⟩ ∈ R.integers := (hτ' _).mpr hjO
  let w : R.integers := ⟨τ.symm ⟨coeffMap A.subtype (jqModC A), hyA⟩, hwO⟩
  let D : R.integers := w ^ (q ^ 2) - jO

  have hcoeD : (D : fieldBar q M') = (w : fieldBar q M') ^ (q ^ 2) - (jO : fieldBar q M') := by
    simp only [D, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
  have hτD : (⟨τ (D : fieldBar q M'), (hτ _).mp D.2⟩ : R.integers) = jO ^ (q ^ 2) - tjO := by
    apply Subtype.ext
    have e1 : ((⟨τ (D : fieldBar q M'), (hτ _).mp D.2⟩ : R.integers) : fieldBar q M') = τ (D : fieldBar q M') := rfl
    have e2 : ((jO ^ (q ^ 2) - tjO : R.integers) : fieldBar q M') = (jO : fieldBar q M') ^ (q ^ 2) - (tjO : fieldBar q M') := by
      simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
    rw [e1, e2, hcoeD, RingEquiv.map_sub, RingEquiv.map_pow]
    have e3 : τ (w : fieldBar q M') = (jO : fieldBar q M') := RingEquiv.apply_symm_apply τ _
    rw [e3]
    congr 1
  have hres0 : R.residue (jO ^ (q ^ 2) - tjO) = 0 := by
    have hp : R.residue (jO ^ (q ^ 2)) = (R.residue jO) ^ (q ^ 2) := RingHom.map_pow _ _ _
    rw [RingHom.map_sub, hp, sub_eq_zero]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    have e4 : ((R.residue jO : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
        LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) (jqModC A) := hjres
    have e5 : ((R.residue tjO : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
        LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) (qExpand A (q ^ 2) (jqModC A)) := hτjres
    rw [e4, e5, coeffMap_jqModC, coeffMap_qExpand, coeffMap_jqModC]
    exact jqModC_pow_sq (ResidueField A) q

  have hDmax : D ∈ maximalIdeal R.integers := by
    have h1 : (⟨τ (D : fieldBar q M'), (hτ _).mp D.2⟩ : R.integers) ∈ maximalIdeal R.integers := by
      rw [hτD, ← R.ker_residue]; exact hres0
    have := mem_maximalIdeal_of_map_mem R.integers τ hτ (D : fieldBar q M') D.2 h1
    simpa using this
  have hresD : R.residue D = 0 := by
    have : D ∈ RingHom.ker R.residue := by rw [R.ker_residue]; exact hDmax
    exact this
  have hpow : (((R.residue w : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
      LaurentSeries (ResidueField A))) ^ (q ^ 2) = jqModC (ResidueField A) := by
    have h1 : R.residue w ^ (q ^ 2) = R.residue jO := by
      rw [← sub_eq_zero, ← RingHom.map_pow, ← RingHom.map_sub]; exact hresD
    have h2 := congrArg (fun z : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') =>
      (z : LaurentSeries (ResidueField A))) h1
    simp only [SubmonoidClass.coe_pow] at h2
    have e4 : ((R.residue jO : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
        LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) (jqModC A) := hjres
    rw [h2, e4, coeffMap_jqModC]

  have hc := congrArg (fun s : LaurentSeries (ResidueField A) => s.coeff (-1)) hpow
  rw [coeff_neg_one_pow_sq_eq_zero (ResidueField A) q, coeff_jqModC_neg_one] at hc
  exact zero_ne_one hc

end

end S_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two (solution)
