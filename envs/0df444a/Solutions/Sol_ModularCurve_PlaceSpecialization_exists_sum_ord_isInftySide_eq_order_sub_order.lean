-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0d6bcbb6-7a07-5c14-a629-d601a7eb82cc

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring
import Theorems.Thm_ModularCurve_exists_place_of_ringHom_laurentSeries
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_ord_cuspInftyBar
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg
import Theorems.Thm_ModularCurve_not_isInftySide_cuspZeroBar
import Theorems.Thm_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue
import Theorems.Thm_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

p2m_open "ModularCurve~coeffEmb_jq HahnSeries PowerSeries"

namespace CuspDisc

section Expand
variable {R : Type*} [CommRing R]

def expandPS (d : ℕ) (P : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk fun n => if d ∣ n then coeff (n / d) P else 0

@[scoped simp] theorem coeff_expandPS (d : ℕ) (P : R⟦X⟧) (n : ℕ) :
    coeff n (expandPS d P) = if d ∣ n then coeff (n / d) P else 0 := by
  simp [expandPS]

theorem expandPS_map {S : Type*} [CommRing S] (f : R →+* S) (d : ℕ) (P : R⟦X⟧) :
    (expandPS d P).map f = expandPS d (P.map f) := by
  ext n; simp only [coeff_map, coeff_expandPS]; split_ifs <;> simp

theorem coeff_ofPowerSeries_int (P : R⟦X⟧) (k : ℤ) :
    (ofPowerSeries ℤ R P).coeff k = if 0 ≤ k then coeff k.toNat P else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [HahnSeries.ofPowerSeries_apply_coeff]
  · exact ModularCurve.ofPowerSeries_coeff_of_neg P (lt_of_not_ge h)

theorem qExpand_ofPowerSeries (d : ℕ) [NeZero d] (P : R⟦X⟧) :
    qExpand R d (ofPowerSeries ℤ R P) = ofPowerSeries ℤ R (expandPS d P) := by
  ext k
  by_cases hdk : (d : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hdk
    rw [qExpand_coeff_mul, coeff_ofPowerSeries_int, coeff_ofPowerSeries_int]
    have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    by_cases hm : 0 ≤ m
    · have hdm : 0 ≤ (d : ℤ) * m := mul_nonneg hd0.le hm
      rw [if_pos hm, if_pos hdm, coeff_expandPS]
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      have : ((d : ℤ) * n).toNat = d * n := by
        rw [show ((d : ℤ) * n) = ((d * n : ℕ) : ℤ) by push_cast; ring]; exact Int.toNat_natCast _
      rw [this, Int.toNat_natCast, if_pos (Dvd.intro n rfl)]
      rcases Nat.eq_zero_or_pos d with hd | hd
      · exact absurd hd (NeZero.ne d)
      · rw [Nat.mul_div_cancel_left n hd]
    · have hdm : ¬ 0 ≤ (d : ℤ) * m := by
        intro h; exact hm (nonneg_of_mul_nonneg_right (by rwa [mul_comm] at h) hd0 |> fun h' => by
          rcases lt_or_ge m 0 with h1 | h1
          · exact absurd (mul_neg_of_pos_of_neg hd0 h1) (not_lt.mpr h)
          · exact h1)
      rw [if_neg hm, if_neg hdm]
  · rw [qExpand_coeff_of_not_dvd _ _ hdk, coeff_ofPowerSeries_int]
    split_ifs with hk
    · rw [coeff_expandPS, if_neg]
      intro hdn
      apply hdk
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk
      subst hn
      rw [Int.toNat_natCast] at hdn
      exact_mod_cast hdn
    · rfl

theorem map_ofPowerSeries {S : Type*} [CommRing S] (f : R →+* S) (P : R⟦X⟧) :
    coeffMap f (ofPowerSeries ℤ R P) = ofPowerSeries ℤ S (P.map f) := by
  ext k
  rw [coeffMap_coeff, coeff_ofPowerSeries_int, coeff_ofPowerSeries_int]
  split_ifs <;> simp

end Expand

def jDen : ℤ⟦X⟧ := jNum.invOfUnit 1

theorem jNum_mul_jDen : jNum * jDen = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum]; rfl)

@[scoped simp] theorem constantCoeff_jDen : constantCoeff jDen = 1 := by
  have h := congrArg constantCoeff jNum_mul_jDen
  rwa [map_mul, constantCoeff_jNum, one_mul, map_one] at h

abbrev GenIdx (N : ℕ) := Option {d : ℕ // d ∈ N.divisors}

def genZ (N : ℕ) : GenIdx N → ℤ⟦X⟧
  | none => X * jDen
  | some d => expandPS d.1 jNum * jDen ^ d.1

def genPS (S : Type*) [CommRing S] (N : ℕ) (i : GenIdx N) : S⟦X⟧ := (genZ N i).map (Int.castRingHom S)

theorem map_map_intCast {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (P : ℤ⟦X⟧) :
    (P.map (Int.castRingHom S)).map f = P.map (Int.castRingHom T) := by
  ext n; simp [coeff_map]

theorem genPS_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (N : ℕ) (i : GenIdx N) :
    (genPS S N i).map f = genPS T N i := by
  rw [genPS, genPS, map_map_intCast]

section OverField
variable (L : Type*) [Field L] [Algebra ℚ L]

def genL (N : ℕ) (i : GenIdx N) : LaurentSeries L := ofPowerSeries ℤ L (genPS L N i)

theorem divisors_pos {N : ℕ} (d : {d : ℕ // d ∈ N.divisors}) : 0 < d.1 :=
  Nat.pos_of_mem_divisors d.2

scoped instance {N : ℕ} (d : {d : ℕ // d ∈ N.divisors}) : NeZero d.1 := ⟨(divisors_pos d).ne'⟩

theorem coeffEmb_jq : coeffEmb L jq = single (-1 : ℤ) 1 * ofPowerSeries ℤ L (jNum.map (Int.castRingHom L)) := by
  rw [jq, map_mul, coeffEmb, coeffMap_single, map_one, map_ofPowerSeries, jNumQ, map_map_intCast]

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq)
      = single (-(d : ℤ)) 1 * ofPowerSeries ℤ L ((expandPS d jNum).map (Int.castRingHom L)) := by
  rw [jq, map_mul, qExpand_single, qExpand_ofPowerSeries, map_mul, coeffEmb, coeffMap_single, map_one,
    map_ofPowerSeries, jNumQ, ← expandPS_map, map_map_intCast, mul_neg_one]

theorem coeffEmb_jq_mul_genL_none (N : ℕ) : coeffEmb L jq * genL L N none = 1 := by
    rw [coeffEmb_jq, genL, genPS, genZ]
    simp only [map_mul, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
    have h1 : (jNum.map (Int.castRingHom L)) * (jDen.map (Int.castRingHom L)) = 1 := by
      rw [← map_mul, jNum_mul_jDen, map_one]
    calc single (-1 : ℤ) (1 : L) * ofPowerSeries ℤ L (jNum.map (Int.castRingHom L))
          * (single 1 1 * ofPowerSeries ℤ L (jDen.map (Int.castRingHom L)))
        = (single (-1 : ℤ) (1 : L) * single 1 1)
          * (ofPowerSeries ℤ L (jNum.map (Int.castRingHom L)) * ofPowerSeries ℤ L (jDen.map (Int.castRingHom L))) := by ring
      _ = 1 := by rw [HahnSeries.single_mul_single, ← map_mul, h1, map_one]; simp

theorem coeffEmb_jq_inv (N : ℕ) : (coeffEmb L jq)⁻¹ = genL L N none :=
  inv_eq_of_mul_eq_one_right (coeffEmb_jq_mul_genL_none L N)

theorem coeffEmb_jq_ne_zero : coeffEmb L jq ≠ 0 :=
  left_ne_zero_of_mul_eq_one (coeffEmb_jq_mul_genL_none L 1)

theorem coeffEmb_qExpand_mul (N : ℕ) (d : {d : ℕ // d ∈ N.divisors}) :
    coeffEmb L (qExpand ℚ d.1 jq) * (genL L N none) ^ d.1 = genL L N (some d) := by
  rw [coeffEmb_qExpand_jq, genL, genL, genPS, genPS, genZ, genZ]
  simp only [map_mul, PowerSeries.map_X, map_pow, HahnSeries.ofPowerSeries_X]
  have hs : (single (-(d.1 : ℤ)) (1 : L)) * (single 1 1) ^ d.1 = 1 := by
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single]; simp
  calc single (-(d.1 : ℤ)) (1 : L) * ofPowerSeries ℤ L ((expandPS d.1 jNum).map (Int.castRingHom L))
        * (single 1 1 * ofPowerSeries ℤ L (jDen.map (Int.castRingHom L))) ^ d.1
      = (single (-(d.1 : ℤ)) (1 : L) * (single 1 1) ^ d.1)
        * (ofPowerSeries ℤ L ((expandPS d.1 jNum).map (Int.castRingHom L))
          * (ofPowerSeries ℤ L (jDen.map (Int.castRingHom L))) ^ d.1) := by ring
    _ = _ := by rw [hs, one_mul]

theorem genL_none_ne_zero (N : ℕ) : genL L N none ≠ 0 :=
  right_ne_zero_of_mul_eq_one (coeffEmb_jq_mul_genL_none L N)

end OverField

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Generation
variable (L : Type*) [Field L] [Algebra ℚ L]

theorem adjoin_coeffEmb_image_adjoin (S : Set (LaurentSeries ℚ)) :
    IntermediateField.adjoin L (coeffEmb L '' (IntermediateField.adjoin ℚ S : Set (LaurentSeries ℚ)))
      = IntermediateField.adjoin L (coeffEmb L '' S) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
    | algebraMap c =>
      rw [ModularCurve.algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
        ← algebraMap_laurentSeries_eq_single]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  · exact IntermediateField.adjoin.mono L _ _ (Set.image_mono (IntermediateField.subset_adjoin ℚ S))

theorem mem_divisors_of_dvd {N d : ℕ} [NeZero N] (hd : d ∣ N) : d ∈ N.divisors :=
  Nat.mem_divisors.mpr ⟨hd, NeZero.ne N⟩

theorem laurentBaseChange_full_eq_adjoin_genL (N : ℕ) [NeZero N] :
    laurentBaseChange L (modularFunctionFieldFull N) = IntermediateField.adjoin L (Set.range (genL L N)) := by
  rw [laurentBaseChange, modularFunctionFieldFull, adjoin_coeffEmb_image_adjoin]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, ⟨d, hne, hdN, rfl⟩, rfl⟩
    haveI := hne
    set dd : {d : ℕ // d ∈ N.divisors} := ⟨d, mem_divisors_of_dvd hdN⟩
    have h := coeffEmb_qExpand_mul L N dd
    have hw : genL L N none ^ d ≠ 0 := pow_ne_zero _ (genL_none_ne_zero L N)
    have : coeffEmb L (qExpand ℚ d jq) = genL L N (some dd) * (genL L N none ^ d)⁻¹ := by
      rw [← h, mul_inv_cancel_right₀ hw]
    rw [this]
    have hnone : genL L N none ∈ IntermediateField.adjoin L (Set.range (genL L N)) :=
      IntermediateField.subset_adjoin L _ ⟨none, rfl⟩
    have hsome : genL L N (some dd) ∈ IntermediateField.adjoin L (Set.range (genL L N)) :=
      IntermediateField.subset_adjoin L _ ⟨some dd, rfl⟩
    exact mul_mem hsome (inv_mem (pow_mem hnone _))
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    have hj : coeffEmb L jq ∈ IntermediateField.adjoin L (coeffEmb L '' divisorExpansions N) := by
      refine IntermediateField.subset_adjoin L _ ⟨jq, ?_, rfl⟩
      have := mem_divisorExpansions N (one_dvd N)
      rwa [qExpand_one_apply] at this
    have hw : genL L N none ∈ IntermediateField.adjoin L (coeffEmb L '' divisorExpansions N) := by
      rw [← coeffEmb_jq_inv L N]; exact inv_mem hj
    cases i with
    | none => exact hw
    | some d =>
      rw [SetLike.mem_coe, ← coeffEmb_qExpand_mul L N d]
      exact mul_mem (IntermediateField.subset_adjoin L _ ⟨_, mem_divisorExpansions N (Nat.dvd_of_mem_divisors d.2), rfl⟩)
        (pow_mem hw _)

theorem modularFunctionFieldBar_eq_adjoin_genL (N : ℕ) [NeZero N] :
    modularFunctionFieldBar N = IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range (genL (AlgebraicClosure ℚ) N)) :=
  laurentBaseChange_full_eq_adjoin_genL _ N

end Generation
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Presentation

open MvPolynomial

variable (N : ℕ) [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ

abbrev evPS (S : Type*) [CommRing S] (p : MvPolynomial (GenIdx N) S) : S⟦X⟧ :=
  MvPolynomial.aeval (genPS S N) p

theorem evPS_map {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (p : MvPolynomial (GenIdx N) S) :
    (evPS N S p).map φ = evPS N T (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [evPS, MvPolynomial.aeval_C, PowerSeries.map_C]
  | add p q hp hq => simp only [evPS, map_add] at *; rw [hp, hq]
  | mul_X p i hp => simp only [evPS, map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X] at *; rw [hp, genPS_map]

theorem aeval_genL_eq (L : Type*) [Field L] [Algebra ℚ L] (p : MvPolynomial (GenIdx N) L) :
    MvPolynomial.aeval (genL L N) p = ofPowerSeries ℤ L (evPS N L p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [evPS, MvPolynomial.aeval_C]
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]
  | add p q hp hq => simp only [evPS, map_add] at *; rw [hp, hq]
  | mul_X p i hp => simp only [evPS, map_mul, MvPolynomial.aeval_X] at *; rw [hp]; rfl

theorem exists_presentation (f : modularFunctionFieldBar N) :
    ∃ r s : MvPolynomial (GenIdx N) ℚbar,
      (f : LaurentSeries ℚbar) = ofPowerSeries ℤ ℚbar (evPS N ℚbar r) / ofPowerSeries ℤ ℚbar (evPS N ℚbar s) := by
  have hf : (f : LaurentSeries ℚbar) ∈ IntermediateField.adjoin ℚbar (Set.range (genL ℚbar N)) := by
    rw [← modularFunctionFieldBar_eq_adjoin_genL]; exact f.2
  rw [IntermediateField.mem_adjoin_iff] at hf
  obtain ⟨r, s, hrs⟩ := hf
  refine ⟨MvPolynomial.rename (Set.rangeSplitting (genL ℚbar N)) r,
    MvPolynomial.rename (Set.rangeSplitting (genL ℚbar N)) s, ?_⟩
  rw [hrs, ← aeval_genL_eq, ← aeval_genL_eq, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename,
    Set.comp_rangeSplitting]

theorem exists_restrict_coeffs {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
    (M : IntermediateField F E) (p : MvPolynomial ι E) (hp : ∀ m ∈ p.support, p.coeff m ∈ M) :
    ∃ p' : MvPolynomial ι M, MvPolynomial.map (algebraMap M E) p' = p := by
  classical
  refine ⟨∑ m ∈ p.support.attach, MvPolynomial.monomial m.1 ⟨p.coeff m.1, hp m.1 m.2⟩, ?_⟩
  calc MvPolynomial.map (algebraMap M E) (∑ m ∈ p.support.attach, MvPolynomial.monomial m.1 ⟨p.coeff m.1, hp m.1 m.2⟩)
      = ∑ m ∈ p.support.attach, MvPolynomial.monomial m.1 (p.coeff m.1) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [MvPolynomial.map_monomial]; rfl
    _ = ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m) :=
        Finset.sum_attach p.support (fun m => MvPolynomial.monomial m (p.coeff m))
    _ = p := p.as_sum.symm

end Presentation
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

open PowerSeries Polynomial Filter Topology

namespace CuspDisc

section Defs

variable {L : Type*} [NormedField L]

def Small (ρ C : ℝ) (m : ℕ) (P : L⟦X⟧) : Prop := ∀ k, ‖coeff k P‖ ≤ C * ρ ^ (m - k)

def Bdd (C : ℝ) (P : L⟦X⟧) : Prop := ∀ k, ‖coeff k P‖ ≤ C

theorem small_zero_iff {ρ C : ℝ} {P : L⟦X⟧} : Small ρ C 0 P ↔ Bdd C P := by
  simp [Small, Bdd]

theorem Small.bdd {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (h : Small ρ C m P) : Bdd C P := fun k =>
  (h k).trans (mul_le_of_le_one_right hC (pow_le_one₀ hρ0 hρ1))

theorem Small.anti {ρ C : ℝ} {m m' : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hm : m' ≤ m) (h : Small ρ C m P) : Small ρ C m' P := fun k =>
  (h k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 (by omega)) hC)

theorem small_of_coeff_eq_zero {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hC : 0 ≤ C)
    (hb : Bdd C P) (hz : ∀ k < m, coeff k P = 0) : Small ρ C m P := by
  intro k
  by_cases hk : k < m
  · rw [hz k hk, norm_zero]; exact mul_nonneg hC (pow_nonneg hρ0 _)
  · have : m - k = 0 := by omega
    simpa [this] using hb k

theorem Small.neg {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hP : Small ρ C m P) : Small ρ C m (-P) := fun k => by
  simpa using hP k

theorem Small.mono_C {ρ C C' : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hCC' : C ≤ C')
    (hP : Small ρ C m P) : Small ρ C' m P := fun k =>
  (hP k).trans (mul_le_mul_of_nonneg_right hCC' (pow_nonneg hρ0 _))

variable (r : L)

def tcoeff (P : L⟦X⟧) (n : ℕ) : L := ∑' k : ℕ, coeff (n + k) P * ((n + k).choose n : L) * r ^ k

private def _root_.CuspDisc.T (P : L⟦X⟧) : L⟦X⟧ := PowerSeries.mk (tcoeff r P)

p2m_export "CuspDisc" "T"
@[scoped simp] theorem coeff_T (P : L⟦X⟧) (n : ℕ) : coeff n (T r P) = tcoeff r P n := by
  simp [T]

variable {r}

theorem T_neg (P : L⟦X⟧) : T r (-P) = -T r P := by
  ext n
  simp only [coeff_T, map_neg, tcoeff]
  rw [← tsum_neg]; congr 1; ext k; ring

@[scoped simp] theorem T_zero' : T r (0 : L⟦X⟧) = 0 := by
  ext n; simp [tcoeff]

theorem T_coe (p : L[X]) : T r (p : L⟦X⟧) = ((taylor r p : L[X]) : L⟦X⟧) := by
  ext n
  rw [coeff_T, Polynomial.coeff_coe, taylor_coeff, tcoeff]
  have hM : (hasseDeriv n p).natDegree < p.natDegree + 1 :=
    Nat.lt_succ_of_le ((natDegree_hasseDeriv_le p n).trans (Nat.sub_le _ _))
  rw [eval_eq_sum_range' hM, tsum_eq_sum (s := Finset.range (p.natDegree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hasseDeriv_coeff, Polynomial.coeff_coe, Nat.add_comm k n]
    ring
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem T_X : T r (PowerSeries.X : L⟦X⟧) = PowerSeries.X + PowerSeries.C r := by
  have := T_coe (r := r) (Polynomial.X : L[X])
  simpa [taylor_X] using this

theorem T_C (a : L) : T r (PowerSeries.C a : L⟦X⟧) = PowerSeries.C a := by
  have := T_coe (r := r) (Polynomial.C a : L[X])
  simpa [taylor_C] using this

@[scoped simp] theorem T_one : T r (1 : L⟦X⟧) = 1 := by
  simpa using T_C (r := r) (1 : L)

theorem constantCoeff_T (P : L⟦X⟧) : constantCoeff (T r P) = ∑' k : ℕ, coeff k P * r ^ k := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_T, tcoeff]
  congr 1; ext k; simp

end Defs
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

section Ultra

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem Small.add {ρ C : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hP : Small ρ C m P) (hQ : Small ρ C m Q) :
    Small ρ C m (P + Q) := fun k => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP k) (hQ k))

theorem Small.sub {ρ C : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hP : Small ρ C m P) (hQ : Small ρ C m Q) :
    Small ρ C m (P - Q) := by
  simpa [sub_eq_add_neg] using hP.add hQ.neg

theorem Bdd.add {C : ℝ} {P Q : L⟦X⟧} (hP : Bdd C P) (hQ : Bdd C Q) : Bdd C (P + Q) :=
  small_zero_iff.mp ((small_zero_iff (ρ := 1)).mpr hP |>.add (small_zero_iff.mpr hQ))

theorem Bdd.sub {C : ℝ} {P Q : L⟦X⟧} (hP : Bdd C P) (hQ : Bdd C Q) : Bdd C (P - Q) :=
  small_zero_iff.mp ((small_zero_iff (ρ := 1)).mpr hP |>.sub (small_zero_iff.mpr hQ))

theorem Small.mul {ρ C C' : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hP : Small ρ C m P) (hQ : Bdd C' Q) : Small ρ (C * C') m (P * Q) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_nonneg hC hC') (pow_nonneg hρ0 _)) fun ij hij => ?_
  have hi : ij.1 ≤ n := Finset.HasAntidiagonal.antidiagonal.fst_le hij
  calc ‖coeff ij.1 P * coeff ij.2 Q‖ = ‖coeff ij.1 P‖ * ‖coeff ij.2 Q‖ := norm_mul _ _
    _ ≤ (C * ρ ^ (m - ij.1)) * C' :=
        mul_le_mul (hP _) (hQ _) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hρ0 _))
    _ = (C * C') * ρ ^ (m - ij.1) := by ring
    _ ≤ (C * C') * ρ ^ (m - n) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 (by omega)) (mul_nonneg hC hC')

theorem Bdd.mul_small {ρ C C' : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hP : Bdd C P) (hQ : Small ρ C' m Q) : Small ρ (C * C') m (P * Q) := by
  rw [mul_comm P Q, mul_comm C C']
  exact hQ.mul hρ0 hρ1 hC' hC hP

theorem Bdd.mul {C C' : ℝ} {P Q : L⟦X⟧} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hP : Bdd C P) (hQ : Bdd C' Q) :
    Bdd (C * C') (P * Q) := by
  rw [← small_zero_iff (ρ := (1/2 : ℝ))] at hP ⊢
  exact hP.mul (by norm_num) (by norm_num) hC hC' hQ

theorem eq_zero_of_forall_small {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ m, Small ρ C m P) : P = 0 := by
  ext k
  rw [map_zero]
  have hlim : Tendsto (fun j : ℕ => C * ρ ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
  have hle : ∀ j, ‖coeff k P‖ ≤ C * ρ ^ j := fun j => by
    simpa using h (k + j) k
  have : ‖coeff k P‖ ≤ 0 := ge_of_tendsto' hlim hle
  exact norm_le_zero_iff.mp this

variable {r : L}

theorem norm_term_le {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Small ρ C m P) (n k : ℕ) :
    ‖coeff (n + k) P * ((n + k).choose n : L) * r ^ k‖ ≤ C * ρ ^ (m - n) := by
  have h1 : ‖((n + k).choose n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L _
  calc ‖coeff (n + k) P * ((n + k).choose n : L) * r ^ k‖
      = ‖coeff (n + k) P‖ * ‖((n + k).choose n : L)‖ * ‖r‖ ^ k := by
        rw [norm_mul, norm_mul, norm_pow]
    _ ≤ (C * ρ ^ (m - (n + k))) * 1 * ρ ^ k :=
        mul_le_mul (mul_le_mul (hP _) h1 (norm_nonneg _) (mul_nonneg hC (pow_nonneg hρ0 _)))
          (pow_le_pow_left₀ (norm_nonneg _) hr k) (pow_nonneg (norm_nonneg _) _)
          (mul_nonneg (mul_nonneg hC (pow_nonneg hρ0 _)) zero_le_one)
    _ = C * (ρ ^ (m - (n + k)) * ρ ^ k) := by ring
    _ ≤ C * ρ ^ (m - n) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [← _root_.pow_add]
        exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)

theorem norm_tcoeff_le {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Small ρ C m P) (n : ℕ) : ‖tcoeff r P n‖ ≤ C * ρ ^ (m - n) :=
  IsUltrametricDist.norm_tsum_le_of_forall_le fun k => norm_term_le hρ0 hρ1 hC hr hP n k

theorem Small.T {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Small ρ C m P) : Small ρ C m (T r P) := fun n => by
  rw [coeff_T]; exact norm_tcoeff_le hρ0 hρ1 hC hr hP n

theorem Bdd.T {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) : Bdd C (T r P) :=
  small_zero_iff.mp ((small_zero_iff.mpr hP).T hρ0 hρ1 hC hr)

end Ultra
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

section Complete

variable {L : Type*} [NormedField L] [CompleteSpace L] [IsUltrametricDist L] {r : L}

theorem summable_term {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (n : ℕ) :
    Summable fun k : ℕ => coeff (n + k) P * ((n + k).choose n : L) * r ^ k := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_left C) fun k => ?_
  have h1 : ‖((n + k).choose n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L _
  calc ‖coeff (n + k) P * ((n + k).choose n : L) * r ^ k‖
      = ‖coeff (n + k) P‖ * ‖((n + k).choose n : L)‖ * ‖r‖ ^ k := by
        rw [norm_mul, norm_mul, norm_pow]
    _ ≤ C * 1 * ρ ^ k :=
        mul_le_mul (mul_le_mul (hP _) h1 (norm_nonneg _) hC)
          (pow_le_pow_left₀ (norm_nonneg _) hr k) (pow_nonneg (norm_nonneg _) _)
          (mul_nonneg hC zero_le_one)
    _ = C * ρ ^ k := by ring

theorem T_add {ρ C C' : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C' Q) : T r (P + Q) = T r P + T r Q := by
  ext n
  simp only [coeff_T, map_add, tcoeff]
  rw [← (summable_term hρ0 hρ1 hC hr hP n).tsum_add (summable_term hρ0 hρ1 hC' hr hQ n)]
  congr 1; ext k; ring

theorem T_sub {ρ C C' : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C' Q) : T r (P - Q) = T r P - T r Q := by
  rw [sub_eq_add_neg, T_add hρ0 hρ1 hC hC' hr hP (by simpa [Bdd] using hQ), T_neg, sub_eq_add_neg]

theorem T_mul {ρ C C' : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C' Q) : T r (P * Q) = T r P * T r Q := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_small (ρ := ρ) (C := C * C') hρ0 hρ1 fun m => ?_
  have hρ1' := hρ1.le
  obtain ⟨p, hp⟩ : ∃ p : L⟦X⟧, p = ((trunc m P : L[X]) : L⟦X⟧) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : L⟦X⟧, q = ((trunc m Q : L[X]) : L⟦X⟧) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC
  have hpB : Bdd C p := fun k => by
    rw [hp, Polynomial.coeff_coe, coeff_trunc]
    split_ifs
    · exact hP k
    · rw [norm_zero]; exact hC
  have hqB : Bdd C' q := fun k => by
    rw [hq, Polynomial.coeff_coe, coeff_trunc]
    split_ifs
    · exact hQ k
    · rw [norm_zero]; exact hC'
  have hP'S : Small ρ C m (P - p) := by
    refine small_of_coeff_eq_zero hρ0 hC (hP.sub hpB) fun k hk => ?_
    rw [map_sub, hp, Polynomial.coeff_coe, coeff_trunc, if_pos hk, sub_self]
  have hQ'S : Small ρ C' m (Q - q) := by
    refine small_of_coeff_eq_zero hρ0 hC' (hQ.sub hqB) fun k hk => ?_
    rw [map_sub, hq, Polynomial.coeff_coe, coeff_trunc, if_pos hk, sub_self]
  have hP'B : Bdd C (P - p) := hP'S.bdd hρ0 hρ1' hC
  have hQ'B : Bdd C' (Q - q) := hQ'S.bdd hρ0 hρ1' hC'
  have hpq : T r (p * q) = T r p * T r q := by
    rw [hp, hq, ← Polynomial.coe_mul, T_coe, T_coe, T_coe, taylor_mul, Polynomial.coe_mul]
  have hE : P * Q = p * q + ((P - p) * Q + p * (Q - q)) := by ring
  have hES : Small ρ (C * C') m ((P - p) * Q + p * (Q - q)) :=
    (hP'S.mul hρ0 hρ1' hC hC' hQ).add (hpB.mul_small hρ0 hρ1' hC hC' hQ'S)
  have hEB : Bdd (C * C') ((P - p) * Q + p * (Q - q)) := hES.bdd hρ0 hρ1' (mul_nonneg hC hC')
  have h1 : T r (P * Q) = T r p * T r q + T r ((P - p) * Q + p * (Q - q)) := by
    rw [hE, T_add hρ0 hρ1 (mul_nonneg hC hC') (mul_nonneg hC hC') hr (hpB.mul hC hC' hqB) hEB, hpq]
  have h2 : T r P = T r p + T r (P - p) := by
    conv_lhs => rw [show P = p + (P - p) by ring]
    exact T_add hρ0 hρ1 hC hC hr hpB hP'B
  have h3 : T r Q = T r q + T r (Q - q) := by
    conv_lhs => rw [show Q = q + (Q - q) by ring]
    exact T_add hρ0 hρ1 hC' hC' hr hqB hQ'B
  have h4 : T r (P * Q) - T r P * T r Q
      = T r ((P - p) * Q + p * (Q - q))
        - (T r p * T r (Q - q) + T r (P - p) * T r q + T r (P - p) * T r (Q - q)) := by
    rw [h1, h2, h3]; ring
  rw [h4]
  refine (hES.T hρ0 hρ1' (mul_nonneg hC hC') hr).sub ?_
  refine ((hpB.T hρ0 hρ1' hC hr).mul_small hρ0 hρ1' hC hC' (hQ'S.T hρ0 hρ1' hC' hr)).add
    ((hP'S.T hρ0 hρ1' hC hr).mul hρ0 hρ1' hC hC' (hqB.T hρ0 hρ1' hC' hr)) |>.add ?_
  exact (hP'S.T hρ0 hρ1' hC hr).mul hρ0 hρ1' hC hC' (hQ'B.T hρ0 hρ1' hC' hr)

theorem T_T {ρ C : ℝ} {P : L⟦X⟧} {s : L} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hs : ‖s‖ ≤ ρ) (hP : Bdd C P) : T s (T r P) = T (s + r) P := by
  have hρ1' := hρ1.le
  have hsr : ‖s + r‖ ≤ ρ := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hs hr)
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_small (ρ := ρ) (C := C) hρ0 hρ1 fun m => ?_
  obtain ⟨p, hp⟩ : ∃ p : L⟦X⟧, p = ((trunc m P : L[X]) : L⟦X⟧) := ⟨_, rfl⟩
  have hpB : Bdd C p := fun k => by
    rw [hp, Polynomial.coeff_coe, coeff_trunc]
    split_ifs
    · exact hP k
    · rw [norm_zero]; exact hC
  have hP'S : Small ρ C m (P - p) := by
    refine small_of_coeff_eq_zero hρ0 hC (hP.sub hpB) fun k hk => ?_
    rw [map_sub, hp, Polynomial.coeff_coe, coeff_trunc, if_pos hk, sub_self]
  have hP'B : Bdd C (P - p) := hP'S.bdd hρ0 hρ1' hC
  have hpp : T s (T r p) = T (s + r) p := by
    rw [hp, T_coe, T_coe, T_coe, taylor_taylor]
  have h2 : T r P = T r p + T r (P - p) := by
    conv_lhs => rw [show P = p + (P - p) by ring]
    exact T_add hρ0 hρ1 hC hC hr hpB hP'B
  have h3 : T (s + r) P = T (s + r) p + T (s + r) (P - p) := by
    conv_lhs => rw [show P = p + (P - p) by ring]
    exact T_add hρ0 hρ1 hC hC hsr hpB hP'B
  have h4 : T s (T r P) - T (s + r) P = T s (T r (P - p)) - T (s + r) (P - p) := by
    rw [h2, T_add hρ0 hρ1 hC hC hs (hpB.T hρ0 hρ1' hC hr) (hP'B.T hρ0 hρ1' hC hr), hpp, h3]
    ring
  rw [h4]
  exact ((hP'S.T hρ0 hρ1' hC hr).T hρ0 hρ1' hC hs).sub (hP'S.T hρ0 hρ1' hC hsr)

omit [CompleteSpace L] [IsUltrametricDist L] in
theorem T_zero_left (P : L⟦X⟧) : T (0 : L) P = P := by
  ext n
  rw [coeff_T, tcoeff, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

theorem T_injective {ρ C : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C Q) (h : T r P = T r Q) : P = Q := by
  have hnr : ‖-r‖ ≤ ρ := by rwa [norm_neg]
  have := congrArg (T (-r)) h
  rwa [T_T hρ0 hρ1 hC hr hnr hP, T_T hρ0 hρ1 hC hr hnr hQ, neg_add_cancel,
    T_zero_left, T_zero_left] at this

theorem T_eq_zero_iff {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) : T r P = 0 ↔ P = 0 := by
  refine ⟨fun h => T_injective hρ0 hρ1 hC hr hP (fun k => by simpa using hC) ?_, fun h => by simp [h]⟩
  rw [h, T_zero']

theorem constantCoeff_T_ne_zero {u : L⟦X⟧} (hu : Bdd 1 u) (hu0 : ‖constantCoeff u‖ = 1)
    (hr : ‖r‖ < 1) : constantCoeff (T r u) ≠ 0 := by
  intro h0
  rw [constantCoeff_T] at h0
  have hsum : Summable fun k : ℕ => coeff k u * r ^ k := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hr) fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hu k)
  have hsplit := hsum.tsum_eq_zero_add
  rw [h0] at hsplit
  simp only [pow_zero, mul_one, coeff_zero_eq_constantCoeff] at hsplit
  have htail : ‖∑' k : ℕ, coeff (k + 1) u * r ^ (k + 1)‖ ≤ ‖r‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k => ?_
    rw [norm_mul, norm_pow]
    calc ‖coeff (k + 1) u‖ * ‖r‖ ^ (k + 1) ≤ 1 * ‖r‖ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (hu _) (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖r‖ := by
          rw [one_mul, pow_succ]
          exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hr.le)
  have : ‖constantCoeff u‖ ≤ ‖r‖ := by
    have h' : constantCoeff u = -∑' k : ℕ, coeff (k + 1) u * r ^ (k + 1) := by
      linear_combination -hsplit
    rw [h', norm_neg]; exact htail
  linarith

end Complete
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Phi

variable {K L : Type*} [Field K] [NormedField L] [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
variable {σ : Type*} (g : σ → L⟦X⟧)

omit [CompleteSpace L] [IsUltrametricDist L] in
theorem Bdd.mono {C C' : ℝ} {P : L⟦X⟧} (h : Bdd C P) (hCC' : C ≤ C') : Bdd C' P := fun k => (h k).trans hCC'

omit [CompleteSpace L] [IsUltrametricDist L] in
theorem bdd_C (a : L) : Bdd ‖a‖ (PowerSeries.C a : L⟦X⟧) := fun k => by
  rw [PowerSeries.coeff_C]; split_ifs <;> simp

omit [CompleteSpace L] in
theorem evL_bdd (hg : ∀ i, Bdd 1 (g i)) (P : MvPolynomial σ K) :
    ∃ C, 0 ≤ C ∧ Bdd C (MvPolynomial.aeval g P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨‖algebraMap K L c‖, norm_nonneg _, ?_⟩
    have : MvPolynomial.aeval g (MvPolynomial.C c : MvPolynomial σ K) = PowerSeries.C (algebraMap K L c) := by
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply K L L⟦X⟧]; rfl
    rw [this]; exact bdd_C _
  | add p q hp hq =>
    obtain ⟨C, hC, hb⟩ := hp; obtain ⟨C', hC', hb'⟩ := hq
    refine ⟨max C C', le_max_of_le_left hC, ?_⟩
    rw [map_add]
    exact (hb.mono (le_max_left _ _)).add (hb'.mono (le_max_right _ _))
  | mul_X p i hp =>
    obtain ⟨C, hC, hb⟩ := hp
    refine ⟨C * 1, by simpa using hC, ?_⟩
    rw [map_mul, MvPolynomial.aeval_X]
    exact hb.mul hC zero_le_one (hg i)

variable (hg : ∀ i, Bdd 1 (g i)) (r : L) (hr : ‖r‖ < 1)

def phi : MvPolynomial σ K →+* L⟦X⟧ where
  toFun P := T r (MvPolynomial.aeval g P)
  map_one' := by simp
  map_mul' P Q := by
    obtain ⟨C, hC, hP⟩ := evL_bdd g hg P
    obtain ⟨C', hC', hQ⟩ := evL_bdd g hg Q
    simp only [map_mul]
    exact T_mul (norm_nonneg r) hr hC hC' le_rfl hP hQ
  map_zero' := by simp
  map_add' P Q := by
    obtain ⟨C, hC, hP⟩ := evL_bdd g hg P
    obtain ⟨C', hC', hQ⟩ := evL_bdd g hg Q
    simp only [map_add]
    exact T_add (norm_nonneg r) hr hC hC' le_rfl hP hQ

theorem phi_apply (P : MvPolynomial σ K) : phi g hg r hr P = T r (MvPolynomial.aeval g P) := rfl

theorem phi_eq_zero_iff (P : MvPolynomial σ K) : phi g hg r hr P = 0 ↔ MvPolynomial.aeval g P = 0 := by
  obtain ⟨C, hC, hP⟩ := evL_bdd g hg P
  rw [phi_apply]
  exact T_eq_zero_iff (norm_nonneg r) hr hC le_rfl hP

theorem phi_X (i : σ) : phi g hg r hr (MvPolynomial.X i : MvPolynomial σ K) = T r (g i) := by
  rw [phi_apply, MvPolynomial.aeval_X]

theorem phi_C (c : K) : phi g hg r hr (MvPolynomial.C c : MvPolynomial σ K) = PowerSeries.C (algebraMap K L c) := by
  rw [phi_apply, MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply K L L⟦X⟧]
  exact T_C _

end Phi
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section GenericBits

open MvPolynomial

theorem powerSeries_map_injective {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Injective φ) : Function.Injective (PowerSeries.map φ) := fun P Q h => by
  ext n; apply hφ; rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map, h]

variable (N : ℕ) [NeZero N]

theorem genPS_bdd {L : Type*} [NormedField L] [IsUltrametricDist L] (i : GenIdx N) : Bdd 1 (genPS L N i) := fun k => by
  rw [genPS, PowerSeries.coeff_map]
  exact IsUltrametricDist.norm_intCast_le_one L _

theorem aeval_genPS_eq {K L : Type*} [Field K] [Field L] [Algebra K L] (p : MvPolynomial (GenIdx N) K) :
    MvPolynomial.aeval (genPS L N) p = (evPS N K p).map (algebraMap K L) := by
  rw [evPS_map, ← MvPolynomial.aeval_map_algebraMap L]

end GenericBits
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

open IsDedekindDomain NumberField

namespace CuspDisc

section VR
variable {K : Type*} [Field K] [NumberField K]

theorem exists_heightOneSpectrum_eq_valuationSubring (B : ValuationSubring K) (hB : B ≠ ⊤) :
    ∃ v : HeightOneSpectrum (𝓞 K), (v.valuation K).valuationSubring = B := by
  have hint : ∀ x : 𝓞 K, (x : K) ∈ B := by
    intro x
    have hx : IsIntegral ℤ (x : K) := x.isIntegral_coe
    have hx' : IsIntegral B (x : K) := hx.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := K)).mp hx'
    rw [← hy]; exact y.2
  let ι : 𝓞 K →+* B := (Subring.inclusion (show (algebraMap (𝓞 K) K).range ≤ B.toSubring from by
      rintro _ ⟨x, rfl⟩; exact hint x)).comp (algebraMap (𝓞 K) K).rangeRestrict
  have hι : ∀ x : 𝓞 K, ((ι x : B) : K) = x := fun x => rfl
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal B).comap ι
  have hP : P.IsPrime := Ideal.comap_isPrime ι _
  have hinv : ∀ b : 𝓞 K, b ∉ P → ((b : K))⁻¹ ∈ B := by
    intro b hbP
    have hbu : IsUnit (ι b) := by
      by_contra h
      exact hbP ((IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨u, hu⟩ := hbu
    have h1 : ((u : B) : K) * ((↑u⁻¹ : B) : K) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    rw [hu, hι] at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact (↑u⁻¹ : B).2
  have hP0 : P ≠ ⊥ := by
    intro hP0
    apply hB
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hbP : b ∉ P := by rw [hP0]; simpa using nonZeroDivisors.ne_zero hb
    rw [div_eq_mul_inv]
    exact mul_mem (hint a) (hinv b hbP)
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
  refine ⟨v, ?_⟩
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ hB
  rintro x ⟨a, s, hs, rfl⟩
  exact mul_mem (hint a) (hinv s hs)

end VR
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Adic

open IsDedekindDomain NumberField IsLocalRing Filter Topology

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev Kv := v.adicCompletion K
abbrev Ov := v.adicCompletionIntegers K

theorem norm_coe_Ov_le_one (x : Ov K v) : ‖(x : Kv K v)‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp x.2)

theorem mem_Ov_iff_norm_le_one (x : Kv K v) : x ∈ Ov K v ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem isUnit_Ov_iff_norm_eq_one (x : Ov K v) : IsUnit x ↔ ‖(x : Kv K v)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := norm_coe_Ov_le_one K v (u : Ov K v)
    have h2 := norm_coe_Ov_le_one K v (↑u⁻¹ : Ov K v)
    have hmul : ‖((u : Ov K v) : Kv K v)‖ * ‖((↑u⁻¹ : Ov K v) : Kv K v)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; simp
    nlinarith [norm_nonneg ((u : Ov K v) : Kv K v), norm_nonneg ((↑u⁻¹ : Ov K v) : Kv K v)]
  · intro h
    have hx0 : (x : Kv K v) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    have hinv : (x : Kv K v)⁻¹ ∈ Ov K v := by
      rw [mem_Ov_iff_norm_le_one, norm_inv, h, inv_one]
    refine ⟨⟨x, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · ext; simp [hx0]
    · ext; simp [hx0]

theorem norm_lt_one_of_mem_maximalIdeal {x : Ov K v} (hx : x ∈ maximalIdeal (Ov K v)) :
    ‖(x : Kv K v)‖ < 1 :=
  lt_of_le_of_ne (norm_coe_Ov_le_one K v x) fun h => hx ((isUnit_Ov_iff_norm_eq_one K v x).mpr h)

theorem norm_eq_one_of_isUnit {x : Ov K v} (hx : IsUnit x) : ‖(x : Kv K v)‖ = 1 :=
  (isUnit_Ov_iff_norm_eq_one K v x).mp hx

theorem dvd_of_norm_le {a b : Ov K v} (ha : a ≠ 0) (h : ‖(b : Kv K v)‖ ≤ ‖(a : Kv K v)‖) : a ∣ b := by
  have ha' : (a : Kv K v) ≠ 0 := by simpa using ha
  have hq : (b : Kv K v) / a ∈ Ov K v := by
    rw [mem_Ov_iff_norm_le_one, norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)
  refine ⟨⟨_, hq⟩, ?_⟩
  ext; simp [mul_div_cancel₀ _ ha']

theorem mem_maximalIdeal_pow_iff {ϖ : Ov K v} (hϖ : Irreducible ϖ) (n : ℕ) (y : Ov K v) :
    y ∈ maximalIdeal (Ov K v) ^ n ↔ ‖(y : Kv K v)‖ ≤ ‖(ϖ : Kv K v)‖ ^ n := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul, Subring.coe_pow, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (norm_coe_Ov_le_one K v c)
  · intro h
    refine dvd_of_norm_le K v (pow_ne_zero _ hϖ.ne_zero) ?_
    rwa [Subring.coe_pow, norm_pow]

theorem irreducible_mem_maximalIdeal {ϖ : Ov K v} (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal (Ov K v) := by
  rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ

theorem smodEq_iff_norm_le {ϖ : Ov K v} (hϖ : Irreducible ϖ) (n : ℕ) (x y : Ov K v) :
    x ≡ y [SMOD (maximalIdeal (Ov K v) ^ n • ⊤ : Submodule (Ov K v) (Ov K v))]
      ↔ ‖(x : Kv K v) - y‖ ≤ ‖(ϖ : Kv K v)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_iff K v hϖ, AddSubgroupClass.coe_sub]

theorem isPrecomplete_Ov : IsPrecomplete (maximalIdeal (Ov K v)) (Ov K v) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ov K v)
  have hq1 : ‖(ϖ : Kv K v)‖ < 1 := norm_lt_one_of_mem_maximalIdeal K v (irreducible_mem_maximalIdeal K v hϖ)
  have hq0 : 0 ≤ ‖(ϖ : Kv K v)‖ := norm_nonneg _
  refine ⟨fun {f} hf => ?_⟩
  have hdist : ∀ m n, m ≤ n → ‖(f n : Kv K v) - f m‖ ≤ ‖(ϖ : Kv K v)‖ ^ m := by
    intro m n hmn
    have h := (hf hmn).symm
    rwa [smodEq_iff_norm_le K v hϖ] at h
  have hcau : CauchySeq fun n => (f n : Kv K v) := by
    refine cauchySeq_of_le_geometric ‖(ϖ : Kv K v)‖ 1 hq1 fun n => ?_
    rw [dist_eq_norm, ← norm_neg, neg_sub, one_mul]
    exact hdist n (n + 1) (Nat.le_succ n)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  have hxn : ∀ n, ‖x - f n‖ ≤ ‖(ϖ : Kv K v)‖ ^ n := fun n => by
    have ht : Tendsto (fun m => ‖(f m : Kv K v) - f n‖) atTop (𝓝 ‖x - f n‖) :=
      (hx.sub_const _).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨n, fun m hm => hdist n m hm⟩)
  have hxO : x ∈ Ov K v := by
    rw [mem_Ov_iff_norm_le_one]
    have : x = (x - f 0) + f 0 := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (norm_coe_Ov_le_one K v _))
    exact (hxn 0).trans (by simp)
  refine ⟨⟨x, hxO⟩, fun n => ?_⟩
  rw [smodEq_iff_norm_le K v hϖ, ← norm_neg, neg_sub]
  exact hxn n

scoped instance isAdicComplete_Ov : IsAdicComplete (maximalIdeal (Ov K v)) (Ov K v) :=
  haveI := isPrecomplete_Ov K v
  IsAdicComplete.mk

scoped instance : NontriviallyNormedField (Kv K v) :=
  NontriviallyNormedField.ofNormNeOne <| by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ov K v)
    refine ⟨(ϖ : Kv K v), fun h => hϖ.ne_zero (by exact_mod_cast h), ?_⟩
    exact (norm_lt_one_of_mem_maximalIdeal K v (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)).ne

abbrev Ωv := AlgebraicClosure (Kv K v)

scoped instance : NormedField (Ωv K v) := spectralNorm.normedField (Kv K v) (Ωv K v)
scoped instance : NormedAlgebra (Kv K v) (Ωv K v) := spectralNorm.normedAlgebra (Kv K v) (Ωv K v)
scoped instance : IsUltrametricDist (Ωv K v) := IsUltrametricDist.of_normedAlgebra (Kv K v)
scoped instance : UniformContinuousConstSMul (Kv K v) (Ωv K v) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

abbrev Lv := UniformSpace.Completion (Ωv K v)

scoped instance : NormedField (Lv K v) := inferInstance
scoped instance : CompleteSpace (Lv K v) := inferInstance
scoped instance : NormedAlgebra (Kv K v) (Lv K v) := inferInstance
scoped instance : IsUltrametricDist (Lv K v) := IsUltrametricDist.of_normedAlgebra (Kv K v)

theorem norm_algebraMap_Kv_Lv (x : Kv K v) : ‖algebraMap (Kv K v) (Lv K v) x‖ = ‖x‖ :=
  norm_algebraMap' _ _

theorem norm_coe_Ωv_Lv (x : Ωv K v) : ‖((x : Ωv K v) : Lv K v)‖ = ‖x‖ :=
  UniformSpace.Completion.norm_coe x

example (g : PowerSeries (Ov K v)) (hg : g.map (IsLocalRing.residue _) ≠ 0) :
    ∃ f h, g.IsWeierstrassFactorization f h :=
  PowerSeries.exists_isWeierstrassFactorization hg

end Adic
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Adic2

open IsDedekindDomain NumberField IsLocalRing Filter Topology

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def jKL : K →+* Lv K v := (algebraMap (Kv K v) (Lv K v)).comp (algebraMap K (Kv K v))

theorem jKL_apply (x : K) : jKL K v x = algebraMap (Kv K v) (Lv K v) (algebraMap K (Kv K v) x) := rfl

scoped instance : CharZero (Lv K v) :=
  (RingHom.charZero_iff (jKL K v).injective).mp inferInstance

scoped instance instNontriviallyNormedFieldLv : NontriviallyNormedField (Lv K v) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NormedField.exists_lt_norm (Kv K v) 1
    exact ⟨algebraMap (Kv K v) (Lv K v) x, by rwa [norm_algebraMap']⟩

scoped instance : IsAlgClosed (Lv K v) :=
  IsAlgClosed.of_denseRange (K := Ωv K v) UniformSpace.Completion.denseRange_coe

theorem valued_algebraMap (x : K) : Valued.v (algebraMap K (Kv K v) x) = v.valuation K x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem algebraMap_mem_Ov_iff (x : K) : algebraMap K (Kv K v) x ∈ Ov K v ↔ v.valuation K x ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]

def ιL : Ov K v →+* Lv K v := (algebraMap (Kv K v) (Lv K v)).comp (Ov K v).subtype

theorem ιL_apply (x : Ov K v) : ιL K v x = algebraMap (Kv K v) (Lv K v) x := rfl

theorem ιL_injective : Function.Injective (ιL K v) :=
  (algebraMap (Kv K v) (Lv K v)).injective.comp Subtype.val_injective

theorem norm_ιL (x : Ov K v) : ‖ιL K v x‖ = ‖(x : Kv K v)‖ := by
  rw [ιL_apply]; exact norm_algebraMap_Kv_Lv K v _

theorem norm_ιL_le_one (x : Ov K v) : ‖ιL K v x‖ ≤ 1 := by
  rw [norm_ιL]; exact norm_coe_Ov_le_one K v x

theorem norm_ιL_lt_one {x : Ov K v} (hx : x ∈ maximalIdeal (Ov K v)) : ‖ιL K v x‖ < 1 := by
  rw [norm_ιL]; exact norm_lt_one_of_mem_maximalIdeal K v hx

def liftOv (P : PowerSeries K) (h : ∀ n, v.valuation K (PowerSeries.coeff n P) ≤ 1) : PowerSeries (Ov K v) :=
  PowerSeries.mk fun n => ⟨algebraMap K (Kv K v) (PowerSeries.coeff n P), (algebraMap_mem_Ov_iff K v _).mpr (h n)⟩

theorem coeff_liftOv (P : PowerSeries K) (h) (n : ℕ) :
    ((PowerSeries.coeff n (liftOv K v P h) : Ov K v) : Kv K v) = algebraMap K (Kv K v) (PowerSeries.coeff n P) := by
  simp [liftOv]

theorem liftOv_map_ιL (P : PowerSeries K) (h) :
    (liftOv K v P h).map (ιL K v) = P.map (jKL K v) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, ιL_apply, coeff_liftOv, jKL_apply]

theorem liftOv_map_subtype (P : PowerSeries K) (h) :
    (liftOv K v P h).map (Ov K v).subtype = P.map (algebraMap K (Kv K v)) := by
  ext n : 1
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
  exact coeff_liftOv K v P h n

theorem exists_primitive_scaling (P : PowerSeries K) (hP : P ≠ 0) (b : ℤ)
    (hb : ∀ n, PowerSeries.coeff n P ≠ 0 → WithZero.log (v.valuation K (PowerSeries.coeff n P)) ≤ b) :
    ∃ c : K, c ≠ 0 ∧ (∀ n, v.valuation K (c * PowerSeries.coeff n P) ≤ 1) ∧
      ∃ n₀, v.valuation K (c * PowerSeries.coeff n₀ P) = 1 := by
  classical
  let Pz : ℤ → Prop := fun z => ∃ n, PowerSeries.coeff n P ≠ 0 ∧ WithZero.log (v.valuation K (PowerSeries.coeff n P)) = z
  have hbdd : ∃ b', ∀ z, Pz z → z ≤ b' := ⟨b, fun z ⟨n, hn, hz⟩ => hz ▸ hb n hn⟩
  have hinh : ∃ z, Pz z := by
    obtain ⟨n, hn⟩ : ∃ n, PowerSeries.coeff n P ≠ 0 :=
      not_forall.mp fun h => hP (PowerSeries.ext fun n => by simpa using h n)
    exact ⟨_, n, hn, rfl⟩
  obtain ⟨z₀, ⟨n₀, hn₀, hz₀⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  have hv0 : v.valuation K (PowerSeries.coeff n₀ P) ≠ 0 := by simpa using hn₀
  refine ⟨(PowerSeries.coeff n₀ P)⁻¹, inv_ne_zero hn₀, fun n => ?_, n₀, ?_⟩
  · rw [map_mul, map_inv₀]
    rcases eq_or_ne (PowerSeries.coeff n P) 0 with h0 | h0
    · rw [h0, map_zero, mul_zero]; exact zero_le'
    have hvn : v.valuation K (PowerSeries.coeff n P) ≠ 0 := by simpa using h0
    rw [inv_mul_le_iff₀ (zero_lt_iff.mpr hv0), mul_one, ← WithZero.log_le_log hvn hv0, hz₀]
    exact hmax _ ⟨n, h0, rfl⟩
  · rw [map_mul, map_inv₀, inv_mul_cancel₀ hv0]

end Adic2
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Theta

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial"

variable (N : ℕ) [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldBar N)

def evQb : MvPolynomial (GenIdx N) ℚbar →+* LaurentSeries ℚbar :=
  (HahnSeries.ofPowerSeries ℤ ℚbar).comp (MvPolynomial.aeval (genPS ℚbar N)).toRingHom

theorem evQb_apply (p : MvPolynomial (GenIdx N) ℚbar) :
    evQb N p = HahnSeries.ofPowerSeries ℤ ℚbar (evPS N ℚbar p) := rfl

theorem evQb_mem (p : MvPolynomial (GenIdx N) ℚbar) : evQb N p ∈ modularFunctionFieldBar N := by
  rw [evQb_apply, ← aeval_genL_eq, modularFunctionFieldBar_eq_adjoin_genL]
  refine IntermediateField.algebra_adjoin_le_adjoin _ _ ?_
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨_, rfl⟩

def evFb : MvPolynomial (GenIdx N) ℚbar →+* FN :=
  (evQb N).codRestrict (modularFunctionFieldBar N).toSubring (evQb_mem N)

@[scoped simp] theorem coe_evFb (p : MvPolynomial (GenIdx N) ℚbar) : ((evFb N p : FN) : LaurentSeries ℚbar) = evQb N p := rfl

theorem evFb_C (c : ℚbar) : evFb N (MvPolynomial.C c) = algebraMap ℚbar FN c := by
  apply Subtype.ext
  show evQb N (MvPolynomial.C c) = ((algebraMap ℚbar FN c : FN) : LaurentSeries ℚbar)
  rw [evQb_apply, ← aeval_genL_eq, MvPolynomial.aeval_C]
  rfl

theorem evFb_eq_zero_iff_evPS (p : MvPolynomial (GenIdx N) ℚbar) : evFb N p = 0 ↔ evPS N ℚbar p = 0 := by
  rw [← Subtype.coe_inj, coe_evFb, ZeroMemClass.coe_zero, evQb_apply,
    map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective]

theorem exists_presentation' (f : FN) :
    ∃ r s : MvPolynomial (GenIdx N) ℚbar, evFb N s ≠ 0 ∧ f = evFb N r / evFb N s := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_zero, zero_div]⟩
  obtain ⟨r, s, hrs⟩ := exists_presentation N f
  have hs : evFb N s ≠ 0 := by
    intro h
    have hs' : evPS N ℚbar s = 0 := (evFb_eq_zero_iff_evPS N s).mp h
    have : (f : LaurentSeries ℚbar) = 0 := by rw [hrs, hs', map_zero, div_zero]
    exact hf (Subtype.ext this)
  refine ⟨r, s, hs, Subtype.ext ?_⟩
  rw [hrs]
  push_cast
  rfl

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [Algebra ℚbar L]

theorem evFb_eq_zero_iff (r : L) (hr : ‖r‖ < 1) (p : MvPolynomial (GenIdx N) ℚbar) :
    evFb N p = 0 ↔ phi (K := ℚbar) (L := L) (genPS L N) (genPS_bdd N) r hr p = 0 := by
  rw [evFb_eq_zero_iff_evPS, phi_eq_zero_iff, aeval_genPS_eq,
    map_eq_zero_iff _ (powerSeries_map_injective _ (algebraMap ℚbar L).injective)]

variable (r : L) (hr : ‖r‖ < 1)

def phiL : MvPolynomial (GenIdx N) ℚbar →+* LaurentSeries L :=
  (HahnSeries.ofPowerSeries ℤ L).comp (phi (K := ℚbar) (L := L) (genPS L N) (genPS_bdd N) r hr)

theorem phiL_apply (p : MvPolynomial (GenIdx N) ℚbar) :
    phiL N r hr p = HahnSeries.ofPowerSeries ℤ L (phi (K := ℚbar) (L := L) (genPS L N) (genPS_bdd N) r hr p) := rfl

theorem phiL_eq_zero_iff (p : MvPolynomial (GenIdx N) ℚbar) : phiL N r hr p = 0 ↔ evFb N p = 0 := by
  rw [phiL_apply, map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective, evFb_eq_zero_iff N (L := L) r hr p]

theorem phiL_div_eq {r₁ s₁ r₂ s₂ : MvPolynomial (GenIdx N) ℚbar} (hs₁ : evFb N s₁ ≠ 0) (hs₂ : evFb N s₂ ≠ 0)
    (h : evFb N r₁ / evFb N s₁ = evFb N r₂ / evFb N s₂) :
    phiL N r hr r₁ / phiL N r hr s₁ = phiL N r hr r₂ / phiL N r hr s₂ := by
  have hS₁ : phiL N r hr s₁ ≠ 0 := fun h0 => hs₁ ((phiL_eq_zero_iff N r hr s₁).mp h0)
  have hS₂ : phiL N r hr s₂ ≠ 0 := fun h0 => hs₂ ((phiL_eq_zero_iff N r hr s₂).mp h0)
  rw [div_eq_div_iff hS₁ hS₂, ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, phiL_eq_zero_iff, map_sub,
    sub_eq_zero, map_mul, map_mul]
  rw [div_eq_div_iff hs₁ hs₂] at h
  exact h

def theta : FN →+* LaurentSeries L where
  toFun f := phiL N r hr (exists_presentation' N f).choose / phiL N r hr (exists_presentation' N f).choose_spec.choose
  map_one' := by
    have hspec := (exists_presentation' N (1 : FN)).choose_spec.choose_spec
    rw [phiL_div_eq N r hr (r₂ := 1) (s₂ := 1) hspec.1 (by rw [map_one]; exact one_ne_zero)
      (by rw [← hspec.2, map_one, div_one]), map_one, div_one]
  map_mul' f g := by
    have hf := (exists_presentation' N f).choose_spec.choose_spec
    have hg := (exists_presentation' N g).choose_spec.choose_spec
    have hfg := (exists_presentation' N (f * g)).choose_spec.choose_spec
    set rf := (exists_presentation' N f).choose
    set sf := (exists_presentation' N f).choose_spec.choose
    set rg := (exists_presentation' N g).choose
    set sg := (exists_presentation' N g).choose_spec.choose
    set rfg := (exists_presentation' N (f * g)).choose
    set sfg := (exists_presentation' N (f * g)).choose_spec.choose
    rw [phiL_div_eq N r hr hfg.1 (by rw [map_mul]; exact mul_ne_zero hf.1 hg.1 : evFb N (sf * sg) ≠ 0)
      (by rw [← hfg.2, hf.2, hg.2, map_mul, map_mul, div_mul_div_comm] : evFb N rfg / evFb N sfg = evFb N (rf * rg) / evFb N (sf * sg)),
      map_mul, map_mul, div_mul_div_comm]
  map_zero' := by
    have hspec := (exists_presentation' N (0 : FN)).choose_spec.choose_spec
    rw [phiL_div_eq N r hr (r₂ := 0) (s₂ := 1) hspec.1 (by rw [map_one]; exact one_ne_zero)
      (by rw [← hspec.2, map_zero, map_one, zero_div]), map_zero, zero_div]
  map_add' f g := by
    have hf := (exists_presentation' N f).choose_spec.choose_spec
    have hg := (exists_presentation' N g).choose_spec.choose_spec
    have hfg := (exists_presentation' N (f + g)).choose_spec.choose_spec
    set rf := (exists_presentation' N f).choose
    set sf := (exists_presentation' N f).choose_spec.choose
    set rg := (exists_presentation' N g).choose
    set sg := (exists_presentation' N g).choose_spec.choose
    set rfg := (exists_presentation' N (f + g)).choose
    set sfg := (exists_presentation' N (f + g)).choose_spec.choose
    have hS₁ : phiL N r hr sf ≠ 0 := fun h0 => hf.1 ((phiL_eq_zero_iff N r hr sf).mp h0)
    have hS₂ : phiL N r hr sg ≠ 0 := fun h0 => hg.1 ((phiL_eq_zero_iff N r hr sg).mp h0)
    rw [phiL_div_eq N r hr hfg.1 (by rw [map_mul]; exact mul_ne_zero hf.1 hg.1 : evFb N (sf * sg) ≠ 0)
      (by rw [← hfg.2, hf.2, hg.2, map_add, map_mul, map_mul, map_mul, div_add_div _ _ hf.1 hg.1]
        : evFb N rfg / evFb N sfg = evFb N (rf * sg + sf * rg) / evFb N (sf * sg)),
      map_add, map_mul, map_mul, map_mul, div_add_div _ _ hS₁ hS₂]

theorem theta_apply_div {a b : MvPolynomial (GenIdx N) ℚbar} (hb : evFb N b ≠ 0) :
    theta N r hr (evFb N a / evFb N b) = phiL N r hr a / phiL N r hr b := by
  have hspec := (exists_presentation' N (evFb N a / evFb N b)).choose_spec.choose_spec
  show phiL N r hr _ / phiL N r hr _ = _
  exact phiL_div_eq N r hr hspec.1 hb hspec.2.symm

theorem theta_evFb (a : MvPolynomial (GenIdx N) ℚbar) : theta N r hr (evFb N a) = phiL N r hr a := by
  have := theta_apply_div N r hr (a := a) (b := 1) (by rw [map_one]; exact one_ne_zero)
  rwa [map_one, div_one, map_one, div_one] at this

theorem theta_algebraMap (c : ℚbar) : theta N r hr (algebraMap ℚbar FN c) = HahnSeries.C (algebraMap ℚbar L c) := by
  rw [← evFb_C, theta_evFb, phiL_apply, phi_C, HahnSeries.ofPowerSeries_C]

end Theta
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section ThetaPlace

open AlgebraicCurve

variable {K₀ F L : Type*} [Field K₀] [Field F] [Algebra K₀ F] [Field L]

omit [Algebra K₀ F] in

theorem forall_coeff_neg_eq_zero_iff (x : LaurentSeries L) : (∀ n < 0, x.coeff n = 0) ↔ 0 ≤ x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact (mt HahnSeries.coeff_order_eq_zero.mp hx) (h _ hlt)
  · intro h n hn
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn h)

omit [Algebra K₀ F] in
theorem valuation_le_one_iff_order (x : LaurentSeries L) : Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) ↔ 0 ≤ x.order := by
  rw [← forall_coeff_neg_eq_zero_iff]
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (f := x) (D := 0)
  simp only [neg_zero, ofAdd_zero, WithZero.coe_one] at h
  exact h

variable (θ : F →+* LaurentSeries L)

def thetaRing : ValuationSubring F := (Valued.v.valuationSubring : ValuationSubring (LaurentSeries L)).comap θ

theorem mem_thetaRing_iff (f : F) : f ∈ thetaRing θ ↔ 0 ≤ (θ f).order := by
  rw [thetaRing, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, valuation_le_one_iff_order]

omit [Algebra K₀ F] in
theorem order_inv' {x : LaurentSeries L} (hx : x ≠ 0) : x⁻¹.order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  linarith

theorem inv_not_mem_thetaRing {f : F} (hf : θ f ≠ 0) (hpos : 0 < (θ f).order) : f⁻¹ ∉ thetaRing θ := by
  rw [mem_thetaRing_iff, map_inv₀, order_inv' hf]
  linarith

theorem thetaRing_ne_top {f : F} (hf : θ f ≠ 0) (hpos : 0 < (θ f).order) : thetaRing θ ≠ ⊤ :=
  fun h => inv_not_mem_thetaRing θ hf hpos (h ▸ ValuationSubring.mem_top _)

theorem algebraMap_mem_thetaRing {σ : K₀ →+* L} (hθ : ∀ a : K₀, θ (algebraMap K₀ F a) = HahnSeries.C (σ a))
    (a : K₀) : algebraMap K₀ F a ∈ thetaRing θ := by
  rw [mem_thetaRing_iff, hθ, HahnSeries.order_C]

theorem order_pos_of_mem_nonunits {f : F} (hf : f ≠ 0) (hmem : f ∈ thetaRing θ)
    (hnu : (⟨f, hmem⟩ : thetaRing θ) ∈ nonunits (thetaRing θ)) : 0 < (θ f).order := by
  have h0 := (mem_thetaRing_iff θ f).mp hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hnu
    have hθf : θ f ≠ 0 := (map_ne_zero θ).mpr hf
    have hinv : f⁻¹ ∈ thetaRing θ := by
      rw [mem_thetaRing_iff, map_inv₀, order_inv' hθf, ← heq, neg_zero]
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf), Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

end ThetaPlace
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section PointPackage

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial"

variable (N : ℕ) [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldBar N)

abbrev jF' : FN := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem evFb_X_none_mul_jF : evFb N (MvPolynomial.X none) * jF' N = 1 := by
  apply Subtype.ext
  show evQb N (MvPolynomial.X none) * coeffEmb ℚbar jq = 1
  rw [evQb_apply, ← aeval_genL_eq, MvPolynomial.aeval_X, mul_comm]
  exact coeffEmb_jq_mul_genL_none ℚbar N

theorem jF'_ne_algebraMap (c : ℚbar) : (jF' N : FN) ≠ algebraMap ℚbar FN c := by
  intro h
  have h1 := congrArg (fun f : FN => (f : LaurentSeries ℚbar).coeff (-1)) h
  simp only [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  rw [show ((algebraMap ℚbar FN c : FN) : LaurentSeries ℚbar) = algebraMap ℚbar (LaurentSeries ℚbar) c from rfl,
    HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
    HahnSeries.coeff_single_of_ne (by norm_num)] at h1
  exact one_ne_zero h1

theorem jF'_ne_zero : (jF' N : FN) ≠ 0 := by
  have := jF'_ne_algebraMap N 0; rwa [map_zero] at this

theorem evFb_X_none_eq_inv : evFb N (MvPolynomial.X none) = (jF' N)⁻¹ :=
  eq_inv_of_mul_eq_one_left (evFb_X_none_mul_jF N)

theorem evFb_X_none_ne_algebraMap (c : ℚbar) : evFb N (MvPolynomial.X none) ≠ algebraMap ℚbar FN c := by
  intro h
  rw [evFb_X_none_eq_inv] at h
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, _root_.inv_eq_zero] at h; exact jF'_ne_zero N h
  · apply jF'_ne_algebraMap N c⁻¹
    rw [map_inv₀, ← h, inv_inv]

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

theorem norm_constantCoeff_T_sub_le {u : L⟦X⟧} (hu : Bdd 1 u) {r : L} (hr : ‖r‖ < 1) :
    ‖PowerSeries.constantCoeff (T r u) - PowerSeries.constantCoeff u‖ ≤ ‖r‖ := by
  rw [constantCoeff_T]
  have hsum : Summable fun k : ℕ => PowerSeries.coeff k u * r ^ k := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hr) fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hu k)
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k => ?_
  rw [norm_mul, norm_pow]
  calc ‖PowerSeries.coeff (k + 1) u‖ * ‖r‖ ^ (k + 1) ≤ 1 * ‖r‖ ^ (k + 1) :=
        mul_le_mul_of_nonneg_right (hu _) (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖r‖ := by
        rw [one_mul, pow_succ]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hr.le)

theorem norm_constantCoeff_T_sub_one_lt {u : L⟦X⟧} (hu : Bdd 1 u) (hu1 : PowerSeries.constantCoeff u = 1)
    {r : L} (hr : ‖r‖ < 1) : ‖PowerSeries.constantCoeff (T r u) - 1‖ < 1 := by
  have := norm_constantCoeff_T_sub_le (L := L) hu hr
  rw [hu1] at this
  exact lt_of_le_of_lt this hr

theorem norm_constantCoeff_T_eq_one {u : L⟦X⟧} (hu : Bdd 1 u) (hu1 : PowerSeries.constantCoeff u = 1)
    {r : L} (hr : ‖r‖ < 1) : ‖PowerSeries.constantCoeff (T r u)‖ = 1 := by
  have h := norm_constantCoeff_T_sub_one_lt (L := L) hu hu1 hr
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := PowerSeries.constantCoeff (T r u) - 1) (y := (1 : L))
    (by rw [norm_one]; exact h.ne)
  rw [sub_add_cancel, norm_one, max_eq_right h.le] at this
  exact this

theorem norm_coeff_T_le {u : L⟦X⟧} (hu : Bdd 1 u) {r : L} (hr : ‖r‖ < 1) (n : ℕ) :
    ‖PowerSeries.coeff n (T r u)‖ ≤ 1 :=
  hu.T (norm_nonneg r) hr.le zero_le_one le_rfl n

def jDenL (L : Type*) [NontriviallyNormedField L] : L⟦X⟧ := jDen.map (Int.castRingHom L)

theorem genPS_none_eq : genPS L N none = PowerSeries.X * jDenL L := by
  simp [genPS, genZ, jDenL]

theorem bdd_jDenL : Bdd 1 (jDenL L) := fun k => by
  rw [jDenL, PowerSeries.coeff_map]; exact IsUltrametricDist.norm_intCast_le_one L _

omit [NeZero N] [CompleteSpace L] [IsUltrametricDist L] in
theorem constantCoeff_jDen_map {R : Type*} [CommRing R] (f : ℤ →+* R) : PowerSeries.constantCoeff (jDen.map f) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_jDen, map_one]

theorem constantCoeff_jDenL : PowerSeries.constantCoeff (jDenL L) = 1 := constantCoeff_jDen_map _

theorem bdd_X : Bdd 1 (PowerSeries.X : L⟦X⟧) := fun k => by
  rw [PowerSeries.coeff_X]; split_ifs <;> simp

theorem T_genPS_none {r : L} (hr : ‖r‖ < 1) :
    T r (genPS L N none) = (PowerSeries.C r + PowerSeries.X) * T r (jDenL L) := by
  rw [genPS_none_eq, T_mul (norm_nonneg r) hr zero_le_one zero_le_one le_rfl bdd_X bdd_jDenL, T_X, add_comm]

theorem norm_constantCoeff_T_genPS_none {r : L} (hr : ‖r‖ < 1) :
    ‖PowerSeries.constantCoeff (T r (genPS L N none))‖ = ‖r‖ := by
  rw [T_genPS_none N hr, map_mul, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero,
    norm_mul, norm_constantCoeff_T_eq_one bdd_jDenL constantCoeff_jDenL hr, mul_one]

theorem norm_coeff_one_T_genPS_none {r : L} (hr : ‖r‖ < 1) :
    ‖PowerSeries.coeff 1 (T r (genPS L N none))‖ = 1 := by
  rw [T_genPS_none N hr, add_mul, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff]
  have h1 : ‖PowerSeries.constantCoeff (T r (jDenL L))‖ = 1 := norm_constantCoeff_T_eq_one bdd_jDenL constantCoeff_jDenL hr
  have h2 : ‖r * PowerSeries.coeff 1 (T r (jDenL L))‖ < 1 := by
    rw [norm_mul]
    calc ‖r‖ * ‖PowerSeries.coeff 1 (T r (jDenL L))‖ ≤ ‖r‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_coeff_T_le bdd_jDenL hr 1) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hr
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (x := r * PowerSeries.coeff 1 (T r (jDenL L))) (y := PowerSeries.constantCoeff (T r (jDenL L)))
    (by rw [h1]; exact h2.ne)
  rw [this, h1, max_eq_right h2.le]

end PointPackage
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section PointPackage2

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial IsLocalRing"

variable (N : ℕ) [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldBar N)

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [Algebra ℚbar L]

omit [NeZero N] [CompleteSpace L] [IsUltrametricDist L] [Algebra ℚbar L] in
theorem order_ofPowerSeries_nonneg (P : L⟦X⟧) : 0 ≤ (HahnSeries.ofPowerSeries ℤ L P).order := by
  rw [← forall_coeff_neg_eq_zero_iff]
  intro n hn
  exact ofPowerSeries_coeff_of_neg _ hn

theorem theta_X_none (r : L) (hr : ‖r‖ < 1) :
    theta N r hr (evFb N (MvPolynomial.X none)) = HahnSeries.ofPowerSeries ℤ L (T r (genPS L N none)) := by
  rw [theta_evFb, phiL_apply, phi_X]

theorem exists_thetaPlace (r : L) (hr : ‖r‖ < 1) (hO : thetaRing (theta N r hr) ≠ ⊤) :
    ∃ V : Place ℚbar FN,
      (∀ f, f ∈ V.toValuationSubring ↔ 0 ≤ (theta N r hr f).order) ∧
      (∀ f, V.ord f = (theta N r hr f).order) ∧
      (∀ f (a : ℚbar), f ∈ V.toValuationSubring →
        (V.HasValue f a ↔ (theta N r hr f).coeff 0 = algebraMap ℚbar L a)) := by
  classical
  set θ := theta N r hr with hθdef
  have hθc : ∀ a : ℚbar, θ (algebraMap ℚbar FN a) = HahnSeries.C (algebraMap ℚbar L a) := theta_algebraMap N r hr
  have hconst : ∀ c : ℚbar, algebraMap ℚbar FN c ∈ thetaRing θ := algebraMap_mem_thetaRing θ hθc
  haveI : FiniteDimensional (IntermediateField.adjoin ℚbar ({jF' N} : Set FN)) FN :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  obtain ⟨V₀, hV₀⟩ := Place.exists_of_valuationSubring (K := ℚbar) (F := FN) (jF' N) (thetaRing θ) hconst hO
  have hmem₀ : ∀ f : FN, f ∈ V₀.toValuationSubring ↔ 0 ≤ (θ f).order := fun f => by
    rw [hV₀, mem_thetaRing_iff]
  set wF : FN := evFb N (MvPolynomial.X none) with hwF
  have hθw : θ wF = HahnSeries.ofPowerSeries ℤ L (T r (genPS L N none)) := theta_X_none N r hr
  have hwmem : wF ∈ V₀.toValuationSubring := by
    rw [hmem₀, hθw]; exact order_ofPowerSeries_nonneg _
  have hsurj : Function.Surjective (algebraMap ℚbar V₀.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField V₀).mp (deg_eq_one_modularFunctionFieldBar N V₀)
  obtain ⟨a₀, ha₀, -⟩ := V₀.exists_hasValue_of_surjective hsurj hwmem
  set π : FN := wF - algebraMap ℚbar FN a₀ with hπ
  have hπ0 : π ≠ 0 := sub_ne_zero.mpr (evFb_X_none_ne_algebraMap N a₀)
  have hπval : V₀.HasValue π 0 := by
    obtain ⟨hw, hres⟩ := ha₀
    refine ⟨sub_mem hw (V₀.algebraMap_mem' a₀), ?_⟩
    have hx : (⟨π, sub_mem hw (V₀.algebraMap_mem' a₀)⟩ : V₀.toValuationSubring)
        = ⟨wF, hw⟩ - algebraMap ℚbar V₀.toValuationSubring a₀ := rfl
    rw [hx, map_sub, hres, map_zero, Place.residue_algebraMap, sub_self]
  have hπpos : 0 < (θ π).order := by
    have hmemπ : π ∈ V₀.toValuationSubring := hπval.mem
    have h0 : 0 ≤ (θ π).order := (hmem₀ π).mp hmemπ
    rcases h0.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hθπ : θ π ≠ 0 := (map_ne_zero θ).mpr hπ0
      have hinv : π⁻¹ ∈ V₀.toValuationSubring := by
        rw [hmem₀, map_inv₀, order_inv' hθπ, ← heq, neg_zero]
      have hunit : IsUnit (⟨π, hmemπ⟩ : V₀.toValuationSubring) :=
        ⟨⟨⟨π, hmemπ⟩, ⟨π⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hπ0), Subtype.ext (inv_mul_cancel₀ hπ0)⟩, rfl⟩
      have := (residue_ne_zero_iff_isUnit _).mpr hunit
      exact this (by rw [hπval.residue_eq, map_zero])
  have hπle : (θ π).order ≤ 1 := by
    apply HahnSeries.order_le_of_coeff_ne_zero
    rw [hπ, map_sub, hθw, hθc, HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.C_apply,
      HahnSeries.coeff_single_of_ne (by norm_num), sub_zero,
      show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff]
    intro h0
    have := norm_coeff_one_T_genPS_none N (L := L) hr
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hunif : ∃ x : FN, (θ x).order = 1 := ⟨π, le_antisymm hπle (by omega)⟩
  obtain ⟨V, hVmem, hVord, ι, hι⟩ := ModularCurve.exists_place_of_ringHom_laurentSeries (k := ℚbar) θ hθc hunif
  refine ⟨V, hVmem, hVord, fun f a hf => ?_⟩
  have hιa : ι (algebraMap ℚbar V.ResidueField a) = algebraMap ℚbar L a := ι.commutes a
  constructor
  · rintro ⟨hf', hres⟩
    have := hι ⟨f, hf'⟩
    rw [hres, hιa] at this
    exact this.symm
  · intro h
    refine ⟨hf, ?_⟩
    apply ι.toRingHom.injective
    change ι _ = ι _
    rw [hι ⟨f, hf⟩, hιa, h]

end PointPackage2
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Helpers

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial IsLocalRing"

local notation "ℚbar" => AlgebraicClosure ℚ

theorem order_coeffMap_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    (z : LaurentSeries R) : (coeffMap f z).order = z.order := by
  by_cases hz : z = 0
  · subst hz; simp
  have h1 : (coeffMap f z).coeff z.order ≠ 0 := by
    rw [coeffMap_coeff]
    exact (map_ne_zero_iff f hf).mpr (mt HahnSeries.coeff_order_eq_zero.mp hz)
  have hne : coeffMap f z ≠ 0 := fun h0 => h1 (by rw [h0, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  have h2 := mt HahnSeries.coeff_order_eq_zero.mp hne
  rw [coeffMap_coeff, HahnSeries.coeff_eq_zero_of_lt_order h, map_zero] at h2
  exact h2 rfl

theorem order_ofPowerSeries_eq {R : Type*} [CommRing R] {P : R⟦X⟧} (hP : P ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ R P).order = ((P.order).toNat : ℤ) := by
  have h1 : (HahnSeries.ofPowerSeries ℤ R P).coeff ((P.order).toNat : ℤ) ≠ 0 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff]; exact PowerSeries.coeff_order hP
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  have hne : HahnSeries.ofPowerSeries ℤ R P ≠ 0 := (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hP
  have h2 := mt HahnSeries.coeff_order_eq_zero.mp hne
  set o := (HahnSeries.ofPowerSeries ℤ R P).order with ho
  rcases lt_or_ge o 0 with hneg | hnn
  · rw [ofPowerSeries_coeff_of_neg _ hneg] at h2; exact h2 rfl
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
    rw [hn, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_of_lt_order_toNat n (by omega)] at h2
    exact h2 rfl

theorem finset_eq_singleton_of_sum_eq_one {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℕ∞)
    (hpos : ∀ i ∈ S, 0 < f i) (hsum : ∑ i ∈ S, f i = 1) :
    ∃ i, S = {i} ∧ f i = 1 := by
  have hone : ∀ i ∈ S, (1 : ℕ∞) ≤ f i := fun i hi => by
    have := Order.add_one_le_of_lt (hpos i hi)
    simpa using this
  have hcard : (S.card : ℕ∞) ≤ 1 := by
    have h := Finset.card_nsmul_le_sum S f 1 hone
    rw [hsum, nsmul_one] at h
    exact h
  have hcard' : S.card ≤ 1 := by exact_mod_cast hcard
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hcard1 : S.card = 1 := le_antisymm hcard' (Finset.card_pos.mpr hne)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
  refine ⟨i, hi, ?_⟩
  rw [hi, Finset.sum_singleton] at hsum
  exact hsum

end Helpers
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

section QHelpers

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial IsLocalRing ModularCurve.PlaceSpecialization Polynomial"

variable {q : ℕ} [Fact q.Prime]

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

theorem jFun_eq_jF' : (jFun (q := q) : FF) = jF' (1 * q) := rfl

theorem jFun_ne_zero'' : (jFun (q := q) : FF) ≠ 0 := jF'_ne_zero (1 * q)

theorem jqFun_eq_tInfty_mul' : (jqFun (q := q) : FF) = tInfty (q := q) * jFun (q := q) ^ (1 * q) := by
  rw [tInfty, div_mul_cancel₀ _ (pow_ne_zero _ jFun_ne_zero'')]

def dTop (q : ℕ) [Fact q.Prime] : {d : ℕ // d ∈ (1 * q).divisors} :=
  ⟨1 * q, Nat.mem_divisors.mpr ⟨dvd_rfl, NeZero.ne _⟩⟩

theorem tInfty_eq_evFb : (tInfty (q := q) : FF) = evFb (1 * q) (MvPolynomial.X (some (dTop q))) := by
  have hw : (jFun (q := q) : FF)⁻¹ = evFb (1 * q) (MvPolynomial.X none) := by
    rw [evFb_X_none_eq_inv]; rfl
  rw [tInfty, div_eq_mul_inv, ← inv_pow, hw, ← map_pow]
  apply Subtype.ext
  show coeffEmb ℚbar (qExpand ℚ (1 * q) jq) * evQb (1 * q) (MvPolynomial.X none ^ (1 * q))
    = evQb (1 * q) (MvPolynomial.X (some (dTop q)))
  rw [evQb_apply, evQb_apply, ← aeval_genL_eq, ← aeval_genL_eq, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  exact coeffEmb_qExpand_mul ℚbar (1 * q) (dTop q)

theorem constantCoeff_genPS_some {S : Type*} [CommRing S] (d : {d : ℕ // d ∈ (1 * q).divisors}) :
    PowerSeries.constantCoeff (genPS S (1 * q) (some d)) = 1 := by
  rw [genPS, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  simp only [genZ, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expandPS]
  simp only [dvd_zero, ↓reduceIte, Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
  have h := congrArg PowerSeries.constantCoeff jNum_mul_jDen
  rw [map_mul, constantCoeff_jNum, one_mul, map_one] at h
  simp [h]

section HV
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem HasValue.add' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem HasValue.neg' {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem HasValue.sub' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact HasValue.add' h (HasValue.neg' h')

theorem HasValue.pow' {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem HasValue.eval₂_int' {g : F} {a : K} (h : v.HasValue g a) (c : Polynomial ℤ) :
    v.HasValue (c.eval₂ (Int.castRingHom F) g) (c.eval₂ (Int.castRingHom K) a) := by
  induction c using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.eval₂_add, Polynomial.eval₂_add]; exact HasValue.add' hp hr
  | monomial n z =>
    rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
    have hz : v.HasValue ((z : ℤ) : F) ((z : ℤ) : K) := by simpa using v.hasValue_algebraMap (z : K)
    simpa using hz.mul (HasValue.pow' h n)

theorem HasValue.eval₂_bivariate' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a')
    (Φ : Polynomial (Polynomial ℤ)) :
    v.HasValue (Φ.eval₂ (eval₂RingHom (Int.castRingHom F) g) g') (Φ.eval₂ (eval₂RingHom (Int.castRingHom K) a) a') := by
  induction Φ using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.eval₂_add, Polynomial.eval₂_add]; exact HasValue.add' hp hr
  | monomial n c =>
    rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
    exact (HasValue.eval₂_int' h c).mul (HasValue.pow' h' n)

theorem ord_pos_of_hasValue_zero' {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  have h0 := v.ord_nonneg_of_mem h.mem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    have := (residue_ne_zero_iff_isUnit _).mpr hu
    exact this (by rw [h.residue_eq, map_zero])
end HV
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

variable {data : ModularPolynomialData q}

theorem modeq_jFun_jqFun'' :
    data.Φ.eval₂ (eval₂RingHom (Int.castRingHom FF) (jFun (q := q))) (jqFun (q := q)) = 0 := by
  apply Subtype.val_injective
  set ι : FF →+* LaurentSeries ℚbar := (algebraMap FF (LaurentSeries ℚbar)) with hι
  have hιapp : ∀ z : FF, ι z = (z : LaurentSeries ℚbar) := fun z => rfl
  show ((data.Φ.eval₂ (eval₂RingHom (Int.castRingHom FF) (jFun (q := q))) (jqFun (q := q)) : FF) : LaurentSeries ℚbar)
    = ((0 : FF) : LaurentSeries ℚbar)
  rw [← hιapp, ← hιapp, map_zero, Polynomial.hom_eval₂]
  have h0 := congrArg (coeffEmb ℚbar) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h0
  have hhom : ι.comp (eval₂RingHom (Int.castRingHom FF) (jFun (q := q))) = (coeffEmb ℚbar).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X, hιapp]; rfl
  have harg : ι (jqFun (q := q)) = coeffEmb ℚbar (jqN q) := by
    rw [hιapp]
    show coeffEmb ℚbar (qExpand ℚ (1 * q) jq) = coeffEmb ℚbar (jqN q)
    rw [jqN, qExpand_congr (one_mul q)]
  rw [hhom, harg]
  exact h0

def PsiAt' (data : ModularPolynomialData q) (x₀ : ℚbar) : Polynomial ℚbar :=
  data.Φ.map (eval₂RingHom (Int.castRingHom ℚbar) x₀)

theorem psiAt'_ne_zero (x₀ : ℚbar) : PsiAt' data x₀ ≠ 0 := (data.monic.map _).ne_zero

theorem isRoot_psiAt'_of_hasValue {W : Place ℚbar FF} {x₀ y : ℚbar} (hx : W.HasValue (jFun (q := q)) x₀)
    (hy : W.HasValue (jqFun (q := q)) y) : (PsiAt' data x₀).IsRoot y := by
  rw [IsRoot.def, PsiAt', Polynomial.eval_map]
  have h1 := HasValue.eval₂_bivariate' hx hy data.Φ
  rw [modeq_jFun_jqFun''] at h1
  have h0 : W.HasValue (0 : FF) (0 : ℚbar) := by simpa using W.hasValue_algebraMap (0 : ℚbar)
  exact h1.unique h0

theorem order_coe_jFun : ((jFun (q := q) : FF) : LaurentSeries ℚbar).order = -1 := by
  show (coeffEmb ℚbar jq).order = -1
  have h1 : (coeffEmb ℚbar jq).coeff (-1) ≠ 0 := by
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]; exact one_ne_zero
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  have hne : coeffEmb ℚbar jq ≠ 0 := fun h0 => h1 (by rw [h0, HahnSeries.coeff_zero])
  have h2 := mt HahnSeries.coeff_order_eq_zero.mp hne
  rw [coeffEmb_coeff, coeff_jq_of_lt h, map_zero] at h2
  exact h2 rfl

end QHelpers
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section TubeLemmas

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial IsLocalRing IsDedekindDomain NumberField"

local notation "ℚbar" => AlgebraicClosure ℚ

theorem order_map_eq_of_injective {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Injective f) (P : R⟦X⟧) : (P.map f).order = P.order := by
  by_cases hP : P = 0
  · subst hP; simp
  have hfin : P.order ≠ ⊤ := (PowerSeries.order_finite_iff_ne_zero.mpr hP).ne
  rw [← ENat.coe_toNat hfin, PowerSeries.order_eq_nat]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [PowerSeries.coeff_map]; exact (map_ne_zero_iff f hf).mpr (PowerSeries.coeff_order hP)
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_of_lt_order_toNat i hi, map_zero]

section Bounds
variable (N : ℕ) [NeZero N] (K : IntermediateField ℚ ℚbar) [FiniteDimensional ℚ K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

theorem exists_log_valuation_le (p : MvPolynomial (GenIdx N) K) :
    ∃ b : ℤ, ∀ n, PowerSeries.coeff n (evPS N K p) ≠ 0 →
      WithZero.log (v.valuation K (PowerSeries.coeff n (evPS N K p))) ≤ b := by
  obtain ⟨C, hC, hbdd⟩ := evL_bdd (K := K) (genPS (Kv K v) N) (genPS_bdd N) p
  obtain ⟨y, hy⟩ := NormedField.exists_lt_norm (Kv K v) C
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hy; exact not_lt.mpr hC hy
  refine ⟨WithZero.log (Valued.v y), fun n hn => ?_⟩
  have h1 : ‖algebraMap K (Kv K v) (PowerSeries.coeff n (evPS N K p))‖ ≤ ‖y‖ := by
    have := hbdd n
    rw [aeval_genPS_eq, PowerSeries.coeff_map] at this
    exact this.trans hy.le
  rw [Valued.toNormedField.norm_le_iff, valued_algebraMap] at h1
  rwa [WithZero.log_le_log (by simpa using hn) (by simpa using hy0)]

end Bounds
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

theorem bdd_X_pow (m : ℕ) : Bdd 1 ((PowerSeries.X : L⟦X⟧) ^ m) := fun k => by
  rw [PowerSeries.coeff_X_pow]; split_ifs <;> simp

theorem T_X_pow_ne_zero_and_order {ρ : L} (hρ : ‖ρ‖ < 1) (hρ0 : ρ ≠ 0) (m : ℕ) :
    (T ρ ((PowerSeries.X : L⟦X⟧) ^ m)).order = 0 := by
  have h : T ρ ((PowerSeries.X : L⟦X⟧) ^ m) = ((Polynomial.taylor ρ (Polynomial.X ^ m) : Polynomial L) : L⟦X⟧) := by
    rw [← T_coe]; simp
  rw [h, show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
  refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  rw [Polynomial.coeff_coe, Polynomial.taylor_coeff_zero, Polynomial.eval_pow, Polynomial.eval_X]
  exact pow_ne_zero _ hρ0

theorem bdd_map' {O : Type*} [CommRing O] (ι : O →+* L) (hι1 : ∀ x, ‖ι x‖ ≤ 1) (P : PowerSeries O) :
    Bdd 1 (P.map ι) := fun k => by
  rw [PowerSeries.coeff_map]; exact hι1 _

theorem order_C_mul'' {c : L} (hc : c ≠ 0) (P : PowerSeries L) : (PowerSeries.C c * P).order = P.order := by
  rw [PowerSeries.order_mul]
  have : (PowerSeries.C c : PowerSeries L).order = 0 := by
    rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
    exact ⟨by simpa using hc, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  rw [this, zero_add]

end TubeLemmas
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section WRoot

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial IsLocalRing IsDedekindDomain NumberField"

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_wroot (w₀ : Ov K v) (hw₀ : ‖(w₀ : Kv K v)‖ < 1) :
    ∃ ρ : Lv K v, ‖ρ‖ < 1 ∧ PowerSeries.constantCoeff (T ρ (genPS (Lv K v) N none)) = ιL K v w₀ ∧
      ∀ ρ' : Lv K v, ‖ρ'‖ < 1 → PowerSeries.constantCoeff (T ρ' (genPS (Lv K v) N none)) = ιL K v w₀ → ρ' = ρ := by
  classical
  set G : PowerSeries (Ov K v) := genPS (Ov K v) N none - PowerSeries.C w₀ with hG
  have hw₀m : w₀ ∈ maximalIdeal (Ov K v) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_Ov_iff_norm_eq_one]
    exact hw₀.ne
  have hres0 : residue (Ov K v) w₀ = 0 := (residue_eq_zero_iff _).mpr hw₀m
  have hGres : G.map (residue (Ov K v)) = genPS (ResidueField (Ov K v)) N none := by
    rw [hG, map_sub, PowerSeries.map_C, hres0, map_zero, sub_zero, genPS_map]
  have hGres0 : G.map (residue (Ov K v)) ≠ 0 := by
    rw [hGres]
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp only [genPS, genZ, map_mul, PowerSeries.map_X, map_zero, PowerSeries.coeff_zero_eq_constantCoeff] at h1
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff] at h1
    rw [constantCoeff_jDen_map] at h1
    exact one_ne_zero h1
  have hGord : (G.map (residue (Ov K v))).order = 1 := by
    rw [hGres, show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
    have hg : genPS (ResidueField (Ov K v)) N none = PowerSeries.X * (jDen.map (Int.castRingHom _)) := by
      simp [genPS, genZ]
    rw [hg]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jDen_map]
      exact one_ne_zero
    · have : i = 0 := by omega
      subst this
      rw [PowerSeries.coeff_zero_X_mul]
  obtain ⟨S, hS, hsum⟩ := PowerSeries.exists_finset_sum_order_taylorShift_eq_order_map_residue (ιL K v)
    (ιL_injective K v) (norm_ιL_le_one K v) (fun x hx => norm_ιL_lt_one K v hx) G hGres0
  change (∀ r, r ∈ S ↔ ‖r‖ < 1 ∧ 0 < (T r (G.map (ιL K v))).order) at hS
  change ∑ r ∈ S, (T r (G.map (ιL K v))).order = _ at hsum
  rw [hGord] at hsum
  obtain ⟨ρ, hSρ, -⟩ := finset_eq_singleton_of_sum_eq_one S _ (fun r hr => ((hS r).mp hr).2) hsum
  have hGL : G.map (ιL K v) = genPS (Lv K v) N none - PowerSeries.C (ιL K v w₀) := by
    rw [hG, map_sub, PowerSeries.map_C, genPS_map]
  have hbw : Bdd 1 (genPS (Lv K v) N none) := genPS_bdd N none
  have hbc : Bdd 1 (PowerSeries.C (ιL K v w₀) : (Lv K v)⟦X⟧) := (bdd_C _).mono (norm_ιL_le_one K v w₀)
  have hT : ∀ r : Lv K v, ‖r‖ < 1 → T r (G.map (ιL K v)) = T r (genPS (Lv K v) N none) - PowerSeries.C (ιL K v w₀) := by
    intro r hr
    rw [hGL, T_sub (norm_nonneg r) hr zero_le_one zero_le_one le_rfl hbw hbc, T_C]
  have hpos_iff : ∀ r : Lv K v, ‖r‖ < 1 →
      (0 < (T r (G.map (ιL K v))).order ↔ PowerSeries.constantCoeff (T r (genPS (Lv K v) N none)) = ιL K v w₀) := by
    intro r hr
    rw [hT r hr]
    have hne : T r (genPS (Lv K v) N none) - PowerSeries.C (ιL K v w₀) ≠ 0 := by
      intro h0
      have h1 := congrArg (PowerSeries.coeff 1) h0
      rw [map_sub, PowerSeries.coeff_C, if_neg one_ne_zero, sub_zero, map_zero] at h1
      have := norm_coeff_one_T_genPS_none N (L := Lv K v) hr
      rw [h1, norm_zero] at this
      exact zero_ne_one this
    constructor
    · intro hpos
      have h0 : PowerSeries.coeff 0 (T r (genPS (Lv K v) N none) - PowerSeries.C (ιL K v w₀)) = 0 :=
        PowerSeries.coeff_of_lt_order 0 (by exact_mod_cast hpos)
      rw [map_sub, PowerSeries.coeff_zero_C, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
      exact sub_eq_zero.mp h0
    · intro heq
      have h1 : ((1 : ℕ) : ℕ∞) ≤ (T r (genPS (Lv K v) N none) - PowerSeries.C (ιL K v w₀)).order := by
        refine PowerSeries.nat_le_order _ 1 fun i hi => ?_
        have : i = 0 := by omega
        subst this
        rw [map_sub, PowerSeries.coeff_zero_C, PowerSeries.coeff_zero_eq_constantCoeff_apply, heq, sub_self]
      exact lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_one) h1
  have hρS : ρ ∈ S := by rw [hSρ]; exact Finset.mem_singleton_self _
  obtain ⟨hρ1, hρpos⟩ := (hS ρ).mp hρS
  refine ⟨ρ, hρ1, (hpos_iff ρ hρ1).mp hρpos, fun ρ' hρ' heq => ?_⟩
  have : ρ' ∈ S := (hS ρ').mpr ⟨hρ', (hpos_iff ρ' hρ').mpr heq⟩
  rw [hSρ] at this
  exact Finset.mem_singleton.mp this

end WRoot
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section Side

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial IsLocalRing ModularCurve.PlaceSpecialization IsDedekindDomain NumberField"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

theorem mem_maximalIdeal_of_valuation_lt {a : ℚbar} (ha : A.valuation a < 1) :
    ∃ h : a ∈ A, (⟨a, h⟩ : A) ∈ maximalIdeal A := by
  have hmem : a ∈ A := (A.valuation_le_one_iff a).mp ha.le
  refine ⟨hmem, ?_⟩
  rw [A.valuation_lt_one_iff]
  exact ha

theorem valuation_lt_one_iff_of_forall {K : IntermediateField ℚ ℚbar} [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (hvB : ∀ z : K, v.valuation K z ≤ 1 ↔ (z : ℚbar) ∈ A) (z : K) :
    v.valuation K z < 1 ↔ A.valuation (z : ℚbar) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : (z : ℚbar) ≠ 0 := by exact_mod_cast hz
  have h1 : v.valuation K z < 1 ↔ ¬ v.valuation K z⁻¹ ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hz)), not_le]
  have h2 : A.valuation (z : ℚbar) < 1 ↔ ¬ A.valuation ((z : ℚbar)⁻¹) ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hz')), not_le]
  rw [h1, h2, hvB, A.valuation_le_one_iff]
  push_cast
  exact Iff.rfl

theorem jFun_mem_of_isInftySide (P : PlaceSpecialization A q 1 data hKr k red hα hβ) {W : Place ℚbar FF}
    (hW : P.IsInftySide W) (hne : W ≠ cuspInftyBar (1 * q)) : (jFun (q := q) : FF) ∈ W.toValuationSubring := by
  by_contra h
  have hneg : W.ord (jFun (q := q)) < 0 := by
    by_contra h2
    push Not at h2
    exact h (W.mem_of_ord_nonneg jFun_ne_zero'' h2)
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg W hneg with h1 | h1
  · exact hne h1
  · exact ModularCurve.not_isInftySide_cuspZeroBar P (h1 ▸ hW)

theorem cuspInftyBar_not_mem : (jFun (q := q) : FF) ∉ (cuspInftyBar (1 * q)).toValuationSubring := by
  intro h
  have h1 := (cuspInftyBar (1 * q)).ord_nonneg_of_mem h
  rw [ModularCurve.ord_cuspInftyBar, order_coe_jFun] at h1
  omega

theorem one_lt_valuation_of_isInftySide (P : PlaceSpecialization A q 1 data hKr k red hα hβ) {W : Place ℚbar FF}
    (hW : P.IsInftySide W) {x₀ : ℚbar} (hx : W.HasValue (jFun (q := q)) x₀) : 1 < A.valuation x₀ := by
  rw [← not_le, A.valuation_le_one_iff]
  intro hmem
  have hval : W.HasValue (jFun (q := q) - algebraMap ℚbar FF ((⟨x₀, hmem⟩ : A) : ℚbar)) 0 := by
    have := HasValue.sub' hx (W.hasValue_algebraMap x₀)
    rwa [sub_self] at this
  have hne' : jFun (q := q) - algebraMap ℚbar FF x₀ ≠ 0 := sub_ne_zero.mpr (jF'_ne_algebraMap (1 * q) x₀)
  exact absurd (hW.1 ⟨x₀, hmem⟩) (not_le.mpr (ord_pos_of_hasValue_zero' hval hne'))

theorem coeff_zero_ofPowerSeries {R : Type*} [CommRing R] (G : R⟦X⟧) :
    (HahnSeries.ofPowerSeries ℤ R G).coeff 0 = PowerSeries.constantCoeff G := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff]

set_option maxHeartbeats 12800000 in

theorem isInftySide_thetaPlace (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {K : IntermediateField ℚ ℚbar} [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (hvB : ∀ z : K, v.valuation K z ≤ 1 ↔ (z : ℚbar) ∈ A)
    [Algebra ℚbar (Lv K v)] (halgK : ∀ c : K, algebraMap ℚbar (Lv K v) (c : ℚbar) = jKL K v c)
    {ρ : Lv K v} (hρ : ‖ρ‖ < 1) {V : Place ℚbar FF}
    (hVmem : ∀ f : FF, f ∈ V.toValuationSubring ↔ 0 ≤ (theta (1 * q) ρ hρ f).order)
    (hVval : ∀ (f : FF) (a : ℚbar), f ∈ V.toValuationSubring →
      (V.HasValue f a ↔ (theta (1 * q) ρ hρ f).coeff 0 = algebraMap ℚbar (Lv K v) a))
    (x₀ : K) (hx₀ : 1 < A.valuation (x₀ : ℚbar))
    (hroots : ∀ z ∈ (PsiAt' data (x₀ : ℚbar)).roots, z ∈ K)
    (hw : PowerSeries.constantCoeff (T ρ (genPS (Lv K v) (1 * q) none)) = jKL K v x₀⁻¹) :
    P.IsInftySide V ∧ V.HasValue (jFun (q := q)) (x₀ : ℚbar) := by
  classical
  set θ := theta (1 * q) ρ hρ with hθdef
  have hsurj : Function.Surjective (algebraMap ℚbar V.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField V).mp (deg_eq_one_modularFunctionFieldBar (1 * q) V)
  have hx₀0 : (x₀ : ℚbar) ≠ 0 := by
    intro h; rw [h, map_zero] at hx₀; exact not_lt_zero' hx₀
  have hx₀0' : x₀ ≠ 0 := fun h => hx₀0 (by rw [h]; rfl)
  have hx₀A : ∀ a : A, (a : ℚbar) ≠ (x₀ : ℚbar) := by
    intro a ha
    have : A.valuation (x₀ : ℚbar) ≤ 1 := by rw [← ha]; exact A.valuation_le_one a
    exact absurd hx₀ (not_lt.mpr this)
  set wF : FF := evFb (1 * q) (MvPolynomial.X none) with hwF
  have hθw : θ wF = HahnSeries.ofPowerSeries ℤ (Lv K v) (T ρ (genPS (Lv K v) (1 * q) none)) := theta_X_none (1 * q) ρ hρ
  have hwmem : wF ∈ V.toValuationSubring := by rw [hVmem, hθw]; exact order_ofPowerSeries_nonneg _
  have hwval : V.HasValue wF ((x₀⁻¹ : K) : ℚbar) := by
    rw [hVval _ _ hwmem, hθw, coeff_zero_ofPowerSeries, hw, halgK]
  have hjval : V.HasValue (jFun (q := q)) (x₀ : ℚbar) := by
    have h := hwval.inv (by push_cast; exact inv_ne_zero hx₀0)
    have h1 : wF⁻¹ = jFun (q := q) := by rw [hwF, evFb_X_none_eq_inv, inv_inv]; rfl
    rw [h1] at h
    push_cast at h
    rwa [inv_inv] at h
  have hcusp : P.IsCuspidal V := by
    intro a
    have hval : V.HasValue (jFun (q := q) - algebraMap ℚbar FF (a : ℚbar)) ((x₀ : ℚbar) - a) :=
      HasValue.sub' hjval (V.hasValue_algebraMap (a : ℚbar))
    rw [hval.ord_eq_zero (sub_ne_zero.mpr (hx₀A a).symm)]
  set tF : FF := tInfty (q := q) with htF
  have hθt : θ tF = HahnSeries.ofPowerSeries ℤ (Lv K v) (T ρ (genPS (Lv K v) (1 * q) (some (dTop q)))) := by
    rw [htF, tInfty_eq_evFb, hθdef, theta_evFb, phiL_apply, phi_X]
  have htmem : tF ∈ V.toValuationSubring := by rw [hVmem, hθt]; exact order_ofPowerSeries_nonneg _
  obtain ⟨τ', hτ', -⟩ := V.exists_hasValue_of_surjective hsurj htmem
  have hjbτ : algebraMap ℚbar (Lv K v) τ' = PowerSeries.constantCoeff (T ρ (genPS (Lv K v) (1 * q) (some (dTop q)))) := by
    have := (hVval _ _ htmem).mp hτ'
    rw [hθt, coeff_zero_ofPowerSeries] at this
    exact this.symm
  have hnorm : ‖algebraMap ℚbar (Lv K v) τ' - 1‖ < 1 := by
    rw [hjbτ]
    exact norm_constantCoeff_T_sub_one_lt (genPS_bdd (1 * q) _) (constantCoeff_genPS_some (dTop q)) hρ
  set y' : ℚbar := τ' * (x₀ : ℚbar) ^ (1 * q) with hy'
  have hyval : V.HasValue (jqFun (q := q)) y' := by
    rw [jqFun_eq_tInfty_mul']; exact hτ'.mul (HasValue.pow' hjval _)
  have hroot : (PsiAt' data (x₀ : ℚbar)).IsRoot y' := isRoot_psiAt'_of_hasValue hjval hyval
  have hy'K : y' ∈ K := hroots y' ((mem_roots (psiAt'_ne_zero _)).mpr hroot)
  set τK : K := ⟨y', hy'K⟩ * (x₀ ^ (1 * q))⁻¹ with hτK
  have hτKcoe : (τK : ℚbar) = τ' := by
    rw [hτK]; push_cast
    rw [hy', mul_inv_cancel_right₀ (pow_ne_zero _ hx₀0)]
  have hvlt : A.valuation (τ' - 1) < 1 := by
    have h1 : ‖jKL K v (τK - 1)‖ < 1 := by
      rw [map_sub, map_one, ← halgK, hτKcoe]; exact hnorm
    rw [jKL_apply, norm_algebraMap_Kv_Lv, Valued.toNormedField.norm_lt_one_iff, valued_algebraMap,
      valuation_lt_one_iff_of_forall v hvB] at h1
    push_cast at h1
    rwa [hτKcoe] at h1
  obtain ⟨hmemτ1, hmaxτ1⟩ := mem_maximalIdeal_of_valuation_lt hvlt
  have hτA : τ' ∈ A := by
    have : τ' = (τ' - 1) + 1 := by ring
    rw [this]; exact add_mem hmemτ1 A.one_mem
  haveI : Algebra.IsAlgebraic ℚ ℚbar := AlgebraicClosure.isAlgebraic ℚ
  have hred : red ⟨τ', hτA⟩ = 1 := by
    have : (⟨τ', hτA⟩ : A) = ⟨τ' - 1, hmemτ1⟩ + 1 := Subtype.ext (by push_cast; ring)
    rw [this, map_add, map_one, ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal A q red hmaxτ1, zero_add]
  exact ⟨⟨hcusp, ⟨τ', hτA⟩, hred, hτ'⟩, hjval⟩

end Side
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

namespace CuspDisc

section TubeCount

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq MvPolynomial IsLocalRing ModularCurve.PlaceSpecialization IsDedekindDomain NumberField"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

def evFbA (N : ℕ) [NeZero N] : MvPolynomial (GenIdx N) ℚbar →ₐ[ℚbar] ↥(modularFunctionFieldBar N) :=
  { evFb N with commutes' := evFb_C N }

omit [Fact q.Prime] in
@[scoped simp] theorem evFbA_apply (N : ℕ) [NeZero N] (p : MvPolynomial (GenIdx N) ℚbar) : evFbA N p = evFb N p := rfl

theorem exists_evFb_of_mem_adjoin {x : FF}
    (hx : x ∈ Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF)) :
    ∃ r : MvPolynomial (GenIdx (1 * q)) ℚbar, x = evFb (1 * q) r := by
  classical
  rw [Algebra.adjoin_eq_range] at hx
  obtain ⟨p, rfl⟩ := hx
  let g : (({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF)) → MvPolynomial (GenIdx (1 * q)) ℚbar :=
    fun z => if (z : FF) = (jFun (q := q))⁻¹ then MvPolynomial.X none else MvPolynomial.X (some (dTop q))
  have hg : ∀ z : (({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF)), evFbA (1 * q) (g z) = (z : FF) := by
    rintro ⟨z, hz⟩
    rcases hz with rfl | hz
    · simp only [g, if_pos rfl, evFbA_apply, evFb_X_none_eq_inv]; rfl
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      simp only [g, evFbA_apply]
      split_ifs with h
      · rw [evFb_X_none_eq_inv, ← jFun_eq_jF']; exact h.symm
      · exact tInfty_eq_evFb.symm
  refine ⟨MvPolynomial.aeval g p, ?_⟩
  rw [← evFbA_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval,
    show (fun i => evFbA (1 * q) (g i)) = Subtype.val from funext hg]
  rfl

set_option maxHeartbeats 25600000 in

theorem tube_count (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (x : FF) (hx0 : x ≠ 0)
    (hx : x ∈ Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF)) :
    ∃ (c : ℚbar) (y : LaurentSeries A) (S : Finset (Place ℚbar FF)),
      c ≠ 0 ∧ coeffMap A.subtype y = c • (x : LaurentSeries ℚbar) ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (∀ W, W ∈ S ↔ P.IsInftySide W ∧ W ≠ cuspInftyBar (1 * q) ∧ W.ord x ≠ 0) ∧
      ∑ W ∈ S, W.ord x = (coeffMap (IsLocalRing.residue A) y).order - y.order := by
  classical
  have hqlt : A.valuation ((q : ℕ) : ℚbar) < 1 := by
    have hmem : ((q : ℕ) : ℚbar) ∈ A := by
      have := ((q : ℕ) : A).2; push_cast at this; exact this
    have hmax : (⟨((q : ℕ) : ℚbar), hmem⟩ : A) ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 := hu.map red
      rw [show (⟨((q : ℕ) : ℚbar), hmem⟩ : A) = ((q : ℕ) : A) from by apply Subtype.ext; push_cast; rfl,
        map_natCast, CharP.cast_eq_zero] at h1
      exact not_isUnit_zero h1
    exact (A.valuation_lt_one_iff _).mp hmax
  obtain ⟨D, hD, -⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)).exists_divisor x hx0
  set Sx : Finset (Place ℚbar FF) := D.support with hSxdef
  have hSx : ∀ W, W ∈ Sx ↔ W.ord x ≠ 0 := fun W => by rw [hSxdef, Finsupp.mem_support_iff, hD]
  have hsurjW : ∀ W : Place ℚbar FF, Function.Surjective (algebraMap ℚbar W.ResidueField) := fun W =>
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField W).mp (deg_eq_one_modularFunctionFieldBar (1 * q) W)
  have hjv : ∀ W : Place ℚbar FF, ∃ a : ℚbar, (jFun (q := q) : FF) ∈ W.toValuationSubring →
      W.HasValue (jFun (q := q)) a := by
    intro W
    by_cases h : (jFun (q := q) : FF) ∈ W.toValuationSubring
    · obtain ⟨a, ha, -⟩ := W.exists_hasValue_of_surjective (hsurjW W) h
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose jval hjval using hjv
  set Jset : Finset ℚbar := Sx.image jval with hJset
  set RΨ : Finset ℚbar := Jset.biUnion fun a => (PsiAt' data a).roots.toFinset with hRΨ
  obtain ⟨r₀, hxr⟩ := exists_evFb_of_mem_adjoin hx
  set Tc : Finset ℚbar := (r₀.support.image fun m => r₀.coeff m) ∪ Jset ∪ RΨ with hTc
  set K : IntermediateField ℚ ℚbar := IntermediateField.adjoin ℚ (Tc : Set ℚbar) with hKdef
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin
    (fun z _ => by convert ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral <;> first | exact Subsingleton.elim _ _ | rfl)
  haveI : NumberField K := NumberField.mk
  have hTK : ∀ z ∈ Tc, z ∈ K := fun z hz => IntermediateField.subset_adjoin ℚ _ hz
  obtain ⟨rK, hrK⟩ := exists_restrict_coeffs K r₀ (fun m hm => hTK _ (by
    simp only [hTc, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨m, hm, rfl⟩)))
  have hJK : ∀ W ∈ Sx, jval W ∈ K := fun W hW => hTK _ (by
    simp only [hTc, Finset.mem_union]; exact Or.inl (Or.inr (Finset.mem_image_of_mem _ hW)))
  have hRK : ∀ W ∈ Sx, ∀ z ∈ (PsiAt' data (jval W)).roots, z ∈ K := fun W hW z hz => hTK _ (by
    simp only [hTc, Finset.mem_union, hRΨ, Finset.mem_biUnion]
    exact Or.inr ⟨jval W, Finset.mem_image_of_mem _ hW, Multiset.mem_toFinset.mpr hz⟩)
  set B : ValuationSubring K := A.comap (algebraMap K ℚbar) with hBdef
  have hBmem : ∀ z : K, z ∈ B ↔ (z : ℚbar) ∈ A := fun z => Iff.rfl
  have hBtop : B ≠ ⊤ := by
    intro hB
    have h1 : ((q : ℕ) : K)⁻¹ ∈ B := hB ▸ ValuationSubring.mem_top _
    rw [hBmem] at h1
    push_cast at h1
    have h2 := (A.valuation_le_one_iff _).mpr h1
    have hq0 : A.valuation ((q : ℕ) : ℚbar) ≠ 0 :=
      (_root_.map_ne_zero _).mpr (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hq0)] at h2
    exact absurd hqlt (not_lt.mpr h2)
  obtain ⟨v, hv⟩ := exists_heightOneSpectrum_eq_valuationSubring B hBtop
  have hvB : ∀ z : K, v.valuation K z ≤ 1 ↔ (z : ℚbar) ∈ A := fun z => by
    rw [← hBmem, ← hv]; exact Iff.rfl
  have hvB' : ∀ z : K, v.valuation K z < 1 ↔ A.valuation (z : ℚbar) < 1 := valuation_lt_one_iff_of_forall v hvB
  have hvB1 : ∀ z : K, v.valuation K z = 1 ↔ A.valuation (z : ℚbar) = 1 := fun z => by
    constructor
    · intro h
      refine le_antisymm ((A.valuation_le_one_iff _).mpr ((hvB z).mp h.le)) ?_
      by_contra hlt; push Not at hlt
      exact absurd ((hvB' z).mpr hlt) (by rw [h]; exact lt_irrefl _)
    · intro h
      refine le_antisymm ((hvB z).mpr ((A.valuation_le_one_iff _).mp h.le)) ?_
      by_contra hlt; push Not at hlt
      exact absurd ((hvB' z).mp hlt) (by rw [h]; exact lt_irrefl _)
  letI : Algebra K (Lv K v) := (jKL K v).toAlgebra
  haveI : Algebra.IsAlgebraic ℚ ℚbar := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic K ℚbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let jb : ℚbar →ₐ[K] Lv K v := IsAlgClosed.lift
  letI : Algebra ℚbar (Lv K v) := jb.toRingHom.toAlgebra
  have halgK : ∀ c : K, algebraMap ℚbar (Lv K v) (c : ℚbar) = jKL K v c := fun c => jb.commutes c
  have hcomp : (algebraMap ℚbar (Lv K v)).comp (algebraMap K ℚbar) = jKL K v := RingHom.ext fun c => halgK c
  set Pk : PowerSeries K := evPS (1 * q) K rK with hPk
  have hr₀ : evPS (1 * q) ℚbar r₀ = Pk.map (algebraMap K ℚbar) := by rw [hPk, evPS_map, hrK]
  have hxPS : (x : LaurentSeries ℚbar) = HahnSeries.ofPowerSeries ℤ ℚbar (Pk.map (algebraMap K ℚbar)) := by
    rw [hxr, coe_evFb, evQb_apply, hr₀]
  have hPk0 : Pk ≠ 0 := by
    intro h
    apply hx0
    apply Subtype.ext
    rw [hxPS, h, map_zero, map_zero]; rfl
  obtain ⟨b, hb⟩ := exists_log_valuation_le (1 * q) K v rK
  obtain ⟨cP, hcP0, hcP, n₀, hn₀⟩ := exists_primitive_scaling K v Pk hPk0 b hb
  set P₀ : PowerSeries K := PowerSeries.C cP * Pk with hP₀
  have hP₀coeff : ∀ n, PowerSeries.coeff n P₀ = cP * PowerSeries.coeff n Pk := fun n => by
    rw [hP₀, PowerSeries.coeff_C_mul]
  have hP₀int : ∀ n, v.valuation K (PowerSeries.coeff n P₀) ≤ 1 := fun n => by rw [hP₀coeff]; exact hcP n
  have hP₀A : ∀ n, ((PowerSeries.coeff n P₀ : K) : ℚbar) ∈ A := fun n => (hvB _).mp (hP₀int n)
  have hP₀0 : P₀ ≠ 0 := mul_ne_zero (by simpa using hcP0) hPk0
  set Y : PowerSeries A := PowerSeries.mk fun n => ⟨((PowerSeries.coeff n P₀ : K) : ℚbar), hP₀A n⟩ with hY
  have hYcoeff : ∀ n, ((PowerSeries.coeff n Y : A) : ℚbar) = ((PowerSeries.coeff n P₀ : K) : ℚbar) := fun n => by
    simp [hY]
  have hYmap : Y.map A.subtype = P₀.map (algebraMap K ℚbar) := by
    ext n; simp [hY]
  set y : LaurentSeries A := HahnSeries.ofPowerSeries ℤ A Y with hy
  have hycoe : coeffMap A.subtype y = cP • (x : LaurentSeries ℚbar) := by
    rw [hy, map_ofPowerSeries, hYmap, hP₀, map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C,
      hxPS, HahnSeries.C_mul_eq_smul]
    rfl
  have hunit_iff : ∀ n, IsUnit (PowerSeries.coeff n Y) ↔ v.valuation K (PowerSeries.coeff n P₀) = 1 := fun n => by
    rw [ValuationSubring.valuation_eq_one_iff, hvB1, hYcoeff]
  have hres_ne_iff : ∀ n, residue A (PowerSeries.coeff n Y) ≠ 0 ↔ v.valuation K (PowerSeries.coeff n P₀) = 1 := fun n => by
    rw [residue_ne_zero_iff_isUnit, hunit_iff]
  have hY0 : Y ≠ 0 := by
    intro h
    have := (hres_ne_iff n₀).mpr (by rw [hP₀coeff]; exact hn₀)
    rw [h, map_zero, map_zero] at this
    exact this rfl
  have hybar : coeffMap (IsLocalRing.residue A) y ≠ 0 := by
    intro h
    have h1 := congrArg (fun z => HahnSeries.coeff z (n₀ : ℤ)) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero, hy, HahnSeries.ofPowerSeries_apply_coeff] at h1
    exact (hres_ne_iff n₀).mpr (by rw [hP₀coeff]; exact hn₀) h1
  set m : ℕ := P₀.order.toNat with hm
  obtain ⟨G₀, hG₀⟩ : (PowerSeries.X : PowerSeries K) ^ m ∣ P₀ := by rw [hm]; exact PowerSeries.X_pow_order_dvd
  have hG₀coeff : ∀ n, PowerSeries.coeff n G₀ = PowerSeries.coeff (n + m) P₀ := fun n => by
    rw [hG₀, PowerSeries.coeff_X_pow_mul]
  have hG₀int : ∀ n, v.valuation K (PowerSeries.coeff n G₀) ≤ 1 := fun n => by rw [hG₀coeff]; exact hP₀int _
  have hG₀c : PowerSeries.constantCoeff G₀ ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hG₀coeff, zero_add]
    exact PowerSeries.coeff_order hP₀0
  have hG₀0 : G₀ ≠ 0 := fun h => hG₀c (by rw [h, map_zero])
  set F₀ : PowerSeries (Ov K v) := liftOv K v G₀ hG₀int with hF₀
  have hF₀unit : ∀ n, IsUnit (PowerSeries.coeff n F₀) ↔ v.valuation K (PowerSeries.coeff n G₀) = 1 := fun n => by
    rw [isUnit_Ov_iff_norm_eq_one, hF₀, coeff_liftOv]
    constructor
    · intro h
      apply le_antisymm
      · rw [← valued_algebraMap, ← Valued.toNormedField.norm_le_one_iff]; exact h.le
      · rw [← valued_algebraMap, ← Valued.toNormedField.one_le_norm_iff]; exact h.ge
    · intro h
      apply le_antisymm
      · rw [Valued.toNormedField.norm_le_one_iff, valued_algebraMap]; exact h.le
      · rw [Valued.toNormedField.one_le_norm_iff, valued_algebraMap]; exact h.ge
  have hn₀m : m ≤ n₀ := by
    have h1 : PowerSeries.coeff n₀ P₀ ≠ 0 := by
      intro h0; rw [hP₀coeff] at h0; rw [h0, map_zero] at hn₀; exact zero_ne_one hn₀
    have := PowerSeries.order_le n₀ h1
    rw [hm]
    exact ENat.toNat_le_of_le_coe this
  have hF₀res : F₀.map (residue (Ov K v)) ≠ 0 := by
    intro h
    have h1 : residue _ (PowerSeries.coeff (n₀ - m) F₀) = 0 := by rw [← PowerSeries.coeff_map, h, map_zero]
    rw [residue_eq_zero_iff] at h1
    apply h1
    rw [hF₀unit, hG₀coeff, Nat.sub_add_cancel hn₀m, hP₀coeff]
    exact hn₀
  set F₀L : (Lv K v)⟦X⟧ := F₀.map (ιL K v) with hF₀L
  have hF₀LG : F₀L = G₀.map (algebraMap K (Lv K v)) := by rw [hF₀L, hF₀, liftOv_map_ιL]; rfl
  have hF₀Lbdd : Bdd 1 F₀L := bdd_map' (ιL K v) (norm_ιL_le_one K v) F₀
  have hF₀Lc : PowerSeries.constantCoeff F₀L ≠ 0 := by
    rw [hF₀LG, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (_root_.map_ne_zero _).mpr hG₀c
  have hF₀L0 : F₀L ≠ 0 := fun h => hF₀Lc (by rw [h, map_zero])
  obtain ⟨SL, hSL, hsumL⟩ := PowerSeries.exists_finset_sum_order_taylorShift_eq_order_map_residue (ιL K v)
    (ιL_injective K v) (norm_ιL_le_one K v) (fun z hz => norm_ιL_lt_one K v hz) F₀ hF₀res
  change (∀ ρ, ρ ∈ SL ↔ ‖ρ‖ < 1 ∧ 0 < (T ρ F₀L).order) at hSL
  change ∑ ρ ∈ SL, (T ρ F₀L).order = _ at hsumL
  have hTF₀0 : ∀ ρ : Lv K v, ‖ρ‖ < 1 → T ρ F₀L ≠ 0 := fun ρ hρ =>
    fun h => hF₀L0 ((T_eq_zero_iff (norm_nonneg ρ) hρ zero_le_one le_rfl hF₀Lbdd).mp h)
  have hSL0 : ∀ ρ ∈ SL, ρ ≠ 0 := by
    intro ρ hρS h0
    subst h0
    obtain ⟨-, hpos⟩ := (hSL 0).mp hρS
    rw [T_zero_left] at hpos
    have : F₀L.order = 0 := by
      rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
      exact ⟨by rwa [PowerSeries.coeff_zero_eq_constantCoeff], fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    rw [this] at hpos
    exact lt_irrefl _ hpos
  set wL := genPS (Lv K v) (1 * q) none with hwL
  have hθx : ∀ (ρ : Lv K v) (hρ : ‖ρ‖ < 1), ρ ≠ 0 →
      theta (1 * q) ρ hρ x ≠ 0 ∧ (theta (1 * q) ρ hρ x).order = ((T ρ F₀L).order.toNat : ℤ) := by
    intro ρ hρ hρ0
    have hPL : MvPolynomial.aeval (genPS (Lv K v) (1 * q)) r₀ = Pk.map (algebraMap K (Lv K v)) := by
      rw [aeval_genPS_eq (1 * q) (K := ℚbar) (L := Lv K v) r₀, hr₀]
      ext n
      simp only [PowerSeries.coeff_map]
      exact halgK _
    have hθ : theta (1 * q) ρ hρ x = HahnSeries.ofPowerSeries ℤ (Lv K v) (T ρ (Pk.map (algebraMap K (Lv K v)))) := by
      rw [hxr, theta_evFb, phiL_apply, phi_apply, hPL]
    obtain ⟨C, hC, hBk⟩ := evL_bdd (K := K) (genPS (Lv K v) (1 * q)) (genPS_bdd (1 * q)) rK
    rw [aeval_genPS_eq] at hBk
    have hP₀L : P₀.map (algebraMap K (Lv K v)) = PowerSeries.C (jKL K v cP) * Pk.map (algebraMap K (Lv K v)) := by
      rw [hP₀, map_mul, PowerSeries.map_C]; rfl
    have hP₀L' : P₀.map (algebraMap K (Lv K v)) = PowerSeries.X ^ m * F₀L := by
      rw [hG₀, map_mul, map_pow, PowerSeries.map_X, hF₀LG]
    have hρ0' := norm_nonneg ρ
    have hT1 : T ρ (P₀.map (algebraMap K (Lv K v))) = PowerSeries.C (jKL K v cP) * T ρ (Pk.map (algebraMap K (Lv K v))) := by
      rw [hP₀L, T_mul hρ0' hρ (norm_nonneg _) hC le_rfl (bdd_C _) hBk, T_C]
    have hT2 : T ρ (P₀.map (algebraMap K (Lv K v))) = T ρ (PowerSeries.X ^ m) * T ρ F₀L := by
      rw [hP₀L', T_mul hρ0' hρ zero_le_one zero_le_one le_rfl (bdd_X_pow m) hF₀Lbdd]
    have hcP' : jKL K v cP ≠ 0 := (_root_.map_ne_zero _).mpr hcP0
    have horder : (T ρ (Pk.map (algebraMap K (Lv K v)))).order = (T ρ F₀L).order := by
      rw [← order_C_mul'' hcP', ← hT1, hT2, PowerSeries.order_mul, T_X_pow_ne_zero_and_order hρ hρ0, zero_add]
    have hne : T ρ (Pk.map (algebraMap K (Lv K v))) ≠ 0 := by
      intro h0
      rw [h0, PowerSeries.order_zero] at horder
      exact (PowerSeries.order_finite_iff_ne_zero.mpr (hTF₀0 ρ hρ)).ne horder.symm
    refine ⟨by rw [hθ]; exact (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hne, ?_⟩
    rw [hθ, order_ofPowerSeries_eq hne, horder]
  have hwnorm : ∀ ρ : Lv K v, ‖ρ‖ < 1 → ‖PowerSeries.constantCoeff (T ρ wL)‖ = ‖ρ‖ := fun ρ hρ =>
    norm_constantCoeff_T_genPS_none (1 * q) hρ
  have hθj_order : ∀ (ρ : Lv K v) (hρ : ‖ρ‖ < 1), ρ ≠ 0 → (theta (1 * q) ρ hρ (jFun (q := q))).order = 0 := by
    intro ρ hρ hρ0
    have h1 : theta (1 * q) ρ hρ (evFb (1 * q) (MvPolynomial.X none)) = HahnSeries.ofPowerSeries ℤ (Lv K v) (T ρ wL) :=
      theta_X_none (1 * q) ρ hρ
    have hc0 : PowerSeries.constantCoeff (T ρ wL) ≠ 0 := by
      intro h0; have := hwnorm ρ hρ; rw [h0, norm_zero] at this; exact hρ0 (norm_eq_zero.mp this.symm)
    have hT0 : T ρ wL ≠ 0 := fun h => hc0 (by rw [h, map_zero])
    have hord0 : (HahnSeries.ofPowerSeries ℤ (Lv K v) (T ρ wL)).order = 0 := by
      rw [order_ofPowerSeries_eq hT0]
      have : (T ρ wL).order = 0 := by
        rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
        exact ⟨by rwa [PowerSeries.coeff_zero_eq_constantCoeff], fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      rw [this]; rfl
    have hj : (jFun (q := q) : FF) = (evFb (1 * q) (MvPolynomial.X none))⁻¹ := by
      rw [evFb_X_none_eq_inv, inv_inv]; rfl
    rw [hj, map_inv₀, h1, order_inv' ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hT0), hord0, neg_zero]
  set Wset : Finset (Place ℚbar FF) := Sx.filter fun W => P.IsInftySide W ∧ W ≠ cuspInftyBar (1 * q) with hWdef
  have hWset : ∀ W, W ∈ Wset ↔ P.IsInftySide W ∧ W ≠ cuspInftyBar (1 * q) ∧ W.ord x ≠ 0 := fun W => by
    rw [hWdef, Finset.mem_filter, hSx]; tauto
  have hWfacts : ∀ W ∈ Wset, W ∈ Sx ∧ P.IsInftySide W ∧ W.HasValue (jFun (q := q)) (jval W) ∧
      1 < A.valuation (jval W) := by
    intro W hW
    rw [hWdef, Finset.mem_filter] at hW
    obtain ⟨hWS, hside, hne⟩ := hW
    have hjmem := jFun_mem_of_isInftySide P hside hne
    have hval := hjval W hjmem
    exact ⟨hWS, hside, hval, one_lt_valuation_of_isInftySide P hside hval⟩
  have hroot : ∀ x₀ : K, 1 < A.valuation (x₀ : ℚbar) → ∃ ρ : Lv K v, ‖ρ‖ < 1 ∧ ρ ≠ 0 ∧
      PowerSeries.constantCoeff (T ρ wL) = jKL K v x₀⁻¹ ∧
      ∀ ρ' : Lv K v, ‖ρ'‖ < 1 → PowerSeries.constantCoeff (T ρ' wL) = jKL K v x₀⁻¹ → ρ' = ρ := by
    intro x₀ hx₀
    have hx₀0 : (x₀ : ℚbar) ≠ 0 := by intro h; rw [h, map_zero] at hx₀; exact not_lt_zero' hx₀
    have hx₀0' : x₀ ≠ 0 := fun h => hx₀0 (by rw [h]; rfl)
    have hvlt : v.valuation K x₀⁻¹ < 1 := by
      rw [hvB']; push_cast
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hx₀0))]
      exact hx₀
    have hmem : algebraMap K (Kv K v) x₀⁻¹ ∈ Ov K v := (algebraMap_mem_Ov_iff K v _).mpr hvlt.le
    set w₀ : Ov K v := ⟨algebraMap K (Kv K v) x₀⁻¹, hmem⟩ with hw₀
    have hw₀norm : ‖(w₀ : Kv K v)‖ < 1 := by
      rw [hw₀]; change ‖algebraMap K (Kv K v) x₀⁻¹‖ < 1
      rw [Valued.toNormedField.norm_lt_one_iff, valued_algebraMap]; exact hvlt
    obtain ⟨ρ, hρ1, hρc, huniq⟩ := exists_wroot (1 * q) K v w₀ hw₀norm
    have hιw₀ : ιL K v w₀ = jKL K v x₀⁻¹ := rfl
    rw [hιw₀] at hρc huniq
    refine ⟨ρ, hρ1, ?_, hρc, huniq⟩
    intro h0
    have h1 := hwnorm ρ hρ1
    rw [hρc, h0, norm_zero, jKL_apply, norm_algebraMap_Kv_Lv] at h1
    have : algebraMap K (Kv K v) x₀⁻¹ = 0 := norm_eq_zero.mp h1
    exact (inv_ne_zero hx₀0') ((_root_.map_eq_zero _).mp this)
  have hplace : ∀ (x₀ : K) (ρ : Lv K v) (hρ : ‖ρ‖ < 1), ρ ≠ 0 →
      PowerSeries.constantCoeff (T ρ wL) = jKL K v x₀⁻¹ →
      ∃ V : Place ℚbar FF,
        (∀ f, f ∈ V.toValuationSubring ↔ 0 ≤ (theta (1 * q) ρ hρ f).order) ∧
        (∀ f, V.ord f = (theta (1 * q) ρ hρ f).order) ∧
        (∀ f (a : ℚbar), f ∈ V.toValuationSubring →
          (V.HasValue f a ↔ (theta (1 * q) ρ hρ f).coeff 0 = algebraMap ℚbar (Lv K v) a)) := by
    intro x₀ ρ hρ hρ0 hc
    apply exists_thetaPlace (1 * q) ρ hρ
    set π : FF := evFb (1 * q) (MvPolynomial.X none) - algebraMap ℚbar FF ((x₀⁻¹ : K) : ℚbar) with hπ
    have hθπ : theta (1 * q) ρ hρ π = HahnSeries.ofPowerSeries ℤ (Lv K v) (T ρ wL - PowerSeries.C (jKL K v x₀⁻¹)) := by
      rw [hπ, map_sub, theta_X_none, theta_algebraMap, halgK, map_sub, HahnSeries.ofPowerSeries_C]
    have hne : T ρ wL - PowerSeries.C (jKL K v x₀⁻¹) ≠ 0 := by
      intro h0
      have h1 := congrArg (PowerSeries.coeff 1) h0
      rw [map_sub, PowerSeries.coeff_C, if_neg one_ne_zero, sub_zero, map_zero] at h1
      have := norm_coeff_one_T_genPS_none (1 * q) (L := Lv K v) hρ
      rw [h1, norm_zero] at this
      exact zero_ne_one this
    have hord : (T ρ wL - PowerSeries.C (jKL K v x₀⁻¹)).order = 1 := by
      rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
      refine ⟨?_, fun i hi => ?_⟩
      · rw [map_sub, PowerSeries.coeff_C, if_neg one_ne_zero, sub_zero]
        intro h1
        have := norm_coeff_one_T_genPS_none (1 * q) (L := Lv K v) hρ
        rw [h1, norm_zero] at this
        exact zero_ne_one this
      · have : i = 0 := by omega
        subst this
        rw [map_sub, PowerSeries.coeff_zero_C, PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, sub_self]
    refine thetaRing_ne_top _ (f := π) ?_ ?_
    · rw [hθπ]; exact (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hne
    · rw [hθπ, order_ofPowerSeries_eq hne, hord]; norm_num
  have hWroot : ∀ (W) (hW : W ∈ Wset), ∃ ρ : Lv K v, ∃ hρ : ‖ρ‖ < 1, ρ ≠ 0 ∧
      PowerSeries.constantCoeff (T ρ wL) = jKL K v (⟨jval W, hJK W (hWfacts W hW).1⟩ : K)⁻¹ ∧
      W.ord x = ((T ρ F₀L).order.toNat : ℤ) ∧ ρ ∈ SL := by
    intro W hW
    obtain ⟨hWS, hside, hval, hbig⟩ := hWfacts W hW
    set x₀ : K := ⟨jval W, hJK W hWS⟩ with hx₀
    have hbig' : 1 < A.valuation (x₀ : ℚbar) := hbig
    obtain ⟨ρ, hρ1, hρ0, hρc, -⟩ := hroot x₀ hbig'
    obtain ⟨V, hVmem, hVord, hVval⟩ := hplace x₀ ρ hρ1 hρ0 hρc
    obtain ⟨hVside, hVj⟩ := isInftySide_thetaPlace P v hvB halgK hρ1 hVmem hVval x₀ hbig'
      (fun z hz => hRK W hWS z hz) hρc
    have hWV : W = V := ModularCurve.PlaceSpecialization.eq_of_isInftySide_of_hasValue_jFun P hside hVside hval hVj
    have hordx : W.ord x = ((T ρ F₀L).order.toNat : ℤ) := by rw [hWV, hVord, (hθx ρ hρ1 hρ0).2]
    refine ⟨ρ, hρ1, hρ0, hρc, hordx, ?_⟩
    rw [hSL]
    refine ⟨hρ1, ?_⟩
    have hne : W.ord x ≠ 0 := (hSx W).mp hWS
    rw [hordx] at hne
    have hfin := (PowerSeries.order_finite_iff_ne_zero.mpr (hTF₀0 ρ hρ1))
    by_contra h
    push Not at h
    have : (T ρ F₀L).order = 0 := le_antisymm h bot_le
    rw [this] at hne
    exact hne rfl
  have hZplace : ∀ ρ ∈ SL, ∃ hρ : ‖ρ‖ < 1, ∃ V, ∃ hV : V ∈ Wset,
      PowerSeries.constantCoeff (T ρ wL) = jKL K v (⟨jval V, hJK V ((hWfacts V hV).1)⟩ : K)⁻¹ ∧
      V.ord x = ((T ρ F₀L).order.toNat : ℤ) := by
    intro ρ hρS
    obtain ⟨hρ1, hpos⟩ := (hSL ρ).mp hρS
    have hρ0 := hSL0 ρ hρS
    obtain ⟨hθ0, hθord⟩ := hθx ρ hρ1 hρ0
    have hposZ : 0 < (theta (1 * q) ρ hρ1 x).order := by
      rw [hθord]
      have hfin := (PowerSeries.order_finite_iff_ne_zero.mpr (hTF₀0 ρ hρ1)).ne
      have : (T ρ F₀L).order.toNat ≠ 0 := by
        intro h0
        rw [ENat.toNat_eq_zero] at h0
        rcases h0 with h0 | h0
        · rw [h0] at hpos; exact lt_irrefl _ hpos
        · exact hfin h0
      exact_mod_cast Nat.pos_of_ne_zero this
    obtain ⟨V, hVmem, hVord, hVval⟩ := exists_thetaPlace (1 * q) ρ hρ1 (thetaRing_ne_top _ hθ0 hposZ)
    have hVS : V ∈ Sx := by rw [hSx, hVord]; exact hposZ.ne'
    have hjmem : (jFun (q := q) : FF) ∈ V.toValuationSubring := by rw [hVmem, hθj_order ρ hρ1 hρ0]
    have hval := hjval V hjmem
    set x₀' : K := ⟨jval V, hJK V hVS⟩ with hx₀'
    have hx₀'0 : (x₀' : ℚbar) ≠ 0 := by
      intro h0
      have h1 : V.HasValue (jFun (q := q)) 0 := by rw [← h0]; exact hval
      have := ord_pos_of_hasValue_zero' h1 jFun_ne_zero''
      rw [hVord, hθj_order ρ hρ1 hρ0] at this
      exact lt_irrefl _ this
    have hwmem : evFb (1 * q) (MvPolynomial.X none) ∈ V.toValuationSubring := by
      rw [hVmem, theta_X_none]; exact order_ofPowerSeries_nonneg _
    have hwval : V.HasValue (evFb (1 * q) (MvPolynomial.X none)) ((x₀' : ℚbar)⁻¹) := by
      have h := hval.inv hx₀'0
      rwa [jFun_eq_jF', ← evFb_X_none_eq_inv] at h
    have hc : PowerSeries.constantCoeff (T ρ wL) = jKL K v x₀'⁻¹ := by
      have := (hVval _ _ hwmem).mp hwval
      rw [theta_X_none, coeff_zero_ofPowerSeries] at this
      rw [this, ← halgK]; push_cast; rfl
    have hbig : 1 < A.valuation (x₀' : ℚbar) := by
      have h1 : ‖jKL K v x₀'⁻¹‖ < 1 := by rw [← hc, hwnorm ρ hρ1]; exact hρ1
      rw [jKL_apply, norm_algebraMap_Kv_Lv, Valued.toNormedField.norm_lt_one_iff, valued_algebraMap, hvB'] at h1
      push_cast at h1
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hx₀'0))] at h1
      exact h1
    obtain ⟨hVside, -⟩ := isInftySide_thetaPlace P v hvB halgK hρ1 hVmem hVval x₀' hbig
      (fun z hz => hRK V hVS z hz) hc
    have hVne : V ≠ cuspInftyBar (1 * q) := fun h => cuspInftyBar_not_mem (q := q) (h ▸ hjmem)
    have hVW : V ∈ Wset := (hWset V).mpr ⟨hVside, hVne, (hSx V).mp hVS⟩
    refine ⟨hρ1, V, hVW, hc, ?_⟩
    rw [hVord, hθord]
  choose ρW hρW1 hρWspec using hWroot
  have hsumZ : ∑ W ∈ Wset, W.ord x = ∑ ρ ∈ SL, ((T ρ F₀L).order.toNat : ℤ) := by
    refine Finset.sum_bij ρW (fun W hW => (hρWspec W hW).2.2.2) ?_ ?_ (fun W hW => (hρWspec W hW).2.2.1)
    ·
      intro W₁ hW₁ W₂ hW₂ heq
      obtain ⟨hρ0₁, hc₁, hord₁, -⟩ := hρWspec W₁ hW₁
      obtain ⟨hρ0₂, hc₂, hord₂, -⟩ := hρWspec W₂ hW₂
      obtain ⟨hWS₁, hside₁, hval₁, hbig₁⟩ := hWfacts W₁ hW₁
      obtain ⟨hWS₂, hside₂, hval₂, hbig₂⟩ := hWfacts W₂ hW₂
      have hx : (⟨jval W₁, hJK W₁ hWS₁⟩ : K)⁻¹ = (⟨jval W₂, hJK W₂ hWS₂⟩ : K)⁻¹ := by
        apply (jKL K v).injective
        rw [← hc₁, ← hc₂, heq]
      have hx' : jval W₁ = jval W₂ := by
        have := congrArg (fun z : K => ((z⁻¹ : K) : ℚbar)) hx
        simpa using this
      rw [hx'] at hval₁
      exact ModularCurve.PlaceSpecialization.eq_of_isInftySide_of_hasValue_jFun P hside₁ hside₂ hval₁ hval₂
    ·
      intro ρ hρS
      obtain ⟨hρ1, V, hVW, hc, hord⟩ := hZplace ρ hρS
      refine ⟨V, hVW, ?_⟩
      obtain ⟨hρ0', hc', -, -⟩ := hρWspec V hVW
      obtain ⟨-, -, -, hbigV⟩ := hWfacts V hVW
      obtain ⟨ρ₀, -, -, -, huniq⟩ := hroot (⟨jval V, hJK V (hWfacts V hVW).1⟩ : K) hbigV
      rw [huniq ρ hρ1 hc, huniq (ρW V hVW) (hρW1 V hVW) hc']
  have hfinT : ∀ ρ ∈ SL, (T ρ F₀L).order ≠ ⊤ := fun ρ hρ =>
    (PowerSeries.order_finite_iff_ne_zero.mpr (hTF₀0 ρ ((hSL ρ).mp hρ).1)).ne
  set d : ℕ := (F₀.map (residue (Ov K v))).order.toNat with hd
  have hdfin : (F₀.map (residue (Ov K v))).order ≠ ⊤ := (PowerSeries.order_finite_iff_ne_zero.mpr hF₀res).ne
  have hsumN : ∑ ρ ∈ SL, (T ρ F₀L).order.toNat = d := by
    have h1 : ∑ ρ ∈ SL, ((T ρ F₀L).order.toNat : ℕ∞) = ∑ ρ ∈ SL, (T ρ F₀L).order :=
      Finset.sum_congr rfl fun ρ hρ => ENat.coe_toNat (hfinT ρ hρ)
    rw [← Nat.cast_sum, hsumL] at h1
    rw [hd, ← h1, ENat.toNat_coe]
  have hyord : y.order = (m : ℤ) := by
    rw [hy, order_ofPowerSeries_eq hY0]
    congr 1
    rw [hm, ← order_map_eq_of_injective A.subtype Subtype.val_injective, hYmap,
      order_map_eq_of_injective _ (algebraMap K ℚbar).injective]
  have hYbar0 : Y.map (residue A) ≠ 0 := by
    intro h
    apply hybar
    rw [hy, map_ofPowerSeries, h, map_zero]
  have hval_coeff : ∀ n, v.valuation K (PowerSeries.coeff (n + m) P₀) = 1 ↔ PowerSeries.coeff n (F₀.map (residue (Ov K v))) ≠ 0 := by
    intro n
    rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit, hF₀unit, hG₀coeff]
  have hYbar_order : (Y.map (residue A)).order = ((m + d : ℕ) : ℕ∞) := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, add_comm]
      apply (hres_ne_iff _).mpr
      rw [hval_coeff]
      exact PowerSeries.coeff_order hF₀res
    · rw [PowerSeries.coeff_map]
      by_contra hne0
      have hne := (hres_ne_iff i).mp hne0
      rcases lt_or_ge i m with him | him
      · have h0 : PowerSeries.coeff i P₀ = 0 := PowerSeries.coeff_of_lt_order_toNat i (by rw [← hm]; exact him)
        rw [h0, map_zero] at hne
        exact zero_ne_one hne
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le him
        rw [add_comm] at hne
        have h1 := (hval_coeff j).mp hne
        exact h1 (PowerSeries.coeff_of_lt_order_toNat j (by rw [← hd]; exact Nat.lt_of_add_lt_add_left hi))
  have hybar_ord : (coeffMap (IsLocalRing.residue A) y).order = ((m + d : ℕ) : ℤ) := by
    rw [hy, map_ofPowerSeries, order_ofPowerSeries_eq hYbar0, hYbar_order, ENat.toNat_coe]
  refine ⟨(cP : ℚbar), y, Wset, by exact_mod_cast hcP0, ?_, hybar, hWset, ?_⟩
  · rw [hycoe]; rfl
  · rw [hsumZ, hybar_ord, hyord, ← Nat.cast_sum, hsumN]
    push_cast
    ring

end TubeCount
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order.CuspDisc"

p2m_open "ModularCurve~coeffEmb_jq" in open AlgebraicCurve IsLocalRing  in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (x : ↥(modularFunctionFieldBar (1 * q))) (hx0 : x ≠ 0)
    (hx : x ∈ Algebra.adjoin (AlgebraicClosure ℚ)
      ({(PlaceSpecialization.jFun (q := q))⁻¹, PlaceSpecialization.tInfty (q := q)} :
        Set ↥(modularFunctionFieldBar (1 * q)))) :
    ∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A)
      (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))),
      c ≠ 0 ∧ coeffMap A.subtype y = c • (x : LaurentSeries (AlgebraicClosure ℚ)) ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (∀ W, W ∈ S ↔ P.IsInftySide W ∧ W ≠ cuspInftyBar (1 * q) ∧ W.ord x ≠ 0) ∧
      ∑ W ∈ S, W.ord x = (coeffMap (IsLocalRing.residue A) y).order - y.order :=
  CuspDisc.tube_count P x hx0 hx

end
end S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order (solution)
