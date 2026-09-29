-- Prove2me | solution 1 for ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4aaecf42-5810-5ee5-b20c-e0aca8bdc94d

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_PowerSeries_dvd_of_forall_taylorShift_order_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
open ModularCurve HahnSeries PowerSeries
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
noncomputable section
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
noncomputable section
open PowerSeries
namespace CuspDisc
section Frac
variable {R F L : Type*} [CommRing R] [Field F] [Field L]
variable (ev : R →+* F) (φ : R →+* L⟦X⟧) (hker : ∀ a, ev a = 0 ↔ φ a = 0)
def FracMem (x : F) : Prop :=
  ∃ a b : R, ev b ≠ 0 ∧ x = ev a / ev b ∧ (φ b).order ≤ (φ a).order
include hker
omit hker in
theorem fracMem_of (a b : R) (hb : ev b ≠ 0) (h : (φ b).order ≤ (φ a).order) :
    FracMem ev φ (ev a / ev b) := ⟨a, b, hb, rfl, h⟩
theorem phi_ne_zero_of_ev_ne_zero {b : R} (hb : ev b ≠ 0) : φ b ≠ 0 := fun h => hb ((hker b).mpr h)
theorem order_lt_top_of_ev_ne_zero {b : R} (hb : ev b ≠ 0) : (φ b).order < ⊤ := by
  rw [lt_top_iff_ne_top, Ne, PowerSeries.order_eq_top]; exact phi_ne_zero_of_ev_ne_zero ev φ hker hb
def fracSubring : Subring F where
  carrier := {x | FracMem ev φ x}
  zero_mem' := ⟨0, 1, by simp, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp, le_rfl⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, rfl, hab⟩ ⟨c, d, hd, rfl, hcd⟩
    refine ⟨a * d + c * b, b * d, by simp [hb, hd], ?_, ?_⟩
    · rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hb hd]; ring
    · rw [map_mul, map_add, map_mul, map_mul, PowerSeries.order_mul]
      refine le_trans ?_ (PowerSeries.min_order_le_order_add _ _)
      rw [PowerSeries.order_mul, PowerSeries.order_mul, le_min_iff]
      constructor
      · exact add_le_add hab le_rfl |>.trans_eq (by ring)
      · calc (φ b).order + (φ d).order ≤ (φ b).order + (φ c).order := add_le_add le_rfl hcd
          _ = (φ c).order + (φ b).order := add_comm _ _
  neg_mem' := by
    rintro x ⟨a, b, hb, rfl, hab⟩
    exact ⟨-a, b, hb, by rw [map_neg, neg_div], by rwa [map_neg, PowerSeries.order_neg]⟩
  mul_mem' := by
    rintro x y ⟨a, b, hb, rfl, hab⟩ ⟨c, d, hd, rfl, hcd⟩
    refine ⟨a * c, b * d, by simp [hb, hd], ?_, ?_⟩
    · rw [map_mul, map_mul, div_mul_div_comm]
    · rw [map_mul, map_mul, PowerSeries.order_mul, PowerSeries.order_mul]
      exact add_le_add hab hcd
omit hker in
theorem mem_fracSubring_iff {x : F} : x ∈ fracSubring ev φ ↔ FracMem ev φ x := Iff.rfl
omit hker in
theorem ev_mem_fracSubring (a : R) : ev a ∈ fracSubring ev φ :=
  ⟨a, 1, by simp, by simp, by
    rw [map_one, PowerSeries.order_one]; exact bot_le⟩
theorem isUnit_of_order_eq {a b : R} (hb : ev b ≠ 0) (h : (φ a).order = (φ b).order) :
    IsUnit (⟨ev a / ev b, fracMem_of ev φ a b hb h.ge⟩ : fracSubring ev φ) := by
  have ha : ev a ≠ 0 := by
    intro ha0
    have : (φ a).order = ⊤ := by rw [PowerSeries.order_eq_top]; exact (hker a).mp ha0
    rw [this] at h
    exact (order_lt_top_of_ev_ne_zero ev φ hker hb).ne h.symm
  refine ⟨⟨⟨ev a / ev b, fracMem_of ev φ a b hb h.ge⟩, ⟨ev b / ev a, fracMem_of ev φ b a ha h.le⟩, ?_, ?_⟩, rfl⟩
  · ext; simp [div_mul_div_comm, mul_comm, div_self (mul_ne_zero ha hb)]
  · ext; simp [div_mul_div_comm, mul_comm, div_self (mul_ne_zero ha hb)]
theorem isLocalRing_fracSubring : IsLocalRing (fracSubring ev φ) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨a, b, hb, hx, hab⟩ := x.2
  rcases hab.lt_or_eq with hlt | heq
  ·
    right
    have hba : (φ (b - a)).order = (φ b).order := by
      rw [map_sub, sub_eq_add_neg, PowerSeries.order_add_of_order_ne] <;> rw [PowerSeries.order_neg]
      · exact (min_eq_left hlt.le)
      · exact hlt.ne
    have h1x : (1 - x : fracSubring ev φ) = ⟨ev (b - a) / ev b, fracMem_of ev φ _ _ hb hba.ge⟩ := by
      apply Subtype.ext
      show ((1 - x : fracSubring ev φ) : F) = ev (b - a) / ev b
      rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, hx, map_sub, sub_div, div_self hb]
    rw [h1x]
    exact isUnit_of_order_eq ev φ hker hb hba
  · left
    have hxe : x = ⟨ev a / ev b, fracMem_of ev φ a b hb hab⟩ := Subtype.ext hx
    rw [hxe]
    exact isUnit_of_order_eq ev φ hker hb heq.symm
def fracLocalSubring : LocalSubring F :=
  LocalSubring.mk (fracSubring ev φ) (isLocalRing := isLocalRing_fracSubring ev φ hker)
theorem not_mem_of_order_lt {a b : R} (hb : ev b ≠ 0) (hlt : (φ a).order < (φ b).order) :
    ev a / ev b ∉ fracSubring ev φ := by
  rintro ⟨c, d, hd, heq, hcd⟩
  have hcross : ev (a * d - c * b) = 0 := by
    rw [map_sub, map_mul, map_mul, sub_eq_zero]
    field_simp at heq
    linear_combination heq
  have h0 : φ (a * d) = φ (c * b) := by
    have := (hker _).mp hcross
    rwa [map_sub, sub_eq_zero] at this
  have hord : (φ a).order + (φ d).order = (φ c).order + (φ b).order := by
    rw [← PowerSeries.order_mul, ← PowerSeries.order_mul, ← map_mul, ← map_mul, h0]
  have hdfin : (φ d).order ≠ ⊤ := (order_lt_top_of_ev_ne_zero ev φ hker hd).ne
  have hbfin : (φ b).order ≠ ⊤ := (order_lt_top_of_ev_ne_zero ev φ hker hb).ne
  have hafin : (φ a).order ≠ ⊤ := (hlt.trans_le le_top).ne
  have hna := (ENat.coe_toNat hafin).symm
  have hnb := (ENat.coe_toNat hbfin).symm
  have hnd := (ENat.coe_toNat hdfin).symm
  rcases eq_or_ne (φ c).order ⊤ with hc | hc
  · rw [hc, top_add, hna, hnd] at hord
    exact WithTop.add_ne_top.mpr ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩ hord
  · have hnc := (ENat.coe_toNat hc).symm
    rw [hna, hnb, hnc, hnd] at hord
    rw [hnd, hnc] at hcd
    rw [hna, hnb] at hlt
    norm_cast at hord hcd hlt
    omega
theorem inv_mem_of_order_lt {a b : R} (hb : ev b ≠ 0) (hlt : (φ a).order < (φ b).order) :
    (ev a / ev b)⁻¹ ∈ fracSubring ev φ := by
  have ha : ev a ≠ 0 := by
    intro ha0
    have : (φ a).order = ⊤ := by rw [PowerSeries.order_eq_top]; exact (hker a).mp ha0
    rw [this] at hlt; exact not_top_lt hlt
  rw [inv_div]; exact fracMem_of ev φ b a ha hlt.le
theorem not_isUnit_inv_of_order_lt {a b : R} (hb : ev b ≠ 0) (hlt : (φ a).order < (φ b).order) :
    ¬ IsUnit (⟨(ev a / ev b)⁻¹, inv_mem_of_order_lt ev φ hker hb hlt⟩ : fracSubring ev φ) := by
  rintro ⟨u, hu⟩
  have hinv : ((↑u⁻¹ : fracSubring ev φ) : F) = ev a / ev b := by
    have h1 : ((u : fracSubring ev φ) : F) * ((↑u⁻¹ : fracSubring ev φ) : F) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
    rw [hu] at h1
    have hne : (ev a / ev b)⁻¹ ≠ 0 := by
      rw [Ne, _root_.inv_eq_zero, div_eq_zero_iff, not_or]; exact ⟨fun ha0 => by
        have : (φ a).order = ⊤ := by rw [PowerSeries.order_eq_top]; exact (hker a).mp ha0
        rw [this] at hlt; exact not_top_lt hlt, hb⟩
    calc ((↑u⁻¹ : fracSubring ev φ) : F) = (ev a / ev b)⁻¹⁻¹ * ((ev a / ev b)⁻¹ * ↑(↑u⁻¹ : fracSubring ev φ)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = ev a / ev b := by rw [h1, mul_one, inv_inv]
  exact not_mem_of_order_lt ev φ hker hb hlt (hinv ▸ (↑u⁻¹ : fracSubring ev φ).2)
theorem not_mem_valuationSubring_of_order_lt (V : ValuationSubring F)
    (hV : fracLocalSubring ev φ hker ≤ V.toLocalSubring)
    {a b : R} (hb : ev b ≠ 0) (hlt : (φ a).order < (φ b).order) :
    ev a / ev b ∉ V := by
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  intro hx
  have hy : (ev a / ev b)⁻¹ ∈ V := hle (inv_mem_of_order_lt ev φ hker hb hlt)
  have hnu : ¬ IsUnit (⟨(ev a / ev b)⁻¹, hy⟩ : V) := by
    intro hu
    exact not_isUnit_inv_of_order_lt ev φ hker hb hlt
      ((isUnit_map_iff (Subring.inclusion hle) _).mp (by exact hu))
  apply hnu
  have hne : (ev a / ev b) ≠ 0 := fun h =>
    not_mem_of_order_lt ev φ hker hb hlt (h ▸ (fracSubring ev φ).zero_mem)
  have ha : ev a ≠ 0 := fun h => hne (by rw [h, zero_div])
  exact ⟨⟨⟨_, hy⟩, ⟨_, hx⟩, by ext; simp [div_mul_div_comm, mul_comm, div_self (mul_ne_zero ha hb)],
    by ext; simp [div_mul_div_comm, mul_comm, div_self (mul_ne_zero ha hb)]⟩, rfl⟩
end Frac
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
namespace CuspDisc
section PlaceArg
open AlgebraicCurve ModularCurve MvPolynomial
variable (N : ℕ) [NeZero N]
local notation "ℚbar" => AlgebraicClosure ℚ
local notation "FN" => modularFunctionFieldBar N
abbrev jF : FN := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
variable (K : IntermediateField ℚ ℚbar)
def evQ : MvPolynomial (GenIdx N) K →+* LaurentSeries ℚbar :=
  (HahnSeries.ofPowerSeries ℤ ℚbar).comp
    ((MvPolynomial.aeval (genPS ℚbar N)).toRingHom.comp (MvPolynomial.map (algebraMap K ℚbar)))
theorem evQ_apply (p : MvPolynomial (GenIdx N) K) :
    evQ N K p = HahnSeries.ofPowerSeries ℤ ℚbar (evPS N ℚbar (MvPolynomial.map (algebraMap K ℚbar) p)) := rfl
theorem evQ_mem (p : MvPolynomial (GenIdx N) K) : evQ N K p ∈ FN := by
  rw [evQ_apply, ← aeval_genL_eq, modularFunctionFieldBar_eq_adjoin_genL]
  refine IntermediateField.algebra_adjoin_le_adjoin _ _ ?_
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨_, rfl⟩
def evF : MvPolynomial (GenIdx N) K →+* FN :=
  (evQ N K).codRestrict (modularFunctionFieldBar N).toSubring (evQ_mem N K)
@[scoped simp] theorem coe_evF (p : MvPolynomial (GenIdx N) K) : ((evF N K p : FN) : LaurentSeries ℚbar) = evQ N K p := rfl
theorem evF_X_none_mul_jF : evF N K (MvPolynomial.X none) * jF N = 1 := by
  apply Subtype.ext
  show evQ N K (MvPolynomial.X none) * coeffEmb ℚbar jq = 1
  rw [evQ_apply, MvPolynomial.map_X, ← aeval_genL_eq, MvPolynomial.aeval_X, mul_comm]
  exact coeffEmb_jq_mul_genL_none ℚbar N
theorem evF_C (c : K) : evF N K (MvPolynomial.C c) = algebraMap ℚbar FN (c : ℚbar) := by
  apply Subtype.ext
  show evQ N K (MvPolynomial.C c) = ((algebraMap ℚbar FN (c : ℚbar) : FN) : LaurentSeries ℚbar)
  rw [evQ_apply, MvPolynomial.map_C, ← aeval_genL_eq, MvPolynomial.aeval_C]
  rfl
variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
theorem genPS_bdd (i : GenIdx N) : Bdd 1 (genPS L N i) := fun k => by
  rw [genPS, PowerSeries.coeff_map]
  exact IsUltrametricDist.norm_intCast_le_one L _
theorem powerSeries_map_injective {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Injective φ) : Function.Injective (PowerSeries.map φ) := fun P Q h => by
  ext n; apply hφ; rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map, h]
theorem evF_eq_zero_iff_evPS (p : MvPolynomial (GenIdx N) K) : evF N K p = 0 ↔ evPS N K p = 0 := by
  rw [← Subtype.coe_inj, coe_evF, ZeroMemClass.coe_zero, evQ_apply,
    map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective, ← evPS_map,
    map_eq_zero_iff _ (powerSeries_map_injective _ (algebraMap K ℚbar).injective)]
theorem aeval_genPS_eq (p : MvPolynomial (GenIdx N) K) :
    MvPolynomial.aeval (genPS L N) p = (evPS N K p).map (algebraMap K L) := by
  rw [evPS_map, ← MvPolynomial.aeval_map_algebraMap L]
theorem evF_eq_zero_iff (r : L) (hr : ‖r‖ < 1) (p : MvPolynomial (GenIdx N) K) :
    evF N K p = 0 ↔ phi (K := K) (genPS L N) (genPS_bdd N) r hr p = 0 := by
  rw [evF_eq_zero_iff_evPS, phi_eq_zero_iff, aeval_genPS_eq,
    map_eq_zero_iff _ (powerSeries_map_injective _ (algebraMap K L).injective)]
theorem order_le_of_poles (f : FN)
    (aK : Place ℚbar FN → K)
    (ha : ∀ W : Place ℚbar FN, W.ord f < 0 → 0 < W.ord (jF N - algebraMap ℚbar FN (aK W : ℚbar)))
    (hnorm : ∀ W : Place ℚbar FN, W.ord f < 0 → ‖algebraMap K L (aK W)‖ ≤ 1)
    (rK sK : MvPolynomial (GenIdx N) K) (hs0 : evF N K sK ≠ 0)
    (hpres : f * evF N K sK = evF N K rK)
    (r : L) (hr : ‖r‖ < 1) :
    (phi (K := K) (genPS L N) (genPS_bdd N) r hr sK).order ≤ (phi (K := K) (genPS L N) (genPS_bdd N) r hr rK).order := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set φ := phi (K := K) (genPS L N) (genPS_bdd N) r hr with hφ
  have hker : ∀ p, evF N K p = 0 ↔ φ p = 0 := evF_eq_zero_iff N K r hr
  set W' := fracLocalSubring (evF N K) φ hker
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring W'
  have hle : W'.toSubring ≤ V.toSubring := (LocalSubring.le_def.mp hV).1
  have hfV : f ∉ V := by
    have : f = evF N K rK / evF N K sK := by rw [← hpres, mul_div_cancel_right₀ _ hs0]
    rw [this]
    exact not_mem_valuationSubring_of_order_lt (evF N K) φ hker V hV hs0 hlt
  have hVtop : V ≠ ⊤ := fun h => hfV (h ▸ ValuationSubring.mem_top f)
  have hQV : ∀ q : ℚ, algebraMap ℚ FN q ∈ V := by
    intro q
    have : algebraMap ℚ FN q = evF N K (MvPolynomial.C (q : K)) := by
      rw [evF_C, eq_ratCast, SubfieldClass.coe_ratCast, map_ratCast]
    rw [this]; exact hle (ev_mem_fracSubring (evF N K) φ _)
  let ιQ : ℚ →+* V := (algebraMap ℚ FN).codRestrict V.toSubring hQV
  have hconst : ∀ c : ℚbar, algebraMap ℚbar FN c ∈ V := by
    intro c
    have hint : IsIntegral V (algebraMap ℚbar FN c) := by
      have hc : IsIntegral ℚ c := by
        convert ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c).isIntegral <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
      refine ⟨(minpoly ℚ c).map ιQ, (minpoly.monic hc).map ιQ, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap V FN).comp ιQ = (algebraMap ℚbar FN).comp (algebraMap ℚ ℚbar) := by
        ext q; simp [ιQ]
      rw [this, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := FN)).mp hint
    rw [← hy]; exact y.2
  haveI : FiniteDimensional (IntermediateField.adjoin ℚbar ({jF N} : Set FN)) FN :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  obtain ⟨W, hW⟩ := AlgebraicCurve.Place.exists_of_valuationSubring (K := ℚbar) (F := FN) (jF N) V hconst hVtop
  have hf0 : f ≠ 0 := by
    rintro rfl; rw [zero_mul] at hpres
    have : φ rK = 0 := (hker rK).mp hpres.symm
    rw [this, PowerSeries.order_zero] at hlt
    exact not_top_lt hlt
  have hpole : W.ord f < 0 := by
    by_contra h
    rw [not_lt] at h
    exact hfV (hW ▸ (AlgebraicCurve.Place.mem_iff_ord_nonneg W hf0).mpr h)
  have hx : jF N - algebraMap ℚbar FN (aK W : ℚbar)
      = evF N K (1 - MvPolynomial.C (aK W) * MvPolynomial.X none) / evF N K (MvPolynomial.X none) := by
    have hXu : evF N K (MvPolynomial.X none) ≠ 0 := left_ne_zero_of_mul_eq_one (evF_X_none_mul_jF N K)
    rw [eq_div_iff hXu, map_sub, map_one, map_mul, evF_C, sub_mul, mul_comm (jF N), evF_X_none_mul_jF]
  have hnum : PowerSeries.constantCoeff (φ (1 - MvPolynomial.C (aK W) * MvPolynomial.X none)) ≠ 0 := by
    rw [map_sub, map_one, map_mul, hφ, phi_C, phi_X]
    have hg : genPS L N none = PowerSeries.X * (jDen.map (Int.castRingHom L)) := by
      simp [genPS, genZ]
    have hbd : Bdd 1 (jDen.map (Int.castRingHom L) : L⟦X⟧) := fun k => by
      rw [PowerSeries.coeff_map]; exact IsUltrametricDist.norm_intCast_le_one L _
    have hbX : Bdd 1 (PowerSeries.X : L⟦X⟧) := fun k => by
      rw [PowerSeries.coeff_X]; split_ifs <;> simp
    rw [hg, T_mul (norm_nonneg r) hr zero_le_one zero_le_one le_rfl hbX hbd, T_X]
    simp only [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C, map_add, PowerSeries.constantCoeff_X,
      zero_add]
    intro h0
    have h1 : algebraMap K L (aK W) * (r * PowerSeries.constantCoeff (T r (jDen.map (Int.castRingHom L)))) = 1 := by
      linear_combination -h0
    have hn : ‖algebraMap K L (aK W) * (r * PowerSeries.constantCoeff (T r (jDen.map (Int.castRingHom L))))‖ < 1 := by
      rw [norm_mul, norm_mul]
      have hc0 : ‖PowerSeries.constantCoeff (T r (jDen.map (Int.castRingHom L)))‖ ≤ 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hbd.T (norm_nonneg r) hr.le zero_le_one le_rfl 0
      calc ‖algebraMap K L (aK W)‖ * (‖r‖ * ‖PowerSeries.constantCoeff (T r (jDen.map (Int.castRingHom L)))‖)
          ≤ 1 * (‖r‖ * 1) := by
            gcongr
            · exact hnorm W hpole
        _ < 1 := by simpa using hr
    rw [h1, norm_one] at hn
    exact lt_irrefl _ hn
  have hnum0 : φ (1 - MvPolynomial.C (aK W) * MvPolynomial.X none) ≠ 0 := fun h => hnum (by rw [h, map_zero])
  have hnumE : evF N K (1 - MvPolynomial.C (aK W) * MvPolynomial.X none) ≠ 0 := fun h => hnum0 ((hker _).mp h)
  have hord0 : (φ (1 - MvPolynomial.C (aK W) * MvPolynomial.X none)).order = 0 := by
    rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
    exact ⟨by rwa [PowerSeries.coeff_zero_eq_constantCoeff], fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  have hinv : (jF N - algebraMap ℚbar FN (aK W : ℚbar))⁻¹ ∈ V := by
    rw [hx, inv_div]
    exact hle (fracMem_of (evF N K) φ _ _ hnumE (by rw [hord0]; exact bot_le))
  have hne : jF N - algebraMap ℚbar FN (aK W : ℚbar) ≠ 0 := by
    intro h; have := ha W hpole; rw [h, AlgebraicCurve.Place.ord_zero] at this; exact lt_irrefl _ this
  have := (AlgebraicCurve.Place.mem_iff_ord_nonneg W (inv_ne_zero hne)).mp (hW ▸ hinv)
  rw [AlgebraicCurve.Place.ord_inv] at this
  have := ha W hpole
  omega
end PlaceArg
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
noncomputable section
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
open IsDedekindDomain NumberField IsLocalRing Filter Topology in
section
end
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
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
  ext n
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
namespace CuspDisc
section Main
open AlgebraicCurve ModularCurve MvPolynomial IsDedekindDomain NumberField
local notation "ℚbar" => AlgebraicClosure ℚ
theorem valuationSubring_eq_top_of_rat_mem (A : ValuationSubring ℚbar) (h : ∀ q : ℚ, (q : ℚbar) ∈ A) : A = ⊤ := by
  refine eq_top_iff.mpr fun c _ => ?_
  let ιQ : ℚ →+* A := (algebraMap ℚ ℚbar).codRestrict A.toSubring (fun q => by rw [eq_ratCast]; exact h q)
  have hc : IsIntegral ℚ c := by
        convert ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c).isIntegral <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  have hint : IsIntegral A c := by
    refine ⟨(minpoly ℚ c).map ιQ, (minpoly.monic hc).map ιQ, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap A ℚbar).comp ιQ = algebraMap ℚ ℚbar := by ext q; simp [ιQ]
    rw [this, ← Polynomial.aeval_def, minpoly.aeval]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := ℚbar)).mp hint
  rw [← hy]; exact y.2
theorem order_C_mul' {L : Type*} [Field L] {c : L} (hc : c ≠ 0) (P : PowerSeries L) :
    (PowerSeries.C c * P).order = P.order := by
  rw [PowerSeries.order_mul]
  have : (PowerSeries.C c : PowerSeries L).order = 0 := by
    rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
    exact ⟨by simpa using hc, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  rw [this, zero_add]
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
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main_U1
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), W.ord f < 0 →
      ∃ a : A, 0 < W.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      ∀ k : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A := by
  classical
  by_cases hAtop : A = ⊤
  · exact ⟨1, one_ne_zero, fun k => by rw [hAtop]; exact ValuationSubring.mem_top _⟩
  obtain ⟨r, s, hrs⟩ := exists_presentation N f
  have hf0 : (f : LaurentSeries ℚbar) ≠ 0 := fun h => hf (Subtype.ext h)
  have hs0 : HahnSeries.ofPowerSeries ℤ ℚbar (evPS N ℚbar s) ≠ 0 := by
    intro h; rw [h, div_zero] at hrs; exact hf0 hrs
  obtain ⟨D, hD, -⟩ := (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor f hf
  let S : Finset (Place ℚbar (modularFunctionFieldBar N)) := D.support
  have hS : ∀ W : Place ℚbar (modularFunctionFieldBar N), W.ord f < 0 → W ∈ S := by
    intro W hW
    rw [Finsupp.mem_support_iff, hD]; exact hW.ne
  have hchoice : ∀ W : Place ℚbar (modularFunctionFieldBar N), ∃ a : A, W.ord f < 0 →
      0 < W.ord (jF N - algebraMap ℚbar (modularFunctionFieldBar N) (a : ℚbar)) := by
    intro W
    by_cases hW : W.ord f < 0
    · obtain ⟨a, ha⟩ := hpole W hW; exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hW⟩
  choose a ha using hchoice
  let Tc : Finset ℚbar := (r.support.image fun m => r.coeff m) ∪ (s.support.image fun m => s.coeff m)
    ∪ (S.image fun W => (a W : ℚbar))
  let K : IntermediateField ℚ ℚbar := IntermediateField.adjoin ℚ (Tc : Set ℚbar)
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => by convert ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _)
  haveI : NumberField K := NumberField.mk
  have hTK : ∀ x ∈ Tc, x ∈ K := fun x hx => IntermediateField.subset_adjoin ℚ _ hx
  obtain ⟨rK, hrK⟩ := exists_restrict_coeffs K r (fun m hm => hTK _ (by
    simp only [Tc, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨m, hm, rfl⟩)))
  obtain ⟨sK, hsK⟩ := exists_restrict_coeffs K s (fun m hm => hTK _ (by
    simp only [Tc, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨m, hm, rfl⟩)))
  have haK : ∀ W ∈ S, (a W : ℚbar) ∈ K := fun W hW => hTK _ (by
    simp only [Tc, Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨W, hW, rfl⟩)
  let aK : Place ℚbar (modularFunctionFieldBar N) → K := fun W =>
    if h : W ∈ S then ⟨a W, haK W h⟩ else 0
  have haK_coe : ∀ W ∈ S, ((aK W : K) : ℚbar) = a W := fun W hW => by simp [aK, hW]
  let B : ValuationSubring K := A.comap (algebraMap K ℚbar)
  have hBmem : ∀ x : K, x ∈ B ↔ (x : ℚbar) ∈ A := fun x => Iff.rfl
  have hBtop : B ≠ ⊤ := by
    intro hB
    apply hAtop
    refine valuationSubring_eq_top_of_rat_mem A fun q => ?_
    have : ((q : K) : ℚbar) = q := SubfieldClass.coe_ratCast _ q
    rw [← this, ← hBmem, hB]; exact ValuationSubring.mem_top _
  obtain ⟨v, hv⟩ := exists_heightOneSpectrum_eq_valuationSubring B hBtop
  have hvB : ∀ x : K, v.valuation K x ≤ 1 ↔ (x : ℚbar) ∈ A := fun x => by
    rw [← hBmem, ← hv]; exact Iff.rfl
  letI : Algebra K (Lv K v) := (jKL K v).toAlgebra
  have halg : ∀ x : K, algebraMap K (Lv K v) x = jKL K v x := fun x => rfl
  have hnorm : ∀ W : Place ℚbar (modularFunctionFieldBar N), W.ord f < 0 →
      ‖algebraMap K (Lv K v) (aK W)‖ ≤ 1 := by
    intro W hW
    rw [halg, jKL_apply, norm_algebraMap_Kv_Lv, ← mem_Ov_iff_norm_le_one, algebraMap_mem_Ov_iff, hvB,
      haK_coe W (hS W hW)]
    exact (a W).2
  have hevQr : evQ N K rK = HahnSeries.ofPowerSeries ℤ ℚbar (evPS N ℚbar r) := by
    rw [evQ_apply, hrK]
  have hevQs : evQ N K sK = HahnSeries.ofPowerSeries ℤ ℚbar (evPS N ℚbar s) := by
    rw [evQ_apply, hsK]
  have hs0' : evF N K sK ≠ 0 := fun h => hs0 (by rw [← hevQs, ← coe_evF, h]; rfl)
  have hpres : f * evF N K sK = evF N K rK := by
    apply Subtype.ext
    show (f : LaurentSeries ℚbar) * evQ N K sK = evQ N K rK
    rw [hevQs, hevQr, hrs, div_mul_cancel₀ _ hs0]
  have ha' : ∀ W : Place ℚbar (modularFunctionFieldBar N), W.ord f < 0 →
      0 < W.ord (jF N - algebraMap ℚbar (modularFunctionFieldBar N) (aK W : ℚbar)) := by
    intro W hW
    rw [haK_coe W (hS W hW)]
    exact ha W hW
  have hgood : ∀ (ρ : Lv K v) (hρ : ‖ρ‖ < 1),
      (phi (K := K) (genPS (Lv K v) N) (genPS_bdd N) ρ hρ sK).order
        ≤ (phi (K := K) (genPS (Lv K v) N) (genPS_bdd N) ρ hρ rK).order :=
    fun ρ hρ => order_le_of_poles N K f aK ha' hnorm rK sK hs0' hpres ρ hρ
  obtain ⟨P, hPdef⟩ : ∃ P : PowerSeries K, P = evPS N K rK := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : PowerSeries K, Q = evPS N K sK := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := fun h => hs0' ((evF_eq_zero_iff_evPS N K sK).mpr (hQdef ▸ h))
  have hP0 : P ≠ 0 := by
    intro h
    have h1 : evF N K rK = 0 := (evF_eq_zero_iff_evPS N K rK).mpr (hPdef ▸ h)
    rw [h1, mul_eq_zero] at hpres
    exact hpres.elim hf hs0'
  obtain ⟨bQ, hbQ⟩ := exists_log_valuation_le N K v sK
  obtain ⟨bP, hbP⟩ := exists_log_valuation_le N K v rK
  rw [← hQdef] at hbQ
  rw [← hPdef] at hbP
  obtain ⟨cQ, hcQ0, hcQ, n₀, hn₀⟩ := exists_primitive_scaling K v Q hQ0 bQ hbQ
  obtain ⟨cP, hcP0, hcP, -⟩ := exists_primitive_scaling K v P hP0 bP hbP
  have hcQ' : ∀ n, v.valuation K (PowerSeries.coeff n (PowerSeries.C cQ * Q)) ≤ 1 := fun n => by
    rw [PowerSeries.coeff_C_mul]; exact hcQ n
  have hcP' : ∀ n, v.valuation K (PowerSeries.coeff n (PowerSeries.C cP * P)) ≤ 1 := fun n => by
    rw [PowerSeries.coeff_C_mul]; exact hcP n
  obtain ⟨Q₀, hQ₀def⟩ : ∃ Q₀, Q₀ = liftOv K v (PowerSeries.C cQ * Q) hcQ' := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀def⟩ : ∃ P₀, P₀ = liftOv K v (PowerSeries.C cP * P) hcP' := ⟨_, rfl⟩
  have hQres : Q₀.map (IsLocalRing.residue (Ov K v)) ≠ 0 := by
    intro h
    have h1 : IsLocalRing.residue _ (PowerSeries.coeff n₀ Q₀) = 0 := by
      rw [← PowerSeries.coeff_map, h, map_zero]
    rw [IsLocalRing.residue_eq_zero_iff] at h1
    have hu : IsUnit (PowerSeries.coeff n₀ Q₀) := by
      rw [isUnit_Ov_iff_norm_eq_one, hQ₀def, coeff_liftOv, PowerSeries.coeff_C_mul]
      apply le_antisymm
      · rw [Valued.toNormedField.norm_le_one_iff, valued_algebraMap]; exact hn₀.le
      · rw [Valued.toNormedField.one_le_norm_iff, valued_algebraMap]; exact hn₀.ge
    exact h1 hu
  have hgood' : ∀ ρ : Lv K v, ‖ρ‖ < 1 → (T ρ (Q₀.map (ιL K v))).order ≤ (T ρ (P₀.map (ιL K v))).order := by
    intro ρ hρ
    obtain ⟨C1, hC1, hB1⟩ := evL_bdd (K := K) (genPS (Lv K v) N) (genPS_bdd N) sK
    obtain ⟨C2, hC2, hB2⟩ := evL_bdd (K := K) (genPS (Lv K v) N) (genPS_bdd N) rK
    have hQL : Q₀.map (ιL K v) = PowerSeries.C (jKL K v cQ) * MvPolynomial.aeval (genPS (Lv K v) N) sK := by
      rw [hQ₀def, liftOv_map_ιL, map_mul, PowerSeries.map_C, aeval_genPS_eq, hQdef]; rfl
    have hPL : P₀.map (ιL K v) = PowerSeries.C (jKL K v cP) * MvPolynomial.aeval (genPS (Lv K v) N) rK := by
      rw [hP₀def, liftOv_map_ιL, map_mul, PowerSeries.map_C, aeval_genPS_eq, hPdef]; rfl
    have hρ0 := norm_nonneg ρ
    rw [hQL, hPL, T_mul hρ0 hρ (norm_nonneg _) hC1 le_rfl (bdd_C _) hB1,
      T_mul hρ0 hρ (norm_nonneg _) hC2 le_rfl (bdd_C _) hB2, T_C, T_C,
      order_C_mul' ((_root_.map_ne_zero _).mpr hcQ0), order_C_mul' ((_root_.map_ne_zero _).mpr hcP0)]
    exact hgood ρ hρ
  obtain ⟨G, hG⟩ := PowerSeries.dvd_of_forall_taylorShift_order_le (ιL K v) (ιL_injective K v)
    (norm_ιL_le_one K v) (fun x hx => norm_ιL_lt_one K v hx) P₀ Q₀ hQres hgood'
  obtain ⟨fK, hfKdef⟩ : ∃ fK : LaurentSeries K,
      fK = HahnSeries.ofPowerSeries ℤ K P / HahnSeries.ofPowerSeries ℤ K Q := ⟨_, rfl⟩
  have hfK : coeffMap (algebraMap K ℚbar) fK = (f : LaurentSeries ℚbar) := by
    rw [hfKdef, map_div₀, map_ofPowerSeries, map_ofPowerSeries, hPdef, hQdef, evPS_map, evPS_map, hrK, hsK, hrs]
  let ψ : LaurentSeries K →+* LaurentSeries (Kv K v) := coeffMap (algebraMap K (Kv K v))
  have hQv0 : HahnSeries.ofPowerSeries ℤ (Kv K v) (Q.map (algebraMap K (Kv K v))) ≠ 0 := by
    rw [map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective,
      map_ne_zero_iff _ (powerSeries_map_injective _ (algebraMap K (Kv K v)).injective)]
    exact hQ0
  have hfKv : ψ fK * HahnSeries.ofPowerSeries ℤ (Kv K v) (Q.map (algebraMap K (Kv K v)))
      = HahnSeries.ofPowerSeries ℤ (Kv K v) (P.map (algebraMap K (Kv K v))) := by
    rw [hfKdef, map_div₀, map_ofPowerSeries, map_ofPowerSeries, div_mul_cancel₀ _ hQv0]
  have hGv : PowerSeries.C (algebraMap K (Kv K v) cP) * P.map (algebraMap K (Kv K v))
      = PowerSeries.C (algebraMap K (Kv K v) cQ) * Q.map (algebraMap K (Kv K v)) * G.map (Ov K v).subtype := by
    have := congrArg (PowerSeries.map (Ov K v).subtype) hG
    rw [map_mul, hP₀def, hQ₀def, liftOv_map_subtype, liftOv_map_subtype, map_mul, map_mul,
      PowerSeries.map_C, PowerSeries.map_C] at this
    exact this
  have hkey : HahnSeries.C (algebraMap K (Kv K v) (cP / cQ)) * ψ fK
      = HahnSeries.ofPowerSeries ℤ (Kv K v) (G.map (Ov K v).subtype) := by
    have hcQv : algebraMap K (Kv K v) cQ ≠ 0 := (_root_.map_ne_zero _).mpr hcQ0
    have h1 := congrArg (HahnSeries.ofPowerSeries ℤ (Kv K v)) hGv
    rw [map_mul, map_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_C, ← hfKv] at h1
    have h2 : (HahnSeries.C (algebraMap K (Kv K v) cP) * ψ fK
        - HahnSeries.C (algebraMap K (Kv K v) cQ) * HahnSeries.ofPowerSeries ℤ (Kv K v) (G.map (Ov K v).subtype))
        * HahnSeries.ofPowerSeries ℤ (Kv K v) (Q.map (algebraMap K (Kv K v))) = 0 := by
      rw [sub_mul]; linear_combination h1
    rw [mul_eq_zero, sub_eq_zero] at h2
    rcases h2 with h2 | h2
    · have hCq : (HahnSeries.C (algebraMap K (Kv K v) cQ) : LaurentSeries (Kv K v)) ≠ 0 :=
        (_root_.map_ne_zero HahnSeries.C).mpr hcQv
      calc HahnSeries.C (algebraMap K (Kv K v) (cP / cQ)) * ψ fK
          = (HahnSeries.C (algebraMap K (Kv K v) cQ))⁻¹ * (HahnSeries.C (algebraMap K (Kv K v) cP) * ψ fK) := by
            rw [map_div₀, map_div₀, div_eq_mul_inv]; ring
        _ = (HahnSeries.C (algebraMap K (Kv K v) cQ))⁻¹ * (HahnSeries.C (algebraMap K (Kv K v) cQ)
              * HahnSeries.ofPowerSeries ℤ (Kv K v) (G.map (Ov K v).subtype)) := by rw [h2]
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hCq, one_mul]
    · exact absurd h2 hQv0
  refine ⟨algebraMap K ℚbar (cP / cQ), (_root_.map_ne_zero _).mpr (div_ne_zero hcP0 hcQ0), fun k => ?_⟩
  rw [← hfK, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, ← map_mul]
  change ((cP / cQ * fK.coeff k : K) : ℚbar) ∈ A
  rw [← hvB, ← algebraMap_mem_Ov_iff]
  have hk := congrArg (fun x => HahnSeries.coeff x k) hkey
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at hk
  rw [show (ψ fK).coeff k = algebraMap K (Kv K v) (fK.coeff k) from rfl, ← map_mul] at hk
  rw [hk, coeff_ofPowerSeries_int]
  split_ifs
  · rw [PowerSeries.coeff_map]; exact Subtype.coe_prop _
  · exact zero_mem _
end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
end CuspDisc
p2m_reactivate "P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.CuspDisc"
open AlgebraicCurve ModularCurve
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), W.ord f < 0 →
      ∃ a : A, 0 < W.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      ∀ k : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A :=
  CuspDisc.main_U1 A N f hf hpole

end
end
end
end
end S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
end P2MW
export P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg (solution)
