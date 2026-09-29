-- Prove2me | solution 1 for ModularCurve.exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a17656d3-09cb-53b1-a3fc-fdaf9b62f35a

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
import Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
open IntermediateField AlgebraicCurve ModularCurve Polynomial

namespace W7B0B

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

theorem ι_injective : Function.Injective (ι A) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact h1

theorem ι_eq_zero_iff (x : LaurentSeries A) : ι A x = 0 ↔ x = 0 := by
  rw [← map_zero (ι A)]; exact (ι_injective A).eq_iff

theorem ϖ_ne_zero_iff (y : LaurentSeries A) :
    ϖ A y ≠ 0 ↔ ∃ n, y.coeff n ∉ IsLocalRing.maximalIdeal A := by
  rw [Ne, not_iff_comm, not_exists]
  simp only [not_not]
  constructor
  · intro h
    ext n
    simp only [coeffMap_coeff, HahnSeries.coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h n)
  · intro h n
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries A} (hy : ϖ A y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

theorem ι_C (a : A) : ι A (HahnSeries.C a) = algebraMap L (LaurentSeries L) (a : L) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]; rfl

theorem ϖ_C (a : A) : ϖ A (HahnSeries.C a) =
    algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
      (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]

theorem exists_ι_eq (x : LaurentSeries L) (hx : ∀ n, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, ι A y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
  · ext n
    rfl

theorem ι_qExpand_jqModC (d : ℕ) [NeZero d] :
    ι A (qExpand A d (jqModC A)) = qExpand L d (jqModC L) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem ϖ_qExpand_jqModC (d : ℕ) [NeZero d] :
    ϖ A (qExpand A d (jqModC A)) =
      qExpand (IsLocalRing.ResidueField A) d (jqModC (IsLocalRing.ResidueField A)) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem ι_eval₂ (P : A[X]) (x : LaurentSeries A) :
    ι A (P.eval₂ HahnSeries.C x) = (P.map (algebraMap A L)).eval₂ (algebraMap L (LaurentSeries L)) (ι A x) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext a : 1
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact ι_C A a

theorem ϖ_eval₂ (P : A[X]) (x : LaurentSeries A) :
    ϖ A (P.eval₂ HahnSeries.C x) = (P.map (IsLocalRing.residue A)).eval₂
      (algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))) (ϖ A x) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext a : 1
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact ϖ_C A a

end Coeff

section Red

variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem liesOverPrime_of_red {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  change ((q : ℕ) : ℚ̄) ∈ A.nonunits
  have hq : ((q : ℕ) : ℚ̄) = ((q : A) : ℚ̄) := by simp
  rw [hq, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : IsUnit (red (q : A)) := hu.map red
  rw [map_natCast, CharP.cast_eq_zero k q] at h1
  exact not_isUnit_zero h1

theorem red_eq_zero_of_mem_maximalIdeal {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  haveI : Ring.KrullDimLE 1 A :=
    @ValuationSubring.krullDimLE_one_of_isAlgebraic_rat ℚ̄ _ _ (AlgebraicClosure.isAlgebraic ℚ) A
  have hprime : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hne : RingHom.ker red ≠ ⊥ := by
    intro h
    have hq : (q : A) ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero k q]
    rw [h, Ideal.mem_bot] at hq
    have hq' : ((q : A) : ℚ̄) = 0 := by rw [hq]; rfl
    have hq'' : (q : ℚ̄) = 0 := by simpa using hq'
    exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast hq'')
  have hmax : (RingHom.ker red).IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot hprime hne
  have heq : RingHom.ker red = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  have : a ∈ RingHom.ker red := heq ▸ ha
  exact this

theorem red_ne_zero_iff {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : A) :
    red a ≠ 0 ↔ a ∉ IsLocalRing.maximalIdeal A := by
  constructor
  · exact fun h ha => h (red_eq_zero_of_mem_maximalIdeal q A red ha)
  · intro ha h0
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at ha
    have := ha.map red
    rw [h0] at this
    exact not_isUnit_zero this

theorem charP_residueField (hA : A.LiesOverPrime q) : CharP (IsLocalRing.ResidueField A) q :=
  ValuationSubring.charP_residueField_of_liesOverPrime q A hA

theorem natCast_residueField_ne_zero (hA : A.LiesOverPrime q) {m : ℕ} (hm : ¬ q ∣ m) :
    (m : IsLocalRing.ResidueField A) ≠ 0 := by
  haveI := charP_residueField q A hA
  rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) q]
  exact hm

end Red

section Transport

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]

theorem mem_comap_iff (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : F) :
    x ∈ R.integers.comap (w : F →+* F) ↔ w x ∈ R.integers := Iff.rfl

def comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers.comap (w : F →+* F) →+* R.integers :=
  (w : F →+* F).restrict _ _ (fun _ hx => (mem_comap_iff A R w _).mp hx)

@[scoped simp] theorem coe_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : (comapHom A R w x : F) = w x := rfl

def symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers →+* R.integers.comap (w : F →+* F) :=
  (w.symm : F →+* F).restrict _ _ (fun x hx => by
    rw [mem_comap_iff]
    change w (w.symm x) ∈ R.integers
    rw [AlgEquiv.apply_symm_apply]; exact hx)

@[scoped simp] theorem coe_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers) : (symmHom A R w x : F) = w.symm x := rfl

theorem comapHom_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : R.integers) :
    comapHom A R w (symmHom A R w x) = x :=
  Subtype.ext (by simp)

theorem symmHom_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : symmHom A R w (comapHom A R w x) = x :=
  Subtype.ext (by simp)

def transport (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) : RegularProlongation A F Fb where
  integers := R.integers.comap (w : F →+* F)
  residue := R.residue.comp (comapHom A R w)
  algebraMap_mem_iff x := by
    rw [mem_comap_iff, AlgEquiv.commutes]
    exact R.algebraMap_mem_iff x
  residue_surjective z := by
    obtain ⟨f, hf⟩ := R.residue_surjective z
    exact ⟨symmHom A R w f, by rw [RingHom.comp_apply, comapHom_symmHom, hf]⟩
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R.ker_residue,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, not_iff_not]
    constructor
    · intro hu; simpa [symmHom_comapHom] using hu.map (symmHom A R w)
    · intro hu; exact hu.map (comapHom A R w)
  residue_algebraMap a := by
    rw [RingHom.comp_apply]
    convert R.residue_algebraMap a using 2
    exact Subtype.ext (by simp)
  exists_smul_mem f hf := by
    have hwf : w f ≠ 0 := (map_ne_zero_iff _ w.injective).mpr hf
    obtain ⟨c, hc, hne⟩ := R.exists_smul_mem (w f) hwf
    have hmem : c • f ∈ R.integers.comap (w : F →+* F) := by
      rw [mem_comap_iff, map_smul]; exact hc
    refine ⟨c, hmem, ?_⟩
    rw [RingHom.comp_apply]
    have h : comapHom A R w ⟨c • f, hmem⟩ = ⟨c • w f, hc⟩ := Subtype.ext (by simp)
    rwa [h]

@[scoped simp] theorem transport_integers (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    (transport A R w).integers = R.integers.comap (w : F →+* F) := rfl

theorem transport_residue (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : F) (hx : x ∈ (transport A R w).integers) :
    (transport A R w).residue ⟨x, hx⟩ = R.residue ⟨w x, hx⟩ := rfl

end Transport

section ResidueSide

variable (κ : Type*) [Field κ] (q : ℕ) [Fact q.Prime] [CharP κ q] (N : ℕ) [NeZero N]

local notation "Λκ" => LaurentSeries κ

abbrev φ : Λκ →ₐ[κ] Λκ := qExpandAlgHomC κ q

abbrev jb : Λκ := jqModC κ

abbrev jbN : Λκ := qExpand κ N (jqModC κ)

theorem φ_apply (x : Λκ) : φ κ q x = qExpand κ q x := rfl

theorem φ_jb : φ κ q (jb κ) = (jb κ) ^ q := qExpand_jqModC_eq_pow_unconditional κ

theorem qExpand_comm (a b : ℕ) [NeZero a] [NeZero b] (x : Λκ) :
    qExpand κ a (qExpand κ b x) = qExpand κ b (qExpand κ a x) := by
  rw [qExpand_qExpand, qExpand_qExpand, qExpand_congr (Nat.mul_comm b a)]

theorem φ_qExpand (e : ℕ) [NeZero e] : φ κ q (qExpand κ e (jb κ)) = (qExpand κ e (jb κ)) ^ q := by
  rw [φ_apply, qExpand_comm, qExpand_jqModC_eq_pow_unconditional κ, map_pow]

theorem φ_jbN : φ κ q (jbN κ N) = (jbN κ N) ^ q := φ_qExpand κ q N

theorem φ_injective : Function.Injective (φ κ q) := qExpand_injective (R := κ) (N := q)

theorem coeff_φ_of_not_dvd (z : Λκ) {n : ℤ} (hn : ¬ (q : ℤ) ∣ n) : (φ κ q z).coeff n = 0 :=
  qExpand_coeff_of_not_dvd q z hn

theorem jb_not_mem_range : ∀ z : Λκ, φ κ q z ≠ jb κ := by
  intro z hz
  have h1 : (φ κ q z).coeff (-1) = 0 := coeff_φ_of_not_dvd κ q z (by
    rintro ⟨c, hc⟩
    have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
    have : (q : ℤ) ∣ 1 := ⟨-c, by linarith⟩
    have := Int.le_of_dvd one_pos this
    omega)
  rw [hz, coeff_jqModC_neg_one] at h1
  exact one_ne_zero h1

theorem jbN_not_mem_range (hqN : ¬ q ∣ N) : ∀ z : Λκ, φ κ q z ≠ jbN κ N := by
  intro z hz
  have h1 : (φ κ q z).coeff (-(N : ℤ)) = 0 := coeff_φ_of_not_dvd κ q z (by
    rw [Int.dvd_neg]; exact_mod_cast hqN)
  have h2 : (jbN κ N).coeff (-(N : ℤ)) = 1 := by
    rw [show (-(N : ℤ)) = (N : ℤ) * (-1) by ring]
    change (qExpand κ N (jqModC κ)).coeff ((N : ℤ) * (-1)) = 1
    rw [qExpand_coeff_mul, coeff_jqModC_neg_one]
  rw [hz, h2] at h1
  exact one_ne_zero h1

abbrev K₁ : IntermediateField κ Λκ := IntermediateField.adjoin κ {jb κ}

abbrev K₀ : IntermediateField κ Λκ := IntermediateField.adjoin κ {(jb κ) ^ q}

abbrev F₁ : IntermediateField κ Λκ := IntermediateField.adjoin κ {jb κ, jbN κ N}

abbrev F₀ : IntermediateField κ Λκ := IntermediateField.adjoin κ {(jb κ) ^ q, (jbN κ N) ^ q}

theorem K₁_map : (K₁ κ).map (φ κ q) = K₀ κ q := by
  rw [adjoin_map, Set.image_singleton, φ_jb]

theorem F₁_map : (F₁ κ N).map (φ κ q) = F₀ κ q N := by
  rw [adjoin_map, Set.image_pair, φ_jb, φ_jbN]

theorem F₁_eq_C : F₁ κ N = modularFunctionFieldC κ N := rfl

theorem K₀_le_K₁ : K₀ κ q ≤ K₁ κ :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (pow_mem (mem_adjoin_simple_self κ (jb κ)) q))

theorem K₁_le_F₁ : K₁ κ ≤ F₁ κ N :=
  adjoin.mono κ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem jb_mem_F₁ : jb κ ∈ F₁ κ N := subset_adjoin κ _ (Set.mem_insert _ _)
theorem jbN_mem_F₁ : jbN κ N ∈ F₁ κ N := subset_adjoin κ _ (Set.mem_insert_of_mem _ rfl)

theorem adjoin_pair_le {a b : Λκ} {E : IntermediateField κ Λκ} (ha : a ∈ E) (hb : b ∈ E) :
    IntermediateField.adjoin κ {a, b} ≤ E :=
  adjoin_le_iff.mpr (Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hb⟩)

theorem mem_adjoin_pair_left (a b : Λκ) : a ∈ IntermediateField.adjoin κ {a, b} :=
  subset_adjoin κ _ (Set.mem_insert _ _)

theorem mem_adjoin_pair_right (a b : Λκ) : b ∈ IntermediateField.adjoin κ {a, b} :=
  subset_adjoin κ _ (Set.mem_insert_of_mem _ rfl)

theorem F₀_le_F₁ : F₀ κ q N ≤ F₁ κ N :=
  adjoin_pair_le κ (pow_mem (jb_mem_F₁ κ N) q) (pow_mem (jbN_mem_F₁ κ N) q)

theorem K₀_le_F₀ : K₀ κ q ≤ F₀ κ q N :=
  adjoin.mono κ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem mem_F₀_iff (x : Λκ) : x ∈ F₀ κ q N ↔ ∃ z ∈ F₁ κ N, φ κ q z = x := by
  rw [← F₁_map, IntermediateField.mem_map]

theorem jb_not_mem_F₀ : jb κ ∉ F₀ κ q N := fun h => by
  obtain ⟨z, _, hz⟩ := (mem_F₀_iff κ q N _).mp h
  exact jb_not_mem_range κ q z hz

theorem jbN_not_mem_F₀ (hqN : ¬ q ∣ N) : jbN κ N ∉ F₀ κ q N := fun h => by
  obtain ⟨z, _, hz⟩ := (mem_F₀_iff κ q N _).mp h
  exact jbN_not_mem_range κ q N hqN z hz

theorem relfinrank_K₁_F₁ (hqN : ¬ q ∣ N) : relfinrank (K₁ κ) (F₁ κ N) = dedekindPsi N :=
  ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi κ N q hqN

theorem relfinrank_K₀_F₀ (hqN : ¬ q ∣ N) : relfinrank (K₀ κ q) (F₀ κ q N) = dedekindPsi N := by
  rw [← K₁_map, ← F₁_map, relfinrank_map_map, relfinrank_K₁_F₁ κ q N hqN]

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne N]
  calc 0 < N / 1 := by simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ dedekindPsi N := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

theorem order_jqModC_pow (b : ℕ) : ((jqModC κ) ^ b).order = -(b : ℤ) := by
  have h1 : ((jqModC κ) ^ b).coeff (-(b : ℤ)) ≠ 0 := by
    rw [coeff_jqModC_pow_self]; exact one_ne_zero
  have hne : (jqModC κ) ^ b ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push Not at hlt
  exact (mt HahnSeries.coeff_order_eq_zero.mp hne) (coeff_jqModC_pow_of_lt κ hlt)

theorem jqModC_pow_ne_zero (b : ℕ) : (jqModC κ) ^ b ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (by rw [coeff_jqModC_pow_self]; exact one_ne_zero)

theorem order_qExpand {x : Λκ} (hx : x ≠ 0) : (qExpand κ q x).order = (q : ℤ) * x.order := by
  have hq0 : qExpand κ q x ≠ 0 := fun h => hx (qExpand_injective (R := κ) (N := q) (by rw [h, map_zero]))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [qExpand_coeff_mul]; exact mt HahnSeries.coeff_order_eq_zero.mp hx
  · by_contra hlt
    push Not at hlt
    have hc := mt HahnSeries.coeff_order_eq_zero.mp hq0
    by_cases hdvd : (q : ℤ) ∣ (qExpand κ q x).order
    · obtain ⟨c, hc'⟩ := hdvd
      rw [hc', qExpand_coeff_mul] at hc
      have hle := HahnSeries.order_le_of_coeff_ne_zero hc
      rw [hc'] at hlt
      have hp : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
      nlinarith
    · exact hc (qExpand_coeff_of_not_dvd q x hdvd)

theorem eq_zero_of_sum_eq_zero_of_order_injOn {ι' : Type*} [Fintype ι'] (t : ι' → Λκ)
    (hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → (t i).order = (t j).order → i = j)
    (hsum : ∑ i, t i = 0) : ∀ i, t i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  set s : Finset ι' := Finset.univ.filter fun i => t i ≠ 0 with hs
  have hsne : s.Nonempty := ⟨i₁, by simp [hs, hi₁]⟩
  obtain ⟨i₀, hi₀s, hmin⟩ := Finset.exists_min_image s (fun i => (t i).order) hsne
  have hi₀ : t i₀ ≠ 0 := by simpa [hs] using hi₀s
  have hcoeff : (∑ i, t i).coeff (t i₀).order = (t i₀).coeff (t i₀).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases hti : t i = 0
    · rw [hti, HahnSeries.coeff_zero]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      have hle := hmin i (by simp [hs, hti])
      exact lt_of_le_of_ne hle fun h => hi (hdist i i₀ hti hi₀ h.symm)
  rw [hsum, HahnSeries.coeff_zero] at hcoeff
  exact (mt HahnSeries.coeff_order_eq_zero.mp hi₀) hcoeff.symm

theorem exists_qExpand_eq_of_mem_K₀ {c : Λκ} (hc : c ∈ K₀ κ q) : ∃ d : Λκ, qExpand κ q d = c := by
  rw [← K₁_map, IntermediateField.mem_map] at hc
  obtain ⟨d, _, rfl⟩ := hc
  exact ⟨d, rfl⟩

theorem isIntegral_K₀_jb : IsIntegral (K₀ κ q) (jb κ) := by
  refine ⟨X ^ q - C ⟨(jb κ) ^ q, mem_adjoin_simple_self κ _⟩, monic_X_pow_sub_C _ (Fact.out : q.Prime).ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, IntermediateField.algebraMap_apply,
    sub_self]

theorem extendScalars_K₀_K₁ : extendScalars (K₀_le_K₁ κ q) = IntermediateField.adjoin (K₀ κ q) {jb κ} :=
  extendScalars_adjoin (K₀_le_K₁ κ q)

theorem relfinrank_K₀_K₁ : relfinrank (K₀ κ q) (K₁ κ) = q := by
  have hint := isIntegral_K₀_jb κ q
  rw [relfinrank_eq_finrank_of_le (K₀_le_K₁ κ q)]
  haveI hfin : FiniteDimensional (K₀ κ q) (extendScalars (K₀_le_K₁ κ q)) := by
    rw [extendScalars_K₀_K₁]; exact adjoin.finiteDimensional hint
  refine le_antisymm ?_ ?_
  ·
    rw [extendScalars_K₀_K₁, adjoin.finrank hint]
    have hmonic : (X ^ q - C (⟨(jb κ) ^ q, mem_adjoin_simple_self κ _⟩ : K₀ κ q)).Monic :=
      monic_X_pow_sub_C _ (Fact.out : q.Prime).ne_zero
    have hroot : Polynomial.aeval (jb κ) (X ^ q - C (⟨(jb κ) ^ q, mem_adjoin_simple_self κ _⟩ : K₀ κ q)) = 0 := by
      simp [IntermediateField.algebraMap_apply]
    have h := minpoly.min (K₀ κ q) (jb κ) hmonic hroot
    calc (minpoly (K₀ κ q) (jb κ)).natDegree
        ≤ (X ^ q - C (⟨(jb κ) ^ q, mem_adjoin_simple_self κ _⟩ : K₀ κ q)).natDegree :=
          Polynomial.natDegree_le_natDegree h
      _ = q := by rw [natDegree_X_pow_sub_C]
  ·
    let v : Fin q → extendScalars (K₀_le_K₁ κ q) := fun i =>
      ⟨(jb κ) ^ (i : ℕ), (mem_extendScalars _).mpr (pow_mem (mem_adjoin_simple_self κ (jb κ)) _)⟩
    have hli : LinearIndependent (K₀ κ q) v := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hsum : ∑ i, ((g i : K₀ κ q) : Λκ) * (jb κ) ^ (i : ℕ) = 0 := by
        have := congrArg (fun z : extendScalars (K₀_le_K₁ κ q) => (z : Λκ)) hg
        first
          | simpa only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] using this
          | (simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at this; exact this)
          | (simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, SetLike.val_smul, smul_eq_mul] at this
             exact this)
      have hd : ∀ i, ∃ d : Λκ, qExpand κ q d = ((g i : K₀ κ q) : Λκ) :=
        fun i => exists_qExpand_eq_of_mem_K₀ κ q (g i).2
      choose d hd using hd
      have hall := eq_zero_of_sum_eq_zero_of_order_injOn κ
        (fun i : Fin q => ((g i : K₀ κ q) : Λκ) * (jb κ) ^ (i : ℕ)) ?_ hsum
      · have hi := hall i
        rcases mul_eq_zero.mp hi with h0 | h0
        · exact Subtype.ext (by simpa using h0)
        · exact absurd h0 (jqModC_pow_ne_zero κ _)
      · intro i j hi hj hij
        have hgi : ((g i : K₀ κ q) : Λκ) ≠ 0 := left_ne_zero_of_mul hi
        have hgj : ((g j : K₀ κ q) : Λκ) ≠ 0 := left_ne_zero_of_mul hj
        have hdi : d i ≠ 0 := by rintro h; apply hgi; rw [← hd i, h, map_zero]
        have hdj : d j ≠ 0 := by rintro h; apply hgj; rw [← hd j, h, map_zero]
        beta_reduce at hij
        rw [HahnSeries.order_mul hgi (jqModC_pow_ne_zero κ _),
          HahnSeries.order_mul hgj (jqModC_pow_ne_zero κ _), ← hd i, ← hd j,
          order_qExpand κ q hdi, order_qExpand κ q hdj, order_jqModC_pow, order_jqModC_pow] at hij
        have hdvd : (q : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) :=
          ⟨(d j).order - (d i).order, by linarith⟩
        have habs : |((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)| < q := by
          rw [abs_sub_lt_iff]; constructor <;> omega
        have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
        exact Fin.ext (by omega)
    simpa using hli.fintype_card_le_finrank

theorem relfinrank_K₀_F₁ (hqN : ¬ q ∣ N) : relfinrank (K₀ κ q) (F₁ κ N) = q * dedekindPsi N := by
  rw [← relfinrank_mul_relfinrank (K₀_le_K₁ κ q) (K₁_le_F₁ κ N), relfinrank_K₀_K₁,
    relfinrank_K₁_F₁ κ q N hqN]

theorem relfinrank_F₀_F₁ (hqN : ¬ q ∣ N) : relfinrank (F₀ κ q N) (F₁ κ N) = q := by
  have h := relfinrank_mul_relfinrank (K₀_le_F₀ κ q N) (F₀_le_F₁ κ q N)
  rw [relfinrank_K₀_F₀ κ q N hqN, relfinrank_K₀_F₁ κ q N hqN] at h
  have hpos := dedekindPsi_pos N
  nlinarith [h]

theorem eq_F₁_of_le_of_not_le (hqN : ¬ q ∣ N) {E : IntermediateField κ Λκ}
    (h₀ : F₀ κ q N ≤ E) (h₁ : E ≤ F₁ κ N) (hne : ¬ E ≤ F₀ κ q N) : E = F₁ κ N := by
  have htow := relfinrank_mul_relfinrank h₀ h₁
  rw [relfinrank_F₀_F₁ κ q N hqN] at htow
  have h1 : relfinrank (F₀ κ q N) E ≠ 1 := fun h => hne (relfinrank_eq_one_iff.mp h)
  have hdvd : relfinrank E (F₁ κ N) ∣ q := Dvd.intro_left _ htow
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hdvd with h | h
  · exact le_antisymm h₁ (relfinrank_eq_one_iff.mp h)
  · exfalso; rw [h] at htow
    have hq : 0 < q := (Fact.out : q.Prime).pos
    have : relfinrank (F₀ κ q N) E = 1 := by nlinarith
    exact h1 this

theorem adjoin_jb_jbN_pow_eq (hqN : ¬ q ∣ N) :
    IntermediateField.adjoin κ {jb κ, (jbN κ N) ^ q} = F₁ κ N := by
  refine eq_F₁_of_le_of_not_le κ q N hqN ?_ ?_ ?_
  · exact adjoin_pair_le κ (pow_mem (mem_adjoin_pair_left κ _ _) q) (mem_adjoin_pair_right κ _ _)
  · exact adjoin_pair_le κ (jb_mem_F₁ κ N) (pow_mem (jbN_mem_F₁ κ N) q)
  · exact fun h => jb_not_mem_F₀ κ q N (h (mem_adjoin_pair_left κ _ _))

theorem adjoin_jb_pow_jbN_eq (hqN : ¬ q ∣ N) :
    IntermediateField.adjoin κ {(jb κ) ^ q, jbN κ N} = F₁ κ N := by
  refine eq_F₁_of_le_of_not_le κ q N hqN ?_ ?_ ?_
  · exact adjoin_pair_le κ (mem_adjoin_pair_left κ _ _) (pow_mem (mem_adjoin_pair_right κ _ _) q)
  · exact adjoin_pair_le κ (pow_mem (jb_mem_F₁ κ N) q) (jbN_mem_F₁ κ N)
  · exact fun h => jbN_not_mem_F₀ κ q N hqN (h (mem_adjoin_pair_right κ _ _))

theorem finrank_congr {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]
    {X Y : IntermediateField K E} (h : X = Y) : Module.finrank K X = Module.finrank K Y := by
  subst h; rfl

theorem adjoin_insert_algebraMap {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]
    (a : K) (S : Set E) :
    IntermediateField.adjoin K (insert (algebraMap K E a) S) = IntermediateField.adjoin K S := by
  refine le_antisymm (adjoin_le_iff.mpr (Set.insert_subset ?_ (subset_adjoin K S)))
    (adjoin.mono K _ _ (Set.subset_insert _ _))
  exact IntermediateField.algebraMap_mem _ a

theorem natDegree_minpoly_K₀ (x : Λκ) (E : IntermediateField κ Λκ)
    (hE : IntermediateField.adjoin κ {(jb κ) ^ q, x} = E) (hpos : 0 < relfinrank (K₀ κ q) E) :
    IsIntegral (K₀ κ q) x ∧ (minpoly (K₀ κ q) x).natDegree = relfinrank (K₀ κ q) E := by
  subst hE
  have hle : K₀ κ q ≤ IntermediateField.adjoin κ {(jb κ) ^ q, x} :=
    adjoin.mono κ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hext : extendScalars hle = IntermediateField.adjoin (K₀ κ q) {x} := by
    rw [extendScalars_adjoin hle]
    have h2 : ((jb κ) ^ q : Λκ) = algebraMap (K₀ κ q) Λκ ⟨(jb κ) ^ q, mem_adjoin_simple_self κ _⟩ := rfl
    rw [h2, adjoin_insert_algebraMap]
  have hfr : relfinrank (K₀ κ q) (IntermediateField.adjoin κ {(jb κ) ^ q, x})
      = Module.finrank (K₀ κ q) (IntermediateField.adjoin (K₀ κ q) {x}) := by
    rw [relfinrank_eq_finrank_of_le hle, finrank_congr hext]
  haveI : FiniteDimensional (K₀ κ q) (IntermediateField.adjoin (K₀ κ q) {x}) :=
    Module.finite_of_finrank_pos (by rw [← hfr]; exact hpos)
  have hint : IsIntegral (K₀ κ q) x := by
    have hx : x ∈ IntermediateField.adjoin (K₀ κ q) {x} := mem_adjoin_simple_self _ x
    have h := IsIntegral.of_finite (K₀ κ q) (⟨x, hx⟩ : IntermediateField.adjoin (K₀ κ q) {x})
    exact h.map (IntermediateField.val _)
  exact ⟨hint, by rw [hfr, adjoin.finrank hint]⟩

theorem minpoly_jbN (hqN : ¬ q ∣ N) :
    IsIntegral (K₀ κ q) (jbN κ N) ∧ (minpoly (K₀ κ q) (jbN κ N)).natDegree = q * dedekindPsi N := by
  have h := natDegree_minpoly_K₀ κ q (jbN κ N) (F₁ κ N) (adjoin_jb_pow_jbN_eq κ q N hqN)
    (by rw [relfinrank_K₀_F₁ κ q N hqN]; exact Nat.mul_pos (Fact.out : q.Prime).pos (dedekindPsi_pos N))
  rwa [relfinrank_K₀_F₁ κ q N hqN] at h

theorem minpoly_y₂ (hqN : ¬ q ∣ N) :
    IsIntegral (K₀ κ q) (φ κ q ((jbN κ N) ^ q)) ∧
      (minpoly (K₀ κ q) (φ κ q ((jbN κ N) ^ q))).natDegree = dedekindPsi N := by
  have hmap : (IntermediateField.adjoin κ {jb κ, (jbN κ N) ^ q}).map (φ κ q)
      = IntermediateField.adjoin κ {(jb κ) ^ q, φ κ q ((jbN κ N) ^ q)} := by
    rw [adjoin_map, Set.image_pair, φ_jb]
  have hrel : relfinrank (K₀ κ q) (IntermediateField.adjoin κ {(jb κ) ^ q, φ κ q ((jbN κ N) ^ q)})
      = dedekindPsi N := by
    rw [← hmap, ← K₁_map, relfinrank_map_map, adjoin_jb_jbN_pow_eq κ q N hqN, relfinrank_K₁_F₁ κ q N hqN]
  have h := natDegree_minpoly_K₀ κ q (φ κ q ((jbN κ N) ^ q)) _ rfl (by rw [hrel]; exact dedekindPsi_pos N)
  rwa [hrel] at h

theorem coeff_sum_C_mul_X_pow {K : Type*} [Semiring K] {d : ℕ} (c : Fin d → K) (τ : Fin d) :
    (∑ σ : Fin d, C (c σ) * X ^ (σ : ℕ)).coeff τ = c τ := by
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single τ]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro σ _ hσ
    rw [coeff_C_mul_X_pow, if_neg]
    exact fun h => hσ (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ τ) h

theorem aeval_sum_C_mul_X_pow {K E : Type*} [CommSemiring K] [Semiring E] [Algebra K E] {d : ℕ}
    (c : Fin d → K) (x : E) :
    Polynomial.aeval x (∑ σ : Fin d, C (c σ) * X ^ (σ : ℕ)) = ∑ σ : Fin d, algebraMap K E (c σ) * x ^ (σ : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, aeval_C, map_pow, aeval_X]

theorem residue_independence (hqN : ¬ q ∣ N) {d : ℕ} (hd : d = dedekindPsi N * (q + 1)) (g : Fin d → κ[X])
    (H₁ : ∑ τ, Polynomial.aeval (jb κ) (g τ) * ((jbN κ N) ^ q) ^ (τ : ℕ) = 0)
    (H₂ : ∑ τ, Polynomial.aeval ((jb κ) ^ q) (g τ) * (jbN κ N) ^ (τ : ℕ) = 0) :
    ∀ τ, g τ = 0 := by

  have hcmem : ∀ τ, Polynomial.aeval ((jb κ) ^ q) (g τ) ∈ K₀ κ q := fun τ =>
    (algebra_adjoin_le_adjoin κ _) (Polynomial.aeval_mem_adjoin_singleton κ _)
  let c : Fin d → K₀ κ q := fun τ => ⟨_, hcmem τ⟩
  set G : (K₀ κ q)[X] := ∑ σ : Fin d, C (c σ) * X ^ (σ : ℕ) with hG
  have hcoe : ∀ σ, algebraMap (K₀ κ q) Λκ (c σ) = Polynomial.aeval ((jb κ) ^ q) (g σ) := fun σ => rfl

  have hG₂ : Polynomial.aeval (jbN κ N) G = 0 := by
    rw [hG, aeval_sum_C_mul_X_pow]
    simp only [hcoe]
    exact H₂

  have hG₁ : Polynomial.aeval (φ κ q ((jbN κ N) ^ q)) G = 0 := by
    rw [hG, aeval_sum_C_mul_X_pow]
    simp only [hcoe]
    have := congrArg (φ κ q) H₁
    rw [map_zero, map_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) this
    rw [map_mul, map_pow (φ κ q) ((jbN κ N) ^ q) (σ : ℕ), ← Polynomial.aeval_algHom_apply, φ_jb]

  obtain ⟨hint₂, hdeg₂⟩ := minpoly_jbN κ q N hqN
  obtain ⟨hint₁, hdeg₁⟩ := minpoly_y₂ κ q N hqN
  set m₁ := minpoly (K₀ κ q) (φ κ q ((jbN κ N) ^ q)) with hm₁
  set m₂ := minpoly (K₀ κ q) (jbN κ N) with hm₂
  have hdvd₁ : m₁ ∣ G := minpoly.dvd _ _ hG₁
  have hdvd₂ : m₂ ∣ G := minpoly.dvd _ _ hG₂
  have hirr₁ : Irreducible m₁ := minpoly.irreducible hint₁
  have hirr₂ : Irreducible m₂ := minpoly.irreducible hint₂
  have hψ := dedekindPsi_pos N
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hne : m₁ ≠ m₂ := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hdeg₁, hdeg₂] at this
    nlinarith
  have hcop : IsCoprime m₁ m₂ := by
    rw [hirr₁.coprime_iff_not_dvd]
    intro h
    obtain ⟨u, hu⟩ := h
    rcases hirr₂.isUnit_or_isUnit hu with h1 | h1
    · exact hirr₁.not_isUnit h1
    · apply hne
      exact eq_of_monic_of_associated (minpoly.monic hint₁) (minpoly.monic hint₂) ⟨h1.unit, by rw [hu]; rfl⟩
  have hdvd : m₁ * m₂ ∣ G := hcop.mul_dvd hdvd₁ hdvd₂

  have hG0 : G = 0 := by
    by_contra hG0
    have h1 : (m₁ * m₂).natDegree ≤ G.natDegree := natDegree_le_of_dvd hdvd hG0
    rw [natDegree_mul (minpoly.ne_zero hint₁) (minpoly.ne_zero hint₂), hdeg₁, hdeg₂] at h1
    have h2 : G.degree < d := by rw [hG]; exact degree_sum_fin_lt _
    have h3 : G.natDegree < d := (natDegree_lt_iff_degree_lt hG0).mpr h2
    rw [hd] at h3
    nlinarith

  have htr : Transcendental κ ((jb κ) ^ q) := by
    rw [← φ_jb]
    exact fun h => (ModularCurve.transcendental_jqModC κ)
      ((isAlgebraic_algHom_iff (φ κ q) (φ_injective κ q)).mp h)
  intro τ
  have hc : c τ = 0 := by rw [← coeff_sum_C_mul_X_pow c τ, ← hG, hG0, coeff_zero]
  have hc' : Polynomial.aeval ((jb κ) ^ q) (g τ) = 0 := congrArg Subtype.val hc
  exact (transcendental_iff_injective.mp htr) (by rw [hc', map_zero])

end ResidueSide

section LevelNq

variable (N q : ℕ) [NeZero N] [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Λ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "FF" => modularFunctionFieldBar (N * q)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

abbrev yA (d : ℕ) [NeZero d] : LaurentSeries A := qExpand A d (jqModC A)

omit [NeZero N] [Fact q.Prime] in
theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb ℚ̄ (qExpand ℚ d jq) = qExpand ℚ̄ d (jqModC ℚ̄) := by
  rw [coeffEmb, ← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]

theorem ι_yA (d : ℕ) [NeZero d] : ι A (yA A d) = coeffEmb ℚ̄ (qExpand ℚ d jq) := by
  rw [ι_qExpand_jqModC, coeffEmb_qExpand_jq]

theorem ι_yA' (d : ℕ) [NeZero d] : ι A (yA A d) = qExpand ℚ̄ d (jqModC ℚ̄) := ι_qExpand_jqModC A d

theorem ι_yA_mem {d : ℕ} [NeZero d] (hd : d ∣ N * q) : ι A (yA A d) ∈ FF := by
  rw [ι_yA]; exact coeffEmb_mem_laurentBaseChange _ (jqd_mem_full (N * q) hd)

def gF {d : ℕ} [NeZero d] (hd : d ∣ N * q) : FF := ⟨ι A (yA A d), ι_yA_mem N q A hd⟩

@[scoped simp] theorem coe_gF {d : ℕ} [NeZero d] (hd : d ∣ N * q) : ((gF N q A hd : FF) : Λ) = ι A (yA A d) := rfl

abbrev jF : FF := gF N q A (d := 1) (one_dvd _)

abbrev jqF : FF := gF N q A (d := 1 * q) (mul_dvd_mul_right (one_dvd N) q)

abbrev jNF : FF := gF N q A (d := N) (dvd_mul_right N q)

abbrev yF : FF := gF N q A (d := N * q) dvd_rfl

theorem coe_jF : ((jF N q A : FF) : Λ) = jqModC ℚ̄ := by
  rw [coe_gF, ι_yA', qExpand_one_apply]

theorem coe_yF : ((yF N q A : FF) : Λ) = jqNModC ℚ̄ (N * q) := by
  rw [coe_gF, ι_yA']; rfl

structure Setup where
  R : RegularProlongation A FF Fb
  mem_iff : ∀ f : FF, f ∈ R.integers ↔
    ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ (f : Λ) * ι A y = ι A x
  res_ι : ∀ (y : LaurentSeries A) (hy : ι A y ∈ FF),
    ∃ hint : (⟨ι A y, hy⟩ : FF) ∈ R.integers, ((R.residue ⟨_, hint⟩ : Fb) : LaurentSeries kk) = ϖ A y
  w : FF ≃ₐ[ℚ̄] FF
  w_gF : ∀ (d : ℕ) [NeZero d] (hd : d ∣ N),
    w (gF N q A (dvd_trans hd (dvd_mul_right N q))) = gF N q A (mul_dvd_mul_right hd q)
  w_gF' : ∀ (d : ℕ) [NeZero d] (hd : d ∣ N),
    w (gF N q A (mul_dvd_mul_right hd q)) = gF N q A (dvd_trans hd (dvd_mul_right N q))

theorem nonempty_setup (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) : Nonempty (Setup N q A) := by
  obtain ⟨R, hmem, hres⟩ :=
    ModularCurve.exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd N q hqN A hA
  obtain ⟨w, hw⟩ := ModularCurve.exists_algEquiv_modularFunctionFieldBar_atkinLehner N q Fact.out hqN
  refine ⟨⟨R, hmem, hres, w, fun d _ hd => Subtype.ext ?_, fun d _ hd => Subtype.ext ?_⟩⟩
  · rw [((hw d hd (gF N q A (dvd_trans hd (dvd_mul_right N q)))).1 (ι_yA A d)), coe_gF, ι_yA',
      coeffEmb_qExpand_jq, qExpand_qExpand, qExpand_congr (Nat.mul_comm q d)]
  · rw [coe_gF, ι_yA]
    refine (hw d hd (gF N q A (mul_dvd_mul_right hd q))).2 ?_
    rw [coe_gF, ι_yA', coeffEmb_qExpand_jq, qExpand_qExpand, qExpand_congr (Nat.mul_comm q d)]

variable {N q A}
variable (S : Setup N q A)

abbrev Setup.R₂ : RegularProlongation A FF Fb := transport A S.R S.w

def Setup.fam : Fin 2 → RegularProlongation A FF Fb := ![S.R, S.R₂]

@[scoped simp] theorem Setup.fam_zero : S.fam 0 = S.R := rfl
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B.Setup"
@[scoped simp] theorem Setup.fam_one : S.fam 1 = S.R₂ := rfl

p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B.Setup"
theorem Setup.gF_mem {d : ℕ} [NeZero d] (hd : d ∣ N * q) : gF N q A hd ∈ S.R.integers :=
  (S.res_ι (yA A d) (ι_yA_mem N q A hd)).fst

theorem Setup.res_gF {d : ℕ} [NeZero d] (hd : d ∣ N * q) (h : gF N q A hd ∈ S.R.integers) :
    ((S.R.residue ⟨gF N q A hd, h⟩ : Fb) : LaurentSeries kk) = qExpand kk d (jqModC kk) := by
  obtain ⟨h', e⟩ := S.res_ι (yA A d) (ι_yA_mem N q A hd)
  exact e.trans (ϖ_qExpand_jqModC A d)

theorem Setup.w_jF : S.w (jF N q A) = jqF N q A := S.w_gF 1 (one_dvd N)

theorem Setup.w_yF : S.w (yF N q A) = jNF N q A := S.w_gF' N dvd_rfl

theorem Setup.jF_mem₂ : jF N q A ∈ S.R₂.integers := by
  change S.w (jF N q A) ∈ S.R.integers
  rw [S.w_jF]; exact S.gF_mem _

theorem Setup.yF_mem₂ : yF N q A ∈ S.R₂.integers := by
  change S.w (yF N q A) ∈ S.R.integers
  rw [S.w_yF]; exact S.gF_mem _

theorem Setup.jF_mem_fam : ∀ i, jF N q A ∈ (S.fam i).integers :=
  Fin.forall_fin_two.mpr ⟨S.gF_mem _, S.jF_mem₂⟩

theorem Setup.yF_pow_mem_fam (n : ℕ) : ∀ i, (yF N q A) ^ n ∈ (S.fam i).integers :=
  Fin.forall_fin_two.mpr ⟨pow_mem (S.gF_mem _) n, pow_mem S.yF_mem₂ n⟩

theorem Setup.res₁_jF (h : jF N q A ∈ (S.fam 0).integers) :
    (((S.fam 0).residue ⟨jF N q A, h⟩ : Fb) : LaurentSeries kk) = jb kk := by
  change ((S.R.residue ⟨jF N q A, h⟩ : Fb) : LaurentSeries kk) = _
  rw [S.res_gF _ h, qExpand_one_apply]

theorem Setup.res₁_yF (hA : A.LiesOverPrime q) (h : yF N q A ∈ (S.fam 0).integers) :
    (((S.fam 0).residue ⟨yF N q A, h⟩ : Fb) : LaurentSeries kk) = (jbN kk N) ^ q := by
  haveI := charP_residueField q A hA
  change ((S.R.residue ⟨yF N q A, h⟩ : Fb) : LaurentSeries kk) = _
  rw [S.res_gF _ h, ← qExpand_qExpand, qExpand_jqModC_eq_pow_unconditional kk, map_pow]

theorem Setup.res₂_jF (hA : A.LiesOverPrime q) (h : jF N q A ∈ (S.fam 1).integers) :
    (((S.fam 1).residue ⟨jF N q A, h⟩ : Fb) : LaurentSeries kk) = (jb kk) ^ q := by
  haveI := charP_residueField q A hA
  change ((S.R₂.residue ⟨jF N q A, h⟩ : Fb) : LaurentSeries kk) = _
  have hmem : jqF N q A ∈ S.R.integers := S.gF_mem _
  have h1 : (⟨S.w (jF N q A), h⟩ : S.R.integers) = ⟨jqF N q A, hmem⟩ := Subtype.ext S.w_jF
  rw [transport_residue, h1, S.res_gF _ hmem, qExpand_congr (Nat.one_mul q),
    qExpand_jqModC_eq_pow_unconditional kk]

theorem Setup.res₂_yF (h : yF N q A ∈ (S.fam 1).integers) :
    (((S.fam 1).residue ⟨yF N q A, h⟩ : Fb) : LaurentSeries kk) = jbN kk N := by
  change ((S.R₂.residue ⟨yF N q A, h⟩ : Fb) : LaurentSeries kk) = _
  have hmem : jNF N q A ∈ S.R.integers := S.gF_mem _
  have h1 : (⟨S.w (yF N q A), h⟩ : S.R.integers) = ⟨jNF N q A, hmem⟩ := Subtype.ext S.w_yF
  rw [transport_residue, h1, S.res_gF _ hmem]

theorem Setup.res_yF_pow (i : Fin 2) (n : ℕ) (h : (yF N q A) ^ n ∈ (S.fam i).integers)
    (h1 : yF N q A ∈ (S.fam i).integers) :
    (S.fam i).residue ⟨(yF N q A) ^ n, h⟩ = ((S.fam i).residue ⟨yF N q A, h1⟩) ^ n := by
  rw [← map_pow]; rfl

theorem coe_sum_aeval_mul {d : ℕ} (r : Fb) (z : Fin d → Fb) (p : Fin d → kk[X]) :
    (((∑ τ, Polynomial.aeval r (p τ) * z τ : Fb)) : LaurentSeries kk)
      = ∑ τ, Polynomial.aeval (r : LaurentSeries kk) (p τ) * (z τ : LaurentSeries kk) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [MulMemClass.coe_mul]
  congr 1
  exact (Polynomial.aeval_algHom_apply (IntermediateField.val _) r (p τ)).symm

set_option maxHeartbeats 6400000 in
theorem Setup.uniq (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) {d : ℕ} (hd : d = dedekindPsi N * (q + 1))
    (p p' : Fin d → kk[X])
    (H : ∀ i, ∑ τ, Polynomial.aeval ((S.fam i).residue ⟨jF N q A, S.jF_mem_fam i⟩) (p τ)
        * (S.fam i).residue ⟨(yF N q A) ^ (τ : ℕ), S.yF_pow_mem_fam τ i⟩
      = ∑ τ, Polynomial.aeval ((S.fam i).residue ⟨jF N q A, S.jF_mem_fam i⟩) (p' τ)
        * (S.fam i).residue ⟨(yF N q A) ^ (τ : ℕ), S.yF_pow_mem_fam τ i⟩) :
    p = p' := by
  haveI := charP_residueField q A hA
  have hy : ∀ i, yF N q A ∈ (S.fam i).integers := fun i => by
    have h := S.yF_pow_mem_fam 1 i
    rwa [pow_one] at h

  have key : ∀ i, ∑ τ, Polynomial.aeval (((S.fam i).residue ⟨jF N q A, S.jF_mem_fam i⟩ : Fb) : LaurentSeries kk)
      (p τ - p' τ) * ((((S.fam i).residue ⟨yF N q A, hy i⟩ : Fb) : LaurentSeries kk)) ^ (τ : ℕ) = 0 := by
    intro i
    have h : ((∑ τ, Polynomial.aeval ((S.fam i).residue ⟨jF N q A, S.jF_mem_fam i⟩) (p τ)
        * (S.fam i).residue ⟨(yF N q A) ^ (τ : ℕ), S.yF_pow_mem_fam τ i⟩ : Fb) : LaurentSeries kk)
      = ((∑ τ, Polynomial.aeval ((S.fam i).residue ⟨jF N q A, S.jF_mem_fam i⟩) (p' τ)
        * (S.fam i).residue ⟨(yF N q A) ^ (τ : ℕ), S.yF_pow_mem_fam τ i⟩ : Fb) : LaurentSeries kk) :=
      congrArg Subtype.val (H i)
    rw [coe_sum_aeval_mul, coe_sum_aeval_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h
    refine Eq.trans (Finset.sum_congr rfl fun τ _ => ?_) h
    rw [map_sub, sub_mul, S.res_yF_pow i τ _ (hy i), SubmonoidClass.coe_pow]
  have h0 := key 0
  have h1 := key 1
  rw [Finset.sum_congr rfl fun τ _ => by rw [S.res₁_jF, S.res₁_yF hA]] at h0
  rw [Finset.sum_congr rfl fun τ _ => by rw [S.res₂_jF hA, S.res₂_yF]] at h1
  have := residue_independence kk q N hqN hd (fun τ => p τ - p' τ) h0 h1
  funext τ
  exact sub_eq_zero.mp (this τ)

variable (N q A)

theorem FF_eq_adjoin : (modularFunctionFieldBar (N * q) : IntermediateField ℚ̄ Λ)
    = IntermediateField.adjoin ℚ̄ {jqModC ℚ̄, jqNModC ℚ̄ (N * q)} := by
  change laurentBaseChange ℚ̄ (modularFunctionFieldFull (N * q)) = _
  rw [ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC,
    ← ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero]
  rfl

theorem finrank_adjoin_transport {E E' : IntermediateField ℚ̄ Λ} (h : E = E')
    {x : Λ} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin ℚ̄ ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin ℚ̄ ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

theorem dedekindPsi_mul_eq (hqN : ¬ q ∣ N) : dedekindPsi (N * q) = dedekindPsi N * (q + 1) := by
  rw [dedekindPsi_mul_of_coprime N q ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqN).symm,
    dedekindPsi_prime (Fact.out : q.Prime)]

theorem finrank_adjoin_jF (hqN : ¬ q ∣ N) :
    Module.finrank (IntermediateField.adjoin ℚ̄ {(jF N q A : FF)}) FF = dedekindPsi N * (q + 1) := by
  have heq : (modularFunctionFieldBar (N * q) : IntermediateField ℚ̄ Λ) = modularFunctionFieldFullC ℚ̄ (N * q) :=
    ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℚ̄ (N * q)
  have hj : (jF N q A : FF) = ⟨jqModC ℚ̄, heq ▸ jqModC_mem_full ℚ̄ (N * q)⟩ := Subtype.ext (coe_jF N q A)
  rw [hj, finrank_adjoin_transport heq _ (jqModC_mem_full ℚ̄ (N * q)), ← dedekindPsi_mul_eq N q hqN]
  exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi ℚ̄ (N * q)
    (Nat.cast_ne_zero.mpr (NeZero.ne (N * q)))

theorem adjoin_jF_yF_eq_top :
    IntermediateField.adjoin ℚ̄ {(jF N q A : FF), (yF N q A : FF)} = ⊤ := by
  rw [eq_top_iff]
  intro c _
  set T : IntermediateField ℚ̄ FF := IntermediateField.adjoin ℚ̄ {(jF N q A : FF), (yF N q A : FF)} with hT
  let S' : Subfield Λ := T.toSubfield.map ((modularFunctionFieldBar (N * q)).val : FF →+* Λ)
  have hle : Subfield.closure (Set.range (algebraMap ℚ̄ Λ) ∪ {jqModC ℚ̄, jqNModC ℚ̄ (N * q)}) ≤ S' := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | hz)
    · exact ⟨algebraMap ℚ̄ FF t, T.algebraMap_mem t, rfl⟩
    · rcases hz with rfl | rfl
      · exact ⟨jF N q A, subset_adjoin ℚ̄ _ (Set.mem_insert _ _), coe_jF N q A⟩
      · exact ⟨yF N q A, subset_adjoin ℚ̄ _ (Set.mem_insert_of_mem _ rfl), coe_yF N q A⟩
  have hc : (c : Λ) ∈ IntermediateField.adjoin ℚ̄ {jqModC ℚ̄, jqNModC ℚ̄ (N * q)} := by
    rw [← FF_eq_adjoin]; exact c.2
  obtain ⟨x, hx, hxc⟩ := hle (show (c : Λ) ∈ Subfield.closure _ from hc)
  have : x = c := Subtype.ext hxc
  rwa [← this]

theorem adjoin_yF_eq_top :
    IntermediateField.adjoin (IntermediateField.adjoin ℚ̄ {(jF N q A : FF)}) {(yF N q A : FF)} = ⊤ := by
  apply IntermediateField.restrictScalars_injective ℚ̄
  rw [IntermediateField.restrictScalars_top, adjoin_simple_adjoin_simple, adjoin_jF_yF_eq_top]

theorem exists_coord (hqN : ¬ q ∣ N) (c : FF) :
    ∃ (r : Fin (dedekindPsi N * (q + 1)) → ℚ̄[X]) (D : ℚ̄[X]),
      Polynomial.aeval (jF N q A) D ≠ 0 ∧
      c * Polynomial.aeval (jF N q A) D = ∑ τ, Polynomial.aeval (jF N q A) (r τ) * (yF N q A) ^ (τ : ℕ) := by
  set d := dedekindPsi N * (q + 1) with hd
  set K : IntermediateField ℚ̄ FF := IntermediateField.adjoin ℚ̄ {(jF N q A : FF)} with hK
  have hfin : Module.finrank K FF = d := finrank_adjoin_jF N q A hqN
  have hdpos : 0 < d := Nat.mul_pos (dedekindPsi_pos N) (Nat.succ_pos q)
  haveI : FiniteDimensional K FF := Module.finite_of_finrank_pos (by rw [hfin]; exact hdpos)
  have hint : IsIntegral K (yF N q A) := IsIntegral.of_finite K _
  have htop : IntermediateField.adjoin K {(yF N q A : FF)} = ⊤ := adjoin_yF_eq_top N q A
  have hnat : (minpoly K (yF N q A)).natDegree = d := by
    rw [← adjoin.finrank hint, finrank_congr htop, IntermediateField.finrank_top', hfin]

  have hcmem : c ∈ (IntermediateField.adjoin K {(yF N q A : FF)}).toSubalgebra := by
    rw [htop]; exact IntermediateField.mem_top
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval] at hcmem
  obtain ⟨P, hP⟩ := hcmem
  set P' := P %ₘ minpoly K (yF N q A) with hP'
  have hP'c : Polynomial.aeval (yF N q A) P' = c := by
    rw [hP', aeval_modByMonic_eq_self_of_root (minpoly.aeval K _)]; exact hP
  have hdeg : P'.natDegree < d := by
    by_cases h0 : P' = 0
    · rw [h0, natDegree_zero]; exact hdpos
    · rw [natDegree_lt_iff_degree_lt h0, ← hnat]
      exact lt_of_lt_of_le (degree_modByMonic_lt P (minpoly.monic hint)) (degree_le_natDegree)
  have hsum : c = ∑ i : Fin d, ((P'.coeff i : K) : FF) * (yF N q A) ^ (i : ℕ) := by
    rw [← hP'c, aeval_eq_sum_range' hdeg, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]; rfl

  have hcoef : ∀ i : Fin d, ∃ r s : ℚ̄[X], Polynomial.aeval (jF N q A) s ≠ 0 ∧
      ((P'.coeff i : K) : FF) * Polynomial.aeval (jF N q A) s = Polynomial.aeval (jF N q A) r := by
    intro i
    obtain ⟨r, s, h⟩ := (mem_adjoin_simple_iff ℚ̄ _).mp (P'.coeff i).2
    by_cases hs : Polynomial.aeval (jF N q A) s = 0
    · refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      have : ((P'.coeff i : K) : FF) = 0 := by rw [h, hs, div_zero]
      rw [this, zero_mul, map_zero]
    · exact ⟨r, s, hs, by rw [h, div_mul_cancel₀ _ hs]⟩
  choose r s hs hrs using hcoef
  refine ⟨fun i => r i * ∏ i' ∈ Finset.univ.erase i, s i', ∏ i, s i, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hs i
  · rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_prod, ← Finset.mul_prod_erase Finset.univ (fun i => Polynomial.aeval (jF N q A) (s i))
      (Finset.mem_univ i), map_mul, map_prod, ← hrs i]
    ring

theorem exists_primitive_poly (D : ℚ̄[X]) (hD : D ≠ 0) :
    ∃ e : ℚ̄, e ≠ 0 ∧ ∃ DA : A[X], DA.map (algebraMap A ℚ̄) = C e * D ∧ ∃ i, DA.coeff i = 1 := by
  have hne : D.support.Nonempty := Polynomial.nonempty_support_iff.mpr hD
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image D.support (fun i => A.valuation (D.coeff i)) hne
  set c₀ := D.coeff i₀ with hc₀
  have hc₀0 : c₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hcA : ∀ i, c₀⁻¹ * D.coeff i ∈ A := by
    intro i
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    have hv0 : A.valuation c₀ ≠ 0 := by simpa using hc₀0
    rw [inv_mul_le_one₀ (zero_lt_iff.mpr hv0)]
    by_cases hi : i ∈ D.support
    · exact hmax i hi
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero]; exact zero_le'
  refine ⟨c₀⁻¹, inv_ne_zero hc₀0, ?_⟩
  have hlift : C c₀⁻¹ * D ∈ Polynomial.lifts (algebraMap A ℚ̄) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    exact ⟨⟨_, hcA n⟩, rfl⟩
  obtain ⟨DA, hDA⟩ := (Polynomial.mem_lifts _).mp hlift
  refine ⟨DA, hDA, i₀, ?_⟩
  have h := congrArg (fun P : ℚ̄[X] => P.coeff i₀) hDA
  simp only [coeff_map, coeff_C_mul] at h
  rw [← hc₀, inv_mul_cancel₀ hc₀0] at h
  exact Subtype.ext h

theorem transcendental_qExpand_jb (K : Type*) [Field K] (d : ℕ) [NeZero d] :
    Transcendental K (qExpand K d (jqModC K)) := fun h =>
  (ModularCurve.transcendental_jqModC K) ((isAlgebraic_algHom_iff (qExpandAlgHomC K d)
    (qExpand_injective (R := K) (N := d))).mp h)

abbrev polyA (P : A[X]) (d : ℕ) [NeZero d] : LaurentSeries A := P.eval₂ HahnSeries.C (yA A d)

theorem ι_polyA (P : A[X]) (d : ℕ) [NeZero d] :
    ι A (polyA A P d) = Polynomial.aeval (ι A (yA A d)) (P.map (algebraMap A ℚ̄)) := by
  rw [Polynomial.aeval_def, ι_eval₂]

theorem ϖ_polyA (P : A[X]) (d : ℕ) [NeZero d] :
    ϖ A (polyA A P d) = Polynomial.aeval (qExpand kk d (jqModC kk)) (P.map (IsLocalRing.residue A)) := by
  rw [Polynomial.aeval_def, ϖ_eval₂, ϖ_qExpand_jqModC]

theorem coe_aeval (x : FF) (P : ℚ̄[X]) : ((Polynomial.aeval x P : FF) : Λ) = Polynomial.aeval (x : Λ) P :=
  (Polynomial.aeval_algHom_apply (IntermediateField.val _) x P).symm

theorem aeval_gF_eq (P : A[X]) {d : ℕ} [NeZero d] (hd : d ∣ N * q) :
    ∃ hmem : ι A (polyA A P d) ∈ FF,
      (Polynomial.aeval (gF N q A hd) (P.map (algebraMap A ℚ̄)) : FF) = ⟨ι A (polyA A P d), hmem⟩ := by
  have hcoe : ((Polynomial.aeval (gF N q A hd) (P.map (algebraMap A ℚ̄)) : FF) : Λ) = ι A (polyA A P d) := by
    rw [coe_aeval, ι_polyA]; rfl
  exact ⟨hcoe ▸ SetLike.coe_mem _, Subtype.ext hcoe⟩

theorem map_residue_ne_zero {P : A[X]} (hP : ∃ i, P.coeff i = 1) : P.map (IsLocalRing.residue A) ≠ 0 := by
  obtain ⟨i, hi⟩ := hP
  intro h
  have := congrArg (fun Q => Polynomial.coeff Q i) h
  simp only [coeff_map, hi, map_one, coeff_zero] at this
  exact one_ne_zero this

variable {N q A}

theorem Setup.aeval_gF_mem_ne (P : A[X]) (hP : ∃ i, P.coeff i = 1) {d : ℕ} [NeZero d] (hd : d ∣ N * q) :
    ∃ h : Polynomial.aeval (gF N q A hd) (P.map (algebraMap A ℚ̄)) ∈ S.R.integers,
      S.R.residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨hmem, heq⟩ := aeval_gF_eq N q A P hd
  obtain ⟨hint, hres⟩ := S.res_ι (polyA A P d) hmem
  rw [heq]
  refine ⟨hint, fun h0 => ?_⟩
  have h1 : ((S.R.residue ⟨⟨ι A (polyA A P d), hmem⟩, hint⟩ : Fb) : LaurentSeries kk) = 0 := by
    rw [h0]; rfl
  rw [hres, ϖ_polyA] at h1
  exact (map_residue_ne_zero A hP)
    ((transcendental_iff_injective.mp (transcendental_qExpand_jb kk d)) (by rw [h1, map_zero]))

theorem Setup.aeval_jF_mem_fam (P : A[X]) (hP : ∃ i, P.coeff i = 1) :
    ∀ i, ∃ h : Polynomial.aeval (jF N q A) (P.map (algebraMap A ℚ̄)) ∈ (S.fam i).integers,
      (S.fam i).residue ⟨_, h⟩ ≠ 0 := by
  refine Fin.forall_fin_two.mpr ⟨S.aeval_gF_mem_ne P hP _, ?_⟩
  obtain ⟨h, hne⟩ := S.aeval_gF_mem_ne P hP (d := 1 * q) (mul_dvd_mul_right (one_dvd N) q)
  have hw : S.w (Polynomial.aeval (jF N q A) (P.map (algebraMap A ℚ̄)))
      = Polynomial.aeval (jqF N q A) (P.map (algebraMap A ℚ̄)) := by
    rw [← Polynomial.aeval_algHom_apply, S.w_jF]
  have hmem : Polynomial.aeval (jF N q A) (P.map (algebraMap A ℚ̄)) ∈ (S.fam 1).integers := by
    change S.w _ ∈ S.R.integers; rw [hw]; exact h
  refine ⟨hmem, ?_⟩
  change S.R.residue ⟨S.w _, hmem⟩ ≠ 0
  have h1 : (⟨S.w (Polynomial.aeval (jF N q A) (P.map (algebraMap A ℚ̄))), hmem⟩ : S.R.integers) = ⟨_, h⟩ :=
    Subtype.ext hw
  rw [h1]; exact hne

set_option maxHeartbeats 6400000 in

theorem Setup.coeff_mem (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q)
    (r : Fin (dedekindPsi N * (q + 1)) → ℚ̄[X])
    (hsum : ∀ i, ∑ τ, Polynomial.aeval (jF N q A) (r τ) * (yF N q A) ^ (τ : ℕ) ∈ (S.fam i).integers) :
    ∀ τ n, (r τ).coeff n ∈ A :=
  AlgebraicCurve.RegularProlongation.coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr A
    (fun _ : Fin 2 => (Fb : Type _)) S.fam (jF N q A) S.jF_mem_fam (dedekindPsi N * (q + 1))
    (fun τ => (yF N q A) ^ (τ : ℕ)) (fun τ i => S.yF_pow_mem_fam τ i) (S.uniq hqN hA rfl) r hsum

section Presentation

variable {k : Type*} [Field k] [CharP k q] (red : A →+* k)

local notation "MR" => CharPReduction.modularRing (N * q) A.toSubring
local notation "ML" => CharPReduction.modularLocalized (N * q) A.toSubring red

theorem algebraMap_mem_MR (a : ℚ̄) (ha : a ∈ A) : algebraMap ℚ̄ Λ a ∈ MR :=
  CharPReduction.constSeries_mem_modularRing (N * q) A.toSubring ⟨a, ha⟩

theorem aeval_jqModC_mem_MR (P : ℚ̄[X]) (hP : ∀ n, P.coeff n ∈ A) : Polynomial.aeval (jqModC ℚ̄) P ∈ MR := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun n _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (algebraMap_mem_MR (P.coeff n) (hP n))
    (Subring.pow_mem _ (CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring) n)

theorem MR_le_FF : ∀ x ∈ MR, x ∈ FF := by
  intro x hx
  refine (Subring.closure_le.mpr ?_) hx
  rintro z (⟨a, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar (N * q)).algebraMap_mem (a : ℚ̄)
  · rw [← coe_jF N q A]; exact SetLike.coe_mem _
  · rw [← coe_yF N q A]; exact SetLike.coe_mem _

theorem exists_ι_eq_of_mem_MR {x : Λ} (hx : x ∈ MR) : ∃ x₀ : LaurentSeries A, ι A x₀ = x :=
  exists_ι_eq A x (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring hx)

theorem notMem_redKer_iff_ϖ (s₀ : LaurentSeries A) (hs : ι A s₀ ∈ MR) :
    (⟨ι A s₀, hs⟩ : MR) ∉ CharPReduction.redKer A.toSubring red MR
        (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring) ↔ ϖ A s₀ ≠ 0 := by
  rw [CharPReduction.notMem_redKer_iff, ϖ_ne_zero_iff]
  constructor
  · intro h
    by_contra hall
    push Not at hall
    apply h
    ext n
    rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_zero]
    exact red_eq_zero_of_mem_maximalIdeal q A red (a := s₀.coeff n) (hall n)
  · rintro ⟨n, hn⟩ h0
    have h1 := congrArg (fun z : LaurentSeries k => z.coeff n) h0
    simp only [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_zero] at h1
    exact ((red_ne_zero_iff q A red (s₀.coeff n)).mpr hn) h1

theorem notMem_redKer_iff_ϖ' (s : MR) (s₀ : LaurentSeries A) (hs₀ : ι A s₀ = s) :
    s ∉ CharPReduction.redKer A.toSubring red MR
        (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring) ↔ ϖ A s₀ ≠ 0 := by
  obtain ⟨s, hs⟩ := s
  simp only at hs₀
  subst hs₀
  exact notMem_redKer_iff_ϖ red s₀ hs

set_option maxHeartbeats 3200000 in

theorem Setup.coe_mem_ML_of_mem_inter (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) (c : FF)
    (h₁ : c ∈ S.R.integers) (h₂ : c ∈ S.R₂.integers) : (c : Λ) ∈ ML := by

  obtain ⟨r, D, hD, hcD⟩ := exists_coord N q A hqN c
  have hD0 : D ≠ 0 := by rintro rfl; exact hD (map_zero _)
  obtain ⟨e, he, DA, hDA, hprim⟩ := exists_primitive_poly A D hD0
  set r' : Fin (dedekindPsi N * (q + 1)) → ℚ̄[X] := fun τ => C e * r τ with hr'
  set DF : FF := Polynomial.aeval (jF N q A) (DA.map (algebraMap A ℚ̄)) with hDF
  have hcD' : c * DF = ∑ τ, Polynomial.aeval (jF N q A) (r' τ) * (yF N q A) ^ (τ : ℕ) := by
    rw [hDF, hDA, map_mul, aeval_C, ← mul_assoc, mul_comm c, mul_assoc, hcD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hr', map_mul, aeval_C, mul_assoc]

  have hDmem := S.aeval_jF_mem_fam DA hprim
  have hcmem : ∀ i, c ∈ (S.fam i).integers := Fin.forall_fin_two.mpr ⟨h₁, h₂⟩
  have hsum : ∀ i, ∑ τ, Polynomial.aeval (jF N q A) (r' τ) * (yF N q A) ^ (τ : ℕ) ∈ (S.fam i).integers := by
    intro i
    rw [← hcD']
    exact mul_mem (hcmem i) (hDmem i).fst
  have hcoef := S.coeff_mem hqN hA r' hsum

  have hnum : ((∑ τ, Polynomial.aeval (jF N q A) (r' τ) * (yF N q A) ^ (τ : ℕ) : FF) : Λ) ∈ MR := by
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Subring.sum_mem _ fun τ _ => ?_
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_aeval, coe_yF]
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ (CharPReduction.jqNModC_mem_modularRing (N * q) A.toSubring) _)
    rw [coe_jF]
    exact aeval_jqModC_mem_MR (r' τ) (hcoef τ)
  have hden : ((DF : FF) : Λ) ∈ MR := by
    rw [hDF, coe_aeval, coe_jF]
    refine aeval_jqModC_mem_MR _ fun n => ?_
    rw [coeff_map]; exact SetLike.coe_mem _

  obtain ⟨hmemF, heqF⟩ := aeval_gF_eq N q A DA (d := 1) (one_dvd _)
  have hden' : ι A (polyA A DA 1) ∈ MR := by
    have : ((DF : FF) : Λ) = ι A (polyA A DA 1) := by rw [hDF, heqF]
    rwa [this] at hden
  have hϖ : ϖ A (polyA A DA 1) ≠ 0 := by
    rw [ϖ_polyA]
    exact fun h0 => (map_residue_ne_zero A hprim)
      ((transcendental_iff_injective.mp (transcendental_qExpand_jb kk 1)) (by rw [h0, map_zero]))
  refine ⟨⟨_, hnum⟩, ⟨ι A (polyA A DA 1), hden'⟩, (notMem_redKer_iff_ϖ red _ hden').mpr hϖ, ?_⟩
  change (c : Λ) * ι A (polyA A DA 1) = ((∑ τ, Polynomial.aeval (jF N q A) (r' τ) * (yF N q A) ^ (τ : ℕ) : FF) : Λ)
  rw [← hcD', MulMemClass.coe_mul, hDF, heqF]

set_option maxHeartbeats 3200000 in

theorem Setup.coe_mem_ML_of_residue_ne_zero (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) (g : FF)
    (h₁ : g ∈ S.R.integers) (hres : S.R.residue ⟨g, h₁⟩ ≠ 0) (h₂ : g ∉ S.R₂.integers) :
    (g : Λ) ∈ ML := by
  have hg0 : g ≠ 0 := by rintro rfl; exact h₂ (zero_mem _)

  obtain ⟨u, hu⟩ := S.R.isUnit_of_residue_ne_zero hres
  have hinv₁ : g⁻¹ ∈ S.R.integers := by
    have hmul : ((↑u⁻¹ : S.R.integers) : FF) * g = 1 := by
      have h := congrArg (fun y : S.R.integers => (y : FF)) u.inv_mul
      beta_reduce at h
      rw [hu] at h
      exact h
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  have hinv₂ : g⁻¹ ∈ S.R₂.integers := (S.R₂.integers.mem_or_inv_mem g).resolve_left h₂
  obtain ⟨r, s, hs, hrs⟩ := S.coe_mem_ML_of_mem_inter red hqN hA g⁻¹ hinv₁ hinv₂

  obtain ⟨r₀, hr₀⟩ := exists_ι_eq_of_mem_MR (N := N) (q := q) r.2
  obtain ⟨s₀, hs₀⟩ := exists_ι_eq_of_mem_MR (N := N) (q := q) s.2
  have hsF : ι A s₀ ∈ FF := by rw [hs₀]; exact MR_le_FF _ s.2
  have hrF : ι A r₀ ∈ FF := by rw [hr₀]; exact MR_le_FF _ r.2
  obtain ⟨hsint, hsres⟩ := S.res_ι s₀ hsF
  obtain ⟨hrint, hrres⟩ := S.res_ι r₀ hrF
  have hϖs : ϖ A s₀ ≠ 0 := (notMem_redKer_iff_ϖ' red s s₀ hs₀).mp hs
  have hsunit : IsUnit (⟨⟨ι A s₀, hsF⟩, hsint⟩ : S.R.integers) := by
    refine S.R.isUnit_of_residue_ne_zero fun h0 => hϖs ?_
    rw [← hsres, h0]; rfl
  have hginv_unit : IsUnit (⟨g⁻¹, hinv₁⟩ : S.R.integers) :=
    ⟨⟨⟨g⁻¹, hinv₁⟩, ⟨g, h₁⟩, Subtype.ext (inv_mul_cancel₀ hg0), Subtype.ext (mul_inv_cancel₀ hg0)⟩, rfl⟩
  have hreq : (⟨⟨ι A r₀, hrF⟩, hrint⟩ : S.R.integers) = ⟨g⁻¹, hinv₁⟩ * ⟨⟨ι A s₀, hsF⟩, hsint⟩ := by
    apply Subtype.ext; apply Subtype.ext
    change ι A r₀ = ((g⁻¹ : FF) : Λ) * ι A s₀
    rw [hr₀, hs₀, IntermediateField.coe_inv]; exact hrs.symm
  have hrunit : IsUnit (⟨⟨ι A r₀, hrF⟩, hrint⟩ : S.R.integers) := by
    rw [hreq]; exact hginv_unit.mul hsunit
  have hϖr : ϖ A r₀ ≠ 0 := by
    rw [← hrres]
    intro h0
    exact S.R.residue_ne_zero_of_isUnit hrunit (Subtype.ext (by rw [h0]; rfl))
  refine ⟨s, r, (notMem_redKer_iff_ϖ' red r r₀ hr₀).mpr hϖr, ?_⟩
  have hg' : (g : Λ) ≠ 0 := fun h => hg0 (Subtype.ext h)
  calc (g : Λ) * (r : Λ) = (g : Λ) * ((g⁻¹ : FF) : Λ) * (s : Λ) := by rw [← hrs]; ring
    _ = (s : Λ) := by rw [IntermediateField.coe_inv, mul_inv_cancel₀ hg', one_mul]

set_option maxHeartbeats 3200000 in

theorem Setup.coe_mem_ML (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) (f : FF) (h₁ : f ∈ S.R.integers) :
    (f : Λ) ∈ ML := by
  by_cases h₂ : f ∈ S.R₂.integers
  · exact S.coe_mem_ML_of_mem_inter red hqN hA f h₁ h₂
  by_cases hres : S.R.residue ⟨f, h₁⟩ = 0
  ·
    have hg₁ : 1 + f ∈ S.R.integers := add_mem (one_mem _) h₁
    have hgres : S.R.residue ⟨1 + f, hg₁⟩ ≠ 0 := by
      have : (⟨1 + f, hg₁⟩ : S.R.integers) = 1 + ⟨f, h₁⟩ := Subtype.ext rfl
      rw [this, map_add, map_one, hres, add_zero]; exact one_ne_zero
    have hg₂ : 1 + f ∉ S.R₂.integers := fun h => h₂ (by
      have h' := sub_mem h (one_mem S.R₂.integers)
      rwa [add_sub_cancel_left] at h')
    have h := S.coe_mem_ML_of_residue_ne_zero red hqN hA (1 + f) hg₁ hgres hg₂
    have : (f : Λ) = ((1 + f : FF) : Λ) - 1 := by rw [AddMemClass.coe_add, OneMemClass.coe_one]; ring
    rw [this]
    exact sub_mem h (one_mem _)
  · exact S.coe_mem_ML_of_residue_ne_zero red hqN hA f h₁ hres h₂

theorem isInt_of_coe_mem_ML (f : FF) (hf : (f : Λ) ∈ ML) :
    ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ (f : Λ) * ι A y = ι A x := by
  obtain ⟨r, s, hs, hrs⟩ := hf
  obtain ⟨r₀, hr₀⟩ := exists_ι_eq_of_mem_MR (N := N) (q := q) r.2
  obtain ⟨s₀, hs₀⟩ := exists_ι_eq_of_mem_MR (N := N) (q := q) s.2
  refine ⟨r₀, s₀, (notMem_redKer_iff_ϖ' red s s₀ hs₀).mp hs, ?_⟩
  rw [hr₀, hs₀]; exact hrs

end Presentation
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B.Setup"

theorem main {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N) (f : FF) :
    (∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ (f : Λ) * ι A y = ι A x) ↔
      (f : Λ) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
  have hA : A.LiesOverPrime q := liesOverPrime_of_red q A red
  obtain ⟨S⟩ := nonempty_setup N q A hqN hA
  constructor
  · intro hf
    exact S.coe_mem_ML red hqN hA f ((S.mem_iff f).mpr hf)
  · exact isInt_of_coe_mem_ML red f

end LevelNq
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B.Setup"

end W7B0B
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B.Setup P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B"

open W7B0B in
theorem solution (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (f : ModularCurve.modularFunctionFieldBar (N * q)) :
    (∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y
          = ModularCurve.coeffMap A.subtype x) ↔
      (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
        ModularCurve.CharPReduction.modularLocalized (N * q) A.toSubring red :=
  W7B0B.main red hqN f

end
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B.Setup P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd.W7B0B"

end S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd (solution)
