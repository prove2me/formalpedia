-- Prove2me | solution 1 for ModularCurve.exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ed64fb57-692e-552b-acbd-d49f37b68052

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
p2m_open "IntermediateField AlgebraicCurve ModularCurve~coeffEmb_jq~coeffEmb_qExpand Polynomial"

namespace NeronLeg1TwoBranches

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

theorem ι_qExpand_jqModC (d : ℕ) [NeZero d] :
    ι A (qExpand A d (jqModC A)) = qExpand L d (jqModC L) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem ϖ_qExpand_jqModC (d : ℕ) [NeZero d] :
    ϖ A (qExpand A d (jqModC A)) = qExpand (IsLocalRing.ResidueField A) d
      (jqModC (IsLocalRing.ResidueField A)) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

end Coeff

section Gens

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull M)

theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem coeffEmb_jq : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]; exact coeffMap_jqModC _

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  rw [coeffEmb_qExpand, coeffEmb_jq]

def jF : FF := ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (modularFunctionField_le_full M (jq_mem M))⟩

@[scoped simp] theorem coe_jF : ((jF L M : FF) : LaurentSeries L) = jqModC L := coeffEmb_jq L

def jdF (d : ℕ) [NeZero d] (hd : d ∣ M) : FF :=
  ⟨coeffEmb L (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange L (jqd_mem_full M hd)⟩

@[scoped simp] theorem coe_jdF (d : ℕ) [NeZero d] (hd : d ∣ M) :
    ((jdF L M d hd : FF) : LaurentSeries L) = qExpand L d (jqModC L) := coeffEmb_qExpand_jq L d

theorem finrank_adjoin_transport {E E' : IntermediateField L (LaurentSeries L)} (h : E = E')
    {x : LaurentSeries L} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin L ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin L ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

theorem finrank_adjoin_jF (hM : (M : L) ≠ 0) :
    Module.finrank (IntermediateField.adjoin L {(jF L M : FF)}) FF = dedekindPsi M := by
  have heq := ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC L M
  have hj : (jF L M : FF) = ⟨jqModC L, heq ▸ jqModC_mem_full L M⟩ := Subtype.ext (coe_jF L M)
  rw [hj, finrank_adjoin_transport L heq _ (jqModC_mem_full L M)]
  exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi L M hM

theorem dedekindPsi_pos : 0 < dedekindPsi M := by
  have h1 : (1 : ℕ) ∈ M.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne M]
  calc 0 < M / 1 := by simpa using Nat.pos_of_ne_zero (NeZero.ne M)
    _ ≤ dedekindPsi M := Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1

end Gens

section Orders

variable (K : Type*) [Field K]

theorem coeff_order_ne_zero' {x : LaurentSeries K} (hx : x ≠ 0) : x.coeff x.order ≠ 0 :=
  fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)

theorem order_jqModC_pow (b : ℕ) : ((jqModC K) ^ b).order = -(b : ℤ) := by
  have h1 : ((jqModC K) ^ b).coeff (-(b : ℤ)) ≠ 0 := by
    rw [coeff_jqModC_pow_self]; exact one_ne_zero
  have hne : (jqModC K) ^ b ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push Not at hlt
  exact coeff_order_ne_zero' K hne (coeff_jqModC_pow_of_lt K hlt)

theorem jqModC_pow_ne_zero (b : ℕ) : (jqModC K) ^ b ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (by rw [coeff_jqModC_pow_self]; exact one_ne_zero)

variable (p : ℕ) [Fact p.Prime]

theorem order_qExpand {x : LaurentSeries K} (hx : x ≠ 0) :
    (qExpand K p x).order = (p : ℤ) * x.order := by
  have hq0 : qExpand K p x ≠ 0 := fun h => hx (qExpand_injective (R := K) (N := p) (by rw [h, map_zero]))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [qExpand_coeff_mul]; exact coeff_order_ne_zero' K hx
  · by_contra hlt
    push Not at hlt
    have hc := coeff_order_ne_zero' K hq0
    by_cases hdvd : (p : ℤ) ∣ (qExpand K p x).order
    · obtain ⟨k, hk⟩ := hdvd
      rw [hk, qExpand_coeff_mul] at hc
      have hle := HahnSeries.order_le_of_coeff_ne_zero hc
      rw [hk] at hlt
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      nlinarith
    · exact hc (qExpand_coeff_of_not_dvd p x hdvd)

theorem eq_zero_of_sum_eq_zero_of_order_injOn {ι : Type*} [Fintype ι] (t : ι → LaurentSeries K)
    (hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → (t i).order = (t j).order → i = j)
    (hsum : ∑ i, t i = 0) : ∀ i, t i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  set s : Finset ι := Finset.univ.filter fun i => t i ≠ 0 with hs
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
  exact coeff_order_ne_zero' K hi₀ hcoeff.symm

variable [CharP K p]

theorem adjoin_pow_le :
    IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))
      ≤ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
    (pow_mem (mem_adjoin_simple_self K (jqModC K)) p))

theorem exists_qExpand_eq_of_mem_adjoin_pow {c : LaurentSeries K}
    (hc : c ∈ IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))) :
    ∃ d : LaurentSeries K, qExpand K p d = c := by
  have hle : Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ {(jqModC K) ^ p})
      ≤ (qExpand K p).fieldRange := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | rfl)
    · refine ⟨algebraMap K (LaurentSeries K) t, ?_⟩
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
    · exact ⟨jqModC K, qExpand_jqModC_eq_pow_unconditional K⟩
  obtain ⟨d, hd⟩ := hle (show c ∈ Subfield.closure _ from hc)
  exact ⟨d, hd⟩

theorem le_finrank_adjoin_pow
    [Module.Finite (IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)))
      (extendScalars (adjoin_pow_le K p))] :
    p ≤ Module.finrank (IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)))
      (extendScalars (adjoin_pow_le K p)) := by
  set K₀ := IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)) with hK₀
  let v : Fin p → extendScalars (adjoin_pow_le K p) := fun i =>
    ⟨(jqModC K) ^ (i : ℕ), (mem_extendScalars _).mpr
      (pow_mem (mem_adjoin_simple_self K (jqModC K)) _)⟩
  have hli : LinearIndependent K₀ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : ∑ i, ((g i : K₀) : LaurentSeries K) * (jqModC K) ^ (i : ℕ) = 0 := by
      have := congrArg (fun z : extendScalars (adjoin_pow_le K p) => (z : LaurentSeries K)) hg
      first
        | simpa only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] using this
        | simpa only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, v, SetLike.val_smul,
            IntermediateField.coe_smul, IntermediateField.smul_def, Algebra.smul_def, smul_eq_mul] using this
        | (simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at this;
           simpa [v, Algebra.smul_def] using this)
    have hd : ∀ i, ∃ d : LaurentSeries K, qExpand K p d = ((g i : K₀) : LaurentSeries K) :=
      fun i => exists_qExpand_eq_of_mem_adjoin_pow K p (g i).2
    choose d hd using hd
    have hall := eq_zero_of_sum_eq_zero_of_order_injOn K
      (fun i : Fin p => ((g i : K₀) : LaurentSeries K) * (jqModC K) ^ (i : ℕ)) ?_ hsum
    · have hi := hall i
      rcases mul_eq_zero.mp hi with h0 | h0
      · exact Subtype.ext (by simpa using h0)
      · exact absurd h0 (jqModC_pow_ne_zero K _)
    · intro i j hi hj hij
      have hgi : ((g i : K₀) : LaurentSeries K) ≠ 0 := left_ne_zero_of_mul hi
      have hgj : ((g j : K₀) : LaurentSeries K) ≠ 0 := left_ne_zero_of_mul hj
      have hdi : d i ≠ 0 := by rintro h; apply hgi; rw [← hd i, h, map_zero]
      have hdj : d j ≠ 0 := by rintro h; apply hgj; rw [← hd j, h, map_zero]
      beta_reduce at hij
      rw [HahnSeries.order_mul hgi (jqModC_pow_ne_zero K _),
        HahnSeries.order_mul hgj (jqModC_pow_ne_zero K _), ← hd i, ← hd j,
        order_qExpand K p hdi, order_qExpand K p hdj, order_jqModC_pow, order_jqModC_pow] at hij
      have hdvd : (p : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) :=
        ⟨(d j).order - (d i).order, by linarith⟩
      have habs : |((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)| < p := by
        rw [abs_sub_lt_iff]; constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact Fin.ext (by omega)
  simpa using hli.fintype_card_le_finrank

end Orders

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

theorem transport_residue_apply (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (f : F) (h₁ : f ∈ (transport A R w).integers) (h₀ : w f ∈ R.integers) :
    (transport A R w).residue ⟨f, h₁⟩ = R.residue ⟨w f, h₀⟩ := rfl

theorem residue_div (R : RegularProlongation A F Fb) {a b : F} (ha : a ∈ R.integers)
    (hb : b ∈ R.integers) (hbr : R.residue ⟨b, hb⟩ ≠ 0) :
    ∃ h : a / b ∈ R.integers, R.residue ⟨a / b, h⟩ = R.residue ⟨a, ha⟩ / R.residue ⟨b, hb⟩ := by
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hbr
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hbr
    have : (⟨(0 : F), hb⟩ : R.integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  have hinv : b⁻¹ ∈ R.integers := by
    have hmul : ((↑u⁻¹ : R.integers) : F) * b = 1 := by
      have := congrArg (fun y : R.integers => (y : F)) u.inv_mul
      simpa [hu] using this
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  have hmem : a / b ∈ R.integers := by rw [div_eq_mul_inv]; exact mul_mem ha hinv
  refine ⟨hmem, ?_⟩
  rw [eq_div_iff hbr, ← map_mul]
  congr 1
  exact Subtype.ext (div_mul_cancel₀ a hb0)

end Transport

section TwoProlongations

variable (N p : ℕ) [NeZero N] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * p))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem charP_kk (hA : A.LiesOverPrime p) : CharP kk p :=
  ValuationSubring.charP_residueField_of_liesOverPrime p A hA

theorem natCast_residueField_ne_zero (hA : A.LiesOverPrime p) {m : ℕ}
    (hm : ¬ p ∣ m) : (m : IsLocalRing.ResidueField A) ≠ 0 := by
  intro h0
  have hℓ : ((p : A) : ℚ̄) ∈ A.nonunits := by first | exact hA | simpa [ValuationSubring.LiesOverPrime] using hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have hmA : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact h0
  have hcop : IsCoprime (p : A) (m : A) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓ) (Ideal.mul_mem_left _ _ hmA)

theorem atkinLehner_swap (hpN : ¬ p ∣ N) :
    geomAut ℚ̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p) (jF ℚ̄ (N * p))
        = jdF ℚ̄ (N * p) p (dvd_mul_left p N) ∧
      geomAut ℚ̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p)
        (jdF ℚ̄ (N * p) p (dvd_mul_left p N)) = jF ℚ̄ (N * p) := by
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  obtain ⟨h1, h2⟩ := hσ 1 inferInstance (one_dvd N)
  set f1 : modularFunctionFieldFull (N * p) :=
    ⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ with hf1
  set fp : modularFunctionFieldFull (N * p) :=
    ⟨qExpand ℚ (1 * p) jq, jqd_mem_full (N * p) (Nat.mul_dvd_mul_right (one_dvd N) p)⟩ with hfp
  have hjF : jF ℚ̄ (N * p) = ⟨coeffEmb ℚ̄ (f1 : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange ℚ̄ f1.2⟩ :=
    Subtype.ext (by change coeffEmb ℚ̄ jq = coeffEmb ℚ̄ (qExpand ℚ 1 jq); rw [qExpand_one_apply])
  have hjdF : jdF ℚ̄ (N * p) p (dvd_mul_left p N) = ⟨coeffEmb ℚ̄ (fp : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange ℚ̄ fp.2⟩ :=
    Subtype.ext (by
      change coeffEmb ℚ̄ (qExpand ℚ p jq) = coeffEmb ℚ̄ (qExpand ℚ (1 * p) jq)
      rw [qExpand_congr (one_mul p)])
  refine ⟨?_, ?_⟩
  · rw [hjF, hjdF, geomAut_coeffEmb]
    exact Subtype.ext (congrArg (fun y : modularFunctionFieldFull (N * p) =>
      coeffEmb ℚ̄ (y : LaurentSeries ℚ)) h1)
  · rw [hjF, hjdF, geomAut_coeffEmb]
    exact Subtype.ext (congrArg (fun y : modularFunctionFieldFull (N * p) =>
      coeffEmb ℚ̄ (y : LaurentSeries ℚ)) h2)

variable {N p A}

theorem finrank_adjoin_eq_relfinrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (x : K) :
    Module.finrank (IntermediateField.adjoin F ({x} : Set K)) K =
      IntermediateField.relfinrank (IntermediateField.adjoin F ({(x : E)} : Set E)) K := by
  have h1 := IntermediateField.relfinrank_map_map (IntermediateField.adjoin F ({x} : Set K)) ⊤ K.val
  rw [IntermediateField.relfinrank_top_right] at h1
  rw [← h1]
  change IntermediateField.relfinrank (IntermediateField.lift _) (IntermediateField.lift _) = _
  rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]

set_option maxHeartbeats 12800000 in

theorem main_of_gauss (hpN : ¬ p ∣ N) (hA : A.LiesOverPrime p)
    (R₀ : RegularProlongation A FF Fb)
    (hres : ∀ (y : LaurentSeries A) (hy : ι A y ∈ FF),
        ∃ hint : (⟨ι A y, hy⟩ : FF) ∈ R₀.integers,
          ((R₀.residue ⟨_, hint⟩ : Fb) : LaurentSeries kk) = ϖ A y) :
    let w := geomAut ℚ̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p)
    let R₁ := transport A R₀ w
    R₀.integers ≠ R₁.integers ∧
    ∃ (hj₀ : jF ℚ̄ (N * p) ∈ R₀.integers) (hj₁ : jF ℚ̄ (N * p) ∈ R₁.integers),
      ((R₀.residue ⟨_, hj₀⟩ : Fb) : LaurentSeries kk) = jqModC kk ∧
      ((R₁.residue ⟨_, hj₁⟩ : Fb) : LaurentSeries kk) = jqModC kk ^ p ∧
      Module.finrank (IntermediateField.adjoin kk {R₀.residue ⟨_, hj₀⟩}) Fb = dedekindPsi N ∧
      Module.finrank (IntermediateField.adjoin kk {R₁.residue ⟨_, hj₁⟩}) Fb = p * dedekindPsi N ∧
      Module.finrank (IntermediateField.adjoin ℚ̄ {(jF ℚ̄ (N * p) : FF)}) FF
        = (p + 1) * dedekindPsi N ∧
      ∀ V : ValuationSubring FF,
        (∀ e ∈ IntermediateField.adjoin ℚ̄ {(jF ℚ̄ (N * p) : FF)}, e ∈ V ↔ e ∈ R₀.integers) →
        V = R₀.integers ∨ V = R₁.integers := by
  intro w R₁
  haveI := charP_kk (A := A) (p := p) hA
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hjk : (jqModC kk) ≠ 0 := jqModC_ne_zero_of_nontrivial kk
  obtain ⟨hw₁, hw₂⟩ := atkinLehner_swap N p hpN

  have hjmemF : ι A (jqModC A) ∈ FF := by
    rw [coeffMap_jqModC, ← coe_jF ℚ̄ (N * p)]; exact (jF ℚ̄ (N * p)).2
  have hjQmemF : ι A (qExpand A p (jqModC A)) ∈ FF := by
    rw [ι_qExpand_jqModC, ← coe_jdF ℚ̄ (N * p) p (dvd_mul_left p N)]
    exact (jdF ℚ̄ (N * p) p (dvd_mul_left p N)).2
  have hjF_eq : (jF ℚ̄ (N * p) : FF) = ⟨ι A (jqModC A), hjmemF⟩ :=
    Subtype.ext ((coe_jF ℚ̄ (N * p)).trans (coeffMap_jqModC A.subtype).symm)
  have hjdF_eq : (jdF ℚ̄ (N * p) p (dvd_mul_left p N) : FF) = ⟨ι A (qExpand A p (jqModC A)), hjQmemF⟩ :=
    Subtype.ext ((coe_jdF ℚ̄ (N * p) p (dvd_mul_left p N)).trans (ι_qExpand_jqModC A p).symm)
  obtain ⟨hj₀', hresj'⟩ := hres (jqModC A) hjmemF
  obtain ⟨hjQ₀', hresjQ'⟩ := hres (qExpand A p (jqModC A)) hjQmemF
  have hj₀ : (jF ℚ̄ (N * p) : FF) ∈ R₀.integers := by rw [hjF_eq]; exact hj₀'
  have hjQ₀ : (jdF ℚ̄ (N * p) p (dvd_mul_left p N) : FF) ∈ R₀.integers := by rw [hjdF_eq]; exact hjQ₀'
  have hresj : ((R₀.residue ⟨_, hj₀⟩ : Fb) : LaurentSeries kk) = jqModC kk := by
    have : (⟨(jF ℚ̄ (N * p) : FF), hj₀⟩ : R₀.integers) = ⟨_, hj₀'⟩ := Subtype.ext hjF_eq
    rw [this, hresj', coeffMap_jqModC]
  have hresjQ : ((R₀.residue ⟨_, hjQ₀⟩ : Fb) : LaurentSeries kk) = jqModC kk ^ p := by
    have : (⟨(jdF ℚ̄ (N * p) p (dvd_mul_left p N) : FF), hjQ₀⟩ : R₀.integers) = ⟨_, hjQ₀'⟩ :=
      Subtype.ext hjdF_eq
    rw [this, hresjQ', ϖ_qExpand_jqModC, qExpand_jqModC_eq_pow_unconditional kk]
  have hj₁ : (jF ℚ̄ (N * p) : FF) ∈ R₁.integers := by
    change w (jF ℚ̄ (N * p)) ∈ R₀.integers
    rw [hw₁]; exact hjQ₀
  have hresj₁ : ((R₁.residue ⟨_, hj₁⟩ : Fb) : LaurentSeries kk) = jqModC kk ^ p := by
    have h := transport_residue_apply A R₀ w (jF ℚ̄ (N * p)) hj₁ (by rw [hw₁]; exact hjQ₀)
    rw [h]
    have : (⟨w (jF ℚ̄ (N * p)), by rw [hw₁]; exact hjQ₀⟩ : R₀.integers) = ⟨_, hjQ₀⟩ :=
      Subtype.ext hw₁
    rw [this, hresjQ]

  have hresj_ne : R₀.residue ⟨_, hj₀⟩ ≠ 0 := fun h0 => hjk (by
    rw [← hresj, h0]; rfl)
  have hresjQ_ne : R₀.residue ⟨_, hjQ₀⟩ ≠ 0 := fun h0 => pow_ne_zero p hjk (by
    rw [← hresjQ, h0]; rfl)

  have hne : R₀.integers ≠ R₁.integers := by

    set t : FF := jdF ℚ̄ (N * p) p (dvd_mul_left p N) / (jF ℚ̄ (N * p)) ^ p with ht
    set t' : FF := jF ℚ̄ (N * p) / (jdF ℚ̄ (N * p) p (dvd_mul_left p N)) ^ p with ht'
    have hwt : w t = t' := by rw [ht, map_div₀, map_pow, hw₁, hw₂]
    have hjp₀ : (jF ℚ̄ (N * p) : FF) ^ p ∈ R₀.integers := pow_mem hj₀ p
    have hjQp₀ : (jdF ℚ̄ (N * p) p (dvd_mul_left p N) : FF) ^ p ∈ R₀.integers := pow_mem hjQ₀ p
    have hres_jp : R₀.residue ⟨_, hjp₀⟩ = R₀.residue ⟨_, hj₀⟩ ^ p := by
      rw [← map_pow]; rfl
    have hres_jQp : R₀.residue ⟨_, hjQp₀⟩ = R₀.residue ⟨_, hjQ₀⟩ ^ p := by
      rw [← map_pow]; rfl
    obtain ⟨ht_mem, hres_t⟩ := residue_div A R₀ hjQ₀ hjp₀ (by rw [hres_jp]; exact pow_ne_zero _ hresj_ne)
    obtain ⟨ht'_mem, hres_t'⟩ := residue_div A R₀ hj₀ hjQp₀ (by rw [hres_jQp]; exact pow_ne_zero _ hresjQ_ne)
    have hres_t1 : R₀.residue ⟨t, ht_mem⟩ = 1 := by
      rw [hres_t, hres_jp, div_eq_one_iff_eq (pow_ne_zero _ hresj_ne)]
      apply Subtype.ext
      rw [hresjQ, SubmonoidClass.coe_pow, hresj]
    have hres_t'1 : R₀.residue ⟨t', ht'_mem⟩ ≠ 1 := by
      rw [hres_t', hres_jQp, Ne, div_eq_one_iff_eq (pow_ne_zero _ hresjQ_ne)]
      intro h
      have h' := congrArg (fun z : Fb => (z : LaurentSeries kk)) h
      simp only [SubmonoidClass.coe_pow] at h'
      rw [hresj, hresjQ, ← pow_mul] at h'
      have h1 : ((jqModC kk) ^ 1).order = ((jqModC kk) ^ (p * p)).order := by
        rw [pow_one]; exact congrArg HahnSeries.order h'
      rw [order_jqModC_pow, order_jqModC_pow] at h1
      have h2 : ((p * p : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by linarith
      have h3 : p * p = 1 := by exact_mod_cast h2
      nlinarith

    set h : FF := t - 1 with hh
    have hh_mem : h ∈ R₀.integers := sub_mem ht_mem (one_mem _)
    have hres_h : R₀.residue ⟨h, hh_mem⟩ = 0 := by
      have : (⟨h, hh_mem⟩ : R₀.integers) = ⟨t, ht_mem⟩ - 1 := Subtype.ext rfl
      rw [this, map_sub, map_one, hres_t1, sub_self]
    have hwh : w h = t' - 1 := by rw [hh, map_sub, map_one, hwt]
    have hwh_mem : w h ∈ R₀.integers := by rw [hwh]; exact sub_mem ht'_mem (one_mem _)
    have hres_wh : R₀.residue ⟨w h, hwh_mem⟩ ≠ 0 := by
      have : (⟨w h, hwh_mem⟩ : R₀.integers) = ⟨t', ht'_mem⟩ - 1 := Subtype.ext hwh
      rw [this, map_sub, map_one, sub_ne_zero]; exact hres_t'1
    have hh0 : h ≠ 0 := by
      intro h0; apply hres_wh
      have : (⟨w h, hwh_mem⟩ : R₀.integers) = 0 := Subtype.ext (by change w h = 0; rw [h0, map_zero])
      rw [this, map_zero]
    intro heq
    obtain ⟨u, hu⟩ := R₀.isUnit_of_residue_ne_zero hres_wh
    have hinv_mem : (w h)⁻¹ ∈ R₀.integers := by
      have hmul : ((↑u⁻¹ : R₀.integers) : FF) * w h = 1 := by
        have := congrArg (fun y : R₀.integers => (y : FF)) u.inv_mul
        simpa [hu] using this
      rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
    have hinv₁ : h⁻¹ ∈ R₁.integers := by
      change w h⁻¹ ∈ R₀.integers
      rw [map_inv₀]; exact hinv_mem
    rw [← heq] at hinv₁
    have hunit : IsUnit (⟨h, hh_mem⟩ : R₀.integers) :=
      ⟨⟨⟨h, hh_mem⟩, ⟨h⁻¹, hinv₁⟩, Subtype.ext (mul_inv_cancel₀ hh0),
        Subtype.ext (inv_mul_cancel₀ hh0)⟩, rfl⟩
    exact R₀.residue_ne_zero_of_isUnit hunit hres_h

  let R : Fin 2 → RegularProlongation A FF Fb := ![R₀, R₁]
  have hR0 : R 0 = R₀ := rfl
  have hR1 : R 1 = R₁ := rfl
  have hR : Function.Injective fun i => (R i).integers := by
    have key : ∀ i j : Fin 2, (R i).integers = (R j).integers → i = j :=
      Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨fun _ => rfl, fun h => absurd h hne⟩,
        Fin.forall_fin_two.mpr ⟨fun h => absurd h.symm hne, fun _ => rfl⟩⟩
    exact fun i j h => key i j h
  have hf : ∀ i, (jF ℚ̄ (N * p) : FF) ∈ (R i).integers := Fin.forall_fin_two.mpr ⟨hj₀, hj₁⟩
  have hres₁ : (((R 0).residue ⟨jF ℚ̄ (N * p), hf 0⟩ : Fb) : LaurentSeries kk) = jqModC kk := hresj
  have hres₂ : (((R 1).residue ⟨jF ℚ̄ (N * p), hf 1⟩ : Fb) : LaurentSeries kk) = (jqModC kk) ^ p :=
    hresj₁
  have htr₁ : Transcendental kk (jqModC kk) := ModularCurve.transcendental_jqModC kk
  have htr₂ : Transcendental kk ((jqModC kk) ^ p) := by
    rw [← qExpand_jqModC_eq_pow_unconditional kk]
    exact fun h => htr₁ ((isAlgebraic_algHom_iff (qExpandAlgHomC kk p)
      (qExpand_injective (R := kk) (N := p))).mp h)
  have htr : ∀ i, Transcendental kk ((R i).residue ⟨jF ℚ̄ (N * p), hf i⟩) := by
    refine Fin.forall_fin_two.mpr ⟨fun h => htr₁ ?_, fun h => htr₂ ?_⟩
    · rw [← hres₁]
      exact (isAlgebraic_algHom_iff (modularFunctionFieldFullC kk N).val Subtype.val_injective).mpr h
    · rw [← hres₂]
      exact (isAlgebraic_algHom_iff (modularFunctionFieldFullC kk N).val Subtype.val_injective).mpr h

  have hψ : Module.finrank (IntermediateField.adjoin ℚ̄ {(jF ℚ̄ (N * p) : FF)}) FF =
      (p + 1) * dedekindPsi N := by
    rw [finrank_adjoin_jF ℚ̄ (N * p) (Nat.cast_ne_zero.mpr (NeZero.ne (N * p))),
      dedekindPsi_mul_of_coprime N p ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm,
      dedekindPsi_prime (Fact.out : p.Prime), Nat.mul_comm]
  haveI hFD : FiniteDimensional (IntermediateField.adjoin ℚ̄ {(jF ℚ̄ (N * p) : FF)}) FF :=
    Module.finite_of_finrank_pos (by
      rw [hψ]; exact Nat.mul_pos (Nat.succ_pos p) (dedekindPsi_pos N))

  obtain ⟨hfin, hsum₀⟩ := AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le A
    (fun _ : Fin 2 => (Fb : Type _)) R hR (jF ℚ̄ (N * p)) hf htr
  have hfin0 := hfin 0
  have hfin1 := hfin 1
  try dsimp only at hfin0 hfin1 hsum₀
  simp only [Fin.sum_univ_two] at hsum₀

  set K₁ : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({jqModC kk} : Set (LaurentSeries kk)) with hK₁def
  set K₀ : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({(jqModC kk) ^ p} : Set (LaurentSeries kk)) with hK₀def
  have hK₀K₁ : K₀ ≤ K₁ := adjoin_pow_le kk p
  have hK₁F : K₁ ≤ (modularFunctionFieldFullC kk N) := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_full kk N))
  have hK₀F : K₀ ≤ (modularFunctionFieldFullC kk N) := hK₀K₁.trans hK₁F

  have hconv₁ : Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨jF ℚ̄ (N * p), hf 0⟩}) Fb
      = IntermediateField.relfinrank K₁ (modularFunctionFieldFullC kk N) :=
    (finrank_adjoin_eq_relfinrank (modularFunctionFieldFullC kk N) ((R 0).residue ⟨jF ℚ̄ (N * p), hf 0⟩)).trans (by rw [hres₁])
  have hconv₂ : Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨jF ℚ̄ (N * p), hf 1⟩}) Fb
      = IntermediateField.relfinrank K₀ (modularFunctionFieldFullC kk N) :=
    (finrank_adjoin_eq_relfinrank (modularFunctionFieldFullC kk N) ((R 1).residue ⟨jF ℚ̄ (N * p), hf 1⟩)).trans (by rw [hres₂])
  have hsum : IntermediateField.relfinrank K₁ (modularFunctionFieldFullC kk N) + IntermediateField.relfinrank K₀ (modularFunctionFieldFullC kk N)
      ≤ (p + 1) * dedekindPsi N := by
    rw [← hconv₁, ← hconv₂, ← hψ]; exact hsum₀

  have hψN : IntermediateField.relfinrank K₁ (modularFunctionFieldFullC kk N) = dedekindPsi N := by
    have h := ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi kk N
      (natCast_residueField_ne_zero (A := A) (p := p) hA hpN)
    have h' := finrank_adjoin_eq_relfinrank (modularFunctionFieldFullC kk N)
      (⟨jqModC kk, jqModC_mem_full kk N⟩ : modularFunctionFieldFullC kk N)
    exact h'.symm.trans h

  have htow := IntermediateField.relfinrank_mul_relfinrank hK₀K₁ hK₁F
  rw [hψN] at htow

  have hψpos := dedekindPsi_pos N
  have he0 : IntermediateField.relfinrank K₀ K₁ ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at htow
    have hpos₂ : 0 < IntermediateField.relfinrank K₀ (modularFunctionFieldFullC kk N) := by
      rw [← hconv₂]; haveI := hfin1; exact Module.finrank_pos
    omega
  have hpe : p ≤ IntermediateField.relfinrank K₀ K₁ := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hK₀K₁]
    haveI : Module.Finite K₀ (extendScalars hK₀K₁) := Module.finite_of_finrank_pos (by
      rw [← IntermediateField.relfinrank_eq_finrank_of_le hK₀K₁]; exact Nat.pos_of_ne_zero he0)
    exact le_finrank_adjoin_pow kk p

  have hK₀F₁ : IntermediateField.relfinrank K₀ (modularFunctionFieldFullC kk N) = p * dedekindPsi N := by
    apply le_antisymm
    ·
      have : dedekindPsi N + IntermediateField.relfinrank K₀ (modularFunctionFieldFullC kk N)
          ≤ (p + 1) * dedekindPsi N := by
        rw [hψN] at hsum; exact hsum
      nlinarith
    · rw [← htow]; exact Nat.mul_le_mul_right _ hpe
  have hdeg₀ : Module.finrank (IntermediateField.adjoin kk {R₀.residue ⟨_, hj₀⟩}) Fb = dedekindPsi N := by
    rw [← hψN]; exact hconv₁
  have hdeg₁ : Module.finrank (IntermediateField.adjoin kk {R₁.residue ⟨_, hj₁⟩}) Fb
      = p * dedekindPsi N := by
    rw [← hK₀F₁]; exact hconv₂

  have heq : ∑ i, Module.finrank (IntermediateField.adjoin kk
        ({(R i).residue ⟨jF ℚ̄ (N * p), hf i⟩} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin ℚ̄ ({(jF ℚ̄ (N * p) : FF)} : Set FF)) FF := by
    rw [Fin.sum_univ_two, hψ]
    change Module.finrank (IntermediateField.adjoin kk {R₀.residue ⟨_, hj₀⟩}) Fb +
      Module.finrank (IntermediateField.adjoin kk {R₁.residue ⟨_, hj₁⟩}) Fb = _
    rw [hdeg₀, hdeg₁]; ring

  have hcomplete : ∀ V : ValuationSubring FF,
      (∀ e ∈ IntermediateField.adjoin ℚ̄ {(jF ℚ̄ (N * p) : FF)}, e ∈ V ↔ e ∈ R₀.integers) →
      V = R₀.integers ∨ V = R₁.integers := by
    intro V hV
    obtain ⟨i, hi⟩ :=
      AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
        A (fun _ : Fin 2 => (Fb : Type _)) R hR (jF ℚ̄ (N * p)) hf htr heq 0 V hV
    revert hi
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hi; exact Or.inl hi
    · intro hi
      have : i = 0 := Subsingleton.elim _ _
      subst this
      exact Or.inr hi
  exact ⟨hne, hj₀, hj₁, hresj, hresj₁, hdeg₀, hdeg₁, hψ, hcomplete⟩

end TwoProlongations

section Assembly

variable (N p : ℕ) [NeZero N] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * p))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

set_option maxHeartbeats 6400000 in
theorem main (hpN : ¬ p ∣ N) (hA : A.LiesOverPrime p) :
    ∃ R : Fin 2 → RegularProlongation A FF Fb,
      (∀ f : FF, f ∈ (R 0).integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ (R 0).integers,
          (((R 0).residue ⟨_, hint⟩ : Fb) : LaurentSeries kk) = coeffMap (IsLocalRing.residue A) y) ∧
      (∀ f : FF, f ∈ (R 1).integers ↔
        geomAut ℚ̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p) f
          ∈ (R 0).integers) ∧
      (∀ (f : FF) (h₁ : f ∈ (R 1).integers)
        (h₀ : geomAut ℚ̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p) f
          ∈ (R 0).integers),
        (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨_, h₀⟩) ∧
      (R 0).integers ≠ (R 1).integers ∧
      (∃ hj : ∀ i, (jF ℚ̄ (N * p) : FF) ∈ (R i).integers,
        (((R 0).residue ⟨_, hj 0⟩ : Fb) : LaurentSeries kk) = jqModC kk ∧
        (((R 1).residue ⟨_, hj 1⟩ : Fb) : LaurentSeries kk) = jqModC kk ^ p ∧
        Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨_, hj 0⟩}) Fb = dedekindPsi N ∧
        Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨_, hj 1⟩}) Fb
          = p * dedekindPsi N ∧
        Module.finrank (IntermediateField.adjoin ℚ̄ {(jF ℚ̄ (N * p) : FF)}) FF
          = (p + 1) * dedekindPsi N) ∧
      ∀ V : ValuationSubring FF,
        (∀ e ∈ IntermediateField.adjoin ℚ̄ {(jF ℚ̄ (N * p) : FF)}, e ∈ V ↔ e ∈ (R 0).integers) →
        V = (R 0).integers ∨ V = (R 1).integers := by
  obtain ⟨R₀, hmem, hres⟩ :=
    ModularCurve.exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd N p hpN A hA
  obtain ⟨hne, hj₀, hj₁, hresj, hresj₁, hdeg₀, hdeg₁, hψ, hcomplete⟩ :=
    main_of_gauss (N := N) (p := p) (A := A) hpN hA R₀ hres
  set w := geomAut ℚ̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p) with hw
  refine ⟨![R₀, transport A R₀ w], hmem, hres, fun f => Iff.rfl, fun f h₁ h₀ => rfl, hne,
    ⟨Fin.forall_fin_two.mpr ⟨hj₀, hj₁⟩, hresj, hresj₁, hdeg₀, hdeg₁, hψ⟩, hcomplete⟩

end Assembly

end NeronLeg1TwoBranches
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd.NeronLeg1TwoBranches"

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ R : Fin 2 → AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * p))
        (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),

      (∀ f : ModularCurve.modularFunctionFieldBar (N * p), f ∈ (R 0).integers ↔
        ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y
            = ModularCurve.coeffMap A.subtype x) ∧

      (∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * p)),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.modularFunctionFieldBar (N * p)) ∈ (R 0).integers,
          (((R 0).residue ⟨_, hint⟩ :
              ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y) ∧

      (∀ f : ModularCurve.modularFunctionFieldBar (N * p), f ∈ (R 1).integers ↔
        ModularCurve.geomAut (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldFull (N * p))
          (ModularCurve.atkinLehnerInvolutionFull N p) f ∈ (R 0).integers) ∧
      (∀ (f : ModularCurve.modularFunctionFieldBar (N * p)) (h₁ : f ∈ (R 1).integers)
        (h₀ : ModularCurve.geomAut (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldFull (N * p))
          (ModularCurve.atkinLehnerInvolutionFull N p) f ∈ (R 0).integers),
        (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨_, h₀⟩) ∧

      (R 0).integers ≠ (R 1).integers ∧

      (∃ hj : ∀ i, (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.modularFunctionField_le_full (N * p) (ModularCurve.jq_mem (N * p)))⟩ :
            ModularCurve.modularFunctionFieldBar (N * p)) ∈ (R i).integers,
        (((R 0).residue ⟨_, hj 0⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
        (((R 1).residue ⟨_, hj 1⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) ^ p ∧
        Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            {(R 0).residue ⟨_, hj 0⟩})
          (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) = dedekindPsi N ∧
        Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            {(R 1).residue ⟨_, hj 1⟩})
          (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
            = p * dedekindPsi N ∧
        Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
            {(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.modularFunctionField_le_full (N * p) (ModularCurve.jq_mem (N * p)))⟩ :
              ModularCurve.modularFunctionFieldBar (N * p))})
          (ModularCurve.modularFunctionFieldBar (N * p)) = (p + 1) * dedekindPsi N) ∧

      ∀ V : ValuationSubring (ModularCurve.modularFunctionFieldBar (N * p)),
        (∀ e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
            {(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.modularFunctionField_le_full (N * p) (ModularCurve.jq_mem (N * p)))⟩ :
              ModularCurve.modularFunctionFieldBar (N * p))},
          e ∈ V ↔ e ∈ (R 0).integers) →
        V = (R 0).integers ∨ V = (R 1).integers :=
  NeronLeg1TwoBranches.main N p A hpN hA

end
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd.NeronLeg1TwoBranches"

end S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd (solution)
