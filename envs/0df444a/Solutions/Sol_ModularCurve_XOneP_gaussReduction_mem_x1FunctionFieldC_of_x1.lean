-- Prove2me | solution 1 for ModularCurve.XOneP.gaussReduction_mem_x1FunctionFieldC_of_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d059ca33-9653-5376-bdd3-bc2207f9d0e9

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_gaussReduction_mem_x1FunctionFieldC_of_x1

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MatrixGroups

namespace ResidME96

open ModularCurve UpperHalfPlane

section contentZ
variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_eq_C_mul_of_forall_dvd (P : PowerSeries ℤ) (h : ∀ n, (p : ℤ) ∣ PowerSeries.coeff n P) :
    ∃ P' : PowerSeries ℤ, P = PowerSeries.C (p : ℤ) * P' := by
  choose c hc using h
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

include hp in

theorem exists_eq_C_pow_mul_not_dvd (P : PowerSeries ℤ) (hP : P ≠ 0) :
    ∃ (a : ℕ) (P₁ : PowerSeries ℤ), P = PowerSeries.C ((p : ℤ) ^ a) * P₁ ∧
      ∃ n, ¬ (p : ℤ) ∣ PowerSeries.coeff n P₁ := by
  obtain ⟨n, hn⟩ : ∃ n, PowerSeries.coeff n P ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (PowerSeries.ext fun n => by simpa using h n)
  suffices H : ∀ (N : ℕ) (Q : PowerSeries ℤ), PowerSeries.coeff n Q ≠ 0 → (PowerSeries.coeff n Q).natAbs ≤ N →
      ∃ (a : ℕ) (Q₁ : PowerSeries ℤ), Q = PowerSeries.C ((p : ℤ) ^ a) * Q₁ ∧ ∃ m, ¬ (p : ℤ) ∣ PowerSeries.coeff m Q₁ from
    H _ P hn le_rfl
  intro N
  induction N with
  | zero =>
    intro Q hQ hle
    exact absurd (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hle)) hQ
  | succ N ih =>
    intro Q hQ hle
    by_cases hall : ∀ m, (p : ℤ) ∣ PowerSeries.coeff m Q
    · obtain ⟨Q', rfl⟩ := exists_eq_C_mul_of_forall_dvd p Q hall
      rw [PowerSeries.coeff_C_mul] at hQ hle
      have hQ' : PowerSeries.coeff n Q' ≠ 0 := fun h => hQ (by rw [h, mul_zero])
      have hlt : (PowerSeries.coeff n Q').natAbs ≤ N := by
        rw [Int.natAbs_mul, Int.natAbs_natCast] at hle
        have h2 : 2 * (PowerSeries.coeff n Q').natAbs ≤ p * (PowerSeries.coeff n Q').natAbs :=
          Nat.mul_le_mul_right _ hp.out.two_le
        have h3 : 1 ≤ (PowerSeries.coeff n Q').natAbs := Int.natAbs_pos.mpr hQ'
        have h4 : 2 * (PowerSeries.coeff n Q').natAbs ≤ N + 1 := le_trans h2 hle
        omega
      obtain ⟨a, Q₁, hQ₁, hm⟩ := ih Q' hQ' hlt
      exact ⟨a + 1, Q₁, by rw [hQ₁, ← mul_assoc, ← map_mul, pow_succ'], hm⟩
    · push Not at hall
      exact ⟨0, Q, by simp, hall⟩

end contentZ

section rescale
variable {M : ℕ}

local notation "Γ₁" => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem strictPeriods_one : (1 : ℝ) ∈ (Γ₁ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact ⟨1, by simp⟩

theorem isIntegralQExp_inv_smul {k : ℤ} (f : ModularForm Γ₁ k) {pf pf' : PowerSeries ℤ} (c : ℤ) (hc : c ≠ 0)
    (hf : IsIntegralQExp f pf) (h : pf = PowerSeries.C c * pf') :
    IsIntegralQExp (⇑(((c : ℂ))⁻¹ • f)) pf' := by
  unfold IsIntegralQExp at *
  have han : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f one_pos strictPeriods_one
  rw [ModularForm.IsGLPos.coe_smul, qExpansion_smul han, ← hf, h, map_mul, PowerSeries.map_C,
    eq_intCast, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc),
    map_one, one_mul]

end rescale

section unif
variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]

theorem exists_unit_natCast_eq_mul_pow (p : ℕ) [hp : Fact p.Prime] (z : A) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ u : Aˣ, (p : A) = u * (z - 1) ^ (p - 1) ∧ (z - 1) ∈ IsLocalRing.maximalIdeal A := by
  set π := z - 1 with hπ
  have hπ0 : π ≠ 0 := sub_ne_zero.mpr hz1
  have hp1 : 1 ≤ p := hp.out.one_le
  have hp2 : 2 ≤ p := hp.out.two_le
  have hz' : z = π + 1 := by rw [hπ]; ring

  have hsum : ∑ k ∈ Finset.Ico 0 (p + 1), π ^ k * (p.choose k : A) = 1 := by
    have := add_pow π 1 p
    simp only [one_pow, mul_one] at this
    rw [← Finset.range_eq_Ico, ← this, ← hz', hz]

  have hd : ∀ k ∈ Finset.Ico 2 p, p * (p.choose k / p) = p.choose k := fun k hk => by
    rw [Finset.mem_Ico] at hk
    exact Nat.mul_div_cancel' (hp.out.dvd_choose_self (by omega) hk.2)
  let m : A := ∑ k ∈ Finset.Ico 2 p, π ^ (k - 1) * ((p.choose k / p : ℕ) : A)
  have hmid : ∑ k ∈ Finset.Ico 2 p, π ^ k * (p.choose k : A) = (p : A) * π * m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by rw [Finset.mem_Ico] at hk; omega
    have hpow : π ^ k = π ^ (k - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel hk1]
    conv_lhs => rw [← hd k hk, hpow]
    push_cast
    ring

  have hsplit : ∑ k ∈ Finset.Ico 0 (p + 1), π ^ k * (p.choose k : A) = 1 + ((p : A) * π + (p : A) * π * m + π ^ p) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1), Finset.sum_Ico_succ_top (by omega : 1 ≤ p),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < p), hmid]
    simp [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self]
    ring
  have hkey : π * ((p : A) * (1 + m) + π ^ (p - 1)) = 0 := by
    have e : (p : A) * π + (p : A) * π * m + π ^ p = 0 := by linear_combination hsum - hsplit
    have hpow : π ^ p = π ^ (p - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel hp1]
    rw [hpow] at e
    linear_combination e
  have hkey' : (p : A) * (1 + m) = -π ^ (p - 1) := by
    have := (mul_eq_zero.mp hkey).resolve_left hπ0
    linear_combination this

  have hπm : π ∈ IsLocalRing.maximalIdeal A := by
    have h1 : π ^ (p - 1) ∈ IsLocalRing.maximalIdeal A := by
      rw [show π ^ (p - 1) = (p : A) * (-(1 + m)) by linear_combination hkey']
      exact Ideal.mul_mem_right _ _ hpA
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ h1

  have hm : m ∈ IsLocalRing.maximalIdeal A := by
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk2 : 2 ≤ k := by rw [Finset.mem_Ico] at hk; exact hk.1
    have : π ^ (k - 1) ∈ IsLocalRing.maximalIdeal A :=
      Ideal.pow_mem_of_mem _ hπm _ (by omega)
    exact Ideal.mul_mem_right _ _ this
  have hu : IsUnit (1 + m) := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-m) with h | h
    · exact absurd h ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.maximalIdeal A).neg_mem hm))
    · simpa using h
  refine ⟨-(hu.unit⁻¹), ?_, hπm⟩
  calc (p : A) = p * ((1 + m) * ↑hu.unit⁻¹) := by rw [hu.mul_val_inv, mul_one]
    _ = ((p : A) * (1 + m)) * ↑hu.unit⁻¹ := by ring
    _ = -π ^ (p - 1) * ↑hu.unit⁻¹ := by rw [hkey']
    _ = ↑(-hu.unit⁻¹) * π ^ (p - 1) := by rw [Units.val_neg]; ring

end unif

section helpers

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [CharZero L] (q : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ q) = intSeriesC L q := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

theorem map_intCast_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (q : PowerSeries ℤ) :
    (q.map (Int.castRingHom R)).map φ = q.map (Int.castRingHom S) := by
  have h : φ.comp (Int.castRingHom R) = Int.castRingHom S := RingHom.ext_int _ _
  rw [← h, PowerSeries.map_comp, RingHom.comp_apply]

theorem intSeriesC_eq_map_map (F : Type*) [Field F] {R : Type*} [CommRing R] (φ : R →+* F) (q : PowerSeries ℤ) :
    intSeriesC F q = HahnSeries.ofPowerSeries ℤ F ((q.map (Int.castRingHom R)).map φ) := by
  rw [intSeriesC, map_intCast_map]

theorem intSeriesC_C_mul (F : Type*) [Field F] (c : ℤ) (q : PowerSeries ℤ) :
    intSeriesC F (PowerSeries.C c * q) = HahnSeries.C (c : F) * intSeriesC F q := by
  rw [intSeriesC_mul]
  congr 1
  simp [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]

theorem intSeriesC_ne_zero_of_ne_zero (F : Type*) [Field F] [CharZero F] {q : PowerSeries ℤ} (hq : q ≠ 0) :
    intSeriesC F q ≠ 0 := by
  intro h
  apply hq
  apply PowerSeries.map_injective (Int.castRingHom F) Int.cast_injective
  rw [map_zero]
  exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)

theorem map_ne_zero_of_not_dvd (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {q : PowerSeries ℤ}
    {n : ℕ} (hn : ¬ (p : ℤ) ∣ PowerSeries.coeff n q) : q.map (Int.castRingHom F) ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_map, map_zero, eq_intCast, CharP.intCast_eq_zero_iff F p] at this
  exact hn this

theorem intSeriesC_ne_zero_of_not_dvd (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {q : PowerSeries ℤ}
    {n : ℕ} (hn : ¬ (p : ℤ) ∣ PowerSeries.coeff n q) : intSeriesC F q ≠ 0 := by
  intro h
  exact map_ne_zero_of_not_dvd F p hn (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))

theorem algebraMap_laurent_eq_C (F : Type*) [Field F] (a : F) : algebraMap F (LaurentSeries F) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']; simp

theorem exists_content (p : ℕ) [Fact p.Prime] (P : PowerSeries ℤ) :
    ∃ (a : ℕ) (P₁ : PowerSeries ℤ), P = PowerSeries.C ((p : ℤ) ^ a) * P₁ ∧
      (P ≠ 0 → ∃ n, ¬ (p : ℤ) ∣ PowerSeries.coeff n P₁) := by
  by_cases hP : P = 0
  · exact ⟨0, P, by simp, fun h => absurd hP h⟩
  · obtain ⟨a, P₁, h1, h2⟩ := exists_eq_C_pow_mul_not_dvd p P hP
    exact ⟨a, P₁, h1, fun _ => h2⟩

theorem exp_inj {d : ℕ} (hd : 0 < d) {i i' n n' : ℕ} (hi : i < d) (hi' : i' < d)
    (h : i + d * n = i' + d * n') : i = i' ∧ n = n' := by
  have h1 : (i + d * n) % d = (i' + d * n') % d := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h1
  subst h1
  refine ⟨rfl, ?_⟩
  have h2 : d * n = d * n' := by omega
  exact Nat.eq_of_mul_eq_mul_left hd h2

end helpers

end ResidME96

set_option maxHeartbeats 16000000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥K) (x y : PowerSeries A) (hy : y.map (IsLocalRing.residue A) ≠ 0)
    (hxy : (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
      ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M := by
  classical
  haveI hp := (inferInstance : Fact p.Prime)

  let κ := IsLocalRing.ResidueField A

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A) p, IsLocalRing.residue_eq_zero_iff]; exact hAp
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpk)
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp hinjAL
  have hcoeA : ∀ a : A, ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = HahnSeries.C (algebraMap A L a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K]
    show algebraMap L (LaurentSeries L) (algebraMap A L a) = _
    exact ResidME96.algebraMap_laurent_eq_C L _

  obtain ⟨W₀, h1, h2, h3, h4, h5⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField M L K hK A j hj
  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K A W₀ h1 h5
  have hfW : f ∈ W₀ := (h1 f).mpr ⟨x, y, hy, hxy⟩
  rw [← hred ⟨f, hfW⟩ x y hy hxy]
  set fW : ↥W₀ := ⟨f, hfW⟩ with hfWdef

  let ψ : ↥W₀ →+* LaurentSeries L := (K.toSubfield.subtype).comp W₀.subtype
  have hψ : ∀ w : ↥W₀, ψ w = ((w : ↥K) : LaurentSeries L) := fun w => rfl
  have hψinj : Function.Injective ψ := fun a b hab => Subtype.ext (Subtype.ext hab)

  have hmaxW : ∀ w : ↥W₀, w ∈ IsLocalRing.maximalIdeal ↥W₀ ↔ (w : ↥K) ∈ W₀.nonunits :=
    fun w => (ValuationSubring.coe_mem_nonunits_iff).symm
  have hred0 : ∀ w : ↥W₀, w ∈ IsLocalRing.maximalIdeal ↥W₀ → red w = 0 := fun w hw => by
    rw [← RingHom.mem_ker, hker]; exact hw
  have hred_ne : ∀ w : ↥W₀, red w ≠ 0 → IsUnit w := fun w hw => by
    by_contra hnu
    exact hw (hred0 w ((IsLocalRing.mem_maximalIdeal _).mpr hnu))

  obtain ⟨z, hz⟩ := hζA
  have hzp : z ^ p = 1 := hinjAL (by rw [map_pow, hz, hζ.pow_eq_one, map_one])
  have hz1 : z ≠ 1 := fun h => hζ.ne_one hp.out.one_lt (by rw [← hz, h, map_one])
  obtain ⟨ε, hε, hπm⟩ := ResidME96.exists_unit_natCast_eq_mul_pow p z hzp hz1 hAp
  set π : A := z - 1 with hπdef
  have hπL : algebraMap A L π = ζ - 1 := by rw [hπdef, map_sub, hz, map_one]
  have hpL : (p : L) = algebraMap A L ε * (ζ - 1) ^ (p - 1) := by
    rw [← hπL, ← map_pow, ← map_mul, ← hε, map_natCast]
  have hp0L : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨πW, hπWdef⟩ : ∃ w : ↥W₀, (w : ↥K) = algebraMap A ↥K π := ⟨⟨_, h2 π⟩, rfl⟩
  obtain ⟨εW, hεWdef⟩ : ∃ w : ↥W₀, (w : ↥K) = algebraMap A ↥K (ε : A) := ⟨⟨_, h2 _⟩, rfl⟩
  have hψπ : ψ πW = HahnSeries.C (ζ - 1) := by rw [hψ, hπWdef, hcoeA, hπL]
  have hψε : ψ εW = HahnSeries.C (algebraMap A L ε) := by rw [hψ, hεWdef, hcoeA]
  have hπW0 : πW ≠ 0 := by
    intro h
    have := congrArg ψ h
    rw [hψπ, map_zero] at this
    exact HahnSeries.C_ne_zero (sub_ne_zero.mpr (hζ.ne_one hp.out.one_lt)) this
  have hπmax : πW ∈ IsLocalRing.maximalIdeal ↥W₀ := (hmaxW πW).mpr (by rw [hπWdef]; exact h3 π hπm)
  have hredπ : red πW = 0 := hred0 πW hπmax

  have hredε : red εW = HahnSeries.C (IsLocalRing.residue A ε) := by
    have e1 := hred εW (PowerSeries.C (ε : A)) 1 (by rw [map_one]; exact one_ne_zero) (by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, hεWdef]
      exact hcoeA ε)
    rw [e1, map_one, map_one, div_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
  have hεbar : IsLocalRing.residue A ε ≠ 0 := ((Units.isUnit ε).map (IsLocalRing.residue A)).ne_zero
  have hredε0 : red εW ≠ 0 := by rw [hredε]; exact HahnSeries.C_ne_zero hεbar
  have hεunit : IsUnit εW := hred_ne εW hredε0

  have hpW : (p : ↥W₀) = εW * πW ^ (p - 1) := by
    apply hψinj
    rw [map_natCast, map_mul, map_pow, hψε, hψπ, ← map_pow, ← map_mul, ← hpL, map_natCast]
  have hpLL : (p : LaurentSeries L) = HahnSeries.C (p : L) := (map_natCast (HahnSeries.C (Γ := ℤ) (R := L)) p).symm
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  set pb := hζ.subOnePowerBasis ℚ with hpb
  have hgen : pb.gen = ζ - 1 := by rw [hpb, IsPrimitiveRoot.subOnePowerBasis_gen]
  have hdim : pb.dim = p - 1 := by
    rw [← pb.finrank, IsCyclotomicExtension.finrank L (Polynomial.cyclotomic.irreducible_rat hp.out.pos),
      Nat.totient_prime hp.out]
  have hfK : (f : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) := hK ▸ f.2
  obtain ⟨h, hfsum⟩ :=
    (ModularCurve.mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb L pb.basis (ModularCurve.x1FunctionField M)
      (f : LaurentSeries L)).mp hfK
  have hb : ∀ i, pb.basis i = (ζ - 1) ^ (i : ℕ) := fun i => by rw [PowerBasis.basis_eq_pow, hgen]

  have hrat : ∀ i, ∃ (k : ℤ) (ff gg : ModularForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg : PowerSeries ℤ), ModularCurve.IsIntegralQExp ff pf ∧ ModularCurve.IsIntegralQExp gg pg ∧
      ModularCurve.intSeriesC ℚ pg ≠ 0 ∧ ((h i : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ)
        = ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg :=
    fun i => (ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC (CongruenceSubgroup.Gamma1 M)
      ResidME96.strictPeriods_one _).mp (h i).2
  choose kw ff gg pf pg hff hgg hpg0 hhi using hrat

  choose a pf' hpfeq hpf'nd using fun i => ResidME96.exists_content p (pf i)
  choose bq pg' hpgeq hpg'nd using fun i => ResidME96.exists_content p (pg i)
  have hpg_ne : ∀ i, pg i ≠ 0 := fun i h0 => hpg0 i (by rw [h0, ModularCurve.intSeriesC_zero])
  have hpg'nd' : ∀ i, ∃ n, ¬ (p : ℤ) ∣ PowerSeries.coeff n (pg' i) := fun i => hpg'nd i (hpg_ne i)
  have hpg'_ne : ∀ i, pg' i ≠ 0 := fun i h0 => hpg_ne i (by rw [hpgeq i, h0, mul_zero])
  have hpf'_of : ∀ i, pf i = 0 → pf' i = 0 := fun i h0 => by
    have h' := hpfeq i
    rw [h0] at h'
    refine PowerSeries.ext fun m => ?_
    have := congrArg (PowerSeries.coeff m) h'
    rw [map_zero, PowerSeries.coeff_C_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hpZ)

  let ff' := fun i => ((((p : ℤ) ^ a i : ℤ) : ℂ))⁻¹ • ff i
  let gg' := fun i => ((((p : ℤ) ^ bq i : ℤ) : ℂ))⁻¹ • gg i
  have hff' : ∀ i, ModularCurve.IsIntegralQExp (⇑(ff' i)) (pf' i) := fun i =>
    ResidME96.isIntegralQExp_inv_smul (ff i) ((p : ℤ) ^ a i) (pow_ne_zero _ hpZ) (hff i) (hpfeq i)
  have hgg' : ∀ i, ModularCurve.IsIntegralQExp (⇑(gg' i)) (pg' i) := fun i =>
    ResidME96.isIntegralQExp_inv_smul (gg i) ((p : ℤ) ^ bq i) (pow_ne_zero _ hpZ) (hgg i) (hpgeq i)

  let U : Fin pb.dim → LaurentSeries L := fun i => ModularCurve.intSeriesC L (pf' i) / ModularCurve.intSeriesC L (pg' i)
  have hUdef : ∀ i, U i = ModularCurve.intSeriesC L (pf' i) / ModularCurve.intSeriesC L (pg' i) := fun i => rfl
  have hUQ : ∀ i, ModularCurve.intSeriesC ℚ (pf' i) / ModularCurve.intSeriesC ℚ (pg' i) ∈ ModularCurve.x1FunctionField M :=
    fun i => ModularCurve.div_mem_qExpFunctionFieldC (ff' i) (gg' i) (hff' i) (hgg' i)
      (ResidME96.intSeriesC_ne_zero_of_ne_zero ℚ (hpg'_ne i))
  have hUeq : ∀ i, U i = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ (pf' i) / ModularCurve.intSeriesC ℚ (pg' i)) :=
    fun i => by rw [map_div₀, ResidME96.coeffEmb_intSeriesC, ResidME96.coeffEmb_intSeriesC]
  have hUK : ∀ i, U i ∈ K := fun i => by
    rw [hK, hUeq]; exact ModularCurve.coeffEmb_mem_laurentBaseChange L (hUQ i)
  let uK : Fin pb.dim → ↥K := fun i => ⟨U i, hUK i⟩

  have hYbar : ∀ i, ((pg' i).map (Int.castRingHom A)).map (IsLocalRing.residue A) ≠ 0 := fun i => by
    rw [ResidME96.map_intCast_map]
    obtain ⟨n, hn⟩ := hpg'nd' i
    exact ResidME96.map_ne_zero_of_not_dvd _ p hn
  have hpres : ∀ i, ((uK i : ↥K) : LaurentSeries L) *
      HahnSeries.ofPowerSeries ℤ L (((pg' i).map (Int.castRingHom A)).map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (((pf' i).map (Int.castRingHom A)).map (algebraMap A L)) := fun i => by
    rw [← ResidME96.intSeriesC_eq_map_map L (algebraMap A L), ← ResidME96.intSeriesC_eq_map_map L (algebraMap A L)]
    exact div_mul_cancel₀ _ (ResidME96.intSeriesC_ne_zero_of_ne_zero L (hpg'_ne i))
  have huW : ∀ i, uK i ∈ W₀ := fun i => (h1 _).mpr ⟨_, _, hYbar i, hpres i⟩
  let uW : Fin pb.dim → ↥W₀ := fun i => ⟨uK i, huW i⟩
  have hψu : ∀ i, ψ (uW i) = U i := fun i => rfl
  have hredu : ∀ i, red (uW i) = ModularCurve.intSeriesC (IsLocalRing.ResidueField A) (pf' i) /
      ModularCurve.intSeriesC (IsLocalRing.ResidueField A) (pg' i) := fun i => by
    rw [hred (uW i) _ _ (hYbar i) (hpres i), ← ResidME96.intSeriesC_eq_map_map _ (IsLocalRing.residue A),
      ← ResidME96.intSeriesC_eq_map_map _ (IsLocalRing.residue A)]
  have hredu_mem : ∀ i, red (uW i) ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M := fun i => by
    rw [hredu]
    obtain ⟨n, hn⟩ := hpg'nd' i
    exact ModularCurve.div_mem_qExpFunctionFieldC (ff' i) (gg' i) (hff' i) (hgg' i)
      (ResidME96.intSeriesC_ne_zero_of_not_dvd _ p hn)
  have hredu_ne : ∀ i, pf i ≠ 0 → red (uW i) ≠ 0 := fun i hi => by
    rw [hredu]
    obtain ⟨n, hn⟩ := hpf'nd i hi
    obtain ⟨n', hn'⟩ := hpg'nd' i
    exact div_ne_zero (ResidME96.intSeriesC_ne_zero_of_not_dvd _ p hn) (ResidME96.intSeriesC_ne_zero_of_not_dvd _ p hn')

  let B : ℕ := ∑ i, bq i
  have hbB : ∀ i, bq i ≤ B := fun i => Finset.single_le_sum (fun i _ => Nat.zero_le (bq i)) (Finset.mem_univ i)
  let n : Fin pb.dim → ℕ := fun i => a i + (B - bq i)
  let e : Fin pb.dim → ℕ := fun i => (i : ℕ) + (p - 1) * n i

  have hE1 : ∀ i, (HahnSeries.C (p : L)) ^ B * (pb.basis i • ModularCurve.coeffEmb L ((h i : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ))
      = HahnSeries.C (algebraMap A L ((ε : A) ^ n i * π ^ e i)) * U i := fun i => by
    rw [hb i, ← HahnSeries.C_mul_eq_smul, hhi i, map_div₀, ResidME96.coeffEmb_intSeriesC,
      ResidME96.coeffEmb_intSeriesC, hpfeq i, hpgeq i, ResidME96.intSeriesC_C_mul, ResidME96.intSeriesC_C_mul, hUdef]
    have hG : ModularCurve.intSeriesC L (pg' i) ≠ 0 := ResidME96.intSeriesC_ne_zero_of_ne_zero L (hpg'_ne i)
    have hCpb : (HahnSeries.C ((((p : ℤ) ^ bq i : ℤ) : L)) : LaurentSeries L) ≠ 0 :=
      HahnSeries.C_ne_zero (by exact_mod_cast pow_ne_zero _ hp.out.ne_zero)

    have hscal : (p : L) ^ B * ((ζ - 1) ^ (i : ℕ) * (((p : ℤ) ^ a i : ℤ) : L)) =
        algebraMap A L ((ε : A) ^ n i * π ^ e i) * (((p : ℤ) ^ bq i : ℤ) : L) := by
      rw [map_mul, map_pow, map_pow, hπL]
      simp only [Int.cast_pow, Int.cast_natCast]
      have hsplit : (p : L) ^ B = (p : L) ^ (B - bq i) * (p : L) ^ (bq i) := by
        rw [← pow_add, Nat.sub_add_cancel (hbB i)]
      rw [hsplit]
      simp only [e, n, pow_add, pow_mul, mul_pow]
      rw [hpL]
      ring
    have hscalC := congrArg (HahnSeries.C (Γ := ℤ) (R := L)) hscal
    simp only [map_mul, map_pow] at hscalC
    have hs' : HahnSeries.C (algebraMap A L ((ε : A) ^ n i * π ^ e i)) =
        (HahnSeries.C (p : L)) ^ B * ((HahnSeries.C (ζ - 1)) ^ (i : ℕ) * HahnSeries.C (((p : ℤ) ^ a i : ℤ) : L)) *
          (HahnSeries.C ((((p : ℤ) ^ bq i : ℤ) : L)) : LaurentSeries L)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hCpb, hscalC]
      simp only [map_mul, map_pow]
    rw [hs', map_pow]
    field_simp
  have hE1sum : (HahnSeries.C (p : L)) ^ B * (f : LaurentSeries L)
      = ∑ i, HahnSeries.C (algebraMap A L ((ε : A) ^ n i * π ^ e i)) * U i := by
    rw [hfsum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hE1 i)

  set I := Finset.univ.filter (fun i => pf i ≠ 0) with hI
  have hUzero : ∀ i, i ∉ I → U i = 0 := fun i hi => by
    have : pf i = 0 := by simpa [hI] using hi
    rw [hUdef, hpf'_of i this, ModularCurve.intSeriesC_zero, zero_div]
  by_cases hIe : I = ∅
  ·
    have hall : ∀ i, U i = 0 := fun i => hUzero i (by rw [hIe]; exact Finset.notMem_empty _)
    have hf0 : (HahnSeries.C (p : L)) ^ B * (f : LaurentSeries L) = 0 := by
      rw [hE1sum]; exact Finset.sum_eq_zero (fun i _ => by rw [hall i, mul_zero])
    have hf0' : (f : LaurentSeries L) = 0 :=
      (mul_eq_zero.mp hf0).resolve_left (pow_ne_zero _ (HahnSeries.C_ne_zero hp0L))
    have : fW = 0 := Subtype.ext (Subtype.ext hf0')
    rw [this, map_zero]; exact zero_mem _
  · obtain ⟨i₀, hi₀I, hmin⟩ := Finset.exists_min_image I e (Finset.nonempty_iff_ne_empty.mpr hIe)
    have hpf0 : pf i₀ ≠ 0 := (Finset.mem_filter.mp hi₀I).2
    have hlt : ∀ i ∈ I, i ≠ i₀ → e i₀ < e i := fun i hi hne => by
      refine lt_of_le_of_ne (hmin i hi) (fun heq => hne ?_)
      have hh := ResidME96.exp_inj (d := p - 1) (by omega) (by rw [← hdim]; exact i.isLt) (by rw [← hdim]; exact i₀.isLt) heq.symm
      exact Fin.ext hh.1

    let gW : ↥W₀ := ∑ i ∈ I, εW ^ n i * πW ^ (e i - e i₀) * uW i

    have hE2 : (p : ↥W₀) ^ B * fW = πW ^ e i₀ * gW := by
      apply hψinj
      rw [map_mul, map_pow, map_natCast, hψ fW, hpLL]
      show (HahnSeries.C (p : L)) ^ B * (f : LaurentSeries L) = _
      rw [hE1sum, map_mul, map_pow, hψπ, map_sum,
        ← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by rw [hUzero i hi, mul_zero]), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [map_mul, map_pow, hψε, hψπ, hψu, hπL]
      have hsplit : e i = e i₀ + (e i - e i₀) := (Nat.add_sub_cancel' (hmin i hi)).symm
      conv_lhs => rw [hsplit, pow_add]
      ring

    have hredg : red gW = (HahnSeries.C (IsLocalRing.residue A ε)) ^ n i₀ * red (uW i₀) := by
      rw [map_sum, Finset.sum_eq_single_of_mem i₀ hi₀I (fun i hi hne => by
        rw [map_mul, map_mul, map_pow, map_pow, hredπ, zero_pow (Nat.sub_ne_zero_of_lt (hlt i hi hne)),
          mul_zero, zero_mul])]
      rw [map_mul, map_mul, map_pow, map_pow, hredε, Nat.sub_self, pow_zero, mul_one]
    have hredg0 : red gW ≠ 0 := by
      rw [hredg]; exact mul_ne_zero (pow_ne_zero _ (HahnSeries.C_ne_zero hεbar)) (hredu_ne i₀ hpf0)
    have hgunit : IsUnit gW := hred_ne gW hredg0

    have hE3 : εW ^ B * πW ^ ((p - 1) * B) * fW = πW ^ e i₀ * gW := by
      rw [← hE2, hpW, mul_pow, ← pow_mul]
    rcases Nat.lt_trichotomy (e i₀) ((p - 1) * B) with hlt' | heq' | hgt'
    · exfalso
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hlt'
      have hg : gW = εW ^ B * πW ^ (t + 1) * fW := by
        apply mul_left_cancel₀ (pow_ne_zero (e i₀) hπW0)
        rw [← hE3, ht, show e i₀ + t + 1 = e i₀ + (t + 1) by ring, pow_add]; ring
      apply (IsLocalRing.mem_maximalIdeal _).mp _ hgunit
      rw [hg]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπmax _ (Nat.succ_pos t)))
    ·
      have hfg : εW ^ B * fW = gW := by
        apply mul_left_cancel₀ (pow_ne_zero ((p - 1) * B) hπW0)
        rw [← mul_assoc, mul_comm (πW ^ _) (εW ^ B), hE3, heq']
      have hval : red fW = ((HahnSeries.C (IsLocalRing.residue A ε)) ^ B)⁻¹ *
          ((HahnSeries.C (IsLocalRing.residue A ε)) ^ n i₀ * red (uW i₀)) := by
        rw [← hredg, ← hfg, map_mul, map_pow, hredε, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ (HahnSeries.C_ne_zero hεbar)), one_mul]
      rw [hval]
      have hCmem : HahnSeries.C (IsLocalRing.residue A ε) ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M := by
        rw [← ResidME96.algebraMap_laurent_eq_C]; exact IntermediateField.algebraMap_mem _ _
      exact mul_mem (inv_mem (pow_mem hCmem _)) (mul_mem (pow_mem hCmem _) (hredu_mem i₀))
    ·
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hgt'
      have hft : εW ^ B * fW = πW ^ (t + 1) * gW := by
        apply mul_left_cancel₀ (pow_ne_zero ((p - 1) * B) hπW0)
        rw [← mul_assoc, mul_comm (πW ^ _) (εW ^ B), hE3, ht,
          show (p - 1) * B + t + 1 = (p - 1) * B + (t + 1) by ring, pow_add, mul_assoc]
      have hmem : εW ^ B * fW ∈ IsLocalRing.maximalIdeal ↥W₀ := by
        rw [hft]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπmax _ (Nat.succ_pos t))
      have hfmem : fW ∈ IsLocalRing.maximalIdeal ↥W₀ :=
        (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left
          (fun hh => (IsLocalRing.mem_maximalIdeal _).mp hh (hεunit.pow B))
      rw [hred0 fW hfmem]; exact zero_mem _

end S_ModularCurve_XOneP_gaussReduction_mem_x1FunctionFieldC_of_x1
end P2MW
export P2MW.S_ModularCurve_XOneP_gaussReduction_mem_x1FunctionFieldC_of_x1 (solution)
