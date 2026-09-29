-- Prove2me | solution 1 for ModularCurve.exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/64272655-f4b2-589d-8722-117c54d65fb5

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve ModularCurve IsLocalRing

namespace QExpKernelGauss

local notation "Qb" => AlgebraicClosure ℚ

section ValLift

variable {L : Type*} [Field L] (A : ValuationSubring L)

def liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) : LaurentSeries A where
  coeff k := ⟨x.coeff k, hx k⟩
  isPWO_support' := by
    refine x.isPWO_support.mono ?_
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk ⊢
    intro h
    exact hk (Subtype.ext h)

@[scoped simp] theorem coeff_liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) (k : ℤ) :
    ((liftVal A x hx).coeff k : L) = x.coeff k := rfl

theorem coeffMap_subtype_liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) :
    coeffMap A.subtype (liftVal A x hx) = x := by
  ext k
  rfl

end ValLift

section RatDVR

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} [hq : Fact q.Prime]

abbrev ratPart (A : ValuationSubring (AlgebraicClosure ℚ)) : ValuationSubring ℚ :=
  A.comap (algebraMap ℚ (AlgebraicClosure ℚ))

theorem mem_ratPart_iff (r : ℚ) : r ∈ ratPart A ↔ algebraMap ℚ (AlgebraicClosure ℚ) r ∈ A :=
  ValuationSubring.mem_comap

theorem isUnit_intCast_of_not_dvd (hA : A.LiesOverPrime q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) :
    ∃ u : A, (u : AlgebraicClosure ℚ) * (n : AlgebraicClosure ℚ) = 1 := by
  have hcop : IsCoprime n (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_dvd_right n q
    have hp : Nat.Prime q := hq.out
    rcases (Nat.dvd_prime hp).mp (by exact_mod_cast this : Int.gcd n q ∣ q) with h | h
    · exact h
    · exfalso; apply hn
      have h2 := Int.gcd_dvd_left n q
      rw [h] at h2
      exact h2
  obtain ⟨a, b, hab⟩ := hcop
  have hnA : (n : AlgebraicClosure ℚ) ∈ A := intCast_mem A n
  have hval : ¬ A.valuation (n : AlgebraicClosure ℚ) < 1 := by
    intro hlt
    have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
    have h1 : A.valuation ((a : AlgebraicClosure ℚ) * n + (b : AlgebraicClosure ℚ) * (q : ℕ)) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_mul]
        exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (intCast_mem A a))).trans_lt hlt
      · rw [Valuation.map_mul]
        exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (intCast_mem A b))).trans_lt hq1
    have h2 : (a : AlgebraicClosure ℚ) * n + (b : AlgebraicClosure ℚ) * (q : ℕ) = 1 := by
      exact_mod_cast hab
    rw [h2, Valuation.map_one] at h1
    exact lt_irrefl _ h1
  have hv1 : A.valuation (n : AlgebraicClosure ℚ) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr hnA) (not_lt.mp hval)
  have hunit : IsUnit (⟨(n : AlgebraicClosure ℚ), hnA⟩ : A) := (A.valuation_eq_one_iff _).mpr hv1
  obtain ⟨u, hu⟩ := hunit
  refine ⟨↑u⁻¹, ?_⟩
  have := congrArg (fun z : A => ((↑u⁻¹ : A) : AlgebraicClosure ℚ) * (z : AlgebraicClosure ℚ)) hu
  simp only at this
  rw [← this, ← Subring.coe_mul]
  simp

theorem inv_natCast_q_not_mem (hA : A.LiesOverPrime q) : ((q : Qb))⁻¹ ∉ A := by
  intro h
  have hq1 : A.valuation ((q : ℕ) : Qb) < 1 := (A.mem_nonunits_iff).mp hA
  have hqA : ((q : ℕ) : Qb) ∈ A := natCast_mem A q
  have hq0 : ((q : ℕ) : Qb) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hunit : IsUnit (⟨(q : Qb), hqA⟩ : A) :=
    ⟨⟨⟨(q : Qb), hqA⟩, ⟨((q : Qb))⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hq0),
      Subtype.ext (inv_mul_cancel₀ hq0)⟩, rfl⟩
  have := (A.valuation_eq_one_iff _).mp hunit
  simp only at this
  rw [this] at hq1
  exact lt_irrefl _ hq1

theorem natCast_mem_and_inv_mem (hA : A.LiesOverPrime q) (n : ℕ) (hn : ¬ q ∣ n) :
    (n : ℚ) ∈ ratPart A ∧ ((n : ℚ))⁻¹ ∈ ratPart A := by
  refine ⟨(mem_ratPart_iff _).mpr (by simpa using natCast_mem A n), ?_⟩
  obtain ⟨u, hu⟩ := isUnit_intCast_of_not_dvd hA (n : ℤ) (by exact_mod_cast hn)
  rw [mem_ratPart_iff, map_inv₀, map_natCast]
  have hn0 : (n : Qb) ≠ 0 := by
    intro h0
    rw [Int.cast_natCast, h0, mul_zero] at hu
    exact zero_ne_one hu
  have : ((n : Qb))⁻¹ = (u : Qb) := by
    rw [Int.cast_natCast] at hu
    exact (eq_inv_of_mul_eq_one_left hu).symm
  rw [this]; exact u.2

theorem exists_unit_mul_pow_div_pow (hA : A.LiesOverPrime q) (r : ℚ) (hr : r ≠ 0) :
    ∃ (u : ℚ) (a b : ℕ), u ∈ ratPart A ∧ u⁻¹ ∈ ratPart A ∧ u ≠ 0 ∧
      r = u * (q : ℚ) ^ a / (q : ℚ) ^ b := by
  have hq1 : q ≠ 1 := hq.out.ne_one
  have hnum0 : r.num.natAbs ≠ 0 := by
    rw [ne_eq, Int.natAbs_eq_zero]; exact Rat.num_ne_zero.mpr hr
  obtain ⟨a, n', hn', hnum⟩ := Nat.exists_eq_pow_mul_and_not_dvd hnum0 q hq1
  obtain ⟨b, d', hd', hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd r.den_nz q hq1
  obtain ⟨hn'mem, hn'inv⟩ := natCast_mem_and_inv_mem hA n' hn'
  obtain ⟨hd'mem, hd'inv⟩ := natCast_mem_and_inv_mem hA d' hd'
  have hn'0 : (n' : ℚ) ≠ 0 := by
    intro h0; apply hnum0; rw [hnum]
    have : n' = 0 := by exact_mod_cast h0
    rw [this, mul_zero]
  have hd'0 : (d' : ℚ) ≠ 0 := by
    intro h0; apply r.den_nz; rw [hden]
    have : d' = 0 := by exact_mod_cast h0
    rw [this, mul_zero]
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdenZ : (r.den : ℚ) = (d' : ℚ) * (q : ℚ) ^ b := by
    rw [hden]; push_cast; ring
  obtain ⟨ε, hε, hnumZ⟩ : ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ (r.num : ℚ) = ε * n' * (q : ℚ) ^ a := by
    rcases Int.natAbs_eq r.num with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h, hnum]; push_cast; ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [h, hnum]; push_cast; ring
  have hεmem : ε ∈ ratPart A ∧ ε⁻¹ ∈ ratPart A ∧ ε ≠ 0 := by
    rcases hε with rfl | rfl
    · exact ⟨one_mem _, by rw [inv_one]; exact one_mem _, one_ne_zero⟩
    · exact ⟨neg_mem (one_mem _), by rw [inv_neg, inv_one]; exact neg_mem (one_mem _),
        neg_ne_zero.mpr one_ne_zero⟩
  refine ⟨ε * n' / d', a, b, ?_, ?_, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    exact mul_mem (mul_mem hεmem.1 hn'mem) hd'inv
  · rw [inv_div, div_eq_mul_inv, mul_inv]
    exact mul_mem hd'mem (mul_mem hεmem.2.1 hn'inv)
  · exact div_ne_zero (mul_ne_zero hεmem.2.2 hn'0) hd'0
  · conv_lhs => rw [← Rat.num_div_den r]
    rw [hnumZ, hdenZ]
    field_simp

theorem inv_q_not_mem_ratPart (hA : A.LiesOverPrime q) : ((q : ℚ))⁻¹ ∉ ratPart A := by
  rw [mem_ratPart_iff, map_inv₀, map_natCast]
  exact inv_natCast_q_not_mem hA

theorem q_mem_ratPart : (q : ℚ) ∈ ratPart A := by
  rw [mem_ratPart_iff, map_natCast]; exact natCast_mem A q

theorem le_of_mem_ratPart (hA : A.LiesOverPrime q) {u : ℚ} {a b : ℕ}
    (hu : u⁻¹ ∈ ratPart A) (hu0 : u ≠ 0)
    (hmem : u * (q : ℚ) ^ a / (q : ℚ) ^ b ∈ ratPart A) : b ≤ a := by
  by_contra hlt
  push Not at hlt
  apply inv_q_not_mem_ratPart hA
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have key : ((q : ℚ))⁻¹ = (u * (q : ℚ) ^ a / (q : ℚ) ^ b) * u⁻¹ * (q : ℚ) ^ (b - a - 1) := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt hlt
    rw [hc, show a + c + 1 - a - 1 = c by omega]
    field_simp
    ring
  rw [key]
  exact mul_mem (mul_mem hmem hu) (pow_mem q_mem_ratPart _)

theorem inv_mem_ratPart_of_div_not_mem (hA : A.LiesOverPrime q) {r : ℚ} (hr : r ∈ ratPart A)
    (hdiv : r / (q : ℚ) ∉ ratPart A) : r⁻¹ ∈ ratPart A := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl; apply hdiv; rw [zero_div]; exact zero_mem _
  obtain ⟨u, a, b, hu, hui, hu0, hreq⟩ := exists_unit_mul_pow_div_pow hA r hr0
  have hba : b ≤ a := le_of_mem_ratPart hA hui hu0 (hreq ▸ hr)
  have hab : a ≤ b := by
    by_contra hlt
    push Not at hlt
    apply hdiv
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt hlt
    have : r / (q : ℚ) = u * (q : ℚ) ^ c := by
      rw [hreq, hc]
      field_simp
      ring
    rw [this]
    exact mul_mem hu (pow_mem q_mem_ratPart _)
  have hab' : a = b := le_antisymm hab hba
  have : r⁻¹ = u⁻¹ := by
    rw [hreq, hab']
    field_simp
  rw [this]
  exact hui

theorem div_mem_ratPart_of_mem_maximalIdeal (hA : A.LiesOverPrime q) {r : ℚ} (hr : r ∈ ratPart A)
    (hmax : (⟨algebraMap ℚ Qb r, (mem_ratPart_iff r).mp hr⟩ : ↥A) ∈ maximalIdeal ↥A) :
    r / (q : ℚ) ∈ ratPart A := by
  by_contra hdiv
  have hinv := inv_mem_ratPart_of_div_not_mem hA hr hdiv
  have hr0 : r ≠ 0 := by
    rintro rfl; apply hdiv; rw [zero_div]; exact zero_mem _
  have hr0' : algebraMap ℚ Qb r ≠ 0 := (map_ne_zero _).mpr hr0
  have hunit : IsUnit (⟨algebraMap ℚ Qb r, (mem_ratPart_iff r).mp hr⟩ : ↥A) := by
    have hinvA : (algebraMap ℚ Qb r)⁻¹ ∈ A := by rw [← map_inv₀]; exact (mem_ratPart_iff _).mp hinv
    refine ⟨⟨⟨algebraMap ℚ Qb r, (mem_ratPart_iff r).mp hr⟩, ⟨_, hinvA⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · exact mul_inv_cancel₀ hr0'
    · exact inv_mul_cancel₀ hr0'
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hunit

end RatDVR

section FunctionField

variable {M' : ℕ} [NeZero M']

theorem coeffEmb_smul_eq_mul (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) (x : LaurentSeries ℚ) :
    coeffEmb L (r • x) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) * coeffEmb L x := by
  have h1 : coeffEmb L (r • x) = (algebraMap ℚ L r) • coeffEmb L x := by
    ext k
    rw [coeffEmb_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul, smul_eq_mul,
      map_mul]
  rw [h1, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]

theorem smul_eq_algebraMap_mul (r : ℚ) (x : LaurentSeries ℚ) :
    r • x = algebraMap ℚ (LaurentSeries ℚ) r * x := by
  rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]

theorem ord_algebraMap {L F : Type*} [Field L] [Field F] [Algebra L F] (P : Place L F) {c : L} (hc : c ≠ 0) :
    P.ord (algebraMap L F c) = 0 := by
  have hu : IsUnit (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) :=
    ⟨⟨⟨algebraMap L F c, P.algebraMap_mem' c⟩, ⟨algebraMap L F c⁻¹, P.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

theorem ord_algebraMap_mul {L F : Type*} [Field L] [Field F] [Algebra L F] (P : Place L F) {c : L} (hc : c ≠ 0)
    (f : F) : P.ord (algebraMap L F c * f) = P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [P.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap P hc, zero_add]

end FunctionField

end QExpKernelGauss
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular.QExpKernelGauss"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular.QExpKernelGauss"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups
open QExpKernelGauss

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')))
    (hzero : R₀.residue ⟨_, hgi⟩ = 0) :
    ∃ (g' : LaurentSeries ℚ) (hg' : g' ∈ modularFunctionFieldFull M'),
      (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers ∧
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
      g = (q : LaurentSeries ℚ) * g' := by
  classical
  have hqprime : Nat.Prime q := Fact.out
  have hq0Q : (q : ℚ) ≠ 0 := by exact_mod_cast hqprime.ne_zero

  have hcoefA : ∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n) ∈ A := fun n =>
    ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular q M' A hA R₀ hR₀ g hg hgi hcusp n
  have hgcoeff : ∀ n, (coeffEmb (AlgebraicClosure ℚ) g).coeff n ∈ A := fun n => by
    rw [coeffEmb_coeff]; exact hcoefA n
  set y : LaurentSeries ↥A := liftVal A (coeffEmb (AlgebraicClosure ℚ) g) hgcoeff with hydef
  have hyeq : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g := coeffMap_subtype_liftVal A _ hgcoeff
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M' := by
    rw [hyeq]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg
  obtain ⟨hyint, hyres⟩ := hR₀ y hy
  have helt : (⟨⟨coeffMap A.subtype y, hy⟩, hyint⟩ : ↥R₀.integers) =
      ⟨⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩, hgi⟩ :=
    Subtype.ext (Subtype.ext hyeq)
  have hres0 : coeffMap (IsLocalRing.residue ↥A) y = 0 := by
    rw [← hyres, helt, hzero]; rfl
  have hmax : ∀ n : ℤ,
      (⟨algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n), hcoefA n⟩ : ↥A) ∈ maximalIdeal ↥A := by
    intro n
    have h1 := congrArg (fun z : LaurentSeries (ResidueField ↥A) => z.coeff n) hres0
    simp only [HahnSeries.coeff_zero] at h1
    rw [coeffMap_coeff] at h1
    have : (y.coeff n : ↥A) = ⟨algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n), hcoefA n⟩ :=
      Subtype.ext (by rw [hydef, coeff_liftVal, coeffEmb_coeff])
    rw [← this]
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1

  have hdiv : ∀ n : ℤ, g.coeff n / (q : ℚ) ∈ ratPart A := fun n =>
    div_mem_ratPart_of_mem_maximalIdeal hA ((mem_ratPart_iff _).mpr (hcoefA n)) (hmax n)

  set g' : LaurentSeries ℚ := ((q : ℚ)⁻¹) • g with hg'def
  have hgeq : g = (q : LaurentSeries ℚ) * g' := by
    rw [hg'def, ← map_natCast (algebraMap ℚ (LaurentSeries ℚ)) q, ← smul_eq_algebraMap_mul, smul_smul,
      mul_inv_cancel₀ hq0Q, one_smul]
  have hg'F : g' ∈ modularFunctionFieldFull M' := by
    rw [hg'def, smul_eq_algebraMap_mul]
    exact mul_mem (IntermediateField.algebraMap_mem (modularFunctionFieldFull M') _) hg
  have hg'coeff : ∀ n, (coeffEmb (AlgebraicClosure ℚ) g').coeff n ∈ A := by
    intro n
    rw [coeffEmb_coeff, hg'def, HahnSeries.coeff_smul, smul_eq_mul, inv_mul_eq_div]
    exact (mem_ratPart_iff _).mp (hdiv n)

  set y' : LaurentSeries ↥A := liftVal A (coeffEmb (AlgebraicClosure ℚ) g') hg'coeff with hy'def
  have hy'eq : coeffMap A.subtype y' = coeffEmb (AlgebraicClosure ℚ) g' := coeffMap_subtype_liftVal A _ hg'coeff
  have hy' : coeffMap A.subtype y' ∈ modularFunctionFieldBar M' := by
    rw [hy'eq]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F
  obtain ⟨hy'int, -⟩ := hR₀ y' hy'
  have hgi' : (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
    have helt' : (⟨coeffMap A.subtype y', hy'⟩ : ↥(modularFunctionFieldBar M')) =
        ⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ :=
      Subtype.ext hy'eq
    rw [← helt']; exact hy'int

  have hrel : (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ :
      ↥(modularFunctionFieldBar M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ)⁻¹) *
        ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ := by
    apply Subtype.ext
    change coeffEmb (AlgebraicClosure ℚ) g' = _
    rw [hg'def, coeffEmb_smul_eq_mul]
    rfl
  have hcusp' : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) := by
    intro P hP
    rw [hrel, ord_algebraMap_mul P ((map_ne_zero _).mpr (inv_ne_zero hq0Q))]
    exact hcusp P hP
  exact ⟨g', hg'F, hgi', hcusp', hgeq⟩

end S_ModularCurve_exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
end P2MW
export P2MW.S_ModularCurve_exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular (solution)
