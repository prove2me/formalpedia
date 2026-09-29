-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_evalAt_lt_one_iff_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8fd84675-f010-538a-a65b-891b3193c4fc

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place.isRational_iff_deg_eq_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ResidueField toValuationSubring IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt evalAt_one evalAt_algebraMap isRational_iff_deg_eq_one evalAt_mul"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.evalAt_add_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_add_of_mem"
private theorem _root_.AlgebraicCurve.Place.evalAt_zero_eq : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), v.evalAt_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_zero_eq"

private noncomputable def _root_.AlgebraicCurve.Place.evalRingHom (hv : v.IsRational) (B : Subring F) (hB : ∀ g ∈ B, g ∈ v.toValuationSubring) :
    B →+* K where
  toFun g := v.evalAt (g : F)
  map_one' := by rw [OneMemClass.coe_one, v.evalAt_one]
  map_mul' a b := by rw [MulMemClass.coe_mul, v.evalAt_mul hv (hB _ a.2) (hB _ b.2)]
  map_zero' := by rw [ZeroMemClass.coe_zero, v.evalAt_zero_eq]
  map_add' a b := by rw [AddMemClass.coe_add, v.evalAt_add_of_mem hv (hB _ a.2) (hB _ b.2)]

p2m_export "AlgebraicCurve.Place" "evalRingHom"
theorem evalRingHom_apply (hv : v.IsRational) (B : Subring F) (hB : ∀ g ∈ B, g ∈ v.toValuationSubring) (g : B) :
    v.evalRingHom hv B hB g = v.evalAt (g : F) := rfl

end AlgebraicCurve.Place

theorem isField_of_forall_exists_pow_eq_self {S : Type*} [CommRing S] [IsDomain S]
    (h : ∀ b : S, b ≠ 0 → ∃ n : ℕ, 2 ≤ n ∧ b ^ n = b) : IsField S := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {b} hb => ?_⟩
  obtain ⟨n, hn, hbn⟩ := h b hb
  refine ⟨b ^ (n - 2), ?_⟩
  have : b * (b * b ^ (n - 2)) = b * 1 := by
    rw [mul_one, ← pow_succ', ← pow_succ', show n - 2 + 1 + 1 = n by omega, hbn]
  exact mul_left_cancel₀ hb this

open ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] (hVI : R.ValueIntegralityLaw w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) (g : ↥(R.nodeIntegersOver K w)) :
    A.valuation (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) < 1 ↔ g ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by

  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  have hVr : V.IsRational := (Place.isRational_iff_deg_eq_one V).2 (IsCurveOver.deg_eq_one_of_isAlgClosed V)
  let ev := Place.evalRingHom V hVr (R.nodeIntegersOver K w) (fun g hg => hg.1.2.2 V hV)
  have hevA : ∀ b : ↥(R.nodeIntegersOver K w), ev b ∈ A.toSubring := fun b => hVI _ b.2.1 V hV
  let evA : ↥(R.nodeIntegersOver K w) →+* A := ev.codRestrict A.toSubring hevA
  have hevA_coe : ∀ b : ↥(R.nodeIntegersOver K w),
      ((evA b : A) : AlgebraicClosure ℚ) = V.evalAt (b : ↥(modularFunctionFieldBar (N * q))) := fun b => rfl

  have hq𝔪 : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red, map_natCast,
      CharP.cast_eq_zero]
  have hA : A.LiesOverPrime q := by
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    rw [ValuationSubring.mem_nonunits_iff, show ((q : ℕ) : AlgebraicClosure ℚ) = (((q : ℕ) : A) : AlgebraicClosure ℚ) by
      norm_cast]
    exact (ValuationSubring.valuation_lt_one_iff A _).1 hq𝔪

  let φ : ↥(R.nodeIntegersOver K w) →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp evA
  set 𝔓 : Ideal ↥(R.nodeIntegersOver K w) := RingHom.ker φ with h𝔓
  haveI h𝔓p : 𝔓.IsPrime := RingHom.ker_isPrime φ

  have hfield : IsField (↥(R.nodeIntegersOver K w) ⧸ 𝔓) := by
    haveI : IsDomain (↥(R.nodeIntegersOver K w) ⧸ 𝔓) := Ideal.Quotient.isDomain 𝔓
    apply isField_of_forall_exists_pow_eq_self
    intro b hb
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨n, hn, hpow⟩ :=
      ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime A (Fact.out : q.Prime) hA (φ b)
    refine ⟨q ^ n, ?_, ?_⟩
    · calc 2 ≤ q := (Fact.out : q.Prime).two_le
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ n := Nat.pow_le_pow_right (Fact.out : q.Prime).pos hn
    ·
      rw [← map_pow, Ideal.Quotient.eq, h𝔓, RingHom.mem_ker, map_sub, map_pow, hpow, sub_self]
  have hmax : 𝔓 = IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) :=
    IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField 𝔓 hfield)

  rw [← hmax, h𝔓, RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff A (evA g), hevA_coe]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal (solution)
