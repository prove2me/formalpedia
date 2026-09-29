-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e9df0aa5-3802-5317-8daa-1770dbfd85b5

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace OrbitIntLevel

theorem natCast_mem_nonunits_of_ringHom_charP {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hle : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hu : IsUnit ((⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ : A)) := (A.valuation_eq_one_iff _).mpr h
    have h2 := hu.map red
    have h3 : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ = ((q : ℕ) : k) := by
      rw [← map_natCast red q]
      congr 1
    rw [h3, CharP.cast_eq_zero k q] at h2
    exact not_isUnit_zero h2

theorem exists_valuation_eq_pow_of_mem_of_forall_mem_inertiaSubgroupIn
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    {z : AlgebraicClosure ℚ} (hzA : z ∈ A) (hz0 : z ≠ 0)
    (hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ z = z) :
    ∃ d : ℕ, A.valuation z = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ d := by
  classical
  obtain ⟨O, hSO, hOA, -, hDVR, hirr, -⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_inertiaSubgroupIn q A hA {z}
      (fun x hx => by
        rw [Finset.mem_singleton] at hx
        subst hx
        exact ⟨hzA, fun σ hσ => hzfix σ hσ⟩)
  have hzO : z ∈ O := hSO (by simp)
  haveI : IsDiscreteValuationRing O := hDVR
  have hz0' : (⟨z, hzO⟩ : O) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz0' hirr
  refine ⟨n, ?_⟩
  have hvu : A.valuation (((u : O) : O) : AlgebraicClosure ℚ) = 1 := by
    apply le_antisymm
    · exact (A.valuation_le_one_iff _).mpr (hOA (u : O).2)
    · have h1 : A.valuation (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (hOA ((u⁻¹ : Oˣ) : O).2)
      have hmul : (((u : O) : AlgebraicClosure ℚ)) * (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
      have h2 : A.valuation (((u : O) : AlgebraicClosure ℚ)) * A.valuation (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
        rw [← map_mul, hmul, map_one]
      by_contra hlt
      push Not at hlt
      have := mul_lt_one_of_lt_of_le hlt h1
      exact absurd h2 this.ne
  have h := congrArg (fun t : O => A.valuation (t : AlgebraicClosure ℚ)) hu
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvu, mul_one] at h
  convert h using 2
  all_goals first | rfl | simp

theorem exists_valuation_eq_zpow_of_forall_mem_inertiaSubgroupIn
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    {z : AlgebraicClosure ℚ} (hz0 : z ≠ 0)
    (hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ z = z) :
    ∃ e : ℤ, A.valuation z = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ e := by
  rcases A.mem_or_inv_mem z with h | h
  · obtain ⟨d, hd⟩ := exists_valuation_eq_pow_of_mem_of_forall_mem_inertiaSubgroupIn hA h hz0 hzfix
    exact ⟨d, by rw [hd, zpow_natCast]⟩
  · obtain ⟨d, hd⟩ := exists_valuation_eq_pow_of_mem_of_forall_mem_inertiaSubgroupIn hA h (inv_ne_zero hz0)
      (fun σ hσ => by rw [map_inv₀, hzfix σ hσ])
    refine ⟨-(d : ℤ), ?_⟩
    rw [map_inv₀] at hd
    rw [zpow_neg, zpow_natCast, ← hd, inv_inv]

section ValueGroup
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem zpow_injective_of_lt_one {γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1) : Function.Injective fun n : ℤ => γ ^ n := by
  intro m n hmn
  simp only at hmn
  set u : Γˣ := Units.mk0 γ h0 with hu
  have hu1 : u < 1 := by
    rw [← Units.val_lt_val, hu, Units.val_mk0, Units.val_one]; exact h1
  have hum : ∀ k : ℤ, ((u ^ k : Γˣ) : Γ) = γ ^ k := fun k => by
    rw [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
  have h' : u ^ m = u ^ n := Units.ext (by rw [hum, hum]; exact hmn)
  have hinv : 1 < u⁻¹ := one_lt_inv'.mpr hu1
  have hsm : StrictMono fun k : ℤ => (u⁻¹) ^ k := zpow_right_strictMono hinv
  have : (u⁻¹) ^ (-m) = (u⁻¹) ^ (-n) := by
    rw [inv_zpow', inv_zpow', neg_neg, neg_neg, h']
  have := hsm.injective this
  omega

end ValueGroup

theorem den_eq_one_of_eq_intCast {x : ℚ} {m : ℤ} (h : x = m) : x.den = 1 := by
  rw [h]; exact Rat.den_intCast m

theorem exists_int_mul_eq_of_den_dvd (t : ℚ) (n : ℤ) (h : (t.den : ℤ) ∣ n) : ∃ m : ℤ, (n : ℚ) * t = m := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * t.num, ?_⟩
  rw [hc]
  push_cast
  have := Rat.mul_den_eq_num t
  calc (t.den : ℚ) * c * t = c * (t * t.den) := by ring
    _ = c * t.num := by rw [this]

theorem exists_int_mul_tent (n : ℤ) (t : ℚ) (d : ℕ) (h : ∃ m : ℤ, (n : ℚ) * t = m) :
    ∃ m : ℤ, (n : ℚ) * max 0 (1 - |t - d|) = m := by
  obtain ⟨m, hm⟩ := h
  rcases le_or_gt 1 |t - (d : ℚ)| with h1 | h1
  · refine ⟨0, ?_⟩
    rw [max_eq_left (by linarith), mul_zero, Int.cast_zero]
  · rw [max_eq_right (by linarith)]

    have habs : ∃ m' : ℤ, (n : ℚ) * |t - d| = m' := by
      rcases lt_trichotomy n 0 with hn | hn | hn
      · refine ⟨-|m - n * d|, ?_⟩
        have : (n : ℚ) = -|(n : ℚ)| := by
          rw [abs_of_neg (by exact_mod_cast hn), neg_neg]
        rw [this, neg_mul, ← abs_mul, mul_sub, hm]
        push_cast
        ring_nf
      · exact ⟨0, by rw [hn]; simp⟩
      · refine ⟨|m - n * d|, ?_⟩
        have : (n : ℚ) = |(n : ℚ)| := (abs_of_pos (by exact_mod_cast hn)).symm
        rw [this, ← abs_mul, mul_sub, hm]
        push_cast
        ring_nf
    obtain ⟨m', hm'⟩ := habs
    refine ⟨n - m', ?_⟩
    rw [mul_sub, mul_one, hm']
    push_cast
    ring

end OrbitIntLevel

namespace OrbitIntLevel

theorem prod_zpow_eq_zpow_sum₀ {Γ : Type*} [CommGroupWithZero Γ] {ι : Type*} (s : Finset ι) (γ : Γ) (hγ : γ ≠ 0)
    (f : ι → ℤ) : ∏ i ∈ s, γ ^ f i = γ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hγ]

theorem zpow_pow_comm₀ {Γ : Type*} [CommGroupWithZero Γ] (a : Γ) (e : ℤ) (d : ℕ) :
    (a ^ e) ^ d = (a ^ d) ^ e := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

set_option maxHeartbeats 6400000 in

theorem core {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k (modularFunctionFieldC k N))} (dat : R.AnnulusDatumLevel W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hKfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hlaw : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
        0 < dat.depthQ V ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hEstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V, V ∈ S ↔ V ∈ E.support ∧ P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
    (t : ℚ) :
    ∃ m : ℤ, ((∑ V ∈ S.filter (fun V => dat.depthQ V = t), E V : ℤ) : ℚ) * t = m := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  set St : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) := S.filter (fun V => dat.depthQ V = t) with hSt
  have hmemSt : ∀ V, V ∈ St ↔ (V ∈ E.support ∧ P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) ∧
      dat.depthQ V = t := fun V => by rw [hSt, Finset.mem_filter, hS]

  by_cases hne : St = ∅
  · refine ⟨0, ?_⟩
    simp [hne]
  obtain ⟨V₀, hV₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne

  have hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := natCast_mem_nonunits_of_ringHom_charP red
  set γ : A.ValueGroup := A.valuation ((q : ℕ) : AlgebraicClosure ℚ) with hγ
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hγ0 : γ ≠ 0 := by rw [hγ]; exact (Valuation.ne_zero_iff _).mpr hq0
  have hγ1 : γ < 1 := by rw [hγ]; exact (ValuationSubring.mem_nonunits_iff A).mp hA

  have ht : 0 < t := by
    obtain ⟨⟨-, h1, h2, h3⟩, h4⟩ := (hmemSt V₀).mp hV₀
    rw [← h4]; exact (hlaw V₀ h1 h2 h3).1

  set y : ↥(modularFunctionFieldBar (N * q)) := (((dat.coord w hw).y : ↥(R.nodeIntegersOver (dat.K w) w)) : ↥(modularFunctionFieldBar (N * q))) with hy
  have hyO : y ∈ R.nodeIntegersOver (dat.K w) w := ((dat.coord w hw).y : ↥(R.nodeIntegersOver (dat.K w) w)).2
  have hyDepth : ∀ V, (dat.coord w hw).yDepth V = A.valuation (V.evalAt y) := fun V => rfl

  have hlawSt : ∀ V ∈ St, A.valuation (V.evalAt y) ^ t.den = γ ^ t.num := by
    intro V hV
    obtain ⟨⟨-, h1, h2, h3⟩, h4⟩ := (hmemSt V).mp hV
    have hl := (hlaw V h1 h2 h3).2
    rw [hyDepth, h4] at hl
    rw [hl, hγ, ← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht.le)
  have hyne : ∀ V ∈ St, V.evalAt y ≠ 0 := by
    intro V hV h0
    have hl := hlawSt V hV
    rw [h0, map_zero, zero_pow (Rat.den_pos t).ne'] at hl
    exact (zpow_ne_zero t.num hγ0) hl.symm

  have hEσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), E (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = E V := by
    intro σ hσ V
    have := SemilinearAut.divisor_smul_apply_smul (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) E V
    rw [hEstab σ hσ] at this
    exact this
  have hstrict₁ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) ↔ P.IsStrictFst V := by
    intro σ hσ V
    unfold PlaceSpecialization.IsStrictFst
    rw [reduceFst_arithmeticGalois_smul P σ hσ, reduceSnd_arithmeticGalois_smul P σ hσ]
  have hstrict₂ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) ↔ P.IsStrictSnd V := by
    intro σ hσ V
    unfold PlaceSpecialization.IsStrictSnd
    rw [reduceFst_arithmeticGalois_smul P σ hσ, reduceSnd_arithmeticGalois_smul P σ hσ]
  have hSσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ St, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V ∈ St := by
    intro σ hσ V hV
    obtain ⟨⟨h0, h1, h2, h3⟩, h4⟩ := (hmemSt V).mp hV
    refine (hmemSt _).mpr ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Finsupp.mem_support_iff] at h0 ⊢
      rw [hEσ σ hσ]; exact h0
    · rw [reduceFst_arithmeticGalois_smul P σ hσ]; exact h1
    · rw [hstrict₁ σ hσ]; exact h2
    · rw [hstrict₂ σ hσ]; exact h3
    · rw [hdepthσ σ hσ]; exact h4

  have hval : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V).evalAt y = σ (V.evalAt y) := by
    intro σ hσ V
    have hVrat : V.IsRational := (Place.isRational_iff_deg_eq_one V).mpr (deg_eq_one_modularFunctionFieldBar (N * q) V)
    exact (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (N * q) (dat.K w) σ
      (hKfix σ hσ) y hyO.2).2 V hVrat

  set z : AlgebraicClosure ℚ := ∏ V ∈ St, (V.evalAt y) ^ (E V) with hz
  have hz0 : z ≠ 0 := by
    rw [hz]; exact Finset.prod_ne_zero_iff.mpr fun V hV => zpow_ne_zero _ (hyne V hV)
  have hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ z = z := by
    intro σ hσ
    rw [hz, map_prod]
    simp_rw [map_zpow₀]
    have step : ∏ V ∈ St, σ (V.evalAt y) ^ E V = ∏ V ∈ St, ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V).evalAt y) ^ E (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) :=
      Finset.prod_congr rfl fun V _ => by rw [hval σ hσ V, hEσ σ hσ V]
    rw [step]
    refine Finset.prod_nbij (fun V => arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) (fun V hV => hSσ σ hσ V hV) ?_ ?_ (fun V _ => rfl)
    · intro V₁ _ V₂ _ h
      exact MulAction.injective (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) h
    · intro V' hV'
      refine ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • V', ?_, ?_⟩
      · exact hSσ σ⁻¹ (Subgroup.inv_mem _ hσ) V' hV'
      · show arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • V') = V'
        rw [map_inv, smul_inv_smul]

  obtain ⟨e, he⟩ := exists_valuation_eq_zpow_of_forall_mem_inertiaSubgroupIn hA hz0 hzfix
  rw [← hγ] at he
  have hvz : A.valuation z = ∏ V ∈ St, A.valuation (V.evalAt y) ^ (E V) := by
    rw [hz, map_prod]; simp_rw [map_zpow₀]
  set n : ℤ := ∑ V ∈ St, E V with hn
  have hpow : γ ^ (e * t.den) = γ ^ (t.num * n) := by
    calc γ ^ (e * t.den) = (A.valuation z) ^ t.den := by rw [zpow_mul, ← he, zpow_natCast]
      _ = ∏ V ∈ St, (A.valuation (V.evalAt y) ^ (E V)) ^ t.den := by rw [hvz, Finset.prod_pow]
      _ = ∏ V ∈ St, (γ ^ t.num) ^ (E V) := Finset.prod_congr rfl fun V hV => by
            rw [zpow_pow_comm₀, hlawSt V hV]
      _ = ∏ V ∈ St, γ ^ (t.num * E V) := Finset.prod_congr rfl fun V _ => by rw [zpow_mul]
      _ = γ ^ (∑ V ∈ St, t.num * E V) := prod_zpow_eq_zpow_sum₀ St γ hγ0 _
      _ = γ ^ (t.num * n) := by rw [hn, Finset.mul_sum]
  have hexp : e * t.den = t.num * n := zpow_injective_of_lt_one hγ0 hγ1 hpow
  have hdvd : (t.den : ℤ) ∣ t.num * n := ⟨e, by rw [← hexp, mul_comm]⟩
  have hgcd : Int.gcd (t.den : ℤ) t.num = 1 := by
    rw [Int.gcd_comm]
    exact t.reduced
  have hdvd' : (t.den : ℤ) ∣ n := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hgcd
  exact exists_int_mul_eq_of_den_dvd t n hdvd'

end OrbitIntLevel

open OrbitIntLevel in
open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (dat : R.AnnulusDatumLevel W)
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    E
    (hEstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E) :
    (∀ w ∈ W, ∀ d : ℕ, (dat.circleDeg E w d).den = 1) ∧ (∀ w ∈ W, (dat.depthMoment E w).den = 1) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have key : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (t : ℚ),
      ∃ m : ℤ, ((∑ V ∈ (E.support.filter
          (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)).filter (fun V => dat.depthQ V = t),
          E V : ℤ) : ℚ) * t = m := by
    intro w hw t
    refine core dat w hw (hKfix w hw) (fun V h1 h2 h3 => ?_) hdepthσ E hEstab _
      (fun V => by rw [Finset.mem_filter]) t
    obtain ⟨hpos, -, hlaw⟩ := hdepthQ w hw V h1 h2 h3
    exact ⟨hpos, hlaw⟩

  have regroup : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (φ : ℚ → ℚ)
      (hφ : ∀ (t : ℚ) (n : ℤ), (∃ m : ℤ, (n : ℚ) * t = m) → ∃ m : ℤ, (n : ℚ) * φ t = m),
      ∃ M : ℤ, (∑ V ∈ E.support.filter
          (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
          (E V : ℚ) * φ (dat.depthQ V)) = M := by
    intro w hw φ hφ
    set S := E.support.filter
      (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) with hS
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image dat.depthQ) (g := dat.depthQ)
      (fun V hV => Finset.mem_image_of_mem _ hV)
      (fun V => (E V : ℚ) * φ (dat.depthQ V))]
    have inner : ∀ t ∈ S.image dat.depthQ, ∃ m : ℤ,
        (∑ V ∈ S.filter (fun V => dat.depthQ V = t), (E V : ℚ) * φ (dat.depthQ V)) = m := by
      intro t _
      have h1 : (∑ V ∈ S.filter (fun V => dat.depthQ V = t), (E V : ℚ) * φ (dat.depthQ V))
          = (∑ V ∈ S.filter (fun V => dat.depthQ V = t), (E V : ℚ)) * φ t := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun V hV => ?_
        rw [(Finset.mem_filter.mp hV).2]
      rw [h1, ← Int.cast_sum]
      exact hφ t _ (key w hw t)
    choose m hm using inner
    refine ⟨∑ t ∈ (S.image dat.depthQ).attach, m t t.2, ?_⟩
    rw [← Finset.sum_attach (S.image dat.depthQ)]
    push_cast
    exact Finset.sum_congr rfl fun t _ => hm t t.2
  refine ⟨fun w hw d => ?_, fun w hw => ?_⟩
  · obtain ⟨M, hM⟩ := regroup w hw (fun t => max 0 (1 - |t - d|)) (fun t n h => exists_int_mul_tent n t d h)
    unfold ProlongationTuple.AnnulusDatumLevel.circleDeg
    exact den_eq_one_of_eq_intCast hM
  · obtain ⟨M, hM⟩ := regroup w hw (fun t => t) (fun t n h => h)
    unfold ProlongationTuple.AnnulusDatumLevel.depthMoment
    exact den_eq_one_of_eq_intCast hM

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable (solution)
