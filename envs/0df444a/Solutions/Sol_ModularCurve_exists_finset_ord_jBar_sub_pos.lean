-- Prove2me | solution 1 for ModularCurve.exists_finset_ord_jBar_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ac7c507d-cc79-55ea-a71e-825ca6c0ac54

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_finset_ord_jBar_sub_pos
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_finset_ord_jBar_sub_pos.ModularCurve IsDedekindDomain WithZero"

namespace B2Peo3

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (w : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ w.ord f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

theorem mem_of_ord_sub_pos (w : Place K F) {f : F} {c : K}
    (h : 0 < w.ord (f - algebraMap K F c)) : f ∈ w.toValuationSubring := by
  have hne : f - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have := add_mem (mem_of_ord_nonneg w hne h.le) (w.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

theorem ord_eq_one_of_valuation_eq (w : Place K F) {v' : Valuation F ℤᵐ⁰}
    (hv' : v'.valuationSubring = w.toValuationSubring) {x : F} (hx : v' x = exp (-1 : ℤ)) :
    w.ord x = 1 := by
  have hE := w.isEquiv_adicValuation_of_valuationSubring_eq hv'
  have hx0 : v' x ≠ 0 := by rw [hx]; exact exp_ne_zero
  have hu0 : w.adicValuation x ≠ 0 := (hE.eq_zero).ne.mp hx0

  have hlt : w.adicValuation x < 1 := by
    refine hE.lt_one_iff_lt_one.mp ?_
    rw [hx, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)

  obtain ⟨ϖ, hϖ⟩ := w.heightOneSpectrum.valuation_exists_uniformizer F
  change w.adicValuation ϖ = exp (-1 : ℤ) at hϖ
  have hϖ0 : w.adicValuation ϖ ≠ 0 := by rw [hϖ]; exact exp_ne_zero
  have hϖlt : v' ϖ < 1 := by
    refine hE.lt_one_iff_lt_one.mpr ?_
    rw [hϖ, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  have hϖ0' : v' ϖ ≠ 0 := (hE.eq_zero).ne.mpr hϖ0
  have hϖle : v' ϖ ≤ v' x := by
    rw [hx, ← log_le_iff_le_exp hϖ0']
    have hlog : log (v' ϖ) < 0 := (log_lt_iff_lt_exp hϖ0').mpr (by rw [exp_zero]; exact hϖlt)
    omega
  have hge : exp (-1 : ℤ) ≤ w.adicValuation x := by
    rw [← hϖ]
    exact (hE ϖ x).mp hϖle

  have hle' : log (w.adicValuation x) ≤ -1 := by
    have hlog : log (w.adicValuation x) < 0 := (log_lt_iff_lt_exp hu0).mpr (by rw [exp_zero]; exact hlt)
    omega
  have hge' : -1 ≤ log (w.adicValuation x) := (le_log_iff_exp_le hu0).mpr hge
  simp only [Place.ord]
  omega

scoped instance instIsPrincipalIdealRingAdjoinSingleton (t : F) :
    IsPrincipalIdealRing (Algebra.adjoin K ({t} : Set F)) := by
  have hmem : ∀ p : Polynomial K, Polynomial.aeval t p ∈ Algebra.adjoin K ({t} : Set F) := by
    intro p
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  refine IsPrincipalIdealRing.of_surjective
    ((Polynomial.aeval t).codRestrict (Algebra.adjoin K ({t} : Set F)) hmem) ?_
  rintro ⟨a, ha⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial K, Polynomial.aeval t p = a := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    exact (AlgHom.mem_range _).mp ha
  exact ⟨p, Subtype.ext hp⟩

def linGen (t : F) (c : K) : Algebra.adjoin K ({t} : Set F) :=
  ⟨t, Algebra.self_mem_adjoin_singleton K t⟩ - algebraMap K _ c

@[scoped simp] theorem coe_linGen (t : F) (c : K) :
    ((linGen t c : Algebra.adjoin K ({t} : Set F)) : F) = t - algebraMap K F c := by
  simp [linGen]

section Transcendental

variable (t : F) (htr : Transcendental K t)

include htr in
theorem linGen_ne_zero (c : K) : linGen t c ≠ 0 := by
  intro h
  have h' := congrArg (fun a : Algebra.adjoin K ({t} : Set F) => (a : F)) h
  simp only [coe_linGen, ZeroMemClass.coe_zero, sub_eq_zero] at h'
  exact htr (by rw [h']; exact isAlgebraic_algebraMap c)

def polyEquiv : Polynomial K ≃ₐ[K] Algebra.adjoin K ({t} : Set F) :=
  (AlgEquiv.ofInjective (Polynomial.aeval t) (transcendental_iff_injective.mp htr)).trans
    (Subalgebra.equivOfEq _ _ (by rw [Algebra.adjoin_singleton_eq_range_aeval]))

theorem polyEquiv_X_sub_C (c : K) :
    polyEquiv t htr (Polynomial.X - Polynomial.C c) = linGen t c := by
  apply Subtype.ext
  rw [coe_linGen]
  simp [polyEquiv, Subalgebra.equivOfEq_apply, AlgEquiv.ofInjective_apply]

include htr in

theorem prime_linGen (c : K) : Prime (linGen t c) := by
  rw [← polyEquiv_X_sub_C t htr c, MulEquiv.prime_iff]
  exact Polynomial.prime_X_sub_C c

def linPrime (c : K) : HeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) :=
  ⟨Ideal.span {linGen t c}, (Ideal.span_singleton_prime (linGen_ne_zero t htr c)).mpr
    (prime_linGen t htr c), by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact linGen_ne_zero t htr c⟩

open scoped IntermediateField.algebraAdjoinAdjoin

def basePlace (c : K) : Place K (IntermediateField.adjoin K ({t} : Set F)) :=
  Place.ofHeightOneSpectrum (K := K) (linPrime t htr c)

theorem algebraMap_linGen (c : K) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F))
        (linGen t c) =
      IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c := by
  apply Subtype.ext
  rw [IntermediateField.algebraAdjoinAdjoin.coe_algebraMap, coe_linGen]
  simp

theorem ord_basePlace (c : K) :
    (basePlace t htr c).ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) = 1 := by
  rw [← algebraMap_linGen]
  refine ord_eq_one_of_valuation_eq (basePlace t htr c)
    (v' := (linPrime t htr c).valuation (IntermediateField.adjoin K ({t} : Set F))) rfl ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (linPrime t htr c).intValuation_singleton (linGen_ne_zero t htr c) rfl

theorem forall_algebraMap_mem (v : Place K (IntermediateField.adjoin K ({t} : Set F)))
    (ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring)
    (r : Algebra.adjoin K ({t} : Set F)) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F)) r ∈
      v.toValuationSubring := by
  obtain ⟨x, hx⟩ := r
  show (⟨x, IntermediateField.algebra_adjoin_le_adjoin K _ hx⟩ :
      IntermediateField.adjoin K ({t} : Set F)) ∈ v.toValuationSubring
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    have hy' : y = t := Set.mem_singleton_iff.mp hy
    subst hy'
    exact ht
  | algebraMap a => exact v.algebraMap_mem' a
  | add y z hy hz ihy ihz => exact add_mem ihy ihz
  | mul y z hy hz ihy ihz => exact mul_mem ihy ihz

include htr in

theorem eq_basePlace_of_ord_pos (v : Place K (IntermediateField.adjoin K ({t} : Set F))) (c : K)
    (hv : 0 < v.ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c)) :
    v = basePlace t htr c := by
  have ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring := mem_of_ord_sub_pos v hv
  have hw := forall_algebraMap_mem t v ht

  have hmem : linGen t c ∈ Place.center (Algebra.adjoin K ({t} : Set F)) v hw := by
    rw [Place.mem_center_iff_ord_pos v hw (linGen_ne_zero t htr c), algebraMap_linGen]
    exact hv

  have hcenter : Place.center (Algebra.adjoin K ({t} : Set F)) v hw = Ideal.span {linGen t c} := by
    haveI : (Ideal.span {linGen t c}).IsPrime := (linPrime t htr c).isPrime
    have hmax : (Ideal.span {linGen t c}).IsMaximal :=
      IsPrime.to_maximal_ideal (linPrime t htr c).ne_bot
    exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
  have hc : Place.centerHeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) v hw =
      linPrime t htr c := HeightOneSpectrum.ext hcenter
  apply Place.ext
  rw [v.toValuationSubring_eq_of_forall_mem hw, hc,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

scoped instance charZero_adjoin [CharZero K] : CharZero (IntermediateField.adjoin K ({t} : Set F)) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

variable [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] in
theorem algebraMap_gen_sub (c : K) :
    algebraMap (IntermediateField.adjoin K ({t} : Set F)) F
        (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) =
      t - algebraMap K F c := by
  rw [map_sub, IntermediateField.AdjoinSimple.algebraMap_gen,
    ← IsScalarTower.algebraMap_apply]

omit [CharZero K] in

theorem ord_sub_eq_mul (w : Place K F) (c : K) :
    w.ord (t - algebraMap K F c) =
      w.ramificationIndex (IntermediateField.adjoin K ({t} : Set F)) *
        (w.restrict (IntermediateField.adjoin K ({t} : Set F))).ord
          (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) := by
  rw [← algebraMap_gen_sub t c, Place.ord_restrict]

omit [CharZero K] in
include htr in

theorem restrict_eq_basePlace_iff (w : Place K F) (c : K) :
    w.restrict (IntermediateField.adjoin K ({t} : Set F)) = basePlace t htr c ↔
      0 < w.ord (t - algebraMap K F c) := by
  constructor
  · intro h
    rw [ord_sub_eq_mul t w c, h, ord_basePlace, mul_one]
    exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F))
  · intro h
    refine eq_basePlace_of_ord_pos t htr _ c ?_
    rw [ord_sub_eq_mul t w c] at h
    exact (pos_iff_pos_of_mul_pos h).mp
      (by exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F)))

omit [CharZero K] in
include htr in

theorem ramificationIndex_eq_ord (w : Place K F) (c : K) (h : 0 < w.ord (t - algebraMap K F c)) :
    (w.ramificationIndex (IntermediateField.adjoin K ({t} : Set F)) : ℤ) =
      w.ord (t - algebraMap K F c) := by
  rw [ord_sub_eq_mul t w c, (restrict_eq_basePlace_iff t htr w c).mpr h, ord_basePlace, mul_one]

omit [CharZero K] in

theorem inertiaDeg_eq_one (w : Place K F) (hw : w.deg = 1) :
    w.inertiaDeg (IntermediateField.adjoin K ({t} : Set F)) = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := IntermediateField.adjoin K ({t} : Set F))
  rw [hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

include htr in

theorem sum_ord_sub_eq_finrank (hdeg : ∀ w : Place K F, w.deg = 1) (c : K)
    (S : Finset (Place K F)) (hS : ∀ w, w ∈ S ↔ 0 < w.ord (t - algebraMap K F c)) :
    ∑ w ∈ S, w.ord (t - algebraMap K F c) =
      Module.finrank (IntermediateField.adjoin K ({t} : Set F)) F := by
  have hSfib : S = (basePlace t htr c).fiberOver F := by
    ext w
    rw [hS, Place.mem_fiberOver, restrict_eq_basePlace_iff t htr]
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := F) (basePlace t htr c)
  rw [← hSfib] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [inertiaDeg_eq_one t w (hdeg w), Nat.cast_one, mul_one,
    ramificationIndex_eq_ord t htr w c ((hS w).mp hw)]

include htr in

theorem exists_finset_ord_sub_pos (c : K) :
    ∃ S : Finset (Place K F), ∀ w, w ∈ S ↔ 0 < w.ord (t - algebraMap K F c) :=
  ⟨(basePlace t htr c).fiberOver F, fun w => by
    rw [Place.mem_fiberOver, restrict_eq_basePlace_iff t htr]⟩

end Transcendental

end General

theorem finrank_adjoin_jBar_eq_dedekindPsi (N : ℕ) [NeZero N] :
    Module.finrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) = dedekindPsi N := by
  have hcm : IntermediateField.comap (modularFunctionFieldBar N).val
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))} :
            Set (LaurentSeries (AlgebraicClosure ℚ))))
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) := by
    rw [← IntermediateField.lift_adjoin_simple]
    exact IntermediateField.comap_map (modularFunctionFieldBar N).val _
  have h1 := IntermediateField.finrank_comap
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))} :
        Set (LaurentSeries (AlgebraicClosure ℚ))))
    (modularFunctionFieldBar N).val
  rw [hcm, IntermediateField.fieldRange_val] at h1
  have h2 : IntermediateField.relfinrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))} :
          Set (LaurentSeries (AlgebraicClosure ℚ))))
      (modularFunctionFieldBar N) = dedekindPsi N := by
    rw [← ModularCurve.relfinrank_full_eq_dedekindPsi N,
      ← ModularCurve.relfinrank_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N]
  rw [← h2]
  exact h1

scoped instance finiteDimensional_adjoin_jBar (N : ℕ) [NeZero N] :
    FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_adjoin_jBar_eq_dedekindPsi]
    exact ModularCurve.dedekindPsi_pos N (NeZero.ne N))

end B2Peo3
p2m_reactivate "P2MW.S_ModularCurve_exists_finset_ord_jBar_sub_pos.B2Peo3"

namespace ModularCurve p2m_export "ModularCurve" "jBar modularFunctionFieldBar dedekindPsi relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos transcendental_coeffEmb_jq" end ModularCurve
p2m_open_scoped "ModularCurve" in
open B2Peo3 in

private theorem ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (hdeg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.deg = 1)
    (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔
      0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)) :
    ∑ v ∈ S, v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
      dedekindPsi N := by
  rw [← finrank_adjoin_jBar_eq_dedekindPsi N]
  exact_mod_cast sum_ord_sub_eq_finrank (jBar N : modularFunctionFieldBar N)
    (ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N) hdeg j₀ S hS

p2m_open_scoped "ModularCurve" in
open B2Peo3 in

private theorem ModularCurve.exists_finset_ord_jBar_sub_pos (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ) :
    ∃ S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), ∀ v, v ∈ S ↔
      0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) :=
  exists_finset_ord_sub_pos (jBar N : modularFunctionFieldBar N)
    (ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N) j₀

end
p2m_reactivate "P2MW.S_ModularCurve_exists_finset_ord_jBar_sub_pos.B2Peo3"

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_finset_ord_jBar_sub_pos.ModularCurve in

theorem solution (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ) :
    ∃ S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), ∀ v, v ∈ S ↔
      0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) :=
  ModularCurve.exists_finset_ord_jBar_sub_pos N j₀

#print axioms solution

end S_ModularCurve_exists_finset_ord_jBar_sub_pos
end P2MW
export P2MW.S_ModularCurve_exists_finset_ord_jBar_sub_pos (solution)
