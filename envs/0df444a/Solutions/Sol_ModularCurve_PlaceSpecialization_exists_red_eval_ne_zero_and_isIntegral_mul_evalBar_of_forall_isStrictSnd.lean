-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7a4d8cda-9e53-5c7b-85b2-b7ba6853ae20

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_MDivRepresents
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb jqModC jqModC_rat map_jqModC modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence jGeomGen jNGeomGen evalModularPair map_evalModularPair evalModularPair_jq_eq_zero IsCentreOf coeff_jqModC_neg_one transcendental_jqModC PlaceSpecialization.evalBar PlaceSpecialization.IsSndTriple isCurveOver_modularFunctionFieldBar nonempty_modularPolynomialData finiteDimensional_adjoin_coeffEmb_jq_of_neZero"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple reduceSnd IsStrictSnd jNFun jNQFun evalBar IsSndTriple isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos"
namespace HorClearSnd
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~coeffEmb_jq"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap_eq_zero {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_prod {ι : Type*} (s : Finset ι) (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hg a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi =>
        hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem ord_sub_evalAt_pos (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) : 0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  · exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (v.evalAt f) = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega

theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end Generic

section LevelNq

variable (N q : ℕ) [NeZero N] [NeZero q]

local notation "Qb" => AlgebraicClosure ℚ

theorem coeffMap_qExpand_aux {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext m
  by_cases h : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem coeffEmb_jq : coeffEmb Qb jq = jqModC Qb := by
  rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ Qb)

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] : coeffEmb Qb (qExpand ℚ d jq) = qExpand Qb d (jqModC Qb) := by
  change coeffMap (algebraMap ℚ Qb) (qExpand ℚ d jq) = _
  rw [coeffMap_qExpand_aux, ← coeffEmb_jq]; rfl

theorem coe_jFun : ((ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) : LaurentSeries Qb) = jqModC Qb := coeffEmb_jq
theorem coe_jNFun : ((jNFun N q : (modularFunctionFieldBar (N * q))) : LaurentSeries Qb) = qExpand Qb N (jqModC Qb) := coeffEmb_qExpand_jq N
theorem coe_jQFun : ((ProlongationTuple.jQFun N q : (modularFunctionFieldBar (N * q))) : LaurentSeries Qb) = qExpand Qb q (jqModC Qb) :=
  coeffEmb_qExpand_jq q
theorem coe_jNQFun : ((jNQFun N q : (modularFunctionFieldBar (N * q))) : LaurentSeries Qb) = qExpand Qb (N * q) (jqModC Qb) :=
  coeffEmb_qExpand_jq (N * q)

theorem sub_algebraMap_ne_zero_of_coeff {x : (modularFunctionFieldBar (N * q))} {m : ℤ} (hm : m ≠ 0) (hx : (x : LaurentSeries Qb).coeff m = 1)
    (a : Qb) : x - algebraMap Qb (modularFunctionFieldBar (N * q)) a ≠ 0 := by
  intro h
  have h' := congrArg (fun y : (modularFunctionFieldBar (N * q)) => (y : LaurentSeries Qb).coeff m) h
  simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h'
  rw [show ((x - algebraMap Qb (modularFunctionFieldBar (N * q)) a : (modularFunctionFieldBar (N * q))) : LaurentSeries Qb) = (x : LaurentSeries Qb) - algebraMap Qb (LaurentSeries Qb) a
      from rfl, HahnSeries.coeff_sub', Pi.sub_apply, hx, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne hm,
    sub_zero] at h'
  exact one_ne_zero h'

theorem jFun_sub_algebraMap_ne_zero (a : Qb) : ProlongationTuple.jFun N q - algebraMap Qb (modularFunctionFieldBar (N * q)) a ≠ 0 :=
  sub_algebraMap_ne_zero_of_coeff N q (m := -1) (by norm_num) (by rw [coe_jFun]; exact coeff_jqModC_neg_one Qb) a

theorem coeff_qExpand_jqModC_neg (d : ℕ) [NeZero d] : (qExpand Qb d (jqModC Qb)).coeff (-(d : ℤ)) = 1 := by
  rw [show (-(d : ℤ)) = (d : ℤ) * (-1) by ring, qExpand_coeff_mul]; exact coeff_jqModC_neg_one Qb

theorem jNFun_sub_algebraMap_ne_zero (a : Qb) : jNFun N q - algebraMap Qb (modularFunctionFieldBar (N * q)) a ≠ 0 :=
  sub_algebraMap_ne_zero_of_coeff N q (m := -(N : ℤ)) (neg_ne_zero.2 (Nat.cast_ne_zero.2 (NeZero.ne N)))
    (by rw [coe_jNFun]; exact coeff_qExpand_jqModC_neg N) a

theorem jQFun_sub_algebraMap_ne_zero (a : Qb) : ProlongationTuple.jQFun N q - algebraMap Qb (modularFunctionFieldBar (N * q)) a ≠ 0 :=
  sub_algebraMap_ne_zero_of_coeff N q (m := -(q : ℤ)) (neg_ne_zero.2 (Nat.cast_ne_zero.2 (NeZero.ne q)))
    (by rw [coe_jQFun]; exact coeff_qExpand_jqModC_neg q) a

theorem jNQFun_sub_algebraMap_ne_zero (a : Qb) : jNQFun N q - algebraMap Qb (modularFunctionFieldBar (N * q)) a ≠ 0 :=
  sub_algebraMap_ne_zero_of_coeff N q (m := -((N * q : ℕ) : ℤ)) (neg_ne_zero.2 (Nat.cast_ne_zero.2 (NeZero.ne (N * q))))
    (by rw [coe_jNQFun]; exact coeff_qExpand_jqModC_neg (N * q)) a

theorem transcendental_jFun : Transcendental Qb (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) := by
  have h := transcendental_jqModC Qb
  rw [← coe_jFun N q] at h
  exact (transcendental_algebraMap_iff (algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries Qb)).injective).1 h

theorem jFun_ne_zero : (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ≠ 0 := by
  simpa using jFun_sub_algebraMap_ne_zero N q 0

theorem evalModularPair_eq_zero_of_coe (x y : (modularFunctionFieldBar (N * q))) (Φ : Polynomial (Polynomial ℤ))
    (h : evalModularPair (x : LaurentSeries Qb) (y : LaurentSeries Qb) Φ = 0) : evalModularPair x y Φ = 0 := by
  have hval := map_evalModularPair (modularFunctionFieldBar (N * q)).val.toRingHom x y Φ
  have hx : (modularFunctionFieldBar (N * q)).val.toRingHom x = (x : LaurentSeries Qb) := rfl
  have hy : (modularFunctionFieldBar (N * q)).val.toRingHom y = (y : LaurentSeries Qb) := rfl
  rw [hx, hy, h] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldBar (N * q)).val.toRingHom.injective).mp hval

theorem evalModularPair_jFun_jNFun (dataN : ModularPolynomialData N) :
    evalModularPair (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) (jNFun N q) dataN.Φ = 0 := by
  refine evalModularPair_eq_zero_of_coe N q _ _ _ ?_
  rw [coe_jFun, coe_jNFun]
  exact evalModularPair_jq_eq_zero Qb dataN

theorem evalModularPair_jFun_jQFun (dataq : ModularPolynomialData q) :
    evalModularPair (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) (ProlongationTuple.jQFun N q) dataq.Φ = 0 := by
  refine evalModularPair_eq_zero_of_coe N q _ _ _ ?_
  rw [coe_jFun, coe_jQFun]
  exact evalModularPair_jq_eq_zero Qb dataq

theorem evalModularPair_jFun_jNQFun (dataNq : ModularPolynomialData (N * q)) :
    evalModularPair (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) (jNQFun N q) dataNq.Φ = 0 := by
  refine evalModularPair_eq_zero_of_coe N q _ _ _ ?_
  rw [coe_jFun, coe_jNQFun]
  exact evalModularPair_jq_eq_zero Qb dataNq

theorem isIntegral_adjoin_jFun_of_evalModularPair {M : ℕ} [NeZero M] (dataM : ModularPolynomialData M) (y : (modularFunctionFieldBar (N * q)))
    (hy : evalModularPair (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) y dataM.Φ = 0) :
    IsIntegral ↥(Algebra.adjoin Qb ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) y := by
  set R := Algebra.adjoin Qb ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q))) with hR
  let jR : R := ⟨ProlongationTuple.jFun N q, Algebra.self_mem_adjoin_singleton Qb _⟩
  let g : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) jR
  refine ⟨dataM.Φ.map g, dataM.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap R (modularFunctionFieldBar (N * q))).comp g = Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldBar (N * q))) (ProlongationTuple.jFun N q) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [g]
    · simp [g, jR]
  rw [hcomp]
  exact hy

theorem isIntegral_jNFun : IsIntegral ↥(Algebra.adjoin Qb ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) (jNFun N q : (modularFunctionFieldBar (N * q))) :=
  isIntegral_adjoin_jFun_of_evalModularPair N q (nonempty_modularPolynomialData N).some _
    (evalModularPair_jFun_jNFun N q _)

theorem isIntegral_jQFun : IsIntegral ↥(Algebra.adjoin Qb ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) (ProlongationTuple.jQFun N q : (modularFunctionFieldBar (N * q))) :=
  isIntegral_adjoin_jFun_of_evalModularPair N q (nonempty_modularPolynomialData q).some _
    (evalModularPair_jFun_jQFun N q _)

theorem isIntegral_jNQFun : IsIntegral ↥(Algebra.adjoin Qb ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) (jNQFun N q : (modularFunctionFieldBar (N * q))) :=
  isIntegral_adjoin_jFun_of_evalModularPair N q (nonempty_modularPolynomialData (N * q)).some _
    (evalModularPair_jFun_jNQFun N q _)

theorem jNFun_mem (V : Place Qb (modularFunctionFieldBar (N * q))) (hV : (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring) :
    (jNFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
  V.mem_toValuationSubring_of_isIntegral_adjoin hV (isIntegral_jNFun N q)

theorem jQFun_mem (V : Place Qb (modularFunctionFieldBar (N * q))) (hV : (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring) :
    (ProlongationTuple.jQFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
  V.mem_toValuationSubring_of_isIntegral_adjoin hV (isIntegral_jQFun N q)

theorem jNQFun_mem (V : Place Qb (modularFunctionFieldBar (N * q))) (hV : (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring) :
    (jNQFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
  V.mem_toValuationSubring_of_isIntegral_adjoin hV (isIntegral_jNQFun N q)

end LevelNq

end ModularCurve.PlaceSpecialization.HorClearSnd

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb jqModC jqModC_rat map_jqModC modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence jGeomGen jNGeomGen evalModularPair map_evalModularPair evalModularPair_jq_eq_zero IsCentreOf coeff_jqModC_neg_one transcendental_jqModC PlaceSpecialization.evalBar PlaceSpecialization.IsSndTriple isCurveOver_modularFunctionFieldBar nonempty_modularPolynomialData finiteDimensional_adjoin_coeffEmb_jq_of_neZero"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple reduceSnd IsStrictSnd jNFun jNQFun evalBar IsSndTriple isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos"
namespace HorClearSnd
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~coeffEmb_jq"

section Core

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

local notation "Qb" => AlgebraicClosure ℚ

noncomputable def evalBarHom (c : Option (Fin 2) → (modularFunctionFieldBar (N * q))) : MvPolynomial (Option (Fin 2)) A →+* (modularFunctionFieldBar (N * q)) :=
  MvPolynomial.eval₂Hom ((algebraMap Qb (modularFunctionFieldBar (N * q))).comp (algebraMap A Qb)) c

theorem evalBar_eq (c : Option (Fin 2) → (modularFunctionFieldBar (N * q))) (H : MvPolynomial (Option (Fin 2)) A) :
    evalBar N q c H = evalBarHom c H := rfl

@[scoped simp] theorem evalBarHom_X (c : Option (Fin 2) → (modularFunctionFieldBar (N * q))) (s : Option (Fin 2)) :
    evalBarHom c (MvPolynomial.X s : MvPolynomial (Option (Fin 2)) A) = c s :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[scoped simp] theorem evalBarHom_C (c : Option (Fin 2) → (modularFunctionFieldBar (N * q))) (a : A) :
    evalBarHom c (MvPolynomial.C a) = algebraMap Qb (modularFunctionFieldBar (N * q)) (a : Qb) :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem inv_mem_and_red_eq_zero (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {v : Qb} (hv : v ∉ A) :
    ∃ hinv : v⁻¹ ∈ A, red ⟨v⁻¹, hinv⟩ = 0 := by
  have hinv : v⁻¹ ∈ A := (A.mem_or_inv_mem v).resolve_left hv
  refine ⟨hinv, (hker _).2 ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  apply hv
  have hv0 : v ≠ 0 := fun h => hv (h ▸ A.zero_mem)
  have h1 : ((u⁻¹ : Aˣ) : A) * (u : A) = 1 := Units.inv_mul u
  have h2 : (((u⁻¹ : Aˣ) : A) : Qb) * v⁻¹ = 1 := by
    have := congrArg (fun x : A => (x : Qb)) h1
    simpa [hu] using this
  have h3 : (((u⁻¹ : Aˣ) : A) : Qb) = v := by
    have := congrArg (· * v) h2
    simpa [mul_assoc, inv_mul_cancel₀ hv0] using this
  exact h3 ▸ ((u⁻¹ : Aˣ) : A).2

theorem exists_form (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (c : Option (Fin 2) → (modularFunctionFieldBar (N * q))) (cen : Option (Fin 2) → A) (s : Option (Fin 2))
    (V : Place Qb (modularFunctionFieldBar (N * q))) (hrat : V.IsRational) (ht : c s ∈ V.toValuationSubring)
    (hne : ∀ a : Qb, c s - algebraMap Qb (modularFunctionFieldBar (N * q)) a ≠ 0)
    (hreg : ∀ V' : Place Qb (modularFunctionFieldBar (N * q)), (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring → c s ∈ V'.toValuationSubring)
    (hbad : ∀ hv : V.evalAt (c s) ∈ A, red ⟨V.evalAt (c s), hv⟩ ≠ red (cen s)) :
    ∃ ℓ : MvPolynomial (Option (Fin 2)) A,
      red (MvPolynomial.eval (fun o => cen o) ℓ) ≠ 0 ∧ evalBarHom c ℓ ≠ 0 ∧ 0 < V.ord (evalBarHom c ℓ) ∧
        ∀ V' : Place Qb (modularFunctionFieldBar (N * q)), (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring → evalBarHom c ℓ ∈ V'.toValuationSubring := by
  set v := V.evalAt (c s) with hvdef
  have hpos : 0 < V.ord (c s - algebraMap Qb (modularFunctionFieldBar (N * q)) v) := ord_sub_evalAt_pos V hrat ht (hne v)
  by_cases hvA : v ∈ A
  ·
    refine ⟨MvPolynomial.X s - MvPolynomial.C ⟨v, hvA⟩, ?_, ?_, ?_, ?_⟩
    · rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, map_sub, sub_ne_zero]
      exact (hbad hvA).symm
    · rw [map_sub, evalBarHom_X, evalBarHom_C]; exact hne v
    · rw [map_sub, evalBarHom_X, evalBarHom_C]; exact hpos
    · intro V' hV'
      rw [map_sub, evalBarHom_X, evalBarHom_C]
      exact sub_mem (hreg V' hV') (V'.algebraMap_mem' _)
  ·
    obtain ⟨hinv, hred⟩ := inv_mem_and_red_eq_zero hker hvA
    have hv0 : v ≠ 0 := fun h => hvA (h ▸ A.zero_mem)
    have hCv : algebraMap Qb (modularFunctionFieldBar (N * q)) v ≠ 0 := (map_ne_zero _).2 hv0
    have key : evalBarHom c (1 - MvPolynomial.C ⟨v⁻¹, hinv⟩ * MvPolynomial.X s)
        = algebraMap Qb (modularFunctionFieldBar (N * q)) (-v⁻¹) * (c s - algebraMap Qb (modularFunctionFieldBar (N * q)) v) := by
      rw [map_sub, map_one, map_mul, evalBarHom_C, evalBarHom_X]
      change (1 : (modularFunctionFieldBar (N * q))) - algebraMap Qb (modularFunctionFieldBar (N * q)) v⁻¹ * c s = algebraMap Qb (modularFunctionFieldBar (N * q)) (-v⁻¹) * (c s - algebraMap Qb (modularFunctionFieldBar (N * q)) v)
      rw [map_neg, map_inv₀]
      have hv1 : (algebraMap Qb (modularFunctionFieldBar (N * q)) v)⁻¹ * algebraMap Qb (modularFunctionFieldBar (N * q)) v = 1 := inv_mul_cancel₀ hCv
      linear_combination (-1 : (modularFunctionFieldBar (N * q))) * hv1
    refine ⟨1 - MvPolynomial.C ⟨v⁻¹, hinv⟩ * MvPolynomial.X s, ?_, ?_, ?_, ?_⟩
    · rw [map_sub, map_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_sub, map_one, map_mul, hred,
        zero_mul, sub_zero]
      exact one_ne_zero
    · rw [key]; exact mul_ne_zero ((map_ne_zero _).2 (neg_ne_zero.2 (inv_ne_zero hv0))) (hne v)
    · rw [key, V.ord_mul ((map_ne_zero _).2 (neg_ne_zero.2 (inv_ne_zero hv0))) (hne v),
        ord_algebraMap_eq_zero V (neg_ne_zero.2 (inv_ne_zero hv0)), zero_add]
      exact hpos
    · intro V' hV'
      rw [map_sub, map_one, map_mul, evalBarHom_C, evalBarHom_X]
      exact sub_mem (one_mem _) (mul_mem (V'.algebraMap_mem' _) (hreg V' hV'))

theorem core (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (Q : Place Qb (modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q)
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (c : Option (Fin 2) → (modularFunctionFieldBar (N * q))) (cen : Option (Fin 2) → A) (s₀ s₁ s₂ : Option (Fin 2))
    (h₀ : c s₀ = ProlongationTuple.jQFun N q) (h₁ : c s₁ = jNQFun N q) (h₂ : c s₂ = ProlongationTuple.jFun N q)
    (hc₀ : 0 < Q.ord (ProlongationTuple.jQFun N q - algebraMap Qb (modularFunctionFieldBar (N * q)) (cen s₀ : Qb)))
    (hc₁ : 0 < Q.ord (jNQFun N q - algebraMap Qb (modularFunctionFieldBar (N * q)) (cen s₁ : Qb)))
    (hc₂ : 0 < Q.ord (ProlongationTuple.jFun N q - algebraMap Qb (modularFunctionFieldBar (N * q)) (cen s₂ : Qb)))
    (f : (modularFunctionFieldBar (N * q)))
    (hf : ∀ W : Place Qb (modularFunctionFieldBar (N * q)), P.IsStrictSnd W → P.reduceSnd W = P.reduceSnd Q → f ∈ W.toValuationSubring) :
    ∃ H : MvPolynomial (Option (Fin 2)) A,
      red (MvPolynomial.eval (fun o => cen o) H) ≠ 0 ∧
      IsIntegral ↥(Algebra.adjoin Qb ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) (f * evalBar N q c H) := by
  classical
  haveI hcurve : IsCurveOver Qb (modularFunctionFieldBar (N * q)) := isCurveOver_modularFunctionFieldBar (N * q)
  haveI : HasPrincipalDivisors Qb (modularFunctionFieldBar (N * q)) := IsCurveOver.hasPrincipalDivisors
  haveI : FiniteDimensional ↥(IntermediateField.adjoin Qb ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) (modularFunctionFieldBar (N * q)) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero (N * q)

  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨1, by simp, by rw [zero_mul]; exact isIntegral_zero⟩

  have sep : ∀ V : Place Qb (modularFunctionFieldBar (N * q)), ∃ ℓ : MvPolynomial (Option (Fin 2)) A,
      ((ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring → f ∉ V.toValuationSubring →
        red (MvPolynomial.eval (fun o => cen o) ℓ) ≠ 0 ∧ evalBarHom c ℓ ≠ 0 ∧ 0 < V.ord (evalBarHom c ℓ)) ∧
      (∀ V' : Place Qb (modularFunctionFieldBar (N * q)), (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring →
        evalBarHom c ℓ ∈ V'.toValuationSubring) := by
    intro V
    by_cases hV : (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring ∧ f ∉ V.toValuationSubring
    swap
    · exact ⟨1, fun h1 h2 => (hV ⟨h1, h2⟩).elim, fun V' _ => by rw [map_one]; exact one_mem _⟩
    obtain ⟨hjV, hfV⟩ := hV
    have hrat : V.IsRational := isRational_of_isCurveOver V
    have hjQV : (ProlongationTuple.jQFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring := jQFun_mem N q V hjV
    have hjNQV : (jNQFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring := jNQFun_mem N q V hjV

    have hnot : ¬ ∃ (g₀ : V.evalAt (ProlongationTuple.jQFun N q : (modularFunctionFieldBar (N * q))) ∈ A) (g₁ : V.evalAt (jNQFun N q : (modularFunctionFieldBar (N * q))) ∈ A)
        (g₂ : V.evalAt (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ A),
        red ⟨_, g₀⟩ = red (cen s₀) ∧ red ⟨_, g₁⟩ = red (cen s₁) ∧ red ⟨_, g₂⟩ = red (cen s₂) := by
      rintro ⟨g₀, g₁, g₂, r₀, r₁, r₂⟩
      have hstrict := isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos P hqN hker Q hQ hsm hgen (cen s₀) (cen s₁) (cen s₂)
        ⟨_, g₀⟩ ⟨_, g₁⟩ ⟨_, g₂⟩ r₀ r₁ r₂ hc₀ hc₁ hc₂ V
        (ord_sub_evalAt_pos V hrat hjQV (jQFun_sub_algebraMap_ne_zero N q _))
        (ord_sub_evalAt_pos V hrat hjNQV (jNQFun_sub_algebraMap_ne_zero N q _))
        (ord_sub_evalAt_pos V hrat hjV (jFun_sub_algebraMap_ne_zero N q _))
      exact hfV (hf V hstrict.1 hstrict.2)

    have main : ∃ ℓ : MvPolynomial (Option (Fin 2)) A,
        red (MvPolynomial.eval (fun o => cen o) ℓ) ≠ 0 ∧ evalBarHom c ℓ ≠ 0 ∧ 0 < V.ord (evalBarHom c ℓ) ∧
          ∀ V' : Place Qb (modularFunctionFieldBar (N * q)), (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring →
            evalBarHom c ℓ ∈ V'.toValuationSubring := by
      by_cases b₀ : ∀ hv : V.evalAt (c s₀) ∈ A, red ⟨V.evalAt (c s₀), hv⟩ ≠ red (cen s₀)
      · exact exists_form hker c cen s₀ V hrat (by rw [h₀]; exact hjQV) (fun a => by rw [h₀]; exact jQFun_sub_algebraMap_ne_zero N q a)
          (fun V' hV' => by rw [h₀]; exact jQFun_mem N q V' hV') b₀
      by_cases b₁ : ∀ hv : V.evalAt (c s₁) ∈ A, red ⟨V.evalAt (c s₁), hv⟩ ≠ red (cen s₁)
      · exact exists_form hker c cen s₁ V hrat (by rw [h₁]; exact hjNQV) (fun a => by rw [h₁]; exact jNQFun_sub_algebraMap_ne_zero N q a)
          (fun V' hV' => by rw [h₁]; exact jNQFun_mem N q V' hV') b₁
      by_cases b₂ : ∀ hv : V.evalAt (c s₂) ∈ A, red ⟨V.evalAt (c s₂), hv⟩ ≠ red (cen s₂)
      · exact exists_form hker c cen s₂ V hrat (by rw [h₂]; exact hjV) (fun a => by rw [h₂]; exact jFun_sub_algebraMap_ne_zero N q a)
          (fun V' hV' => by rw [h₂]; exact hV') b₂
      exfalso
      push_neg at b₀ b₁ b₂
      rw [h₀] at b₀
      rw [h₁] at b₁
      rw [h₂] at b₂
      obtain ⟨g₀, r₀⟩ := b₀
      obtain ⟨g₁, r₁⟩ := b₁
      obtain ⟨g₂, r₂⟩ := b₂
      exact hnot ⟨g₀, g₁, g₂, r₀, r₁, r₂⟩
    obtain ⟨ℓ, hℓ1, hℓ2, hℓ3, hℓ4⟩ := main
    exact ⟨ℓ, fun _ _ => ⟨hℓ1, hℓ2, hℓ3⟩, hℓ4⟩
  choose ℓ hℓ hℓreg using sep

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := Qb) f hf0
  let S : Finset (Place Qb (modularFunctionFieldBar (N * q))) :=
    D.support.filter (fun V => (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring ∧ f ∉ V.toValuationSubring)
  have hS : ∀ V ∈ S, (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring ∧ f ∉ V.toValuationSubring :=
    fun V hV => (Finset.mem_filter.1 hV).2
  let n : Place Qb (modularFunctionFieldBar (N * q)) → ℕ := fun V => (-(D V)).toNat
  refine ⟨∏ V ∈ S, ℓ V ^ n V, ?_, ?_⟩
  ·
    rw [map_prod, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun V hV => ?_
    rw [map_pow, map_pow]
    exact pow_ne_zero _ (hℓ V (hS V hV).1 (hS V hV).2).1
  ·
    refine isIntegral_adjoin_of_forall_ord_nonneg (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) (transcendental_jFun N q) _ fun V' hV' => ?_
    have hjV' : (ProlongationTuple.jFun N q : (modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring := V'.mem_of_ord_nonneg (jFun_ne_zero N q) hV'
    have hne : ∀ V ∈ S, evalBarHom c (ℓ V) ^ n V ≠ 0 := fun V hV =>
      pow_ne_zero _ (hℓ V (hS V hV).1 (hS V hV).2).2.1
    have hprod_ne : (∏ V ∈ S, evalBarHom c (ℓ V) ^ n V) ≠ 0 := Finset.prod_ne_zero_iff.2 hne
    rw [evalBar_eq, map_prod]
    simp only [map_pow]
    rw [V'.ord_mul hf0 hprod_ne, ord_prod V' S _ hne]
    simp only [ord_pow]
    have hterm : ∀ V ∈ S, 0 ≤ (n V : ℤ) * V'.ord (evalBarHom c (ℓ V)) := fun V _ =>
      mul_nonneg (Int.natCast_nonneg _) (V'.ord_nonneg_of_mem (hℓreg V V' hjV'))
    by_cases hfV' : f ∈ V'.toValuationSubring
    · exact add_nonneg (V'.ord_nonneg_of_mem hfV') (Finset.sum_nonneg hterm)
    ·
      have hordf : V'.ord f < 0 := lt_of_not_ge fun h => hfV' (V'.mem_of_ord_nonneg hf0 h)
      have hV'S : V' ∈ S := by
        refine Finset.mem_filter.2 ⟨?_, hjV', hfV'⟩
        rw [Finsupp.mem_support_iff, hD V']
        exact hordf.ne
      have hnV' : (n V' : ℤ) = - V'.ord f := by
        change (((-(D V')).toNat : ℕ) : ℤ) = _
        rw [Int.toNat_of_nonneg (by rw [hD V']; omega), hD V']
      have hle : (n V' : ℤ) * V'.ord (evalBarHom c (ℓ V')) ≤ ∑ V ∈ S, (n V : ℤ) * V'.ord (evalBarHom c (ℓ V)) :=
        Finset.single_le_sum hterm hV'S
      have hone : (n V' : ℤ) ≤ (n V' : ℤ) * V'.ord (evalBarHom c (ℓ V')) :=
        le_mul_of_one_le_right (Int.natCast_nonneg _) (hℓ V' hjV' hfV').2.2
      omega

end Core

end ModularCurve.PlaceSpecialization.HorClearSnd
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve.PlaceSpecialization.HorClearSnd"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd.ModularCurve"

open ModularCurve.PlaceSpecialization.HorClearSnd in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q)
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u : A) (w : Fin 2 → A)
    (htr : PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd Q) (red u) z y₁ y₂)
    (hu : 0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)))
    (hw : ∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j : AlgebraicClosure ℚ)))
    (f : ↥(modularFunctionFieldBar (N * q)))
    (hf : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictSnd W → P.reduceSnd W = P.reduceSnd Q → f ∈ W.toValuationSubring) :
    ∃ H : MvPolynomial (Option (Fin 2)) A,
      red (MvPolynomial.eval (fun o => Option.elim o u w) H) ≠ 0 ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
          ({PlaceSpecialization.ProlongationTuple.jFun N q} : Set ↥(modularFunctionFieldBar (N * q))))
        (f * PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) H) := by
  have hw0 := hw 0
  have hw1 := hw 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hw0 hw1
  unfold IsSndTriple at htr
  rcases htr with ⟨hz, hy₁, hy₂, -⟩ | ⟨hz, hy₁, hy₂, -⟩
  · subst hz hy₁ hy₂
    exact core P hqN hker Q hQ hsm hgen (fun o => Option.elim o (ProlongationTuple.jQFun N q) ![jNQFun N q, ProlongationTuple.jFun N q])
      (fun o => Option.elim o u w) none (some 0) (some 1) rfl rfl rfl hu hw0 hw1 f hf
  · subst hz hy₁ hy₂
    exact core P hqN hker Q hQ hsm hgen (fun o => Option.elim o (jNQFun N q) ![ProlongationTuple.jQFun N q, ProlongationTuple.jFun N q])
      (fun o => Option.elim o u w) (some 0) none (some 1) rfl rfl rfl hw0 hu hw1 f hf

end S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd (solution)
