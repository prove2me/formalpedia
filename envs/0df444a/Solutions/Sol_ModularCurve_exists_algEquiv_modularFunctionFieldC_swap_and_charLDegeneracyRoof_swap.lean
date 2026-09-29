-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a17437c4-7b6b-59bc-9ea4-45905e9b5437

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Definitions.Def_ModularCurve_ModularEquationQ
import Theorems.Thm_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_adjoin_jqNModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
import Theorems.Thm_ModularCurve_eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd
import Theorems.Thm_ModularCurve_eq_jqNModC_mul_sq_of_eval2_modularPolynomial_eq_zero_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

section File1

set_option autoImplicit false

open ModularCurve Polynomial

namespace WExists

theorem aeval_toRingHom_eq_eval₂RingHom {R : Type*} [CommRing R] [Algebra ℤ R] (x : R) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom R) x := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem eval2_swapBivar {R : Type*} [CommRing R] [Algebra ℤ R] (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    (swapBivar Φ).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y =
      Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x := by
  let L : Polynomial (Polynomial ℤ) →+* R := (Polynomial.eval₂RingHom (Polynomial.aeval (R := ℤ) x).toRingHom y).comp swapBivar
  let Rt : Polynomial (Polynomial ℤ) →+* R := Polynomial.eval₂RingHom (Polynomial.aeval (R := ℤ) y).toRingHom x
  suffices h : L = Rt by exact congrArg (fun φ => φ Φ) h
  refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
  · show (swapBivar (Polynomial.C Polynomial.X)).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y =
      (Polynomial.C Polynomial.X : Polynomial (Polynomial ℤ)).eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x
    rw [swapBivar_C_X, Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp
  · show (swapBivar Polynomial.X).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y =
      (Polynomial.X : Polynomial (Polynomial ℤ)).eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x
    rw [swapBivar_X, Polynomial.eval₂_C, Polynomial.eval₂_X]
    simp

theorem eq_swapBivar_of_evalSymm (Φ : Polynomial (Polynomial ℤ)) (h : EvalSymm Φ) : swapBivar Φ = Φ := by
  set P := swapBivar Φ - Φ with hP
  have hvan : ∀ x y : LaurentSeries ℚ, P.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 := by
    intro x y
    rw [hP, Polynomial.eval₂_sub, sub_eq_zero]
    have h' := h y x
    rw [aeval_toRingHom_eq_eval₂RingHom, aeval_toRingHom_eq_eval₂RingHom] at h'
    rw [eval2_swapBivar, aeval_toRingHom_eq_eval₂RingHom, aeval_toRingHom_eq_eval₂RingHom]
    exact h'
  let ι : Polynomial ℤ →+* LaurentSeries ℚ := (Polynomial.aeval (R := ℤ) (jqNModC ℚ 1)).toRingHom
  have hι : Function.Injective ι := by
    have htr := transcendental_jqNModC ℚ 1
    have hinjQ : Function.Injective (Polynomial.aeval (R := ℚ) (jqNModC ℚ 1) : Polynomial ℚ →ₐ[ℚ] LaurentSeries ℚ) :=
      transcendental_iff_injective.mp htr

    have hfac : ι = (Polynomial.aeval (R := ℚ) (jqNModC ℚ 1)).toRingHom.comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp [ι]
    rw [hfac, RingHom.coe_comp]
    exact hinjQ.comp (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
  haveI : Infinite (LaurentSeries ℚ) :=
    Infinite.of_injective (HahnSeries.C : ℚ → LaurentSeries ℚ) HahnSeries.C_injective
  have hmap : P.map ι = 0 := by
    apply Polynomial.funext
    intro y
    rw [Polynomial.eval_map, Polynomial.eval_zero]
    exact hvan _ y
  have : P = 0 := (Polynomial.map_eq_zero_iff hι).mp hmap
  exact sub_eq_zero.mp this

theorem eval2_comm_of_evalSymm {R : Type*} [CommRing R] [Algebra ℤ R] (Φ : Polynomial (Polynomial ℤ)) (h : EvalSymm Φ)
    (x y : R) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x := by
  conv_lhs => rw [← eq_swapBivar_of_evalSymm Φ h]
  exact eval2_swapBivar Φ x y

theorem algHom_ext_of_adjoin {K L E : Type*} [Field K] [Field L] [Algebra K L] [Field E] [Algebra K E]
    (S : Set L) (f g : ↥(IntermediateField.adjoin K S) →ₐ[K] E)
    (h : ∀ (s : L) (hs : s ∈ S), f ⟨s, IntermediateField.subset_adjoin K S hs⟩ = g ⟨s, IntermediateField.subset_adjoin K S hs⟩) :
    f = g := by
  ext ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap c =>
    have : (⟨algebraMap K L c, _⟩ : ↥(IntermediateField.adjoin K S)) = algebraMap K _ c := rfl
    rw [this, AlgHom.commutes, AlgHom.commutes]
  | add x y hx hy ihx ihy =>
    have : (⟨x + y, _⟩ : ↥(IntermediateField.adjoin K S)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
    have : (⟨x * y, _⟩ : ↥(IntermediateField.adjoin K S)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, map_mul, ihx, ihy]
  | inv x hx ihx =>
    have : (⟨x⁻¹, _⟩ : ↥(IntermediateField.adjoin K S)) = (⟨x, hx⟩ : ↥(IntermediateField.adjoin K S))⁻¹ := rfl
    rw [this, map_inv₀, map_inv₀, ihx]

end WExists

end File1

section File2

set_option autoImplicit false

open ModularCurve

namespace WExists

theorem map_eval₂_of_apply_X {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (Φ : Polynomial (Polynomial ℤ)) (φ : Polynomial ℤ →+* A) (φ' : Polynomial ℤ →+* B)
    (hX : φ' Polynomial.X = f (φ Polynomial.X)) (y : A) :
    f (Φ.eval₂ φ y) = Φ.eval₂ φ' (f y) := by
  have hcomp : f.comp φ = φ' := by
    apply Polynomial.ringHom_ext
    · intro a; simp only [eq_intCast, map_intCast, RingHom.coe_comp, Function.comp_apply]
    · rw [RingHom.coe_comp, Function.comp_apply, hX]
  rw [Polynomial.hom_eval₂, hcomp]

theorem eval₂_mk_eq_zero_iff (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ))
    (x y : LaurentSeries κ) (hx : x ∈ modularFunctionFieldC κ N) (hy : y ∈ modularFunctionFieldC κ N) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) (⟨x, hx⟩ : ↥(modularFunctionFieldC κ N))).toRingHom ⟨y, hy⟩ = 0 ↔
      Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 := by
  have h : ((Φ.eval₂ (Polynomial.aeval (R := ℤ) (⟨x, hx⟩ : ↥(modularFunctionFieldC κ N))).toRingHom ⟨y, hy⟩ :
      ↥(modularFunctionFieldC κ N)) : LaurentSeries κ) = Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y :=
    map_eval₂_of_apply_X ((modularFunctionFieldC κ N).val.toRingHom) Φ _ _ (by simp) ⟨y, hy⟩
  constructor
  · intro h0; rw [← h, h0, ZeroMemClass.coe_zero]
  · intro h0
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact h.trans h0

theorem transcendental_mk (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (x : LaurentSeries κ)
    (hx : x ∈ modularFunctionFieldC κ N) (ht : Transcendental κ x) :
    Transcendental κ (⟨x, hx⟩ : ↥(modularFunctionFieldC κ N)) := by
  intro halg
  apply ht
  have := halg.algHom ((modularFunctionFieldC κ N).val)
  simpa using this

theorem exists_algEquiv_modularFunctionFieldC_swap_of_symm (κ : Type*) [Field κ] (N : ℕ) [NeZero N]
    (hN : (N : κ) ≠ 0) (data : ModularPolynomialData N)
    (hsym : ∀ x y : LaurentSeries κ,
      data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = data.Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x) :
    ∃ w : ↥(modularFunctionFieldC κ N) ≃ₐ[κ] ↥(modularFunctionFieldC κ N),
      w ⟨jqModC κ, jqModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩ ∧
      w ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqModC κ, jqModC_mem κ N⟩ := by
  have hirr := ModularPolynomialData.irreducible_map_adjoin_jqNModC κ N data hN

  have hr : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC κ)).toRingHom (jqNModC κ N) = 0 := by
    have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero (ℓ := N) data κ 1
    simp only [one_mul, jqNModC_one] at h
    exact h
  have hr' : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC κ N)).toRingHom (jqModC κ) = 0 := by
    rw [← hsym]; exact hr
  have hroot₁ := (eval₂_mk_eq_zero_iff κ N data.Φ (jqModC κ) (jqNModC κ N) (jqModC_mem κ N) (jqNModC_mem κ N)).mpr hr
  have hroot₂ := (eval₂_mk_eq_zero_iff κ N data.Φ (jqNModC κ N) (jqModC κ) (jqNModC_mem κ N) (jqModC_mem κ N)).mpr hr'
  have htN := transcendental_mk κ N (jqNModC κ N) (jqNModC_mem κ N) (transcendental_jqNModC κ N)
  have htJ := transcendental_mk κ N (jqModC κ) (jqModC_mem κ N) (transcendental_jqModC κ)

  obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ :=
    existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero κ N hN data hirr
      (⟨jqNModC κ N, jqNModC_mem κ N⟩ : ↥(modularFunctionFieldC κ N)) ⟨jqModC κ, jqModC_mem κ N⟩ htN hroot₂

  obtain ⟨ψ', -, huniq⟩ :=
    existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero κ N hN data hirr
      (⟨jqModC κ, jqModC_mem κ N⟩ : ↥(modularFunctionFieldC κ N)) ⟨jqNModC κ N, jqNModC_mem κ N⟩ htJ hroot₁
  have hcomp : ψ.comp ψ = AlgHom.id κ _ := by
    have h1 : ψ.comp ψ = ψ' := huniq _ ⟨by rw [AlgHom.comp_apply, hψ1, hψ2], by rw [AlgHom.comp_apply, hψ2, hψ1]⟩
    have h2 : AlgHom.id κ ↥(modularFunctionFieldC κ N) = ψ' := huniq _ ⟨rfl, rfl⟩
    rw [h1, h2]
  refine ⟨AlgEquiv.ofAlgHom ψ ψ hcomp hcomp, ?_, ?_⟩
  · exact hψ1
  · exact hψ2

theorem exists_algEquiv_modularFunctionFieldC_swap (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (hN : (N : κ) ≠ 0) :
    ∃ w : ↥(ModularCurve.modularFunctionFieldC κ N) ≃ₐ[κ] ↥(ModularCurve.modularFunctionFieldC κ N),
      w ⟨ModularCurve.jqModC κ, ModularCurve.jqModC_mem κ N⟩ = ⟨ModularCurve.jqNModC κ N, ModularCurve.jqNModC_mem κ N⟩ ∧
      w ⟨ModularCurve.jqNModC κ N, ModularCurve.jqNModC_mem κ N⟩ = ⟨ModularCurve.jqModC κ, ModularCurve.jqModC_mem κ N⟩ := by
  by_cases hN1 : N = 1
  · subst hN1
    have e : (⟨jqNModC κ 1, jqNModC_mem κ 1⟩ : ↥(modularFunctionFieldC κ 1)) = ⟨jqModC κ, jqModC_mem κ 1⟩ :=
      Subtype.ext (jqNModC_one κ)
    exact ⟨AlgEquiv.refl, by rw [e]; rfl, by rw [e]; rfl⟩
  · have h1N : 1 < N := lt_of_le_of_ne (NeZero.one_le) (Ne.symm hN1)
    obtain ⟨data⟩ := nonempty_modularPolynomialData N
    exact exists_algEquiv_modularFunctionFieldC_swap_of_symm κ N hN data
      (fun x y => eval2_comm_of_evalSymm data.Φ (ModularPolynomialData.evalSymm_of_one_lt N h1N data) x y)

end WExists

end File2

section File3

set_option autoImplicit false

open ModularCurve

namespace WExists

theorem qExpand_jqNModC (κ : Type*) [Field κ] (m n : ℕ) [NeZero m] [NeZero n] :
    qExpand κ m (jqNModC κ n) = jqNModC κ (m * n) := by
  show qExpand κ m (qExpand κ n (jqModC κ)) = qExpand κ (m * n) (jqModC κ)
  rw [qExpand_qExpand]

theorem jqNModC_congr (κ : Type*) [Field κ] {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    jqNModC κ a = jqNModC κ b := by
  subst h; rfl

theorem qExpand_jqModC (κ : Type*) [Field κ] (m : ℕ) [NeZero m] : qExpand κ m (jqModC κ) = jqNModC κ m := rfl

theorem eval₂_mk_eq_zero_iff' (κ : Type*) [Field κ] (F : IntermediateField κ (LaurentSeries κ))
    (Φ : Polynomial (Polynomial ℤ)) (x y : LaurentSeries κ) (hx : x ∈ F) (hy : y ∈ F) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) (⟨x, hx⟩ : ↥F)).toRingHom ⟨y, hy⟩ = 0 ↔
      Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 := by
  have h : ((Φ.eval₂ (Polynomial.aeval (R := ℤ) (⟨x, hx⟩ : ↥F)).toRingHom ⟨y, hy⟩ : ↥F) : LaurentSeries κ) =
      Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y :=
    map_eval₂_of_apply_X (F.val.toRingHom) Φ _ _ (by simp) ⟨y, hy⟩
  constructor
  · intro h0; rw [← h, h0, ZeroMemClass.coe_zero]
  · intro h0
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact h.trans h0

theorem eval₂_coe_map_eq_zero (κ : Type*) [Field κ] (F : IntermediateField κ (LaurentSeries κ))
    (g : ↥F →+* ↥F) (Φ : Polynomial (Polynomial ℤ)) (a b : ↥F)
    (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) (a : LaurentSeries κ)).toRingHom (b : LaurentSeries κ) = 0) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) ((g a : ↥F) : LaurentSeries κ)).toRingHom ((g b : ↥F) : LaurentSeries κ) = 0 := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have h1 := (eval₂_mk_eq_zero_iff' κ F Φ a b ha hb).mpr h
  have h2 : Φ.eval₂ (Polynomial.aeval (R := ℤ) (g ⟨a, ha⟩)).toRingHom (g ⟨b, hb⟩) = 0 := by
    rw [← map_eval₂_of_apply_X g Φ (Polynomial.aeval (R := ℤ) (⟨a, ha⟩ : ↥F)).toRingHom _ (by simp) ⟨b, hb⟩, h1,
      map_zero]
  have h3 := (eval₂_mk_eq_zero_iff' κ F Φ _ _ (g ⟨a, ha⟩).2 (g ⟨b, hb⟩).2)
  exact h3.mp h2

theorem eval₂_qExpand_eq_zero (κ : Type*) [Field κ] (m : ℕ) [NeZero m] (Φ : Polynomial (Polynomial ℤ))
    (x y : LaurentSeries κ) (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) (qExpand κ m x)).toRingHom (qExpand κ m y) = 0 := by
  rw [← map_eval₂_of_apply_X (qExpand κ m) Φ (Polynomial.aeval (R := ℤ) x).toRingHom _ (by simp) y, h, map_zero]

set_option maxHeartbeats 6400000 in

theorem exists_roof_swap (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (w : ↥(modularFunctionFieldC κ N) ≃ₐ[κ] ↥(modularFunctionFieldC κ N))
    (hw1 : w ⟨jqModC κ, jqModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩)
    (hw2 : w ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqModC κ, jqModC_mem κ N⟩) :
    ∃ w' : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ),
      (∀ x, w' (heckeAlphaC κ N ℓ x) = heckeBetaC κ N ℓ (w x)) ∧
      (∀ x, w' (heckeBetaC κ N ℓ x) = heckeAlphaC κ N ℓ (w x)) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hN : (N : κ) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff κ p N).mp h)
  have hℓ0 : (ℓ : κ) ≠ 0 := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp ((CharP.cast_eq_zero_iff κ p ℓ).mp h)).symm
  have hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hN hℓ0

  have E := charLDegeneracyRoof_eq_modularFunctionFieldC_mul κ p N ℓ hpN (Ne.symm hℓp)

  obtain ⟨w₀, hw₀1, hw₀2⟩ := exists_algEquiv_modularFunctionFieldC_swap κ (N * ℓ) hNℓ
  let eE : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(modularFunctionFieldC κ (N * ℓ)) := IntermediateField.equivOfEq E
  have coe_eE : ∀ z : ↥(charLDegeneracyRoof κ N ℓ), ((eE z : ↥(modularFunctionFieldC κ (N * ℓ))) : LaurentSeries κ) = z :=
    fun z => rfl
  have coe_eEs : ∀ z : ↥(modularFunctionFieldC κ (N * ℓ)), ((eE.symm z : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) = z :=
    fun z => rfl
  let w' : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ) := eE.trans (w₀.trans eE.symm)
  have w'_apply : ∀ z, w' z = eE.symm (w₀ (eE z)) := fun z => rfl

  have hw₀inv : ∀ z, w₀ (w₀ z) = z := by
    have hext := algHom_ext_of_adjoin ({jqModC κ, jqNModC κ (N * ℓ)} : Set (LaurentSeries κ))
      (w₀.toAlgHom.comp w₀.toAlgHom) (AlgHom.id κ _)
      (by
        intro s hs
        rcases hs with rfl | rfl
        · have key : w₀ (w₀ ⟨jqModC κ, jqModC_mem κ (N * ℓ)⟩) = ⟨jqModC κ, jqModC_mem κ (N * ℓ)⟩ := by rw [hw₀1, hw₀2]
          exact key
        · have key : w₀ (w₀ ⟨jqNModC κ (N * ℓ), jqNModC_mem κ (N * ℓ)⟩) = ⟨jqNModC κ (N * ℓ), jqNModC_mem κ (N * ℓ)⟩ := by
            rw [hw₀2, hw₀1]
          exact key)
    intro z
    exact DFunLike.congr_fun hext z
  have hw'inv : ∀ z, w' (w' z) = z := by
    intro z; rw [w'_apply, w'_apply, AlgEquiv.apply_symm_apply, hw₀inv, AlgEquiv.symm_apply_apply]

  have vJ : ((w' (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) =
      jqNModC κ (N * ℓ) := by
    rw [w'_apply, coe_eEs]
    have e : eE (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) = ⟨jqModC κ, jqModC_mem κ (N * ℓ)⟩ :=
      Subtype.ext (by rw [coe_eE, coe_heckeAlphaC])
    rw [e, hw₀1]
  have vNℓ : ((w' (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) =
      jqModC κ := by
    rw [w'_apply, coe_eEs]
    have e : eE (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) = ⟨jqNModC κ (N * ℓ), jqNModC_mem κ (N * ℓ)⟩ :=
      Subtype.ext (by rw [coe_eE, coe_heckeBetaC]; show qExpand κ ℓ (jqNModC κ N) = jqNModC κ (N * ℓ);
                      rw [qExpand_jqNModC, jqNModC_congr κ (Nat.mul_comm ℓ N)])
    rw [e, hw₀2]

  have vN : ((w' (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) =
      jqNModC κ ℓ := by
    obtain ⟨dataℓ⟩ := nonempty_modularPolynomialData ℓ
    have hsymℓ := ModularPolynomialData.evalSymm_of_prime ℓ dataℓ
    obtain ⟨dataN⟩ := nonempty_modularPolynomialData N
    set u : LaurentSeries κ :=
      ((w' (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) with hu

    have r1 : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC κ)).toRingHom u = 0 := by

      have h0 : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC κ N)).toRingHom (jqNModC κ (N * ℓ)) = 0 :=
        ModularPolynomialData.eval_jqNModC_mul_eq_zero dataℓ κ N
      have h1 := eval₂_coe_map_eq_zero κ (charLDegeneracyRoof κ N ℓ) w'.toAlgHom.toRingHom dataℓ.Φ
        (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩)
        (by rw [coe_heckeAlphaC, coe_heckeBetaC]; show dataℓ.Φ.eval₂ _ (qExpand κ ℓ (jqNModC κ N)) = 0;
            rw [qExpand_jqNModC, jqNModC_congr κ (Nat.mul_comm ℓ N)]; exact h0)
      rw [show ((w'.toAlgHom.toRingHom (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) : _) :
          LaurentSeries κ) = jqModC κ from vNℓ] at h1
      rw [eval2_comm_of_evalSymm dataℓ.Φ hsymℓ]
      exact h1

    have r2 : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom (jqNModC κ (N * ℓ)) = 0 := by
      by_cases hN1 : N = 1
      · subst hN1

        have : u = jqNModC κ (1 * ℓ) := by
          rw [hu]
          have e : (⟨jqNModC κ 1, jqNModC_mem κ 1⟩ : ↥(modularFunctionFieldC κ 1)) = ⟨jqModC κ, jqModC_mem κ 1⟩ :=
            Subtype.ext (jqNModC_one κ)
          rw [e, vJ]
        rw [this]
        have h0 := ModularPolynomialData.eval_jqNModC_mul_eq_zero dataN κ (1 * ℓ)
        rw [jqNModC_congr κ (Nat.mul_one (1 * ℓ))] at h0
        exact h0
      · have h1N : 1 < N := lt_of_le_of_ne (NeZero.one_le) (Ne.symm hN1)
        have hsymN := ModularPolynomialData.evalSymm_of_one_lt N h1N dataN
        have h0 : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC κ)).toRingHom (jqNModC κ N) = 0 := by
          have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero (ℓ := N) dataN κ 1
          simp only [one_mul, jqNModC_one] at h
          exact h
        have h1 := eval₂_coe_map_eq_zero κ (charLDegeneracyRoof κ N ℓ) w'.toAlgHom.toRingHom dataN.Φ
          (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩)
          (by rw [coe_heckeAlphaC, coe_heckeAlphaC]; exact h0)
        rw [show ((w'.toAlgHom.toRingHom (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) : _) :
            LaurentSeries κ) = jqNModC κ (N * ℓ) from vJ] at h1
        rw [eval2_comm_of_evalSymm dataN.Φ hsymN]
        exact h1

    have s1 := eval₂_qExpand_eq_zero κ ℓ dataℓ.Φ (jqModC κ) u r1
    have s2 := eval₂_qExpand_eq_zero κ ℓ dataN.Φ u (jqNModC κ (N * ℓ)) r2
    have e2 : qExpand κ ℓ (jqNModC κ (N * ℓ)) = jqNModC κ (N * ℓ * ℓ) := by
      rw [qExpand_jqNModC, jqNModC_congr κ (Nat.mul_comm ℓ (N * ℓ))]
    rw [e2] at s2
    have hW7 := eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero κ N ℓ hN hℓ0 dataN dataℓ
      (qExpand κ ℓ u) s1 s2
    have e3 : jqNModC κ (ℓ * ℓ) = qExpand κ ℓ (jqNModC κ ℓ) := (qExpand_jqNModC κ ℓ ℓ).symm
    rw [e3] at hW7
    exact qExpand_injective (R := κ) (N := ℓ) hW7
  have vℓ : ((w' (heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) =
      jqNModC κ N := by

    have e : heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩ = w' (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) :=
      Subtype.ext (by rw [coe_heckeBetaC, vN]; rfl)
    rw [e, hw'inv, coe_heckeAlphaC]

  refine ⟨w', ?_, ?_⟩
  · have hext := algHom_ext_of_adjoin ({jqModC κ, jqNModC κ N} : Set (LaurentSeries κ))
      ((w'.toAlgHom.comp (heckeAlphaC κ N ℓ)))
      ((heckeBetaC κ N ℓ).comp w.toAlgHom)
      (by
        intro s hs
        rcases hs with rfl | rfl
        · have key : w' (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) = heckeBetaC κ N ℓ (w ⟨jqModC κ, jqModC_mem κ N⟩) := by
            apply Subtype.ext
            rw [vJ, hw1, coe_heckeBetaC, qExpand_jqNModC, jqNModC_congr κ (Nat.mul_comm ℓ N)]
          exact key
        · have key : w' (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) = heckeBetaC κ N ℓ (w ⟨jqNModC κ N, jqNModC_mem κ N⟩) := by
            apply Subtype.ext
            rw [vN, hw2, coe_heckeBetaC]
            rfl
          exact key)
    intro x; exact DFunLike.congr_fun hext x
  · have hext := algHom_ext_of_adjoin ({jqModC κ, jqNModC κ N} : Set (LaurentSeries κ))
      ((w'.toAlgHom.comp (heckeBetaC κ N ℓ)))
      ((heckeAlphaC κ N ℓ).comp w.toAlgHom)
      (by
        intro s hs
        rcases hs with rfl | rfl
        · have key : w' (heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) = heckeAlphaC κ N ℓ (w ⟨jqModC κ, jqModC_mem κ N⟩) := by
            apply Subtype.ext
            rw [vℓ, hw1, coe_heckeAlphaC]
          exact key
        · have key : w' (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) = heckeAlphaC κ N ℓ (w ⟨jqNModC κ N, jqNModC_mem κ N⟩) := by
            apply Subtype.ext
            rw [vNℓ, hw2, coe_heckeAlphaC]
          exact key)
    intro x; exact DFunLike.congr_fun hext x

end WExists

end File3

section File4

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve

namespace WExists

section Lift

variable (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false
local notation "L" => ↥(modularFunctionFieldC κ N)
set_option quotPrecheck false
local notation "Rf" => ↥(charLDegeneracyRoof κ N ℓ)
set_option quotPrecheck false
local notation "α" => heckeAlphaC κ N ℓ
set_option quotPrecheck false
local notation "β" => heckeBetaC κ N ℓ

theorem coe_alpha_j : ((α ⟨jqModC κ, jqModC_mem κ N⟩ : Rf) : LaurentSeries κ) = jqModC κ := coe_heckeAlphaC κ N ℓ _
theorem coe_alpha_jN : ((α ⟨jqNModC κ N, jqNModC_mem κ N⟩ : Rf) : LaurentSeries κ) = jqNModC κ N := coe_heckeAlphaC κ N ℓ _
theorem coe_beta_j : ((β ⟨jqModC κ, jqModC_mem κ N⟩ : Rf) : LaurentSeries κ) = jqNModC κ ℓ := by
  rw [coe_heckeBetaC]; rfl
theorem coe_beta_jN : ((β ⟨jqNModC κ N, jqNModC_mem κ N⟩ : Rf) : LaurentSeries κ) = jqNModC κ (ℓ * N) := by
  rw [coe_heckeBetaC]; exact qExpand_jqNModC κ ℓ N

@[reducible] noncomputable def twistAlg (wN : L ≃ₐ[κ] L) : Algebra L Rf :=
  (((α : L →ₐ[κ] Rf).comp (wN : L →ₐ[κ] L)).toRingHom).toAlgebra

set_option maxHeartbeats 25600000 in

theorem exists_twistLift (p : ℕ) [Fact p.Prime] [CharP κ p] (hpN : ¬ p ∣ N) (hℓp : ℓ ≠ p) (hℓN : ¬ ℓ ∣ N)
    (wN : L ≃ₐ[κ] L)
    (hwN1 : wN ⟨jqModC κ, jqModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩)
    (hwN2 : wN ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqModC κ, jqModC_mem κ N⟩) :
    ∃ u : Rf →ₐ[κ] Rf, (∀ z : L, u (α z) = α (wN z)) ∧
      ((u (β ⟨jqNModC κ N, jqNModC_mem κ N⟩) : Rf) : LaurentSeries κ) = jqNModC κ ℓ := by
  classical
  have hp : p.Prime := Fact.out
  have hℓpr : ℓ.Prime := Fact.out
  obtain ⟨dataℓ⟩ := nonempty_modularPolynomialData ℓ

  letI instA : Algebra L Rf := (α : L →ₐ[κ] Rf).toRingHom.toAlgebra
  have halgA : ∀ z : L, algebraMap L Rf z = α z := fun z => rfl

  let x : Rf := β ⟨jqNModC κ N, jqNModC_mem κ N⟩
  let e : Polynomial ℤ →+* L := Polynomial.eval₂RingHom (Int.castRingHom L) ⟨jqNModC κ N, jqNModC_mem κ N⟩
  let P : Polynomial L := dataℓ.Φ.map e
  have hPmonic : P.Monic := dataℓ.monic.map e
  have hPirr : Irreducible P :=
    irreducible_modularPolynomial_map_jqNModC_of_not_dvd κ p N ℓ hℓN hpN (Ne.symm hℓp) dataℓ

  have hroot0 : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC κ N)).toRingHom (jqNModC κ (ℓ * N)) = 0 := by
    have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero dataℓ κ N
    rwa [jqNModC_congr κ (Nat.mul_comm N ℓ)] at h
  have heX : ((algebraMap L Rf).comp e) Polynomial.X = α ⟨jqNModC κ N, jqNModC_mem κ N⟩ := by
    show algebraMap L Rf (Polynomial.eval₂ (Int.castRingHom L) ⟨jqNModC κ N, jqNModC_mem κ N⟩ Polynomial.X) = _
    rw [Polynomial.eval₂_X]; rfl
  have hPx : Polynomial.aeval x P = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]

    apply Subtype.ext
    have hcoe := map_eval₂_of_apply_X ((charLDegeneracyRoof κ N ℓ).val.toRingHom) dataℓ.Φ
      ((algebraMap L Rf).comp e) (Polynomial.aeval (R := ℤ) (jqNModC κ N)).toRingHom
      (by rw [heX]; simp [coe_heckeAlphaC]) x
    rw [ZeroMemClass.coe_zero]
    change ((charLDegeneracyRoof κ N ℓ).val.toRingHom) (dataℓ.Φ.eval₂ ((algebraMap L Rf).comp e) x) = 0
    rw [hcoe]
    have : ((charLDegeneracyRoof κ N ℓ).val.toRingHom) x = jqNModC κ (ℓ * N) := coe_beta_jN κ N ℓ
    rw [this]; exact hroot0
  have hx : IsIntegral L x := ⟨P, hPmonic, by rwa [Polynomial.aeval_def] at hPx⟩
  have hmin : minpoly L x = P := (minpoly.eq_of_irreducible_of_monic hPirr hPx hPmonic).symm

  let τ : L →+* Rf := ((α : L →ₐ[κ] Rf).comp (wN : L →ₐ[κ] L)).toRingHom
  have hτalg : @algebraMap L Rf _ _ (twistAlg κ N ℓ wN) = τ := rfl
  let y : Rf := β ⟨jqModC κ, jqModC_mem κ N⟩
  have hroot1 : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC κ)).toRingHom (jqNModC κ ℓ) = 0 := by
    have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero dataℓ κ 1
    rwa [jqNModC_one, jqNModC_congr κ (Nat.one_mul ℓ)] at h
  have hτeX : (τ.comp e) Polynomial.X = α ⟨jqModC κ, jqModC_mem κ N⟩ := by
    show τ (Polynomial.eval₂ (Int.castRingHom L) ⟨jqNModC κ N, jqNModC_mem κ N⟩ Polynomial.X) = _
    rw [Polynomial.eval₂_X]
    show α (wN ⟨jqNModC κ N, jqNModC_mem κ N⟩) = _
    rw [hwN2]
  have hy : y ∈ (P.map τ).roots := by
    rw [Polynomial.mem_roots ((hPmonic.map τ).ne_zero), Polynomial.IsRoot.def, Polynomial.eval_map,
      Polynomial.eval₂_map]
    apply Subtype.ext
    have hcoe := map_eval₂_of_apply_X ((charLDegeneracyRoof κ N ℓ).val.toRingHom) dataℓ.Φ
      (τ.comp e) (Polynomial.aeval (R := ℤ) (jqModC κ)).toRingHom (by rw [hτeX]; simp [coe_heckeAlphaC]) y
    rw [ZeroMemClass.coe_zero]
    change ((charLDegeneracyRoof κ N ℓ).val.toRingHom) (dataℓ.Φ.eval₂ (τ.comp e) y) = 0
    rw [hcoe]
    have : ((charLDegeneracyRoof κ N ℓ).val.toRingHom) y = jqNModC κ ℓ := coe_beta_j κ N ℓ
    rw [this]; exact hroot1
  have hy' : y ∈ ((minpoly L x).map τ).roots :=
    Eq.mpr (congrArg (fun Q : Polynomial L => y ∈ (Q.map τ).roots) hmin) hy
  have hyeval : @Polynomial.aeval L Rf _ _ (twistAlg κ N ℓ wN) y (minpoly L x) = 0 := by
    have h1 := (Polynomial.mem_roots (((minpoly.monic hx).map τ).ne_zero)).mp hy'
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at h1
    show Polynomial.eval₂ τ y (minpoly L x) = 0
    exact h1

  let ψ₀ : @AlgHom L ↥(IntermediateField.adjoin L ({x} : Set Rf)) Rf _ _ _ _ (twistAlg κ N ℓ wN) :=
    (@IntermediateField.algHomAdjoinIntegralEquiv L _ Rf _ instA x Rf _ (twistAlg κ N ℓ wN) hx).symm
      ⟨y, by exact hy'⟩
  have hψ₀x : ψ₀ (IntermediateField.AdjoinSimple.gen L x) = y :=
    @IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen L _ Rf _ instA x Rf _ (twistAlg κ N ℓ wN) hx _
  have hψ₀L : ∀ l : L, ψ₀ (algebraMap L _ l) = τ l := fun l =>
    (@AlgHom.commutes L _ Rf _ _ _ _ (twistAlg κ N ℓ wN) ψ₀ l).trans (by rw [hτalg])

  have E := charLDegeneracyRoof_eq_modularFunctionFieldC_mul κ p N ℓ hpN (Ne.symm hℓp)
  have memR : ∀ a : LaurentSeries κ,
      a ∈ IntermediateField.adjoin κ ({jqModC κ, jqNModC κ (N * ℓ)} : Set (LaurentSeries κ)) →
      a ∈ charLDegeneracyRoof κ N ℓ := by
    intro a ha; rw [E]; exact ha
  have hgen : ∀ a : LaurentSeries κ,
      a ∈ IntermediateField.adjoin κ ({jqModC κ, jqNModC κ (N * ℓ)} : Set (LaurentSeries κ)) →
      ∀ ha : a ∈ charLDegeneracyRoof κ N ℓ, (⟨a, ha⟩ : Rf) ∈ IntermediateField.adjoin L ({x} : Set Rf) := by
    intro a ha
    induction ha using IntermediateField.adjoin_induction with
    | mem a ha =>
      intro haR
      rcases ha with rfl | rfl
      · have : (⟨jqModC κ, haR⟩ : Rf) = algebraMap L Rf ⟨jqModC κ, jqModC_mem κ N⟩ :=
          Subtype.ext (by rw [halgA, coe_heckeAlphaC])
        rw [this]; exact IntermediateField.algebraMap_mem _ _
      · have : (⟨jqNModC κ (N * ℓ), haR⟩ : Rf) = x := by
          apply Subtype.ext
          show jqNModC κ (N * ℓ) = ((x : Rf) : LaurentSeries κ)
          rw [jqNModC_congr κ (Nat.mul_comm N ℓ)]; exact (coe_beta_jN κ N ℓ).symm
        rw [this]; exact IntermediateField.mem_adjoin_simple_self L x
    | algebraMap c =>
      intro haR
      have : (⟨algebraMap κ (LaurentSeries κ) c, haR⟩ : Rf) = algebraMap L Rf (algebraMap κ L c) :=
        Subtype.ext (by rw [halgA, coe_heckeAlphaC]; rfl)
      rw [this]; exact IntermediateField.algebraMap_mem _ _
    | add a b ha hb iha ihb =>
      intro haR
      have : (⟨a + b, haR⟩ : Rf) = ⟨a, memR a ha⟩ + ⟨b, memR b hb⟩ := rfl
      rw [this]; exact add_mem (iha _) (ihb _)
    | mul a b ha hb iha ihb =>
      intro haR
      have : (⟨a * b, haR⟩ : Rf) = ⟨a, memR a ha⟩ * ⟨b, memR b hb⟩ := rfl
      rw [this]; exact mul_mem (iha _) (ihb _)
    | inv a ha iha =>
      intro haR
      have : (⟨a⁻¹, haR⟩ : Rf) = (⟨a, memR a ha⟩ : Rf)⁻¹ := rfl
      rw [this]; exact inv_mem (iha _)
  have htop : IntermediateField.adjoin L ({x} : Set Rf) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨z, hz⟩ -
    have hz' : z ∈ modularFunctionFieldC κ (N * ℓ) := by rw [← E]; exact hz
    exact hgen z hz' hz

  let e₀ : Rf ≃ₐ[L] ↥(IntermediateField.adjoin L ({x} : Set Rf)) :=
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm
  have he₀ : ∀ z : Rf, ((e₀ z : ↥(IntermediateField.adjoin L ({x} : Set Rf))) : Rf) = z := fun z => rfl
  have he₀L : ∀ l : L, e₀ (algebraMap L Rf l) = algebraMap L _ l := fun l => e₀.commutes l
  let uR : Rf →+* Rf :=
    (@AlgHom.toRingHom L ↥(IntermediateField.adjoin L ({x} : Set Rf)) Rf _ _ _ _ (twistAlg κ N ℓ wN) ψ₀).comp
      e₀.toRingEquiv.toRingHom
  have huR : ∀ z : Rf, uR z = ψ₀ (e₀ z) := fun z => rfl
  have hακ : ∀ c : κ, algebraMap κ Rf c = algebraMap L Rf (algebraMap κ L c) := fun c =>
    Subtype.ext (by rw [halgA, coe_heckeAlphaC]; rfl)
  let u : Rf →ₐ[κ] Rf :=
    { uR with
      commutes' := fun c => by
        show uR (algebraMap κ Rf c) = algebraMap κ Rf c
        rw [huR, hακ, he₀L, hψ₀L]
        show α (wN (algebraMap κ L c)) = _
        rw [AlgEquiv.commutes, ← halgA] }
  have hu : ∀ z : Rf, u z = ψ₀ (e₀ z) := fun z => rfl
  refine ⟨u, fun z => ?_, ?_⟩
  · rw [hu, ← halgA, he₀L, hψ₀L]; rfl
  · have hex : e₀ x = IntermediateField.AdjoinSimple.gen L x := Subtype.ext (he₀ x)
    rw [hu, hex, hψ₀x]
    exact coe_beta_j κ N ℓ

end Lift

section Main

variable (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] (N : ℕ) [NeZero N]

set_option maxHeartbeats 25600000 in

theorem exists_roof_atkinLehner (hpN : ¬ p ∣ N) (h1N : 1 < N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓN : ¬ ℓ ∣ N) :
    ∃ w'' : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ),
      (∀ x, w'' (heckeAlphaC κ N ℓ x) = heckeBetaC κ N ℓ x) ∧
      (∀ x, w'' (heckeBetaC κ N ℓ x) = heckeAlphaC κ N ℓ x) := by
  classical
  have hp : p.Prime := Fact.out
  have hℓpr : ℓ.Prime := Fact.out
  have hN : (N : κ) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff κ p N).mp h)
  have hℓ0 : (ℓ : κ) ≠ 0 := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓpr).mp ((CharP.cast_eq_zero_iff κ p ℓ).mp h)).symm

  obtain ⟨wN, hwN1, hwN2⟩ := exists_algEquiv_modularFunctionFieldC_swap κ N hN
  obtain ⟨w', hw'α, hw'β⟩ := exists_roof_swap κ p N hpN ℓ hℓp wN hwN1 hwN2
  obtain ⟨u, huα, hux⟩ := exists_twistLift κ N ℓ p hpN hℓp hℓN wN hwN1 hwN2
  obtain ⟨dataN⟩ := nonempty_modularPolynomialData N
  obtain ⟨dataℓ⟩ := nonempty_modularPolynomialData ℓ
  have hsymN := eval2_comm_of_evalSymm (R := LaurentSeries κ) dataN.Φ
    (ModularPolynomialData.evalSymm_of_one_lt N h1N dataN)
  have hsymℓ := eval2_comm_of_evalSymm (R := LaurentSeries κ) dataℓ.Φ
    (ModularPolynomialData.evalSymm_of_prime ℓ dataℓ)

  have hwNinv : ∀ z, wN (wN z) = z := by
    have hcomp : (wN : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(modularFunctionFieldC κ N)).comp
        (wN : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(modularFunctionFieldC κ N)) = AlgHom.id κ _ := by
      apply algHom_ext_of_adjoin
      intro s hs
      rcases hs with rfl | rfl
      · show wN (wN ⟨jqModC κ, _⟩) = ⟨jqModC κ, _⟩
        have e1 : (⟨jqModC κ, IntermediateField.subset_adjoin κ _ (Or.inl rfl)⟩ : ↥(modularFunctionFieldC κ N)) =
            ⟨jqModC κ, jqModC_mem κ N⟩ := rfl
        rw [e1, hwN1, hwN2]
      · show wN (wN ⟨jqNModC κ N, _⟩) = ⟨jqNModC κ N, _⟩
        have e1 : (⟨jqNModC κ N, IntermediateField.subset_adjoin κ _ (Or.inr rfl)⟩ : ↥(modularFunctionFieldC κ N)) =
            ⟨jqNModC κ N, jqNModC_mem κ N⟩ := rfl
        rw [e1, hwN2, hwN1]
    intro z
    exact congrArg (fun φ : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(modularFunctionFieldC κ N) => φ z) hcomp

  have hu_j : ((u (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) =
      jqNModC κ N := by rw [huα, hwN1, coe_heckeAlphaC]
  have hu_jN : ((u (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) =
      jqModC κ := by rw [huα, hwN2, coe_heckeAlphaC]

  have hu_jℓ : ((u (heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) =
      jqNModC κ (ℓ * N) := by

    have r1 : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC κ)).toRingHom (jqNModC κ ℓ) = 0 := by
      have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero dataℓ κ 1
      rwa [jqNModC_one, jqNModC_congr κ (Nat.one_mul ℓ)] at h
    have r1' := eval₂_coe_map_eq_zero κ (charLDegeneracyRoof κ N ℓ) u.toRingHom dataℓ.Φ
      (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) (heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩)
      (by rw [coe_heckeAlphaC, coe_heckeBetaC]; exact r1)

    have r2 : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC κ ℓ)).toRingHom (jqNModC κ (ℓ * N)) = 0 :=
      ModularPolynomialData.eval_jqNModC_mul_eq_zero dataN κ ℓ
    have r2' := eval₂_coe_map_eq_zero κ (charLDegeneracyRoof κ N ℓ) u.toRingHom dataN.Φ
      (heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩)
      (by rw [coe_heckeBetaC, coe_heckeBetaC, qExpand_jqNModC]; exact r2)

    have eu1 : ((u.toRingHom (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) :
        LaurentSeries κ) = jqNModC κ N := hu_j
    have eu2 : ((u.toRingHom (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) : ↥(charLDegeneracyRoof κ N ℓ)) :
        LaurentSeries κ) = jqNModC κ ℓ := hux
    set t : LaurentSeries κ := ((u.toRingHom (heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) :
      ↥(charLDegeneracyRoof κ N ℓ)) : LaurentSeries κ) with ht
    rw [eu1] at r1'
    rw [eu2] at r2'
    have r2'' : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC κ ℓ)).toRingHom t = 0 := by
      rw [hsymN]; exact r2'

    have s1 := eval₂_qExpand_eq_zero κ (N * ℓ) dataℓ.Φ _ _ r1'
    have s2 := eval₂_qExpand_eq_zero κ (N * ℓ) dataN.Φ _ _ r2''
    rw [qExpand_jqNModC, jqNModC_congr κ (show N * ℓ * N = N * N * ℓ by ring)] at s1
    rw [qExpand_jqNModC] at s2
    have w8 := eq_jqNModC_mul_sq_of_eval2_modularPolynomial_eq_zero_of_coprime κ N ℓ hℓN hN hℓ0 dataN dataℓ
      (qExpand κ (N * ℓ) t) s1 s2

    have : qExpand κ (N * ℓ) t = qExpand κ (N * ℓ) (jqNModC κ (ℓ * N)) := by
      rw [w8, qExpand_jqNModC]; exact jqNModC_congr κ (by ring)
    exact qExpand_injective (N * ℓ) this

  have huu : u.comp u = AlgHom.id κ _ := by
    apply algHom_ext_of_adjoin
    intro s hs
    show u (u ⟨s, _⟩) = ⟨s, _⟩
    apply Subtype.ext

    have gj : (⟨jqModC κ, IntermediateField.subset_adjoin κ _ (by simp)⟩ : ↥(charLDegeneracyRoof κ N ℓ)) =
        heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩ := Subtype.ext (by rw [coe_heckeAlphaC])
    have gjN : (⟨jqNModC κ N, IntermediateField.subset_adjoin κ _ (by simp)⟩ : ↥(charLDegeneracyRoof κ N ℓ)) =
        heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩ := Subtype.ext (by rw [coe_heckeAlphaC])
    have gjℓ : (⟨jqNModC κ ℓ, IntermediateField.subset_adjoin κ _ (by simp)⟩ : ↥(charLDegeneracyRoof κ N ℓ)) =
        heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩ := Subtype.ext (by rw [coe_heckeBetaC]; rfl)
    have gjNℓ : (⟨jqNModC κ (N * ℓ), IntermediateField.subset_adjoin κ _ (by simp)⟩ : ↥(charLDegeneracyRoof κ N ℓ)) =
        heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩ :=
      Subtype.ext (by rw [coe_heckeBetaC, qExpand_jqNModC]; exact jqNModC_congr κ (Nat.mul_comm N ℓ))

    have v1 : u (heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) = heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩ :=
      Subtype.ext (by rw [hu_j, coe_heckeAlphaC])
    have v2 : u (heckeAlphaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) = heckeAlphaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩ :=
      Subtype.ext (by rw [hu_jN, coe_heckeAlphaC])
    have v3 : u (heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩) = heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩ :=
      Subtype.ext (by rw [hu_jℓ, coe_heckeBetaC, qExpand_jqNModC])
    have v4 : u (heckeBetaC κ N ℓ ⟨jqNModC κ N, jqNModC_mem κ N⟩) = heckeBetaC κ N ℓ ⟨jqModC κ, jqModC_mem κ N⟩ :=
      Subtype.ext (by rw [hux, coe_heckeBetaC]; rfl)
    rcases hs with rfl | rfl | rfl | rfl
    · rw [gj, v1, v2]
    · rw [gjN, v2, v1]
    · rw [gjℓ, v3, v4]
    · rw [gjNℓ, v4, v3]
  have huinv : ∀ z, u (u z) = z := fun z =>
    congrArg (fun φ : ↥(charLDegeneracyRoof κ N ℓ) →ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ) => φ z) huu
  let uE : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ) := AlgEquiv.ofAlgHom u u huu huu

  have huβ : ∀ z, u (heckeBetaC κ N ℓ z) = heckeBetaC κ N ℓ (wN z) := by
    have hcomp : u.comp (heckeBetaC κ N ℓ) =
        (heckeBetaC κ N ℓ).comp (wN : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(modularFunctionFieldC κ N)) := by
      apply algHom_ext_of_adjoin
      intro s hs
      rcases hs with rfl | rfl
      · show u (heckeBetaC κ N ℓ ⟨jqModC κ, _⟩) = heckeBetaC κ N ℓ (wN ⟨jqModC κ, _⟩)
        have e1 : (⟨jqModC κ, IntermediateField.subset_adjoin κ _ (Or.inl rfl)⟩ : ↥(modularFunctionFieldC κ N)) =
            ⟨jqModC κ, jqModC_mem κ N⟩ := rfl
        rw [e1, hwN1]
        exact Subtype.ext (by rw [hu_jℓ, coe_heckeBetaC, qExpand_jqNModC])
      · show u (heckeBetaC κ N ℓ ⟨jqNModC κ N, _⟩) = heckeBetaC κ N ℓ (wN ⟨jqNModC κ N, _⟩)
        have e1 : (⟨jqNModC κ N, IntermediateField.subset_adjoin κ _ (Or.inr rfl)⟩ : ↥(modularFunctionFieldC κ N)) =
            ⟨jqNModC κ N, jqNModC_mem κ N⟩ := rfl
        rw [e1, hwN2]
        exact Subtype.ext (by rw [hux, coe_heckeBetaC]; rfl)
    intro z
    exact congrArg (fun φ : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ) => φ z) hcomp

  refine ⟨uE.trans w', fun z => ?_, fun z => ?_⟩
  · show w' (u (heckeAlphaC κ N ℓ z)) = heckeBetaC κ N ℓ z
    rw [huα, hw'α, hwNinv]
  · show w' (u (heckeBetaC κ N ℓ z)) = heckeAlphaC κ N ℓ z
    rw [huβ, hw'β, hwNinv]

end Main

end WExists

end File4

set_option autoImplicit false

open ModularCurve

theorem solution
    (κ : Type*) [Field κ] [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (∃ w : ↥(modularFunctionFieldC κ N) ≃ₐ[κ] ↥(modularFunctionFieldC κ N),
        w ⟨jqModC κ, jqModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩ ∧
          w ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqModC κ, jqModC_mem κ N⟩) ∧
    (∀ w : ↥(modularFunctionFieldC κ N) ≃ₐ[κ] ↥(modularFunctionFieldC κ N),
        w ⟨jqModC κ, jqModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩ →
        w ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqModC κ, jqModC_mem κ N⟩ →
        ∃ w' : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ),
          (∀ x, w' (heckeAlphaC κ N ℓ x) = heckeBetaC κ N ℓ (w x)) ∧
            (∀ x, w' (heckeBetaC κ N ℓ x) = heckeAlphaC κ N ℓ (w x))) ∧
    (¬ ℓ ∣ N →
        ∃ w'' : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ),
          (∀ x, w'' (heckeAlphaC κ N ℓ x) = heckeBetaC κ N ℓ x) ∧
            (∀ x, w'' (heckeBetaC κ N ℓ x) = heckeAlphaC κ N ℓ x)) := by
  have hN : (N : κ) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff κ p N).mp h)
  refine ⟨WExists.exists_algEquiv_modularFunctionFieldC_swap κ N hN,
    fun w hw1 hw2 => WExists.exists_roof_swap κ p N hpN ℓ hℓp w hw1 hw2, fun hℓN => ?_⟩
  by_cases hN1 : N = 1
  ·
    subst hN1
    have e : (⟨jqNModC κ 1, jqNModC_mem κ 1⟩ : ↥(modularFunctionFieldC κ 1)) = ⟨jqModC κ, jqModC_mem κ 1⟩ :=
      Subtype.ext (jqNModC_one κ)
    obtain ⟨w', h1, h2⟩ := WExists.exists_roof_swap κ p 1 hpN ℓ hℓp AlgEquiv.refl (by rw [e]; rfl) (by rw [e]; rfl)
    exact ⟨w', fun x => by simpa using h1 x, fun x => by simpa using h2 x⟩
  · have h1N : 1 < N := lt_of_le_of_ne (NeZero.one_le) (Ne.symm hN1)
    exact WExists.exists_roof_atkinLehner κ p N hpN h1N ℓ hℓp hℓN

end S_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap (solution)
