-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.isUnit_det_jacobian_centre_of_mDivRepresents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/88bffd67-433c-5259-b9fe-2b223fa189a6

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_IncidenceSystem
import Definitions.Def_MDivRepresents
import Theorems.Thm_IncidenceSystem_Data_isUnit_det_jacobian_iff
import Theorems.Thm_ModularCurve_eq_zero_of_forall_sum_mul_taylorCoeff_mul_pow_eq_zero_of_generalPosition
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jNFun_sub_jNQFun_sub
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Mathlib
import Definitions.Def_IncidenceSystem
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_PowerSeries_coeff_eq_coeff_of_forall_coeff_eval_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_aeval
import Theorems.Thm_MvPolynomial_coeff_aeval_optionElim_C_add_X_sum_monomial_eq
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_mul
import Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X
import Theorems.Thm_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_isUnit_det_jacobian_centre_of_mDivRepresents
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace RootsCore
open AlgebraicCurve MvPolynomial

theorem aeval_eq_eval_optionEquivLeft {R : Type*} [CommRing R] {σ τ : Type*} {S : Type*} [CommRing S] [Algebra R S]
    (e : Option τ ≃ σ) (g : σ → S) (H : MvPolynomial σ R) :
    aeval g H =
      ((optionEquivLeft R τ (rename e.symm H)).map
        (aeval (fun t => g (e (some t))) : MvPolynomial τ R →ₐ[R] S).toRingHom).eval (g (e none)) := by

  let ev : Polynomial (MvPolynomial τ R) →ₐ[R] S :=
    Polynomial.aevalTower (aeval (fun t => g (e (some t)))) (g (e none))
  let Φ : MvPolynomial σ R →ₐ[R] S :=
    ev.comp (((optionEquivLeft R τ).toAlgHom).comp (rename e.symm))
  have hΦ : ∀ H', Φ H' = ((optionEquivLeft R τ (rename e.symm H')).map
      (aeval (fun t => g (e (some t))) : MvPolynomial τ R →ₐ[R] S).toRingHom).eval (g (e none)) := by
    intro H'
    simp only [Φ, ev, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rw [Polynomial.eval_map]
    rfl
  rw [← hΦ]
  refine congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext (f := aeval g) (g := Φ) fun s => ?_)) H

  rw [aeval_X, hΦ]
  rcases hs : e.symm s with _ | t
  · have : s = e none := by rw [← hs, Equiv.apply_symm_apply]
    rw [rename_X, hs, optionEquivLeft_X_none, Polynomial.map_X, Polynomial.eval_X, this]
  · have : s = e (some t) := by rw [← hs, Equiv.apply_symm_apply]
    rw [rename_X, hs, optionEquivLeft_X_some, Polynomial.map_C, Polynomial.eval_C]
    simp [this]

theorem derivative_optionEquivLeft {R : Type*} [CommRing R] {σ : Type*} (p : MvPolynomial (Option σ) R) :
    Polynomial.derivative (optionEquivLeft R σ p) = optionEquivLeft R σ (pderiv none p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => rw [optionEquivLeft_C, Polynomial.derivative_C, pderiv_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p o hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
    cases o with
    | none => rw [optionEquivLeft_X_none, Polynomial.derivative_X, pderiv_X]; simp; ring
    | some t => rw [optionEquivLeft_X_some, Polynomial.derivative_C, pderiv_X]; simp; ring

theorem aeval_congr_of_not_mem_vars {R : Type*} [CommRing R] {σ : Type*} {S : Type*} [CommRing S] [Algebra R S]
    (H : MvPolynomial σ R) (s : σ) (hH : s ∉ H.vars) (g g' : σ → S) (hg : ∀ o, o ≠ s → g o = g' o) :
    aeval g H = aeval g' H := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, ← coe_eval₂Hom, ← coe_eval₂Hom]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun o ho _ => hg o ?_) rfl
  rintro rfl; exact hH ho

def sw : Option (Fin 2) ≃ Option (Fin 2) := Equiv.swap none (some 0)

theorem sw_none : sw none = some 0 := by simp [sw]
theorem sw_some0 : sw (some 0) = none := by simp [sw]
theorem sw_some1 : sw (some 1) = some 1 := by
  simp [sw, Equiv.swap_apply_of_ne_of_ne]

theorem jet_eq_taylorCoeff_of_branch {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1)
    {m : ℕ} (H : MvPolynomial (Option (Fin 2)) K) (hvars : (some 1 : Option (Fin 2)) ∉ H.vars)
    (fs : Option (Fin 2) → F) (hfs : ∀ o, fs o ∈ Q.toValuationSubring)
    (a : K) (hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C a + PowerSeries.X)
    (hrel : aeval fs H = 0)
    (hunit : Q.evalAt (aeval fs (pderiv (some 0) H)) ≠ 0)
    (w : Fin 2 → Fin m → K)
    (hw0 : ∀ hm : 0 < m, w 0 ⟨0, hm⟩ = Q.evalAt (fs (some 0)))
    (hbranch : ∀ r : Fin m, (aeval (fun o : Option (Fin 2) =>
        Option.elim o (Polynomial.C a + Polynomial.X) (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) H).coeff r = 0) :
    ∀ r : Fin m, w 0 r = Place.taylorCoeff Q t r (fs (some 0)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro r; exact r.elim0

  set Ser : Option (Fin 2) → PowerSeries K := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer
  set φ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K := aeval (fun s => Ser (sw (some s))) with hφ
  set f : Polynomial (PowerSeries K) := (optionEquivLeft K (Fin 2) (rename sw.symm H)).map φ.toRingHom with hf
  have hiso : ∀ (H' : MvPolynomial (Option (Fin 2)) K) (Y : PowerSeries K),
      ((optionEquivLeft K (Fin 2) (rename sw.symm H')).map φ.toRingHom).eval Y
        = aeval (Function.update Ser (some 0) Y) H' := by
    intro H' Y
    rw [aeval_eq_eval_optionEquivLeft sw (Function.update Ser (some 0) Y) H', sw_none, Function.update_self]
    have hg : (fun s : Fin 2 => Function.update Ser (some 0) Y (sw (some s))) = fun s => Ser (sw (some s)) := by
      funext s
      apply Function.update_of_ne
      fin_cases s <;> simp [sw, Equiv.swap_apply_def]
    rw [hg]

  have hroot : f.eval (Ser (some 0)) = 0 := by
    rw [hf, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs H, hrel]
    ext n
    rw [PowerSeries.coeff_mk, map_zero, show (0 : F) = algebraMap K F 0 from (map_zero _).symm,
      Place.taylorCoeff_algebraMap]
    simp

  set Y : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 0 ⟨n, h⟩ else 0 with hYdef
  set Y₂ : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 1 ⟨n, h⟩ else 0 with hY₂def
  have hYcoeff : ∀ j (i : Fin m), PowerSeries.coeff (i : ℕ) (![Y, Y₂] j) = w j i := by
    intro j i
    fin_cases j <;> simp [hYdef, hY₂def, PowerSeries.coeff_mk, i.2]
  have hcand : ∀ r, r < m → PowerSeries.coeff r (f.eval Y) = 0 := by
    intro r hr
    rw [hf, hiso]
    have hcongr : aeval (Function.update Ser (some 0) Y) H
        = aeval (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C a + PowerSeries.X) ![Y, Y₂]) H := by
      refine aeval_congr_of_not_mem_vars H (some 1) hvars _ _ fun o ho => ?_
      rcases o with _ | j
      · rw [Function.update_of_ne (by simp), hSer]; simp only [Option.elim]; exact hz
      · fin_cases j
        · simp
        · exact absurd rfl ho
    rw [hcongr, ← MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq H a w ![Y, Y₂] hYcoeff ⟨r, hr⟩]
    exact hbranch ⟨r, hr⟩

  have h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff (Ser (some 0)) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos hm, Place.taylorCoeff_zero]
    exact hw0 hm

  have hder : f.derivative = (optionEquivLeft K (Fin 2) (rename sw.symm (pderiv (some 0) H))).map φ.toRingHom := by
    rw [hf, Polynomial.derivative_map, derivative_optionEquivLeft]
    congr 2
    have hsw : (none : Option (Fin 2)) = sw.symm (some 0) := by
      rw [Equiv.eq_symm_apply, sw_none]
    rw [hsw, pderiv_rename sw.symm.injective]
  have hunit' : IsUnit (PowerSeries.constantCoeff (f.derivative.eval (Ser (some 0)))) := by
    rw [hder, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs _,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, Place.taylorCoeff_zero]
    exact isUnit_iff_ne_zero.mpr hunit

  have hmain := PowerSeries.coeff_eq_coeff_of_forall_coeff_eval_eq_zero f (Ser (some 0)) Y hroot hunit' h0 m hcand
  intro r
  have e := hmain r r.2
  rw [hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos r.2] at e
  exact e

theorem coeff_aeval_congr {K : Type*} [CommRing K] {σ : Type*} (H : MvPolynomial σ K) (m : ℕ)
    (g g' : σ → PowerSeries K) (h : ∀ s, ∀ r, r < m → PowerSeries.coeff r (g s) = PowerSeries.coeff r (g' s)) :
    ∀ r, r < m → PowerSeries.coeff r (MvPolynomial.aeval g H) = PowerSeries.coeff r (MvPolynomial.aeval g' H) := by
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X ^ m}
  have hq : ∀ s, Ideal.Quotient.mk I (g s) = Ideal.Quotient.mk I (g' s) := by
    intro s
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro r hr
    rw [map_sub, h s r hr, sub_self]
  have hcomp : (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval g)
      = (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval g') := by
    rw [MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
    congr 1
    funext s
    exact hq s
  have hdiff : MvPolynomial.aeval g H - MvPolynomial.aeval g' H ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact congrArg (fun φ : MvPolynomial σ K →ₐ[K] (PowerSeries K ⧸ I) => φ H) hcomp
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hdiff
  intro r hr
  have e := hdiff r hr
  rwa [map_sub, sub_eq_zero] at e

def sw1 : Option (Fin 2) ≃ Option (Fin 2) := Equiv.swap none (some 1)

theorem sw1_none : sw1 none = some 1 := by simp [sw1]

theorem jet_eq_taylorCoeff_of_branch_snd {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1)
    {m : ℕ} (H : MvPolynomial (Option (Fin 2)) K)
    (fs : Option (Fin 2) → F) (hfs : ∀ o, fs o ∈ Q.toValuationSubring)
    (a : K) (hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C a + PowerSeries.X)
    (hrel : aeval fs H = 0)
    (hunit : Q.evalAt (aeval fs (pderiv (some 1) H)) ≠ 0)
    (w : Fin 2 → Fin m → K)
    (hw₀ : ∀ r : Fin m, w 0 r = Place.taylorCoeff Q t r (fs (some 0)))
    (hw0 : ∀ hm : 0 < m, w 1 ⟨0, hm⟩ = Q.evalAt (fs (some 1)))
    (hbranch : ∀ r : Fin m, (aeval (fun o : Option (Fin 2) =>
        Option.elim o (Polynomial.C a + Polynomial.X) (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) H).coeff r = 0) :
    ∀ r : Fin m, w 1 r = Place.taylorCoeff Q t r (fs (some 1)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro r; exact r.elim0
  set Ser : Option (Fin 2) → PowerSeries K := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer
  set φ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K := aeval (fun s => Ser (sw1 (some s))) with hφ
  set f : Polynomial (PowerSeries K) := (optionEquivLeft K (Fin 2) (rename sw1.symm H)).map φ.toRingHom with hf
  have hiso : ∀ (H' : MvPolynomial (Option (Fin 2)) K) (Y : PowerSeries K),
      ((optionEquivLeft K (Fin 2) (rename sw1.symm H')).map φ.toRingHom).eval Y
        = aeval (Function.update Ser (some 1) Y) H' := by
    intro H' Y
    rw [aeval_eq_eval_optionEquivLeft sw1 (Function.update Ser (some 1) Y) H', sw1_none, Function.update_self]
    have hg : (fun s : Fin 2 => Function.update Ser (some 1) Y (sw1 (some s))) = fun s => Ser (sw1 (some s)) := by
      funext s
      apply Function.update_of_ne
      fin_cases s <;> simp [sw1, Equiv.swap_apply_def]
    rw [hg]
  have hroot : f.eval (Ser (some 1)) = 0 := by
    rw [hf, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs H, hrel]
    ext n
    rw [PowerSeries.coeff_mk, map_zero, show (0 : F) = algebraMap K F 0 from (map_zero _).symm,
      Place.taylorCoeff_algebraMap]
    simp
  set Y₁ : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 0 ⟨n, h⟩ else 0 with hY₁def
  set Y : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 1 ⟨n, h⟩ else 0 with hYdef
  have hYcoeff : ∀ j (i : Fin m), PowerSeries.coeff (i : ℕ) (![Y₁, Y] j) = w j i := by
    intro j i
    fin_cases j <;> simp [hYdef, hY₁def, PowerSeries.coeff_mk, i.2]
  have hcand : ∀ r, r < m → PowerSeries.coeff r (f.eval Y) = 0 := by
    intro r hr
    rw [hf, hiso]
    have hcongr := coeff_aeval_congr H m (Function.update Ser (some 1) Y)
      (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C a + PowerSeries.X) ![Y₁, Y]) (fun o r' hr' => ?_) r hr
    · rw [hcongr, ← MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq H a w ![Y₁, Y] hYcoeff ⟨r, hr⟩]
      exact hbranch ⟨r, hr⟩
    · rcases o with _ | j
      · rw [Function.update_of_ne (by simp), hSer]; simp only [Option.elim]; rw [hz]
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, ne_eq, Option.some.injEq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, Option.elim, Matrix.cons_val_zero]
          rw [hSer, PowerSeries.coeff_mk, hY₁def, PowerSeries.coeff_mk, dif_pos hr']
          exact (hw₀ ⟨r', hr'⟩).symm
        · simp
  have h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff (Ser (some 1)) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos hm, Place.taylorCoeff_zero]
    exact hw0 hm
  have hder : f.derivative = (optionEquivLeft K (Fin 2) (rename sw1.symm (pderiv (some 1) H))).map φ.toRingHom := by
    rw [hf, Polynomial.derivative_map, derivative_optionEquivLeft]
    congr 2
    have hsw : (none : Option (Fin 2)) = sw1.symm (some 1) := by
      rw [Equiv.eq_symm_apply, sw1_none]
    rw [hsw, pderiv_rename sw1.symm.injective]
  have hunit' : IsUnit (PowerSeries.constantCoeff (f.derivative.eval (Ser (some 1)))) := by
    rw [hder, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs _,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, Place.taylorCoeff_zero]
    exact isUnit_iff_ne_zero.mpr hunit
  have hmain := PowerSeries.coeff_eq_coeff_of_forall_coeff_eval_eq_zero f (Ser (some 1)) Y hroot hunit' h0 m hcand
  intro r
  have e := hmain r r.2
  rw [hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos r.2] at e
  exact e

theorem sigma_eq_taylorCoeff_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1)
    {m : ℕ} (S : MvPolynomial (Option (Fin 2)) K)
    (fs : Option (Fin 2) → F) (hfs : ∀ o, fs o ∈ Q.toValuationSubring)
    (a : K) (hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C a + PowerSeries.X)
    (hs0 : Q.evalAt (aeval fs S) ≠ 0)
    (w : Fin 2 → Fin m → K) (hw : ∀ j (r : Fin m), w j r = Place.taylorCoeff Q t r (fs (some j)))
    (σ : Fin m → K)
    (hinv : ∀ r : Fin m, ((∑ i : Fin m, Polynomial.monomial (i : ℕ) (σ i)) *
        aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C a + Polynomial.X)
          (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) S - 1).coeff r = 0) :
    ∀ r : Fin m, σ r = Place.taylorCoeff Q t r (aeval fs S)⁻¹ := by
  classical
  set Ser : Option (Fin 2) → PowerSeries K := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer

  have hScoeff : ∀ i : Fin m, (aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C a + Polynomial.X)
      (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) S).coeff i = Place.taylorCoeff Q t i (aeval fs S) := by
    intro i
    rw [MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq S a w (fun j => Ser (some j))
      (fun j i' => by rw [hSer, PowerSeries.coeff_mk, hw]) i]
    have hfun : (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C a + PowerSeries.X) fun j => Ser (some j)) = Ser := by
      funext o; rcases o with _ | j
      · simp only [Option.elim]; rw [← hz]
      · rfl
    rw [hfun, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs S, PowerSeries.coeff_mk]

  have hσcoeff : ∀ n, (∑ i : Fin m, Polynomial.monomial (i : ℕ) (σ i)).coeff n = if h : n < m then σ ⟨n, h⟩ else 0 := by
    intro n
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨n, h⟩ : Fin m)]
      · simp
      · intro j _ hj; rw [if_neg]; intro e; exact hj (Fin.ext e)
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · exact Finset.sum_eq_zero fun j _ => if_neg (fun e => h (by rw [← e]; exact j.2))

  set σ' : ℕ → K := fun n => if h : n < m then σ ⟨n, h⟩ else 0 with hσ'
  have hsys : ∀ r, r < m → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ' x.1 * Place.taylorCoeff Q t x.2 (aeval fs S)
      = if r = 0 then 1 else 0 := by
    intro r hr
    have h := hinv ⟨r, hr⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_one, sub_eq_zero] at h
    simp only [Fin.val_mk] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 < m := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.snd_le hx) hr
    rw [hσcoeff, hσ', hScoeff ⟨x.2, hx2⟩]
  have hsmem : ∀ S' : MvPolynomial (Option (Fin 2)) K, aeval fs S' ∈ Q.toValuationSubring := by
    intro S'
    induction S' using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.aeval_C]; exact Q.algebraMap_mem' c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p o hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hfs o)
  have hres := Place.eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq Q hQ ht (hsmem S) hs0 m σ' hsys
  intro r
  have e := hres r r.2
  simp only [hσ'] at e
  rw [dif_pos r.2] at e
  simpa using e

theorem smul_mem' {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (c : K) {f : F}
    (hf : f ∈ w.toValuationSubring) : c • f ∈ w.toValuationSubring := by
  rw [Algebra.smul_def]; exact mul_mem (w.algebraMap_mem' c) hf

theorem taylorCoeff_sum_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) (hw : w.IsRational) {t : F} (ht : w.ord t = 1)
    {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ w.toValuationSubring) (r : ℕ) :
    Place.taylorCoeff w t r (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * Place.taylorCoeff w t r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, show (0 : F) = algebraMap K F 0 from (map_zero _).symm,
      Place.taylorCoeff_algebraMap]
    simp
  | insert i s hi ih =>
    have hfi : f i ∈ w.toValuationSubring := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ∈ w.toValuationSubring := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsmem : (∑ j ∈ s, c j • f j) ∈ w.toValuationSubring :=
      sum_mem fun j hj => smul_mem' w (c j) (hfs j hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Place.taylorCoeff_add w hw ht (smul_mem' w (c i) hfi) hsmem,
      Place.taylorCoeff_smul w hw ht hfi, ih hfs]

theorem taylorCoeff_sum_smul_div_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1) {m : ℕ}
    {ι : Type*} [Fintype ι] (c : ι → K) (p s : ι → F)
    (hp : ∀ kk, p kk ∈ Q.toValuationSubring) (hsinv : ∀ kk, (s kk)⁻¹ ∈ Q.toValuationSubring)
    (Pp Sg : ι → Polynomial K)
    (hPp : ∀ kk (i : Fin m), (Pp kk).coeff i = Place.taylorCoeff Q t i (p kk))
    (hSg : ∀ kk (i : Fin m), (Sg kk).coeff i = Place.taylorCoeff Q t i (s kk)⁻¹)
    (r : Fin m) :
    ∑ kk, c kk * (Pp kk * Sg kk).coeff r = Place.taylorCoeff Q t r (∑ kk, c kk • (p kk * (s kk)⁻¹)) := by
  classical
  rw [taylorCoeff_sum_smul Q hQ ht _ c _ (fun kk _ => mul_mem (hp kk) (hsinv kk)) r]
  refine Finset.sum_congr rfl fun kk _ => ?_
  congr 1
  rw [Polynomial.coeff_mul, Place.taylorCoeff_mul Q hQ ht (hp kk) (hsinv kk) r]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 : x.1 < m := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.fst_le hx) r.2
  have hx2 : x.2 < m := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.snd_le hx) r.2
  rw [hPp kk ⟨x.1, hx1⟩, hSg kk ⟨x.2, hx2⟩]

theorem eq_of_eval_eq_zero_of_sub_mem {A : Type*} [CommRing A] [IsLocalRing A] (f : Polynomial A) {x y : A}
    (hx : f.eval x = 0) (hy : f.eval y = 0) (hxy : y - x ∈ IsLocalRing.maximalIdeal A)
    (hder : IsUnit (f.derivative.eval x)) : y = x := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f x (y - x)
  rw [show x + (y - x) = y by ring, hy, hx, zero_add] at hk

  have hu : IsUnit (f.derivative.eval x + k * (y - x)) := by
    have hmem : k * (y - x) ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_left _ _ hxy
    by_contra hnu
    have hmem2 : f.derivative.eval x + k * (y - x) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : f.derivative.eval x ∈ IsLocalRing.maximalIdeal A := by
      have := sub_mem hmem2 hmem
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hder
  have h0 : (y - x) * (f.derivative.eval x + k * (y - x)) = 0 := by
    have : (y - x) * (f.derivative.eval x + k * (y - x))
        = f.derivative.eval x * (y - x) + k * (y - x) ^ 2 := by ring
    rw [this, ← hk]
  have : y - x = 0 := (hu.mul_left_eq_zero).mp h0
  exact sub_eq_zero.mp this

theorem hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] {w : Place K F} {g g' : F} {a a' : K}
    (h : w.HasValue g a) (h' : w.HasValue g' a') : w.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : w.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_aeval {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) {ι : Type*}
    (fs : ι → F) (vals : ι → K) (h : ∀ o, w.HasValue (fs o) (vals o)) (H : MvPolynomial ι K) :
    w.HasValue (MvPolynomial.aeval fs H) (MvPolynomial.aeval vals H) := by
  induction H using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    exact Place.hasValue_algebraMap w c
  | add p q hp hq => rw [map_add, map_add]; exact hasValue_add hp hq
  | mul_X p o hp => rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]; exact hp.mul (h o)

theorem evalAt_eq_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {g : F} {a : K} (h : w.HasValue g a) : w.evalAt g = a := by
  rw [w.evalAt_of_mem h.mem, h.residue_eq, Place.residueInv_algebraMap]

theorem eval_sub_eval_mem {A : Type*} [CommRing A] (I : Ideal A) {ι : Type*} (v v' : ι → A)
    (h : ∀ o, v o - v' o ∈ I) (H : MvPolynomial ι A) :
    MvPolynomial.eval v H - MvPolynomial.eval v' H ∈ I := by
  rw [← Ideal.Quotient.eq]
  have hv : (Ideal.Quotient.mk I) ∘ v = (Ideal.Quotient.mk I) ∘ v' :=
    funext fun o => (Ideal.Quotient.eq).mpr (h o)
  show Ideal.Quotient.mk I (MvPolynomial.eval₂ (RingHom.id A) v H) = Ideal.Quotient.mk I (MvPolynomial.eval₂ (RingHom.id A) v' H)
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hv]

theorem aeval_map_algebraMap {A L : Type*} [CommRing A] [CommRing L] [Algebra A L] {ι : Type*} (vA : ι → A)
    (H : MvPolynomial ι A) :
    MvPolynomial.aeval (fun o => algebraMap A L (vA o)) (MvPolynomial.map (algebraMap A L) H)
      = algebraMap A L (MvPolynomial.eval vA H) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  show MvPolynomial.eval₂ ((algebraMap L L).comp (algebraMap A L)) (fun o => algebraMap A L (vA o)) H
    = algebraMap A L (MvPolynomial.eval₂ (RingHom.id A) vA H)
  rw [MvPolynomial.eval₂_comp_left]
  congr 1

theorem eval_zero_substAt {g m' : ℕ} {A' : Type*} [CommRing A'] (Pt : IncidenceSystem.Var g 2 m' → A') (i : Fin g)
    (H : MvPolynomial (Option (Fin 2)) A') :
    (IncidenceSystem.substAt Pt i H).eval 0 = MvPolynomial.eval (IncidenceSystem.Data.ptCoord Pt i) H := by
  classical
  unfold IncidenceSystem.substAt
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.evalRingHom (0 : A')).comp (algebraMap A' (Polynomial A')) = RingHom.id A' := by
    ext a; simp
  rw [hC]
  show MvPolynomial.eval₂ (RingHom.id A') _ H = MvPolynomial.eval₂ (RingHom.id A') (IncidenceSystem.Data.ptCoord Pt i) H
  congr 1
  funext o
  rw [Function.comp_apply, Polynomial.coe_evalRingHom]
  rcases o with _ | j
  · simp [IncidenceSystem.coordAt, IncidenceSystem.Data.ptCoord]
  · simp only [IncidenceSystem.coordAt, IncidenceSystem.Data.ptCoord, Option.elim, IncidenceSystem.wpoly,
      Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [Finset.sum_eq_single (0 : Fin (m' + 1))]
    · simp
    · intro r _ hr
      have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
      simp [zero_pow this]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem map_substAt {g m' : ℕ} {A' L' : Type*} [CommRing A'] [CommRing L'] (φ : A' →+* L')
    (Pt : IncidenceSystem.Var g 2 m' → A') (i : Fin g) (H : MvPolynomial (Option (Fin 2)) A') :
    (IncidenceSystem.substAt Pt i H).map φ
      = MvPolynomial.eval₂ (Polynomial.C : L' →+* Polynomial L') (fun o : Option (Fin 2) => Option.elim o
          (Polynomial.C (φ (Pt (IncidenceSystem.Var.u i))) + Polynomial.X)
          (fun j => ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (φ (Pt (IncidenceSystem.Var.w i j r)))))
        (MvPolynomial.map φ H) := by
  classical
  unfold IncidenceSystem.substAt
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.mapRingHom φ).comp (algebraMap A' (Polynomial A')) = (Polynomial.C : L' →+* Polynomial L').comp φ := by
    ext a; simp
  rw [hC]
  congr 1
  funext o
  rw [Function.comp_apply, Polynomial.coe_mapRingHom]
  rcases o with _ | j
  · simp [IncidenceSystem.coordAt]
  · simp only [IncidenceSystem.coordAt, Option.elim, IncidenceSystem.wpoly]
    rw [← Polynomial.coe_mapRingHom, map_sum]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial]

theorem eval_inc_eq_zero_of_root {g m' : ℕ} {A' : Type*} [CommRing A'] (Dt : IncidenceSystem.Data g 2 m' A')
    (Pt : IncidenceSystem.Var g 2 m' → A') (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (i : Fin g) (r : Fin (m' + 1)) : MvPolynomial.eval Pt (Dt.inc i r) = 0 := by
  induction r using Fin.lastCases with
  | last => exact hroot (IncidenceSystem.Var.u i)
  | cast r =>
    have h := hroot (IncidenceSystem.Var.c (finProdFinEquiv (i, r)))
    simpa [IncidenceSystem.Data.system] using h

theorem eval_branch_eq_zero_of_root {g m' : ℕ} {A' : Type*} [CommRing A'] (Dt : IncidenceSystem.Data g 2 m' A')
    (Pt : IncidenceSystem.Var g 2 m' → A') (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (i : Fin g) (j : Fin 2) (r : Fin (m' + 1)) : MvPolynomial.eval Pt (Dt.branch i j r) = 0 :=
  hroot (IncidenceSystem.Var.w i j r)

theorem eval_inv_eq_zero_of_root {g m' : ℕ} {A' : Type*} [CommRing A'] (Dt : IncidenceSystem.Data g 2 m' A')
    (Pt : IncidenceSystem.Var g 2 m' → A') (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (kk : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) : MvPolynomial.eval Pt (Dt.inv kk i r) = 0 :=
  hroot (IncidenceSystem.Var.σ kk i r)

theorem hasValue_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    {y : F} {b : K} (h : 0 < Q.ord (y - algebraMap K F b)) : Q.HasValue y b := by
  have hmem : y - algebraMap K F b ∈ Q.toValuationSubring := by
    by_cases h0 : y - algebraMap K F b = 0
    · rw [h0]; exact zero_mem _
    · exact Q.mem_of_ord_nonneg h0 h.le
  have hy : y ∈ Q.toValuationSubring := by
    have := add_mem hmem (Q.algebraMap_mem' b)
    rwa [sub_add_cancel] at this
  refine ⟨hy, ?_⟩
  have hmax := Q.mk_mem_maximalIdeal_of_ord_pos hmem h
  have hx : (⟨y - algebraMap K F b, hmem⟩ : Q.toValuationSubring)
      = ⟨y, hy⟩ - algebraMap K Q.toValuationSubring b := by
    refine Subtype.ext ?_
    show y - algebraMap K F b = y - (algebraMap K Q.toValuationSubring b : F)
    rw [Place.coe_algebraMap]
  rw [hx] at hmax
  have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, Q.residue_algebraMap]

private theorem _root_.RootsCore.eq_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    {y : F} {b b' : K} (h : 0 < Q.ord (y - algebraMap K F b)) (h' : 0 < Q.ord (y - algebraMap K F b')) : b = b' :=
  (hasValue_of_ord_sub_pos Q h).unique (hasValue_of_ord_sub_pos Q h')

p2m_export "RootsCore" "eq_of_ord_sub_pos"
theorem coeff_sum_monomial_fin {R : Type*} [Semiring R] {n : ℕ} (c : Fin n → R) (i : Fin n) :
    (∑ r : Fin n, Polynomial.monomial (r : ℕ) (c r)).coeff i = c i := by
  classical
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg]; intro e; exact hj (Fin.ext e)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem map_spoly {g m' : ℕ} {A' L' : Type*} [CommRing A'] [CommRing L'] (φ : A' →+* L')
    (Pt : IncidenceSystem.Var g 2 m' → A') (kk : Option (Fin (g * m'))) (i : Fin g) :
    (IncidenceSystem.spoly Pt kk i).map φ
      = ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (φ (Pt (IncidenceSystem.Var.σ kk i r))) := by
  rw [IncidenceSystem.spoly, ← Polynomial.coe_mapRingHom, map_sum]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial]

set_option maxHeartbeats 6400000 in
theorem point_jets' {L F : Type*} [Field L] [Field F] [Algebra L F] {A : Type*} [CommRing A] [IsLocalRing A] [Algebra A L]
    (hφinj : Function.Injective (algebraMap A L))
    {k : Type*} [Field k] (red : A →+* k) (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    {g m' : ℕ} (Dt : IncidenceSystem.Data g 2 m' A) (i : Fin g)
    (z y₁ y₂ : F) (τ : A) (hsec : Option (Fin (g * m')) → F)
    (hvars : (some 1 : Option (Fin 2)) ∉ (Dt.G i 0).vars)
    (hb : ∀ j, aeval (fun o : Option (Fin 2) => Option.elim o z ![y₁, y₂])
      (MvPolynomial.map (algebraMap A L) (Dt.G i j)) = 0)
    (hd : ∀ kk, aeval (fun o : Option (Fin 2) => Option.elim o z ![y₁, y₂]) (MvPolynomial.map (algebraMap A L) (Dt.p kk i))
      = hsec kk * (z - algebraMap L F (algebraMap A L (Dt.u₀ i))) ^ m' * (z - algebraMap L F (algebraMap A L τ))
        * aeval (fun o : Option (Fin 2) => Option.elim o z ![y₁, y₂]) (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))
    (he : ∀ kk, red (Dt.sVal Dt.centre kk i) ≠ 0) (hf : ∀ j, red (Dt.dG Dt.centre i j) ≠ 0)
    (Pt : IncidenceSystem.Var g 2 m' → A) (hPt : ∀ v, Pt v - Dt.centre v ∈ IsLocalRing.maximalIdeal A)
    (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (Q : Place L F) (hQ : Q.IsRational)
    (hordz : Q.ord (z - algebraMap L F (algebraMap A L (Pt (IncidenceSystem.Var.u i)))) = 1)
    (hvalQ : ∀ j : Fin 2, ∃ b : A, Q.HasValue (![y₁, y₂] j) (algebraMap A L b) ∧ red b = red (Dt.w₀ i j 0))
    (kk : Option (Fin (g * m'))) (r : Fin (m' + 1)) :
    ((IncidenceSystem.substAt Pt i (Dt.p kk i)).map (algebraMap A L) * (IncidenceSystem.spoly Pt kk i).map (algebraMap A L)).coeff r
      = Place.taylorCoeff Q (z - algebraMap L F (algebraMap A L (Pt (IncidenceSystem.Var.u i)))) r
          (hsec kk * (z - algebraMap L F (algebraMap A L (Dt.u₀ i))) ^ m' * (z - algebraMap L F (algebraMap A L τ))) := by
  classical

  set a : A := Pt (IncidenceSystem.Var.u i) with ha
  set t : F := z - algebraMap L F (algebraMap A L a) with htdef
  set fs : Option (Fin 2) → F := fun o => Option.elim o z ![y₁, y₂] with hfsdef
  have hne_of_red : ∀ x : A, red x ≠ 0 → algebraMap A L x ≠ 0 := by
    intro x hx h0
    apply hx
    have : x = 0 := hφinj (by rw [h0, map_zero])
    rw [this, map_zero]
  have hsubmem : ∀ {x y : A}, red x = red y → x - y ∈ IsLocalRing.maximalIdeal A := by
    intro x y h
    rw [← hker, map_sub, h, sub_self]
  have hred_eq_of_sub : ∀ {x y : A}, x - y ∈ IsLocalRing.maximalIdeal A → red x = red y := by
    intro x y h
    have := (hker _).mpr h
    rwa [map_sub, sub_eq_zero] at this

  have ht : Q.ord t = 1 := hordz
  obtain ⟨b₀, hb₀, hrb₀⟩ := hvalQ 0
  obtain ⟨b₁, hb₁, hrb₁⟩ := hvalQ 1
  set vA : Option (Fin 2) → A := fun o => Option.elim o a ![b₀, b₁] with hvAdef
  have hval : ∀ o, Q.HasValue (fs o) (algebraMap A L (vA o)) := by
    intro o
    rcases o with _ | j
    · exact hasValue_of_ord_sub_pos Q (show 0 < Q.ord t by rw [ht]; exact one_pos)
    · fin_cases j
      · exact hb₀
      · exact hb₁
  have hfs : ∀ o, fs o ∈ Q.toValuationSubring := fun o => (hval o).mem

  have hcong : ∀ o, vA o - IncidenceSystem.Data.ptCoord Dt.centre i o ∈ IsLocalRing.maximalIdeal A := by
    intro o
    rcases o with _ | j
    · exact hPt (IncidenceSystem.Var.u i)
    · fin_cases j
      · exact hsubmem hrb₀
      · exact hsubmem hrb₁

  have hvalpoly : ∀ H : MvPolynomial (Option (Fin 2)) A,
      Q.HasValue (aeval fs (MvPolynomial.map (algebraMap A L) H)) (algebraMap A L (MvPolynomial.eval vA H)) := by
    intro H
    have h := hasValue_aeval Q fs (fun o => algebraMap A L (vA o)) hval (MvPolynomial.map (algebraMap A L) H)
    rwa [aeval_map_algebraMap] at h
  have hred_eval : ∀ H : MvPolynomial (Option (Fin 2)) A,
      red (MvPolynomial.eval vA H) = red (MvPolynomial.eval (IncidenceSystem.Data.ptCoord Dt.centre i) H) :=
    fun H => hred_eq_of_sub (eval_sub_eval_mem _ _ _ hcong H)

  have hs_ne : ∀ kk, Q.evalAt (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i))) ≠ 0 := by
    intro kk
    rw [evalAt_eq_of_hasValue Q (hvalpoly _)]
    apply hne_of_red
    rw [hred_eval]
    exact he kk
  have hs_val_ne : ∀ kk, algebraMap A L (MvPolynomial.eval vA (Dt.s kk i)) ≠ 0 := by
    intro kk; have := hs_ne kk; rwa [evalAt_eq_of_hasValue Q (hvalpoly _)] at this
  have hsF_ne : ∀ kk, aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)) ≠ 0 :=
    fun kk => (hvalpoly _).ne_zero (hs_val_ne kk)
  have hsinv : ∀ kk, (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))⁻¹ ∈ Q.toValuationSubring :=
    fun kk => ((hvalpoly _).inv (hs_val_ne kk)).mem
  have hdG_ne : ∀ j, Q.evalAt (aeval fs (pderiv (some j) (MvPolynomial.map (algebraMap A L) (Dt.G i j)))) ≠ 0 := by
    intro j
    rw [MvPolynomial.pderiv_map, evalAt_eq_of_hasValue Q (hvalpoly _)]
    apply hne_of_red
    rw [hred_eval]
    exact hf j

  have hza : Q.evalAt z = algebraMap A L a := evalAt_eq_of_hasValue Q (hval none)
  have hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C (algebraMap A L a) + PowerSeries.X := by
    have h := Place.mk_taylorCoeff_eq_C_add_X Q hQ (hfs none) (by
      show Q.ord (z - algebraMap L F (Q.evalAt z)) = 1
      rw [hza]; exact ht)
    rw [show fs none = z from rfl] at h ⊢
    rw [hza] at h
    exact h

  have hbranch0 : ∀ j, MvPolynomial.eval (IncidenceSystem.Data.ptCoord Pt i) (Dt.G i j) = 0 := by
    intro j
    rw [← eval_zero_substAt, ← Polynomial.coeff_zero_eq_eval_zero]
    exact_mod_cast (by
      have h := eval_branch_eq_zero_of_root Dt Pt hroot i j 0
      rwa [IncidenceSystem.eval_branch] at h)
  have hrootA : ∀ j, MvPolynomial.eval vA (Dt.G i j) = 0 := by
    intro j
    apply hφinj
    rw [map_zero]
    exact ((hvalpoly (Dt.G i j)).unique (by rw [hb j]; simpa using Place.hasValue_algebraMap Q (0 : L))).symm ▸ rfl

  have haev : ∀ (gg : Option (Fin 2) → A) (H' : MvPolynomial (Option (Fin 2)) A),
      aeval gg H' = MvPolynomial.eval gg H' := fun gg H' => RingHom.congr_fun (MvPolynomial.coe_aeval_eq_eval gg) H'
  have hisoA : ∀ (e : Option (Fin 2) ≃ Option (Fin 2)) (H' : MvPolynomial (Option (Fin 2)) A) (Y : A),
      ((optionEquivLeft A (Fin 2) (rename e.symm H')).map
        (aeval (fun s => vA (e (some s))) : MvPolynomial (Fin 2) A →ₐ[A] A).toRingHom).eval Y
        = MvPolynomial.eval (Function.update vA (e none) Y) H' := by
    intro e H' Y
    rw [← haev, aeval_eq_eval_optionEquivLeft e (Function.update vA (e none) Y) H', Function.update_self]
    have hg : (fun s : Fin 2 => Function.update vA (e none) Y (e (some s))) = fun s => vA (e (some s)) := by
      funext s
      apply Function.update_of_ne
      intro h
      exact Option.some_ne_none s (e.injective h)
    rw [hg]
  have hptc : IncidenceSystem.Data.ptCoord Pt i
      = fun o => Option.elim o a ![Pt (IncidenceSystem.Var.w i 0 0), Pt (IncidenceSystem.Var.w i 1 0)] := by
    funext o
    rcases o with _ | j
    · rfl
    · fin_cases j <;> rfl
  have hunitA : ∀ j, IsUnit (MvPolynomial.eval vA (pderiv (some j) (Dt.G i j))) := by
    intro j
    by_contra hnu
    have hmem : MvPolynomial.eval vA (pderiv (some j) (Dt.G i j)) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    apply hf j
    show red (MvPolynomial.eval (IncidenceSystem.Data.ptCoord Dt.centre i) (pderiv (some j) (Dt.G i j))) = 0
    rw [← hred_eval, hker]
    exact hmem

  have hw00 : Pt (IncidenceSystem.Var.w i 0 0) = b₀ := by
    set F₀ : Polynomial A := (optionEquivLeft A (Fin 2) (rename sw.symm (Dt.G i 0))).map
      (aeval (fun s => vA (sw (some s))) : MvPolynomial (Fin 2) A →ₐ[A] A).toRingHom with hF₀
    have hevF : ∀ Y, F₀.eval Y = MvPolynomial.eval (Function.update vA (some 0) Y) (Dt.G i 0) := by
      intro Y; rw [hF₀, hisoA sw, sw_none]
    have hx : F₀.eval (Pt (IncidenceSystem.Var.w i 0 0)) = 0 := by
      rw [hevF, ← hbranch0 0, hptc, ← haev, ← haev]
      refine aeval_congr_of_not_mem_vars _ (some 1) hvars _ _ fun o ho => ?_
      rcases o with _ | j
      · rw [Function.update_of_ne (by simp)]; rfl
      · fin_cases j
        · simp
        · exact absurd rfl ho
    have hy : F₀.eval b₀ = 0 := by
      rw [hevF]
      have : Function.update vA (some 0) b₀ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]; exact hrootA 0
    have hder : F₀.derivative.eval b₀ = MvPolynomial.eval vA (pderiv (some 0) (Dt.G i 0)) := by
      rw [hF₀, Polynomial.derivative_map, derivative_optionEquivLeft,
        show (none : Option (Fin 2)) = sw.symm (some 0) by rw [Equiv.eq_symm_apply, sw_none],
        pderiv_rename sw.symm.injective, hisoA sw, sw_none]
      have : Function.update vA (some 0) b₀ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]
    have hcg : Pt (IncidenceSystem.Var.w i 0 0) - b₀ ∈ IsLocalRing.maximalIdeal A := by
      have h1 := hPt (IncidenceSystem.Var.w i 0 0)
      have h2 : b₀ - Dt.w₀ i 0 0 ∈ IsLocalRing.maximalIdeal A := hsubmem hrb₀
      have := sub_mem h1 h2
      simp only [IncidenceSystem.Data.centre] at this
      convert this using 1; ring
    exact eq_of_eval_eq_zero_of_sub_mem F₀ hy hx hcg (hder ▸ hunitA 0)

  have hw10 : Pt (IncidenceSystem.Var.w i 1 0) = b₁ := by
    set F₁ : Polynomial A := (optionEquivLeft A (Fin 2) (rename sw1.symm (Dt.G i 1))).map
      (aeval (fun s => vA (sw1 (some s))) : MvPolynomial (Fin 2) A →ₐ[A] A).toRingHom with hF₁
    have hevF : ∀ Y, F₁.eval Y = MvPolynomial.eval (Function.update vA (some 1) Y) (Dt.G i 1) := by
      intro Y; rw [hF₁, hisoA sw1, sw1_none]
    have hx : F₁.eval (Pt (IncidenceSystem.Var.w i 1 0)) = 0 := by
      rw [hevF, ← hbranch0 1, hptc, hw00]
      have hfun : Function.update vA (some 1) (Pt (IncidenceSystem.Var.w i 1 0))
          = fun o => Option.elim o a ![b₀, Pt (IncidenceSystem.Var.w i 1 0)] := by
        funext o
        rcases o with _ | j
        · rw [Function.update_of_ne (by simp)]; rfl
        · fin_cases j
          · rw [Function.update_of_ne (by simp)]; rfl
          · simp
      rw [hfun]
    have hy : F₁.eval b₁ = 0 := by
      rw [hevF]
      have : Function.update vA (some 1) b₁ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]; exact hrootA 1
    have hder : F₁.derivative.eval b₁ = MvPolynomial.eval vA (pderiv (some 1) (Dt.G i 1)) := by
      rw [hF₁, Polynomial.derivative_map, derivative_optionEquivLeft,
        show (none : Option (Fin 2)) = sw1.symm (some 1) by rw [Equiv.eq_symm_apply, sw1_none],
        pderiv_rename sw1.symm.injective, hisoA sw1, sw1_none]
      have : Function.update vA (some 1) b₁ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]
    have hcg : Pt (IncidenceSystem.Var.w i 1 0) - b₁ ∈ IsLocalRing.maximalIdeal A := by
      have h1 := hPt (IncidenceSystem.Var.w i 1 0)
      have h2 : b₁ - Dt.w₀ i 1 0 ∈ IsLocalRing.maximalIdeal A := hsubmem hrb₁
      have := sub_mem h1 h2
      simp only [IncidenceSystem.Data.centre] at this
      convert this using 1; ring
    exact eq_of_eval_eq_zero_of_sub_mem F₁ hy hx hcg (hder ▸ hunitA 1)

  set w : Fin 2 → Fin (m' + 1) → L := fun j r => algebraMap A L (Pt (IncidenceSystem.Var.w i j r)) with hwdef
  have hsubst : ∀ H : MvPolynomial (Option (Fin 2)) A, (IncidenceSystem.substAt Pt i H).map (algebraMap A L)
      = aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C (algebraMap A L a) + Polynomial.X)
          (fun j => ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (w j r))) (MvPolynomial.map (algebraMap A L) H) := by
    intro H
    rw [map_substAt, MvPolynomial.aeval_def, Polynomial.algebraMap_eq]
  have hbranch : ∀ j (r : Fin (m' + 1)), (aeval (fun o : Option (Fin 2) => Option.elim o
      (Polynomial.C (algebraMap A L a) + Polynomial.X) (fun j => ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (w j r)))
        (MvPolynomial.map (algebraMap A L) (Dt.G i j))).coeff r = 0 := by
    intro j r
    rw [← hsubst, Polynomial.coeff_map]
    have h := eval_branch_eq_zero_of_root Dt Pt hroot i j r
    rw [IncidenceSystem.eval_branch] at h
    rw [h, map_zero]
  have hvars' : (some 1 : Option (Fin 2)) ∉ (MvPolynomial.map (algebraMap A L) (Dt.G i 0)).vars :=
    fun h => hvars (MvPolynomial.vars_map _ _ h)
  have hw₀ : ∀ r : Fin (m' + 1), w 0 r = Place.taylorCoeff Q t r (fs (some 0)) :=
    jet_eq_taylorCoeff_of_branch Q hQ ht (MvPolynomial.map (algebraMap A L) (Dt.G i 0)) hvars' fs hfs
      (algebraMap A L a) hz (hb 0) (hdG_ne 0) w
      (fun _ => by simp only [hwdef, Fin.zero_eta]; rw [hw00, evalAt_eq_of_hasValue Q (hval (some 0))]; rfl) (hbranch 0)
  have hw₁ : ∀ r : Fin (m' + 1), w 1 r = Place.taylorCoeff Q t r (fs (some 1)) :=
    jet_eq_taylorCoeff_of_branch_snd Q hQ ht (MvPolynomial.map (algebraMap A L) (Dt.G i 1)) fs hfs
      (algebraMap A L a) hz (hb 1) (hdG_ne 1) w hw₀
      (fun _ => by simp only [hwdef, Fin.zero_eta]; rw [hw10, evalAt_eq_of_hasValue Q (hval (some 1))]; rfl) (hbranch 1)
  have hw : ∀ j (r : Fin (m' + 1)), w j r = Place.taylorCoeff Q t r (fs (some j)) := by
    intro j r; fin_cases j; exacts [hw₀ r, hw₁ r]

  set Ser : Option (Fin 2) → PowerSeries L := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer
  have hcoeffH : ∀ (H : MvPolynomial (Option (Fin 2)) A) (r : Fin (m' + 1)),
      ((IncidenceSystem.substAt Pt i H).map (algebraMap A L)).coeff r
        = Place.taylorCoeff Q t r (aeval fs (MvPolynomial.map (algebraMap A L) H)) := by
    intro H r
    rw [hsubst, MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq _ _ w (fun j => Ser (some j))
      (fun j i' => by rw [hSer, PowerSeries.coeff_mk, hw]) r]
    have hfun : (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C (algebraMap A L a) + PowerSeries.X)
        fun j => Ser (some j)) = Ser := by
      funext o; rcases o with _ | j
      · simp only [Option.elim]; rw [← hz]
      · rfl
    rw [hfun, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs _, PowerSeries.coeff_mk]

  have hσ : ∀ kk (r : Fin (m' + 1)), algebraMap A L (Pt (IncidenceSystem.Var.σ kk i r))
      = Place.taylorCoeff Q t r (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))⁻¹ := by
    intro kk
    refine sigma_eq_taylorCoeff_inv Q hQ ht (MvPolynomial.map (algebraMap A L) (Dt.s kk i)) fs hfs
      (algebraMap A L a) hz (hs_ne kk) w hw _ fun r => ?_
    have h := eval_inv_eq_zero_of_root Dt Pt hroot kk i r
    rw [IncidenceSystem.eval_inv] at h
    have h' := congrArg (algebraMap A L) h
    rw [map_zero, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, hsubst] at h'
    rw [← h', map_spoly]

  have hsF_inv_mem := hsinv kk
  have hpmem : aeval fs (MvPolynomial.map (algebraMap A L) (Dt.p kk i)) ∈ Q.toValuationSubring := (hvalpoly _).mem
  have hps : hsec kk * (z - algebraMap L F (algebraMap A L (Dt.u₀ i))) ^ m' * (z - algebraMap L F (algebraMap A L τ))
      = aeval fs (MvPolynomial.map (algebraMap A L) (Dt.p kk i)) * (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))⁻¹ := by
    rw [hd kk, mul_inv_cancel_right₀ (hsF_ne kk)]
  rw [hps, Place.taylorCoeff_mul Q hQ ht hpmem hsF_inv_mem r, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 : x.1 < m' + 1 := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.fst_le hx) r.2
  have hx2 : x.2 < m' + 1 := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.snd_le hx) r.2
  rw [hcoeffH _ ⟨x.1, hx1⟩, map_spoly, coeff_sum_monomial_fin _ ⟨x.2, hx2⟩, hσ kk ⟨x.2, hx2⟩]

theorem reduced_entry {k' F' : Type*} [Field k'] [Field F'] [Algebra k' F'] {g m' : ℕ}
    (D' : IncidenceSystem.Data g 2 m' k') (i : Fin g) (ζ yb₁ yb₂ : F') (τ' : k') (hsec' : Option (Fin (g * m')) → F')
    (hvars : (some 1 : Option (Fin 2)) ∉ (D'.G i 0).vars)
    (hb' : ∀ j, aeval (fun o : Option (Fin 2) => Option.elim o ζ ![yb₁, yb₂]) (D'.G i j) = 0)
    (hd' : ∀ kk, aeval (fun o : Option (Fin 2) => Option.elim o ζ ![yb₁, yb₂]) (D'.p kk i)
      = hsec' kk * (ζ - algebraMap k' F' (D'.u₀ i)) ^ m' * (ζ - algebraMap k' F' τ')
        * aeval (fun o : Option (Fin 2) => Option.elim o ζ ![yb₁, yb₂]) (D'.s kk i))
    (he' : ∀ kk, D'.sVal D'.centre kk i ≠ 0) (hf' : ∀ j, D'.dG D'.centre i j ≠ 0)
    (hroot' : ∀ v, MvPolynomial.eval D'.centre (D'.system v) = 0)
    (w : Place k' F') (hw : w.IsRational)
    (hordz : w.ord (ζ - algebraMap k' F' (D'.u₀ i)) = 1)
    (hvalQ' : ∀ j : Fin 2, w.HasValue (![yb₁, yb₂] j) (D'.w₀ i j 0))
    (kk : Option (Fin (g * m'))) (r : Fin (m' + 1)) :
    (IncidenceSystem.substAt D'.centre i (D'.p kk i) * IncidenceSystem.spoly D'.centre kk i).coeff r
      = Place.taylorCoeff w (ζ - algebraMap k' F' (D'.u₀ i)) r
          (hsec' kk * (ζ - algebraMap k' F' (D'.u₀ i)) ^ m' * (ζ - algebraMap k' F' τ')) := by
  classical
  have hmax : IsLocalRing.maximalIdeal k' = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp (Field.toIsField k')
  have hker : ∀ a : k', (RingHom.id k') a = 0 ↔ a ∈ IsLocalRing.maximalIdeal k' := fun a => by
    rw [hmax, Ideal.mem_bot, RingHom.id_apply]
  have hcu : D'.centre (IncidenceSystem.Var.u i) = D'.u₀ i := rfl
  have h := point_jets' (L := k') (F := F') (A := k') (fun _ _ h => h) (RingHom.id k') hker D' i ζ yb₁ yb₂ τ' hsec' hvars
    (fun j => by rw [Algebra.algebraMap_self, MvPolynomial.map_id]; exact hb' j)
    (fun kk => by
      rw [Algebra.algebraMap_self, MvPolynomial.map_id, MvPolynomial.map_id, RingHom.id_apply, RingHom.id_apply]
      exact hd' kk)
    (fun kk => by rw [RingHom.id_apply]; exact he' kk) (fun j => by rw [RingHom.id_apply]; exact hf' j)
    D'.centre (fun v => by rw [sub_self, hmax]; exact zero_mem _)
    hroot' w hw (by rw [Algebra.algebraMap_self, RingHom.id_apply, hcu]; exact hordz)
    (fun j => ⟨D'.w₀ i j 0, by rw [Algebra.algebraMap_self, RingHom.id_apply]; exact hvalQ' j, rfl⟩) kk r
  rw [Algebra.algebraMap_self, Polynomial.map_id, Polynomial.map_id] at h
  simp only [RingHom.id_apply] at h
  rw [hcu] at h
  exact h

end RootsCore

namespace JacUnitAux
open AlgebraicCurve

theorem hasValue_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    {y : F} {b : K} (h : 0 < Q.ord (y - algebraMap K F b)) : Q.HasValue y b := by
  have hmem : y - algebraMap K F b ∈ Q.toValuationSubring := by
    by_cases h0 : y - algebraMap K F b = 0
    · rw [h0]; exact zero_mem _
    · exact Q.mem_of_ord_nonneg h0 h.le
  have hy : y ∈ Q.toValuationSubring := by
    have := add_mem hmem (Q.algebraMap_mem' b)
    rwa [sub_add_cancel] at this
  refine ⟨hy, ?_⟩
  have hmax := Q.mk_mem_maximalIdeal_of_ord_pos hmem h
  have hx : (⟨y - algebraMap K F b, hmem⟩ : Q.toValuationSubring)
      = ⟨y, hy⟩ - algebraMap K Q.toValuationSubring b := by
    refine Subtype.ext ?_
    show y - algebraMap K F b = y - (algebraMap K Q.toValuationSubring b : F)
    rw [Place.coe_algebraMap]
  rw [hx] at hmax
  have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, Q.residue_algebraMap]

theorem eq_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    {y : F} {b b' : K} (h : 0 < Q.ord (y - algebraMap K F b)) (h' : 0 < Q.ord (y - algebraMap K F b')) : b = b' :=
  (hasValue_of_ord_sub_pos Q h).unique (hasValue_of_ord_sub_pos Q h')

theorem res_evalBar
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] (red : A →+* k)
    (S : ValuationSubring ↥(modularFunctionFieldBar (N * q))) (res : S →+* ↥(modularFunctionFieldC k N))
    (hconst : ∀ a : A, ∃ hm : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ S,
      res ⟨_, hm⟩ = algebraMap k ↥(modularFunctionFieldC k N) (red a))
    (c : Option (Fin 2) → ↥(modularFunctionFieldBar (N * q))) (hc : ∀ o, c o ∈ S)
    (H : MvPolynomial (Option (Fin 2)) A) :
    ∃ hmem : ModularCurve.PlaceSpecialization.evalBar N q c H ∈ S,
      res ⟨_, hmem⟩ = MvPolynomial.aeval (fun o => res ⟨c o, hc o⟩) (MvPolynomial.map red H) := by
  classical

  have hirrel : ∀ (x y : ↥(modularFunctionFieldBar (N * q))) (hx : x ∈ S) (hy : y ∈ S), x = y → res ⟨x, hx⟩ = res ⟨y, hy⟩ := by
    rintro x y hx hy rfl; rfl
  unfold ModularCurve.PlaceSpecialization.evalBar
  set f := (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).comp (algebraMap A (AlgebraicClosure ℚ)) with hf
  induction H using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨hm, hres⟩ := hconst a
    have he : MvPolynomial.eval₂ f c (MvPolynomial.C a) = algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := by
      rw [MvPolynomial.eval₂_C]; rfl
    refine ⟨he ▸ hm, ?_⟩
    rw [hirrel _ _ _ hm he, hres, MvPolynomial.map_C, MvPolynomial.aeval_C]
  | add p p' hp hp' =>
    obtain ⟨hm, hres⟩ := hp
    obtain ⟨hm', hres'⟩ := hp'
    have he : MvPolynomial.eval₂ f c (p + p') = MvPolynomial.eval₂ f c p + MvPolynomial.eval₂ f c p' :=
      MvPolynomial.eval₂_add _ _
    refine ⟨he ▸ add_mem hm hm', ?_⟩
    rw [hirrel _ _ _ (add_mem hm hm') he, map_add, map_add, ← hres, ← hres', ← map_add]
    rfl
  | mul_X p o hp =>
    obtain ⟨hm, hres⟩ := hp
    have he : MvPolynomial.eval₂ f c (p * MvPolynomial.X o) = MvPolynomial.eval₂ f c p * c o := by
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    refine ⟨he ▸ mul_mem hm (hc o), ?_⟩
    rw [hirrel _ _ _ (mul_mem hm (hc o)) he, map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, ← hres, ← map_mul]
    rfl

theorem hasValue_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] {w : Place K F} {g : F} {a : K}
    (h : w.HasValue g a) (n : ℕ) : w.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Place.hasValue_one w
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem pack_fst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (v : Place k ↥(modularFunctionFieldC k N))
    {g' m' : ℕ} (Dt : IncidenceSystem.Data g' 2 m' A) (i : Fin g') (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (τ : A)
    (hsecF : Option (Fin (g' * m')) → ↥(modularFunctionFieldBar (N * q))) (hsecI : ∀ kk, hsecF kk ∈ R.R₁.integers)
    (zgen y1gen y2gen : ↥(modularFunctionFieldC k N))
    (hz : ∀ a : A, ∃ hm : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = zgen - algebraMap k ↥(modularFunctionFieldC k N) (red a))
    (hy1 : ∀ a : A, ∃ hm : y₁ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y1gen - algebraMap k ↥(modularFunctionFieldC k N) (red a))
    (hy2 : ∀ a : A, ∃ hm : y₂ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y2gen - algebraMap k ↥(modularFunctionFieldC k N) (red a))
    (hord : v.ord (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i))) = 1)
    (hv1 : v.HasValue y1gen (red (Dt.w₀ i 0 0))) (hv2 : v.HasValue y2gen (red (Dt.w₀ i 1 0)))
    (hb : ∀ j : Fin 2, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.G i j) = 0)
    (hd : ∀ kk, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.p kk i)
      = hsecF kk * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ)) ^ m' * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ))
        * evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.s kk i))
    (hτ : red τ = red (Dt.u₀ i)) :
    (v.ord (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i))) = 1) ∧
    (∀ j : Fin 2, v.HasValue (![y1gen, y2gen] j) (red (Dt.w₀ i j 0))) ∧
    (∀ j : Fin 2, MvPolynomial.aeval (fun o => Option.elim o zgen ![y1gen, y2gen]) ((Dt.map red).G i j) = 0) ∧
    (∀ kk, MvPolynomial.aeval (fun o => Option.elim o zgen ![y1gen, y2gen]) ((Dt.map red).p kk i)
      = (R.residue₁ ⟨hsecF kk, hsecI kk⟩ : ↥(modularFunctionFieldC k N)) * (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i))) ^ m'
        * (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i)))
        * MvPolynomial.aeval (fun o => Option.elim o zgen ![y1gen, y2gen]) ((Dt.map red).s kk i)) := by
  classical

  have hconstmem : ∀ a : A, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    fun a => (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2
  have hirrel : ∀ (x y : ↥(modularFunctionFieldBar (N * q))) (hx : x ∈ R.R₁.integers) (hy : y ∈ R.R₁.integers), x = y →
      R.residue₁ ⟨x, hx⟩ = R.residue₁ ⟨y, hy⟩ := by rintro x y hx hy rfl; rfl
  have hconst : ∀ a : A, ∃ hm : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    intro a
    refine ⟨hconstmem a, ?_⟩
    obtain ⟨h0, e0⟩ := hz 0
    obtain ⟨ha, ea⟩ := hz a
    have hx : (⟨_, hconstmem a⟩ : R.R₁.integers) = ⟨_, h0⟩ - ⟨_, ha⟩ := by
      refine Subtype.ext ?_
      show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) = (z - _) - (z - _)
      simp
    rw [hx, map_sub, e0, ea, map_zero, map_zero, sub_zero]
    ring

  obtain ⟨hzu, ezu⟩ := hz (Dt.u₀ i)
  obtain ⟨hzτ, ezτ⟩ := hz τ
  obtain ⟨hy1w, ey1w⟩ := hy1 (Dt.w₀ i 0 0)
  obtain ⟨hy2w, ey2w⟩ := hy2 (Dt.w₀ i 1 0)
  have hcI : ∀ o : Option (Fin 2), (Option.elim o z ![y₁, y₂] : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers := by
    intro o
    rcases o with _ | j
    · have := add_mem hzu (hconstmem (Dt.u₀ i)); rwa [sub_add_cancel] at this
    · fin_cases j
      · have := add_mem hy1w (hconstmem (Dt.w₀ i 0 0)); simpa using this
      · have := add_mem hy2w (hconstmem (Dt.w₀ i 1 0)); simpa using this
  have hresc : ∀ o : Option (Fin 2), (R.residue₁ ⟨_, hcI o⟩ : ↥(modularFunctionFieldC k N)) = Option.elim o zgen ![y1gen, y2gen] := by
    have key : ∀ (x : ↥(modularFunctionFieldBar (N * q))) (a : A) (hxa : x - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) (hx : x ∈ R.R₁.integers)
        (xgen : ↥(modularFunctionFieldC k N)), (R.residue₁ ⟨_, hxa⟩ : ↥(modularFunctionFieldC k N)) = xgen - algebraMap k ↥(modularFunctionFieldC k N) (red a) → (R.residue₁ ⟨x, hx⟩ : ↥(modularFunctionFieldC k N)) = xgen := by
      intro x a hxa hx xgen e
      obtain ⟨hm, em⟩ := hconst a
      have hx' : (⟨x, hx⟩ : R.R₁.integers) = ⟨_, hxa⟩ + ⟨_, hm⟩ := Subtype.ext (by simp)
      rw [hx', map_add, e, em, sub_add_cancel]
    intro o
    rcases o with _ | j
    · exact key z _ hzu _ zgen ezu
    · fin_cases j
      · exact key y₁ _ hy1w _ y1gen ey1w
      · exact key y₂ _ hy2w _ y2gen ey2w
  have hfun : (fun o : Option (Fin 2) => (R.residue₁ ⟨_, hcI o⟩ : ↥(modularFunctionFieldC k N))) = fun o => Option.elim o zgen ![y1gen, y2gen] :=
    funext hresc
  refine ⟨hord, fun j => by fin_cases j <;> assumption, fun j => ?_, fun kk => ?_⟩
  ·
    obtain ⟨hmem, hres⟩ := res_evalBar red R.R₁.integers R.residue₁ hconst _ hcI (Dt.G i j)
    rw [hfun] at hres
    rw [show (Dt.map red).G i j = MvPolynomial.map red (Dt.G i j) from rfl, ← hres,
      hirrel _ 0 hmem (zero_mem _) (hb j), show (⟨(0 : ↥(modularFunctionFieldBar (N * q))), zero_mem _⟩ : R.R₁.integers) = 0 from rfl, map_zero]
  ·
    obtain ⟨hmp, hrp⟩ := res_evalBar red R.R₁.integers R.residue₁ hconst _ hcI (Dt.p kk i)
    obtain ⟨hms, hrs⟩ := res_evalBar red R.R₁.integers R.residue₁ hconst _ hcI (Dt.s kk i)
    rw [hfun] at hrp hrs
    rw [show (Dt.map red).p kk i = MvPolynomial.map red (Dt.p kk i) from rfl,
      show (Dt.map red).s kk i = MvPolynomial.map red (Dt.s kk i) from rfl, ← hrp, ← hrs]
    have hx : (⟨_, hmp⟩ : R.R₁.integers)
        = ⟨hsecF kk, hsecI kk⟩ * ⟨_, hzu⟩ ^ m' * ⟨_, hzτ⟩ * ⟨_, hms⟩ := by
      refine Subtype.ext ?_
      push_cast
      exact hd kk
    rw [hx, map_mul, map_mul, map_mul, map_pow, ezu, ezτ, hτ]

theorem pack_snd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (v : Place k ↥(modularFunctionFieldC k N))
    {g' m' : ℕ} (Dt : IncidenceSystem.Data g' 2 m' A) (i : Fin g') (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (τ : A)
    (hsecF : Option (Fin (g' * m')) → ↥(modularFunctionFieldBar (N * q))) (hsecI : ∀ kk, hsecF kk ∈ R.R₂.integers)
    (zgen y1gen y2gen : ↥(modularFunctionFieldC k N))
    (hz : ∀ a : A, ∃ hm : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = zgen - algebraMap k ↥(modularFunctionFieldC k N) (red a))
    (hy1 : ∀ a : A, ∃ hm : y₁ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y1gen - algebraMap k ↥(modularFunctionFieldC k N) (red a))
    (hy2 : ∀ a : A, ∃ hm : y₂ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y2gen - algebraMap k ↥(modularFunctionFieldC k N) (red a))
    (hord : v.ord (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i))) = 1)
    (hv1 : v.HasValue y1gen (red (Dt.w₀ i 0 0))) (hv2 : v.HasValue y2gen (red (Dt.w₀ i 1 0)))
    (hb : ∀ j : Fin 2, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.G i j) = 0)
    (hd : ∀ kk, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.p kk i)
      = hsecF kk * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ)) ^ m' * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ))
        * evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.s kk i))
    (hτ : red τ = red (Dt.u₀ i)) :
    (v.ord (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i))) = 1) ∧
    (∀ j : Fin 2, v.HasValue (![y1gen, y2gen] j) (red (Dt.w₀ i j 0))) ∧
    (∀ j : Fin 2, MvPolynomial.aeval (fun o => Option.elim o zgen ![y1gen, y2gen]) ((Dt.map red).G i j) = 0) ∧
    (∀ kk, MvPolynomial.aeval (fun o => Option.elim o zgen ![y1gen, y2gen]) ((Dt.map red).p kk i)
      = (R.residue₂ ⟨hsecF kk, hsecI kk⟩ : ↥(modularFunctionFieldC k N)) * (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i))) ^ m'
        * (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ i)))
        * MvPolynomial.aeval (fun o => Option.elim o zgen ![y1gen, y2gen]) ((Dt.map red).s kk i)) := by
  classical

  have hconstmem : ∀ a : A, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
    fun a => (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2
  have hirrel : ∀ (x y : ↥(modularFunctionFieldBar (N * q))) (hx : x ∈ R.R₂.integers) (hy : y ∈ R.R₂.integers), x = y →
      R.residue₂ ⟨x, hx⟩ = R.residue₂ ⟨y, hy⟩ := by rintro x y hx hy rfl; rfl
  have hconst : ∀ a : A, ∃ hm : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    intro a
    refine ⟨hconstmem a, ?_⟩
    obtain ⟨h0, e0⟩ := hz 0
    obtain ⟨ha, ea⟩ := hz a
    have hx : (⟨_, hconstmem a⟩ : R.R₂.integers) = ⟨_, h0⟩ - ⟨_, ha⟩ := by
      refine Subtype.ext ?_
      show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) = (z - _) - (z - _)
      simp
    rw [hx, map_sub, e0, ea, map_zero, map_zero, sub_zero]
    ring

  obtain ⟨hzu, ezu⟩ := hz (Dt.u₀ i)
  obtain ⟨hzτ, ezτ⟩ := hz τ
  obtain ⟨hy1w, ey1w⟩ := hy1 (Dt.w₀ i 0 0)
  obtain ⟨hy2w, ey2w⟩ := hy2 (Dt.w₀ i 1 0)
  have hcI : ∀ o : Option (Fin 2), (Option.elim o z ![y₁, y₂] : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₂.integers := by
    intro o
    rcases o with _ | j
    · have := add_mem hzu (hconstmem (Dt.u₀ i)); rwa [sub_add_cancel] at this
    · fin_cases j
      · have := add_mem hy1w (hconstmem (Dt.w₀ i 0 0)); simpa using this
      · have := add_mem hy2w (hconstmem (Dt.w₀ i 1 0)); simpa using this
  have hresc : ∀ o : Option (Fin 2), (R.residue₂ ⟨_, hcI o⟩ : ↥(modularFunctionFieldC k N)) = Option.elim o zgen ![y1gen, y2gen] := by
    have key : ∀ (x : ↥(modularFunctionFieldBar (N * q))) (a : A) (hxa : x - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) (hx : x ∈ R.R₂.integers)
        (xgen : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨_, hxa⟩ : ↥(modularFunctionFieldC k N)) = xgen - algebraMap k ↥(modularFunctionFieldC k N) (red a) → (R.residue₂ ⟨x, hx⟩ : ↥(modularFunctionFieldC k N)) = xgen := by
      intro x a hxa hx xgen e
      obtain ⟨hm, em⟩ := hconst a
      have hx' : (⟨x, hx⟩ : R.R₂.integers) = ⟨_, hxa⟩ + ⟨_, hm⟩ := Subtype.ext (by simp)
      rw [hx', map_add, e, em, sub_add_cancel]
    intro o
    rcases o with _ | j
    · exact key z _ hzu _ zgen ezu
    · fin_cases j
      · exact key y₁ _ hy1w _ y1gen ey1w
      · exact key y₂ _ hy2w _ y2gen ey2w
  have hfun : (fun o : Option (Fin 2) => (R.residue₂ ⟨_, hcI o⟩ : ↥(modularFunctionFieldC k N))) = fun o => Option.elim o zgen ![y1gen, y2gen] :=
    funext hresc
  refine ⟨hord, fun j => by fin_cases j <;> assumption, fun j => ?_, fun kk => ?_⟩
  ·
    obtain ⟨hmem, hres⟩ := res_evalBar red R.R₂.integers R.residue₂ hconst _ hcI (Dt.G i j)
    rw [hfun] at hres
    rw [show (Dt.map red).G i j = MvPolynomial.map red (Dt.G i j) from rfl, ← hres,
      hirrel _ 0 hmem (zero_mem _) (hb j), show (⟨(0 : ↥(modularFunctionFieldBar (N * q))), zero_mem _⟩ : R.R₂.integers) = 0 from rfl, map_zero]
  ·
    obtain ⟨hmp, hrp⟩ := res_evalBar red R.R₂.integers R.residue₂ hconst _ hcI (Dt.p kk i)
    obtain ⟨hms, hrs⟩ := res_evalBar red R.R₂.integers R.residue₂ hconst _ hcI (Dt.s kk i)
    rw [hfun] at hrp hrs
    rw [show (Dt.map red).p kk i = MvPolynomial.map red (Dt.p kk i) from rfl,
      show (Dt.map red).s kk i = MvPolynomial.map red (Dt.s kk i) from rfl, ← hrp, ← hrs]
    have hx : (⟨_, hmp⟩ : R.R₂.integers)
        = ⟨hsecF kk, hsecI kk⟩ * ⟨_, hzu⟩ ^ m' * ⟨_, hzτ⟩ * ⟨_, hms⟩ := by
      refine Subtype.ext ?_
      push_cast
      exact hd kk
    rw [hx, map_mul, map_mul, map_mul, map_pow, ezu, ezτ, hτ]

theorem fst_inputs
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    {B : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hB : P.IsStrictFst B) (haff : IsAffineGeomPlace k N (P.reduceFst B))
    (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u₀ w₀₀ w₁₀ : A)
    (htri : IsFstTriple (q := q) (P.reduceFst B) (red u₀) z y₁ y₂)
    (hc0 : 0 < B.ord (y₁ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀₀ : AlgebraicClosure ℚ)))
    (hc1 : 0 < B.ord (y₂ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₁₀ : AlgebraicClosure ℚ))) :
    ∃ zgen y1gen y2gen : ↥(modularFunctionFieldC k N),
      (∀ a : A, ∃ hm : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
        (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = zgen - algebraMap k ↥(modularFunctionFieldC k N) (red a)) ∧
      (∀ a : A, ∃ hm : y₁ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
        (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y1gen - algebraMap k ↥(modularFunctionFieldC k N) (red a)) ∧
      (∀ a : A, ∃ hm : y₂ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
        (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y2gen - algebraMap k ↥(modularFunctionFieldC k N) (red a)) ∧
      (P.reduceFst B).ord (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red u₀)) = 1 ∧
      (P.reduceFst B).HasValue y1gen (red w₀₀) ∧ (P.reduceFst B).HasValue y2gen (red w₁₀) := by
  classical
  set v := P.reduceFst B with hv
  have hrat : v.IsRational := (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)
  have hsnd : P.reduceSnd B = frobOnPlacesGeomLevel k N data hKr v := hB.1.symm
  have haff' : IsAffineGeomPlace k N (P.reduceSnd B) := by
    rw [hsnd]
    exact ((exists_isCentreOf_of_isRational hrat haff).frobOnPlacesGeomLevel data hKr).isAffineGeomPlace

  have hcen := exists_isCentreOf_of_isRational hrat haff
  have hcenF := hcen.frobOnPlacesGeomLevel data hKr

  have KJ : ∀ a : A, ∃ hm : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := fun a => by
    obtain ⟨h₁, -, -, -, e₁, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN a
    exact ⟨h₁, e₁⟩
  have KN : ∀ a : A, ∃ hm : jNFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := fun a => by
    obtain ⟨h₁, -, -, -, e₁, -, -, -⟩ := R.residue_jNFun_sub_jNQFun_sub hqN a
    exact ⟨h₁, e₁⟩
  have KNQ : ∀ a : A, ∃ hm : jNQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = jNGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) := fun a => by
    obtain ⟨-, -, h₃, -, -, -, e₃, -⟩ := R.residue_jNFun_sub_jNQFun_sub hqN a
    exact ⟨h₃, e₃⟩

  have VJ : ∀ w₀ : A, 0 < B.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀ : AlgebraicClosure ℚ)) →
      v.HasValue (jGeomGen k N) (red w₀) := by
    intro w₀ hw
    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst B haff
    rw [← Subtype.ext (eq_of_ord_sub_pos B ha' hw)]
    exact hasValue_of_ord_sub_pos v ha'v
  have VN : ∀ w₀ : A, 0 < B.ord (jNFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀ : AlgebraicClosure ℚ)) →
      v.HasValue (jNGeomGen k N) (red w₀) := by
    intro w₀ hw
    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst B haff
    rw [← Subtype.ext (eq_of_ord_sub_pos B ha' hw)]
    exact hasValue_of_ord_sub_pos v ha'v
  have VNQ : ∀ w₀ : A, 0 < B.ord (jNQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀ : AlgebraicClosure ℚ)) →
      v.HasValue (jNGeomGen k N ^ q) (red w₀) := by
    intro w₀ hw
    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd B haff'
    rw [← Subtype.ext (eq_of_ord_sub_pos B ha' hw)]

    rw [hsnd] at ha'v
    have e := eq_of_ord_sub_pos _ hcenF.2 ha'v
    rw [← e]
    exact hasValue_pow' (hasValue_of_ord_sub_pos v hcen.2) q
  rcases htri with ⟨hz, hy1, hy2, hord⟩ | ⟨hz, hy1, hy2, hord⟩
  · subst hz hy1 hy2
    exact ⟨_, _, _, KJ, KN, KNQ, hord, VN _ hc0, VNQ _ hc1⟩
  · subst hz hy1 hy2
    exact ⟨_, _, _, KN, KJ, KNQ, hord, VJ _ hc0, VNQ _ hc1⟩

theorem snd_inputs
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    {B : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hB : P.IsStrictSnd B) (haff : IsAffineGeomPlace k N (P.reduceSnd B))
    (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u₀ w₀₀ w₁₀ : A)
    (htri : IsSndTriple (q := q) (P.reduceSnd B) (red u₀) z y₁ y₂)
    (hc0 : 0 < B.ord (y₁ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀₀ : AlgebraicClosure ℚ)))
    (hc1 : 0 < B.ord (y₂ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₁₀ : AlgebraicClosure ℚ))) :
    ∃ zgen y1gen y2gen : ↥(modularFunctionFieldC k N),
      (∀ a : A, ∃ hm : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
        (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = zgen - algebraMap k ↥(modularFunctionFieldC k N) (red a)) ∧
      (∀ a : A, ∃ hm : y₁ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
        (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y1gen - algebraMap k ↥(modularFunctionFieldC k N) (red a)) ∧
      (∀ a : A, ∃ hm : y₂ - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
        (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = y2gen - algebraMap k ↥(modularFunctionFieldC k N) (red a)) ∧
      (P.reduceSnd B).ord (zgen - algebraMap k ↥(modularFunctionFieldC k N) (red u₀)) = 1 ∧
      (P.reduceSnd B).HasValue y1gen (red w₀₀) ∧ (P.reduceSnd B).HasValue y2gen (red w₁₀) := by
  classical
  set v := P.reduceSnd B with hv
  have hrat : v.IsRational := (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)
  have hsnd : P.reduceFst B = frobOnPlacesGeomLevel k N data hKr v := hB.1
  have haff' : IsAffineGeomPlace k N (P.reduceFst B) := by
    rw [hsnd]
    exact ((exists_isCentreOf_of_isRational hrat haff).frobOnPlacesGeomLevel data hKr).isAffineGeomPlace

  have hcen := exists_isCentreOf_of_isRational hrat haff
  have hcenF := hcen.frobOnPlacesGeomLevel data hKr

  have KQ : ∀ a : A, ∃ hm : ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := fun a => by
    obtain ⟨-, -, -, h₄, -, -, -, e₄⟩ := R.residue_jFun_sub_jQFun_sub hqN a
    exact ⟨h₄, e₄⟩
  have KJ2 : ∀ a : A, ∃ hm : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = jGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) := fun a => by
    obtain ⟨-, h₂, -, -, -, e₂, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN a
    exact ⟨h₂, e₂⟩
  have KNQ2 : ∀ a : A, ∃ hm : jNQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, hm⟩ : ↥(modularFunctionFieldC k N)) = jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := fun a => by
    obtain ⟨-, -, -, h₄, -, -, -, e₄⟩ := R.residue_jNFun_sub_jNQFun_sub hqN a
    exact ⟨h₄, e₄⟩

  have VQ : ∀ w₀ : A, 0 < B.ord (ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀ : AlgebraicClosure ℚ)) →
      v.HasValue (jGeomGen k N) (red w₀) := by
    intro w₀ hw
    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd B haff
    rw [← Subtype.ext (eq_of_ord_sub_pos B ha' hw)]
    exact hasValue_of_ord_sub_pos v ha'v
  have VNQ2 : ∀ w₀ : A, 0 < B.ord (jNQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀ : AlgebraicClosure ℚ)) →
      v.HasValue (jNGeomGen k N) (red w₀) := by
    intro w₀ hw
    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd B haff
    rw [← Subtype.ext (eq_of_ord_sub_pos B ha' hw)]
    exact hasValue_of_ord_sub_pos v ha'v
  have VJ2 : ∀ w₀ : A, 0 < B.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀ : AlgebraicClosure ℚ)) →
      v.HasValue (jGeomGen k N ^ q) (red w₀) := by
    intro w₀ hw
    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst B haff'
    rw [← Subtype.ext (eq_of_ord_sub_pos B ha' hw)]
    rw [hsnd] at ha'v
    have e := eq_of_ord_sub_pos _ hcenF.1 ha'v
    rw [← e]
    exact hasValue_pow' (hasValue_of_ord_sub_pos v hcen.1) q
  rcases htri with ⟨hz, hy1, hy2, hord⟩ | ⟨hz, hy1, hy2, hord⟩
  · subst hz hy1 hy2
    exact ⟨_, _, _, KQ, KNQ2, KJ2, hord, VNQ2 _ hc0, VJ2 _ hc1⟩
  · subst hz hy1 hy2
    exact ⟨_, _, _, KNQ2, KQ, KJ2, hord, VQ _ hc0, VJ2 _ hc1⟩

theorem ord_pow_eq {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F'] (w : Place K' F') {x : F'} (hx : x ≠ 0) (n : ℕ) :
    w.ord (x ^ n) = n * w.ord x := by
  induction n with
  | zero => rw [pow_zero, Place.ord_one]; simp
  | succ n ih => rw [pow_succ, Place.ord_mul w (pow_ne_zero n hx) hx, ih]; push_cast; ring

end JacUnitAux

set_option maxHeartbeats 16000000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q))) (hh0 : h 0 = 1)
    (hh₁ : ∀ l, h l ∈ R.R₁.integers)
    (hhL : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
        + (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l))
    (hh₂ : ∀ l, h l ∈ R.R₂.integers)
    (hhland : ∀ l,
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v ∈ T₁, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v ∈ T₂, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)) c ∧
        (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)) c))
    (hhind : LinearIndependent k (fun l =>
      ((R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)))))
    (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A) (hrep : P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt)
    (hm : ((m' + 1 : ℕ) : k) ≠ 0) :
    IsUnit (Dt.jacobian Dt.centre).det := by
  classical

  have hred : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A := by
    intro a
    rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]
  have hunit : ∀ a : A, IsUnit a ↔ red a ≠ 0 := by
    intro a
    rw [Ne, hred, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hdet : red (Dt.jacobian Dt.centre).det = ((Dt.map red).jacobian (red ∘ Dt.centre)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← IncidenceSystem.Data.map_jacobian]
  rw [hunit, hdet, ← isUnit_iff_ne_zero]

  obtain ⟨hpt, happrox⟩ := hrep
  have htri : ∀ i (j j' : Fin 2), j < j' → MvPolynomial.pderiv (some j') ((Dt.map red).G i j) = 0 := by
    intro i j j' hjj
    obtain ⟨z, y₁, y₂, τ, -, -, htri0, -⟩ := hpt i
    have hj : j = 0 ∧ j' = 1 := by
      revert hjj; revert j j'; decide
    obtain ⟨rfl, rfl⟩ := hj
    have hG0 : (Dt.map red).G i 0 = MvPolynomial.map red (Dt.G i 0) := rfl
    rw [hG0, MvPolynomial.pderiv_map, MvPolynomial.pderiv_eq_zero_of_notMem_vars htri0, map_zero]
  have hc : ∀ kk, (red ∘ Dt.centre) (IncidenceSystem.Var.c kk) = 0 := fun kk => by
    simp [IncidenceSystem.Data.centre]
  have hσ : ∀ i r, (red ∘ Dt.centre) (IncidenceSystem.Var.σ none i r) = if (r : ℕ) = 0 then 1 else 0 := by
    intro i r
    obtain ⟨z, y₁, y₂, τ, -, -, -, -, -, -, -, -, -, hσ0, -⟩ := hpt i
    simp only [Function.comp_apply, IncidenceSystem.Data.centre, hσ0, Pi.single_apply]
    by_cases hr : r = 0
    · subst hr; simp
    · have hr' : (r : ℕ) ≠ 0 := fun h0 => hr (Fin.ext h0)
      simp [hr, hr']
  have hs : ∀ i, (Dt.map red).s none i = 1 := by
    intro i
    obtain ⟨z, y₁, y₂, τ, -, -, -, -, -, -, -, -, hs1, -⟩ := hpt i
    simp [IncidenceSystem.Data.map, hs1]

  have hτ : ∀ i, ∃ τ : A, Dt.p none i =
      (MvPolynomial.X none - MvPolynomial.C (Dt.u₀ i)) ^ m' * (MvPolynomial.X none - MvPolynomial.C τ) ∧
      red τ = red (Dt.u₀ i) := by
    intro i
    obtain ⟨z, y₁, y₂, τ, htrip, -, -, hcu, -, hcτ, -, hpin, -⟩ := hpt i
    refine ⟨τ, hpin, ?_⟩

    obtain ⟨s, rfl⟩ : ∃ s, finSumFinEquiv s = i := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hredk : ∀ {a b : A}, (∃ (v : Place k ↥(modularFunctionFieldC k N)) (ygen : ↥(modularFunctionFieldC k N)),
        0 < v.ord (ygen - algebraMap k _ (red a)) ∧ 0 < v.ord (ygen - algebraMap k _ (red b))) → red a = red b := by
      rintro a b ⟨v, ygen, h1, h2⟩
      exact JacUnitAux.eq_of_ord_sub_pos v h1 h2
    rcases s with i₁ | i₂
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl] at htrip hcu hcτ
      have haff : IsAffineGeomPlace k N (P.reduceFst (Q₁ i₁)) := hT₁aff _ ((hT₁ _).mpr ⟨i₁, rfl⟩)
      have haff' : IsAffineGeomPlace k N (P.reduceFst (Q₁' i₁)) := by rw [hred₁]; exact haff
      rcases htrip with ⟨hz, -, -, -⟩ | ⟨hz, -, -, -⟩
      · subst hz
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁' i₁) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
        rw [hred₁] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩
      · subst hz
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁' i₁) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
        rw [hred₁] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr] at htrip hcu hcτ
      have haff : IsAffineGeomPlace k N (P.reduceSnd (Q₂ i₂)) := hT₂aff _ ((hT₂ _).mpr ⟨i₂, rfl⟩)
      have haff' : IsAffineGeomPlace k N (P.reduceSnd (Q₂' i₂)) := by rw [hred₂]; exact haff
      rcases htrip with ⟨hz, -, -, -⟩ | ⟨hz, -, -, -⟩
      · subst hz
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂' i₂) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
        rw [hred₂] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩
      · subst hz
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂' i₂) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
        rw [hred₂] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩
  have hp : ∀ i, (Dt.map red).p none i =
      (MvPolynomial.X none - MvPolynomial.C ((red ∘ Dt.centre) (IncidenceSystem.Var.u i))) ^ (m' + 1) := by
    intro i
    obtain ⟨τ, hpin, hτu⟩ := hτ i
    show MvPolynomial.map red (Dt.p none i) = _
    rw [hpin, map_mul, map_pow, map_sub, map_sub, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.map_C, hτu,
      pow_succ]
    rfl
  have hG : ∀ i j, IsUnit ((Dt.map red).dG (red ∘ Dt.centre) i j) := by
    intro i j
    obtain ⟨z, y₁, y₂, τ, -, -, -, -, -, -, -, -, -, -, -, hf⟩ := hpt i
    rw [IncidenceSystem.Data.map_dG, isUnit_iff_ne_zero]
    exact hf j
  have hsv : ∀ kk i, IsUnit ((Dt.map red).sVal (red ∘ Dt.centre) kk i) := by
    intro kk i
    obtain ⟨z, y₁, y₂, τ, -, -, -, -, -, -, -, -, -, -, he, -⟩ := hpt i
    rw [IncidenceSystem.Data.map_sVal, isUnit_iff_ne_zero]
    exact he kk
  rw [IncidenceSystem.Data.isUnit_det_jacobian_iff (Dt.map red) (red ∘ Dt.centre) htri hc hσ hp hs hG hsv]
  refine ⟨isUnit_iff_ne_zero.mpr (pow_ne_zero _ hm), ?_⟩

  classical
  choose zf y1f y2f τf hcl using hpt

  have hτf : ∀ i, red (τf i) = red (Dt.u₀ i) := by
    intro i
    obtain ⟨htrip, -, -, hcu, -, hcτ, -⟩ := hcl i
    obtain ⟨s, rfl⟩ : ∃ s, finSumFinEquiv s = i := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hredk : ∀ {a b : A}, (∃ (v : Place k ↥(modularFunctionFieldC k N)) (ygen : ↥(modularFunctionFieldC k N)),
        0 < v.ord (ygen - algebraMap k _ (red a)) ∧ 0 < v.ord (ygen - algebraMap k _ (red b))) → red a = red b := by
      rintro a b ⟨v, ygen, h1, h2⟩
      exact JacUnitAux.eq_of_ord_sub_pos v h1 h2
    rcases s with i₁ | i₂
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl] at htrip hcu hcτ
      have haff : IsAffineGeomPlace k N (P.reduceFst (Q₁ i₁)) := hT₁aff _ ((hT₁ _).mpr ⟨i₁, rfl⟩)
      have haff' : IsAffineGeomPlace k N (P.reduceFst (Q₁' i₁)) := by rw [hred₁]; exact haff
      rcases htrip with ⟨hz, -, -, -⟩ | ⟨hz, -, -, -⟩
      · rw [hz] at hcu hcτ
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁' i₁) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
        rw [hred₁] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩
      · rw [hz] at hcu hcτ
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁' i₁) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
        rw [hred₁] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr] at htrip hcu hcτ
      have haff : IsAffineGeomPlace k N (P.reduceSnd (Q₂ i₂)) := hT₂aff _ ((hT₂ _).mpr ⟨i₂, rfl⟩)
      have haff' : IsAffineGeomPlace k N (P.reduceSnd (Q₂' i₂)) := by rw [hred₂]; exact haff
      rcases htrip with ⟨hz, -, -, -⟩ | ⟨hz, -, -, -⟩
      · rw [hz] at hcu hcτ
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂' i₂) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
        rw [hred₂] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩
      · rw [hz] at hcu hcτ
        obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂' i₂) haff'
        obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
        rw [hred₂] at ha'v
        rw [← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha' hcτ), ← Subtype.ext (JacUnitAux.eq_of_ord_sub_pos _ ha'' hcu)]
        exact hredk ⟨_, _, ha'v, ha''v⟩

  set D' : IncidenceSystem.Data (d₁ + d₂) 2 m' k := Dt.map red with hD'
  have hcen' : D'.centre = red ∘ Dt.centre := IncidenceSystem.Data.map_centre Dt red
  have hroot' : ∀ v, MvPolynomial.eval D'.centre (D'.system v) = 0 := fun v => by
    rw [hcen', hD', IncidenceSystem.Data.map_system, IncidenceSystem.eval_comp_map, hred]
    exact happrox v
  have hsval' : ∀ kk i, D'.sVal D'.centre kk i ≠ 0 := fun kk i => by
    rw [hcen', hD', IncidenceSystem.Data.map_sVal]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, he, -⟩ := hcl i
    exact he kk
  have hdG' : ∀ i j, D'.dG D'.centre i j ≠ 0 := fun i j => by
    rw [hcen', hD', IncidenceSystem.Data.map_dG]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hf⟩ := hcl i
    exact hf j
  have hvars' : ∀ i, (some 1 : Option (Fin 2)) ∉ (D'.G i 0).vars := fun i hmem => by
    obtain ⟨-, -, hv, -⟩ := hcl i
    exact hv (MvPolynomial.vars_map _ _ hmem)

  set hsecF : Option (Fin ((d₁ + d₂) * m')) → ↥(modularFunctionFieldBar (N * q)) := fun kk => Option.elim kk (1 : ↥(modularFunctionFieldBar (N * q))) fun kk => h kk.succ with hsecFdef
  have hsecI₁ : ∀ kk, hsecF kk ∈ R.R₁.integers := by
    intro kk; rcases kk with _ | kk
    · exact one_mem _
    · exact hh₁ _
  have hsecI₂ : ∀ kk, hsecF kk ∈ R.R₂.integers := by
    intro kk; rcases kk with _ | kk
    · exact one_mem _
    · exact hh₂ _
  have hrat : ∀ v : Place k ↥(modularFunctionFieldC k N), v.IsRational := fun v =>
    (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)

  have htcM : ∀ (i : Fin (d₁ + d₂)) (r : Fin m') (kc : Fin ((d₁ + d₂) * m')),
      D'.tcMatrix D'.centre (finProdFinEquiv (i, r)) kc
        = (IncidenceSystem.substAt D'.centre i (D'.p (some kc) i) * IncidenceSystem.spoly D'.centre (some kc) i).coeff (Fin.castSucc r) := by
    intro i r kc
    rw [IncidenceSystem.Data.tcMatrix, Matrix.of_apply, Equiv.symm_apply_apply, IncidenceSystem.eval_tc]

  have E1 : ∀ i₁ : Fin d₁, ∃ ζ : ↥(modularFunctionFieldC k N),
      (P.reduceFst (Q₁ i₁)).ord (ζ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inl i₁))))) = 1 ∧
      ∀ (kc : Fin ((d₁ + d₂) * m')) (r : Fin m'),
        D'.tcMatrix D'.centre (finProdFinEquiv (finSumFinEquiv (Sum.inl i₁), r)) kc
          = Place.taylorCoeff (P.reduceFst (Q₁ i₁)) (ζ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inl i₁))))) (Fin.castSucc r)
              ((R.residue₁ ⟨h kc.succ, hh₁ _⟩ : ↥(modularFunctionFieldC k N)) *
                (ζ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inl i₁))))) ^ (m' + 1)) := by
    intro i₁
    set i : Fin (d₁ + d₂) := finSumFinEquiv (Sum.inl i₁) with hidef
    obtain ⟨htrip, hb, -, hcu, hc2, hcτ, hd, -⟩ := hcl i
    simp only [hidef, Equiv.symm_apply_apply, Sum.elim_inl] at htrip hcu hc2 hcτ
    have haff : IsAffineGeomPlace k N (P.reduceFst (Q₁ i₁)) := hT₁aff _ ((hT₁ _).mpr ⟨i₁, rfl⟩)
    obtain ⟨zgen, y1gen, y2gen, hz, hy1, hy2, hord, hv1, hv2⟩ :=
      JacUnitAux.fst_inputs hqN R (hQ₁ i₁) haff (zf i) (y1f i) (y2f i) (Dt.u₀ i) (Dt.w₀ i 0 0) (Dt.w₀ i 1 0)
        htrip (hc2 0) (hc2 1)
    obtain ⟨hord', hval', hb', hd'⟩ := JacUnitAux.pack_fst R (P.reduceFst (Q₁ i₁)) Dt i (zf i) (y1f i) (y2f i) (τf i)
      hsecF hsecI₁ zgen y1gen y2gen hz hy1 hy2 hord hv1 hv2 hb hd (hτf i)
    refine ⟨zgen, hord', fun kc r => ?_⟩
    rw [htcM]
    have hre := RootsCore.reduced_entry D' i zgen y1gen y2gen (red (Dt.u₀ i))
      (fun kk => (R.residue₁ ⟨hsecF kk, hsecI₁ kk⟩ : ↥(modularFunctionFieldC k N))) (hvars' i) hb' hd'
      (fun kk => hsval' kk i) (fun j => hdG' i j) hroot' (P.reduceFst (Q₁ i₁)) (hrat _) hord' hval' (some kc) (Fin.castSucc r)
    have hu : D'.u₀ i = red (Dt.u₀ i) := rfl
    rw [hre, hu, pow_succ, ← mul_assoc]
    have hx : (⟨hsecF (some kc), hsecI₁ (some kc)⟩ : R.R₁.integers) = ⟨h kc.succ, hh₁ _⟩ :=
      Subtype.ext (by simp [hsecFdef])
    rw [hx]

  have E2 : ∀ i₂ : Fin d₂, ∃ ζ : ↥(modularFunctionFieldC k N),
      (P.reduceSnd (Q₂ i₂)).ord (ζ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inr i₂))))) = 1 ∧
      ∀ (kc : Fin ((d₁ + d₂) * m')) (r : Fin m'),
        D'.tcMatrix D'.centre (finProdFinEquiv (finSumFinEquiv (Sum.inr i₂), r)) kc
          = Place.taylorCoeff (P.reduceSnd (Q₂ i₂)) (ζ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inr i₂))))) (Fin.castSucc r)
              ((R.residue₂ ⟨h kc.succ, hh₂ _⟩ : ↥(modularFunctionFieldC k N)) *
                (ζ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inr i₂))))) ^ (m' + 1)) := by
    intro i₂
    set i : Fin (d₁ + d₂) := finSumFinEquiv (Sum.inr i₂) with hidef
    obtain ⟨htrip, hb, -, hcu, hc2, hcτ, hd, -⟩ := hcl i
    simp only [hidef, Equiv.symm_apply_apply, Sum.elim_inr] at htrip hcu hc2 hcτ
    have haff : IsAffineGeomPlace k N (P.reduceSnd (Q₂ i₂)) := hT₂aff _ ((hT₂ _).mpr ⟨i₂, rfl⟩)
    obtain ⟨zgen, y1gen, y2gen, hz, hy1, hy2, hord, hv1, hv2⟩ :=
      JacUnitAux.snd_inputs hqN R (hQ₂ i₂) haff (zf i) (y1f i) (y2f i) (Dt.u₀ i) (Dt.w₀ i 0 0) (Dt.w₀ i 1 0)
        htrip (hc2 0) (hc2 1)
    obtain ⟨hord', hval', hb', hd'⟩ := JacUnitAux.pack_snd R (P.reduceSnd (Q₂ i₂)) Dt i (zf i) (y1f i) (y2f i) (τf i)
      hsecF hsecI₂ zgen y1gen y2gen hz hy1 hy2 hord hv1 hv2 hb hd (hτf i)
    refine ⟨zgen, hord', fun kc r => ?_⟩
    rw [htcM]
    have hre := RootsCore.reduced_entry D' i zgen y1gen y2gen (red (Dt.u₀ i))
      (fun kk => (R.residue₂ ⟨hsecF kk, hsecI₂ kk⟩ : ↥(modularFunctionFieldC k N))) (hvars' i) hb' hd'
      (fun kk => hsval' kk i) (fun j => hdG' i j) hroot' (P.reduceSnd (Q₂ i₂)) (hrat _) hord' hval' (some kc) (Fin.castSucc r)
    have hu : D'.u₀ i = red (Dt.u₀ i) := rfl
    rw [hre, hu, pow_succ, ← mul_assoc]
    have hx : (⟨hsecF (some kc), hsecI₂ (some kc)⟩ : R.R₂.integers) = ⟨h kc.succ, hh₂ _⟩ :=
      Subtype.ext (by simp [hsecFdef])
    rw [hx]
  choose ζ₁ hζ₁ using E1
  choose ζ₂ hζ₂ using E2

  set t₁ : Fin d₁ → ↥(modularFunctionFieldC k N) := fun i₁ => ζ₁ i₁ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inl i₁)))) with ht₁def
  set t₂ : Fin d₂ → ↥(modularFunctionFieldC k N) := fun i₂ => ζ₂ i₂ - algebraMap k ↥(modularFunctionFieldC k N) (red (Dt.u₀ (finSumFinEquiv (Sum.inr i₂)))) with ht₂def
  set b : Fin ((d₁ + d₂) * m') → ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N) :=
    fun kc => ((R.residue₁ ⟨h kc.succ, hh₁ _⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h kc.succ, hh₂ _⟩ : ↥(modularFunctionFieldC k N))) with hbdef

  rw [← hcen']
  by_contra hnu
  have hdet0 : (D'.tcMatrix D'.centre).det = 0 := by
    rwa [isUnit_iff_ne_zero, not_not] at hnu
  obtain ⟨cv, hcv0, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0

  have hmem_of : ∀ (v : Place k ↥(modularFunctionFieldC k N)) (t : ↥(modularFunctionFieldC k N)) (ht : v.ord t = 1) (x : ↥(modularFunctionFieldC k N)),
      (x = 0 ∨ -((m' + 1 : ℕ) : ℤ) ≤ v.ord x) → x * t ^ (m' + 1) ∈ v.toValuationSubring := by
    intro v t ht x hx
    have ht0 : t ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at ht; exact zero_ne_one ht
    rcases hx with rfl | hx
    · rw [zero_mul]; exact zero_mem _
    · by_cases hx0 : x = 0
      · rw [hx0, zero_mul]; exact zero_mem _
      · refine v.mem_of_ord_nonneg (mul_ne_zero hx0 (pow_ne_zero _ ht0)) ?_
        rw [Place.ord_mul v hx0 (pow_ne_zero _ ht0), JacUnitAux.ord_pow_eq v ht0, ht]
        push_cast at hx ⊢
        linarith
  have key : ∀ (v : Place k ↥(modularFunctionFieldC k N)) (t : ↥(modularFunctionFieldC k N)) (ht : v.ord t = 1) (bb : Fin ((d₁ + d₂) * m') → ↥(modularFunctionFieldC k N))
      (hbb : ∀ j, bb j = 0 ∨ -((m' + 1 : ℕ) : ℤ) ≤ v.ord (bb j)),
      (∀ r, r < m' → ∑ j, cv j * Place.taylorCoeff v t r (bb j * t ^ (m' + 1)) = 0) ↔
      ((∑ j, cv j • bb j) = 0 ∨ (-1 : ℤ) ≤ v.ord (∑ j, cv j • bb j)) := by
    intro v t ht bb hbb
    have ht0 : t ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at ht; exact zero_ne_one ht
    have hreg : ∀ j, bb j * t ^ (m' + 1) ∈ v.toValuationSubring := fun j => hmem_of v t ht (bb j) (hbb j)
    have hsm : (∑ j, cv j • bb j * t ^ (m' + 1)) = ∑ j, cv j • (bb j * t ^ (m' + 1)) :=
      Finset.sum_congr rfl fun j _ => smul_mul_assoc (cv j) (bb j) (t ^ (m' + 1))
    have hlin : ∀ r, ∑ j, cv j * Place.taylorCoeff v t r (bb j * t ^ (m' + 1))
        = Place.taylorCoeff v t r ((∑ j, cv j • bb j) * t ^ (m' + 1)) := by
      intro r
      rw [Finset.sum_mul, hsm, RootsCore.taylorCoeff_sum_smul v (hrat v) ht _ cv _ (fun j _ => hreg j) r]
    simp only [hlin]
    have hFmem : (∑ j, cv j • bb j) * t ^ (m' + 1) ∈ v.toValuationSubring := by
      rw [Finset.sum_mul, hsm]
      exact sum_mem fun j _ => RootsCore.smul_mem' v _ (hreg j)
    constructor
    · intro h
      by_cases hF0 : (∑ j, cv j • bb j) = 0
      · exact Or.inl hF0
      · right
        have hne : (∑ j, cv j • bb j) * t ^ (m' + 1) ≠ 0 := mul_ne_zero hF0 (pow_ne_zero _ ht0)
        have hle := (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord v (hrat v) ht hFmem hne m').mp h
        rw [Place.ord_mul v hF0 (pow_ne_zero _ ht0), JacUnitAux.ord_pow_eq v ht0, ht] at hle
        push_cast at hle
        linarith
    · intro h r hr
      rcases h with h0 | hle
      · rw [h0, zero_mul, show (0 : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) 0 from (map_zero _).symm,
          Place.taylorCoeff_algebraMap]
        simp
      · by_cases hF0 : (∑ j, cv j • bb j) = 0
        · rw [hF0, zero_mul, show (0 : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) 0 from (map_zero _).symm,
            Place.taylorCoeff_algebraMap]
          simp
        · have hne : (∑ j, cv j • bb j) * t ^ (m' + 1) ≠ 0 := mul_ne_zero hF0 (pow_ne_zero _ ht0)
          refine (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord v (hrat v) ht hFmem hne m').mpr ?_ r hr
          rw [Place.ord_mul v hF0 (pow_ne_zero _ ht0), JacUnitAux.ord_pow_eq v ht0, ht]
          push_cast
          linarith

  have hbb₁ : ∀ i₁ j, (b j).1 = 0 ∨ -((m' + 1 : ℕ) : ℤ) ≤ (P.reduceFst (Q₁ i₁)).ord ((b j).1) :=
    fun i₁ j => Or.inr ((hhland j.succ).2.1 _ ((hT₁ _).mpr ⟨i₁, rfl⟩))
  have hbb₂ : ∀ i₂ j, (b j).2 = 0 ∨ -((m' + 1 : ℕ) : ℤ) ≤ (P.reduceSnd (Q₂ i₂)).ord ((b j).2) :=
    fun i₂ j => Or.inr ((hhland j.succ).2.2.2.1 _ ((hT₂ _).mpr ⟨i₂, rfl⟩))

  have hF₁ : ∀ i₁, (∑ j, cv j • (b j).1) = 0 ∨ (-1 : ℤ) ≤ (P.reduceFst (Q₁ i₁)).ord (∑ j, cv j • (b j).1) := by
    intro i₁
    refine (key _ (t₁ i₁) (hζ₁ i₁).1 (fun j => (b j).1) (hbb₁ i₁)).mp fun r hr => ?_
    have h0 := congrFun hker (finProdFinEquiv (finSumFinEquiv (Sum.inl i₁), ⟨r, hr⟩))
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun kc _ => ?_
    rw [(hζ₁ i₁).2 kc ⟨r, hr⟩, mul_comm]
    rfl
  have hF₂ : ∀ i₂, (∑ j, cv j • (b j).2) = 0 ∨ (-1 : ℤ) ≤ (P.reduceSnd (Q₂ i₂)).ord (∑ j, cv j • (b j).2) := by
    intro i₂
    refine (key _ (t₂ i₂) (hζ₂ i₂).1 (fun j => (b j).2) (hbb₂ i₂)).mp fun r hr => ?_
    have h0 := congrFun hker (finProdFinEquiv (finSumFinEquiv (Sum.inr i₂), ⟨r, hr⟩))
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun kc _ => ?_
    rw [(hζ₂ i₂).2 kc ⟨r, hr⟩, mul_comm]
    rfl

  set tf : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N) := fun v =>
    if h1 : ∃ i₁, P.reduceFst (Q₁ i₁) = v then t₁ (Classical.choose h1)
    else if h2 : ∃ i₂, P.reduceSnd (Q₂ i₂) = v then t₂ (Classical.choose h2) else 1 with htfdef
  have htf₁ : ∀ v ∈ T₁, ∃ i₁, P.reduceFst (Q₁ i₁) = v ∧ tf v = t₁ i₁ := by
    intro v hv
    have h1 : ∃ i₁, P.reduceFst (Q₁ i₁) = v := (hT₁ v).mp hv
    refine ⟨Classical.choose h1, Classical.choose_spec h1, ?_⟩
    simp only [htfdef, dif_pos h1]
  have htf₂ : ∀ v ∈ T₂, v ∉ T₁ → ∃ i₂, P.reduceSnd (Q₂ i₂) = v ∧ tf v = t₂ i₂ := by
    intro v hv hv1
    have h1 : ¬ ∃ i₁, P.reduceFst (Q₁ i₁) = v := fun h => hv1 ((hT₁ v).mpr h)
    have h2 : ∃ i₂, P.reduceSnd (Q₂ i₂) = v := (hT₂ v).mp hv
    refine ⟨Classical.choose h2, Classical.choose_spec h2, ?_⟩
    simp only [htfdef, dif_neg h1, dif_pos h2]
  have ht₁f : ∀ v ∈ T₁, v.ord (tf v) = 1 := by
    intro v hv
    obtain ⟨i₁, hi, htv⟩ := htf₁ v hv
    rw [htv, ← hi]; exact (hζ₁ i₁).1
  have ht₂f : ∀ v ∈ T₂, v.ord (tf v) = 1 := by
    intro v hv
    by_cases hv1 : v ∈ T₁
    · exact ht₁f v hv1
    · obtain ⟨i₂, hi, htv⟩ := htf₂ v hv hv1
      rw [htv, ← hi]; exact (hζ₂ i₂).1

  have hc₁ : ∀ v ∈ T₁, ∀ r : ℕ, r + 1 < m' + 1 →
      ∑ j, cv j * Place.taylorCoeff v (tf v) r ((b j).1 * tf v ^ (m' + 1)) = 0 := by
    intro v hv r hr
    obtain ⟨i₁, hi, htv⟩ := htf₁ v hv
    subst hi
    rw [htv]
    exact (key _ (t₁ i₁) (hζ₁ i₁).1 (fun j => (b j).1) (hbb₁ i₁)).mpr (hF₁ i₁) r (by omega)
  have hc₂ : ∀ v ∈ T₂, ∀ r : ℕ, r + 1 < m' + 1 →
      ∑ j, cv j * Place.taylorCoeff v (tf v) r ((b j).2 * tf v ^ (m' + 1)) = 0 := by
    intro v hv r hr
    obtain ⟨i₂, hi⟩ := (hT₂ v).mp hv
    subst hi
    exact (key _ (tf _) (ht₂f _ hv) (fun j => (b j).2) (hbb₂ i₂)).mpr (hF₂ i₂) r (by omega)

  have hind : ∀ (c : Fin ((d₁ + d₂) * m') → k) (a : k),
      ∑ j, c j • (b j).1 = algebraMap k ↥(modularFunctionFieldC k N) a → ∑ j, c j • (b j).2 = algebraMap k ↥(modularFunctionFieldC k N) a → c = 0 := by
    intro c a h1 h2
    have hres0₁ : (R.residue₁ ⟨h 0, hh₁ 0⟩ : ↥(modularFunctionFieldC k N)) = 1 := by
      have : (⟨h 0, hh₁ 0⟩ : R.R₁.integers) = 1 := Subtype.ext hh0
      rw [this, map_one]
    have hres0₂ : (R.residue₂ ⟨h 0, hh₂ 0⟩ : ↥(modularFunctionFieldC k N)) = 1 := by
      have : (⟨h 0, hh₂ 0⟩ : R.R₂.integers) = 1 := Subtype.ext hh0
      rw [this, map_one]
    have hrel := Fintype.linearIndependent_iff.mp hhind (Fin.cons (-a) c) (by
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [hres0₁, hres0₂]
      have e1 : (∑ x : Fin ((d₁ + d₂) * m'), c x • ((R.residue₁ ⟨h x.succ, hh₁ x.succ⟩ : ↥(modularFunctionFieldC k N)),
          (R.residue₂ ⟨h x.succ, hh₂ x.succ⟩ : ↥(modularFunctionFieldC k N)))) = (algebraMap k ↥(modularFunctionFieldC k N) a, algebraMap k ↥(modularFunctionFieldC k N) a) := by
        rw [hbdef] at h1 h2
        simp only [] at h1 h2
        rw [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
        simp only [Prod.smul_fst, Prod.smul_snd]
        exact ⟨h1, h2⟩
      rw [e1]
      ext
      · simp [Algebra.algebraMap_eq_smul_one]
      · simp [Algebra.algebraMap_eq_smul_one])
    funext j
    have := hrel j.succ
    rwa [Fin.cons_succ] at this
  have hPJ := ModularCurve.eq_zero_of_forall_sum_mul_taylorCoeff_mul_pow_eq_zero_of_generalPosition
    (arithFrobC q k N) W T₁ T₂ hgp₁ hgp₂ tf ht₁f ht₂f (fun v _ => hrat v) (fun v _ => hrat v) (m' + 1) b
    (fun j v hv => (hhland j.succ).1 v hv) (fun j v hv => (hhland j.succ).2.1 v hv)
    (fun j v hv => (hhland j.succ).2.2.1 v hv) (fun j v hv => (hhland j.succ).2.2.2.1 v hv)
    (fun j w hw => (hhland j.succ).2.2.2.2 w hw) hind cv hc₁ hc₂
  exact hcv0 hPJ

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_isUnit_det_jacobian_centre_of_mDivRepresents
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_isUnit_det_jacobian_centre_of_mDivRepresents (solution)
