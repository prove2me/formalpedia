-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e1007499-e9e4-572e-9ac5-cbe9291ffb3e

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_MDivRepresents
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero
import Theorems.Thm_ModularCurve_derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one
import Theorems.Thm_ModularCurve_derivative_swapBivar_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jNGeomGen_sub_eq_one
import Theorems.Thm_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd
import Theorems.Thm_MvPolynomial_exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv
import Theorems.Thm_Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jNFun_sub_jNQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictSnd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace EMPAlg

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def emp (x y : R) (Φ : Polynomial (Polynomial ℤ)) : R :=
  Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y

theorem emp_hom (φ : R →+* S) (x y : R) (Φ : Polynomial (Polynomial ℤ)) :
    φ (emp x y Φ) = emp (φ x) (φ y) Φ := by
  unfold emp
  rw [Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem emp_add (x y : R) (Φ Ψ : Polynomial (Polynomial ℤ)) : emp x y (Φ + Ψ) = emp x y Φ + emp x y Ψ := by
  simp [emp]

theorem emp_monomial (x y : R) (n : ℕ) (r : Polynomial ℤ) :
    emp x y (Polynomial.monomial n r) = r.eval₂ (Int.castRingHom R) x * y ^ n := by
  simp [emp, Polynomial.eval₂_monomial]

theorem emp_eq_evalEval (x y : R) (Φ : Polynomial (Polynomial ℤ)) :
    emp x y Φ = (Φ.map (Polynomial.mapRingHom (Int.castRingHom R))).evalEval x y := by
  unfold emp Polynomial.evalEval
  rw [Polynomial.eval_map, ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂]
  congr 1
  · refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · simp
    · simp
  · simp

variable {σ : Type*}

theorem pderiv_eval₂_X (c a : σ) (hca : c ≠ a) (r : Polynomial ℤ) :
    pderiv c (r.eval₂ (Int.castRingHom (MvPolynomial σ R)) (X a)) = 0 := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq, add_zero]
  | monomial n z =>
    have hz : (Int.castRingHom (MvPolynomial σ R)) z = C (z : R) := by simp
    rw [Polynomial.eval₂_monomial, hz]
    simp [Pi.single_apply, Ne.symm hca]

theorem pderiv_emp (a b : σ) (hba : b ≠ a) (Φ : Polynomial (Polynomial ℤ)) :
    pderiv b (emp (X a) (X b) Φ : MvPolynomial σ R) = emp (X a) (X b) (Polynomial.derivative Φ) := by
  classical
  induction Φ using Polynomial.induction_on' with
  | add p q hp hq => rw [emp_add, map_add, hp, hq, Polynomial.derivative_add, emp_add]
  | monomial n r =>
    rw [emp_monomial, Polynomial.derivative_monomial, emp_monomial, Derivation.leibniz,
      pderiv_eval₂_X b a hba r, smul_zero, add_zero, Derivation.leibniz_pow, pderiv_X, Pi.single_eq_same,
      Polynomial.eval₂_mul, Polynomial.eval₂_natCast]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring

theorem aeval_emp {A' : Type*} [CommRing A'] [Algebra R A'] (g : σ → A') (a b : σ) (Φ : Polynomial (Polynomial ℤ)) :
    aeval g (emp (X a) (X b) Φ : MvPolynomial σ R) = emp (g a) (g b) Φ := by
  have h := emp_hom (aeval g : MvPolynomial σ R →ₐ[R] A').toRingHom (X a) (X b) Φ
  simpa using h

theorem eval_emp (g : σ → R) (a b : σ) (Φ : Polynomial (Polynomial ℤ)) :
    MvPolynomial.eval g (emp (X a) (X b) Φ) = emp (g a) (g b) Φ := by
  have h := emp_hom (MvPolynomial.eval g) (X a) (X b) Φ
  simpa using h

theorem eval_pderiv_emp (g : σ → R) (a b : σ) (hba : b ≠ a) (Φ : Polynomial (Polynomial ℤ)) :
    MvPolynomial.eval g (pderiv b (emp (X a) (X b) Φ))
      = (Polynomial.derivative (Φ.map (Polynomial.mapRingHom (Int.castRingHom R)))).evalEval (g a) (g b) := by
  rw [pderiv_emp a b hba, eval_emp, emp_eq_evalEval, Polynomial.derivative_map]

theorem not_mem_vars_emp [DecidableEq σ] (a b c : σ) (hca : c ≠ a) (hcb : c ≠ b) (Φ : Polynomial (Polynomial ℤ)) :
    c ∉ (emp (X a) (X b) Φ : MvPolynomial σ R).vars := by
  have hmem : (emp (X a) (X b) Φ : MvPolynomial σ R) ∈ supported R ({a, b} : Set σ) := by
    rw [supported_eq_adjoin_X]
    set T := Algebra.adjoin R (X '' ({a, b} : Set σ) : Set (MvPolynomial σ R)) with hT
    have hXa : (X a : MvPolynomial σ R) ∈ T := Algebra.subset_adjoin ⟨a, by simp, rfl⟩
    have hXb : (X b : MvPolynomial σ R) ∈ T := Algebra.subset_adjoin ⟨b, by simp, rfl⟩
    have hin : ∀ r : Polynomial ℤ, r.eval₂ (Int.castRingHom (MvPolynomial σ R)) (X a) ∈ T := by
      intro r
      induction r using Polynomial.induction_on' with
      | add p q hp hq => rw [Polynomial.eval₂_add]; exact add_mem hp hq
      | monomial n z => rw [Polynomial.eval₂_monomial, eq_intCast]; exact mul_mem (intCast_mem T z) (pow_mem hXa n)
    unfold emp
    induction Φ using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.eval₂_add]; exact add_mem hp hq
    | monomial n r => rw [Polynomial.eval₂_monomial, Polynomial.coe_eval₂RingHom]; exact mul_mem (hin r) (pow_mem hXb n)
  intro hc
  have h := (mem_supported.mp hmem) (Finset.mem_coe.mpr hc)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact hca h
  · exact hcb h

omit [CommRing R] [CommRing S] in
theorem ringHom_eval' {R' S' : Type*} [CommRing R'] [CommRing S'] (g : R' →+* S') (p : Polynomial R') (x : R') :
    g (p.eval x) = (p.map g).eval (g x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem hom_evalEval (φ : R →+* S) (p : Polynomial (Polynomial R)) (x y : R) :
    φ (p.evalEval x y) = (p.map (Polynomial.mapRingHom φ)).evalEval (φ x) (φ y) := by
  unfold Polynomial.evalEval
  rw [ringHom_eval' φ, ← Polynomial.coe_mapRingHom, ringHom_eval' (Polynomial.mapRingHom φ), Polynomial.coe_mapRingHom,
    Polynomial.map_C]

theorem hom_evalEval_derivative_intMap (φ : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    φ ((Polynomial.derivative (Φ.map (Polynomial.mapRingHom (Int.castRingHom R)))).evalEval x y)
      = (Polynomial.derivative (Φ.map (Polynomial.mapRingHom (Int.castRingHom S)))).evalEval (φ x) (φ y) := by
  have hc : φ.comp (Int.castRingHom R) = Int.castRingHom S := RingHom.ext_int _ _
  rw [hom_evalEval, Polynomial.derivative_map, Polynomial.derivative_map, Polynomial.map_map, Polynomial.mapRingHom_comp, hc]

end EMPAlg

namespace PlaceAlg

open AlgebraicCurve MvPolynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ Q.ord f) : f ∈ Q.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
  obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hf hπ
  rw [hu, show Q.ord f = (((Q.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : Q.toValuationSubring).2 (pow_mem (π : Q.toValuationSubring).2 _)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ Q.toValuationSubring) : 0 ≤ Q.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [Place.ord_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨f, hf⟩ : Q.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : Q.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, Q.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ord_algebraMap (a : K) : Q.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, Place.ord_zero]
  set u : Q.toValuationSubringˣ :=
    ⟨⟨algebraMap K F a, Q.algebraMap_mem' a⟩, ⟨algebraMap K F a⁻¹, Q.algebraMap_mem' a⁻¹⟩,
      Subtype.ext (by simp [ha]), Subtype.ext (by simp [ha])⟩ with hu
  have := Q.ord_coe_unit u
  simpa [hu] using this

theorem eq_zero_of_ord_algebraMap_pos {a : K} (h : 0 < Q.ord (algebraMap K F a)) : a = 0 := by
  by_contra ha
  rw [ord_algebraMap] at h
  exact lt_irrefl _ h

theorem mk_mem_maximalIdeal_of_ord_pos {f : F} (hf : f ∈ Q.toValuationSubring) (h : 0 < Q.ord f) :
    (⟨f, hf⟩ : Q.toValuationSubring) ∈ IsLocalRing.maximalIdeal Q.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 := Q.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at h0
  change Q.ord f = 0 at h0
  omega

theorem eq_zero_of_algebraMap_mem_maximalIdeal {a : K}
    (h : algebraMap K Q.toValuationSubring a ∈ IsLocalRing.maximalIdeal Q.toValuationSubring) : a = 0 := by
  by_contra ha
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp h) ((IsUnit.mk0 a ha).map (algebraMap K Q.toValuationSubring))

theorem mem_of_ord_sub_algebraMap_pos {x : F} {a : K} (h : 0 < Q.ord (x - algebraMap K F a)) :
    x ∈ Q.toValuationSubring := by
  have hmem : x - algebraMap K F a ∈ Q.toValuationSubring := by
    by_cases h0 : x - algebraMap K F a = 0
    · rw [h0]; exact zero_mem _
    · exact mem_of_ord_nonneg Q h0 h.le
  have := add_mem hmem (Q.algebraMap_mem' a)
  rwa [sub_add_cancel] at this

theorem eval₂_sub_eval₂_mem {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B) {σ : Type*}
    (v v' : σ → B) (hv : ∀ o, v o - v' o ∈ I) (H : MvPolynomial σ A) :
    MvPolynomial.eval₂ f v H - MvPolynomial.eval₂ f v' H ∈ I := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, add_sub_add_comm]
    exact I.add_mem hp hq
  | mul_X p o hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      show MvPolynomial.eval₂ f v p * v o - MvPolynomial.eval₂ f v' p * v' o
        = (MvPolynomial.eval₂ f v p - MvPolynomial.eval₂ f v' p) * v o + MvPolynomial.eval₂ f v' p * (v o - v' o) by ring]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (hv o))

theorem map_eval_eq_zero_of_eval₂_eq_zero {A : Type*} [CommRing A] (ι : A →+* K) {σ : Type*}
    (c : σ → F) (c₀ : σ → A) (hc : ∀ o, 0 < Q.ord (c o - algebraMap K F (ι (c₀ o))))
    (H : MvPolynomial σ A) (hH : MvPolynomial.eval₂ ((algebraMap K F).comp ι) c H = 0) :
    ι (MvPolynomial.eval c₀ H) = 0 := by
  set O := Q.toValuationSubring with hO
  have hcmem : ∀ o, c o ∈ O := fun o => mem_of_ord_sub_algebraMap_pos Q (hc o)
  set c' : σ → O := fun o => ⟨c o, hcmem o⟩ with hc'
  set c₀' : σ → O := fun o => algebraMap K O (ι (c₀ o)) with hc₀'
  set f' : A →+* O := (algebraMap K O).comp ι with hf'

  have h1 : MvPolynomial.eval₂ f' c' H = 0 := by
    apply Subtype.val_injective
    have hnat := MvPolynomial.eval₂_comp_left O.subtype f' c' H
    rw [show (O.subtype : O → F) ∘ c' = c from funext fun o => rfl,
      show O.subtype.comp f' = (algebraMap K F).comp ι from by
        rw [hf', ← RingHom.comp_assoc]; congr 1] at hnat
    change (O.subtype) (MvPolynomial.eval₂ f' c' H) = (O.subtype) 0
    rw [hnat, hH, map_zero]

  have h2 : ∀ o, c₀' o - c' o ∈ IsLocalRing.maximalIdeal O := by
    intro o
    have hmem : algebraMap K F (ι (c₀ o)) - c o ∈ O := sub_mem (Q.algebraMap_mem' _) (hcmem o)
    have hpos : 0 < Q.ord (algebraMap K F (ι (c₀ o)) - c o) := by
      rw [← neg_sub, show Q.ord (-(c o - algebraMap K F (ι (c₀ o)))) = Q.ord (c o - algebraMap K F (ι (c₀ o))) from by
        rw [neg_eq_neg_one_mul, show (-1 : F) = algebraMap K F (-1) from by simp]
        rcases eq_or_ne (c o - algebraMap K F (ι (c₀ o))) 0 with h0 | h0
        · rw [h0, mul_zero]
        · rw [Place.ord_mul Q (by simp) h0, ord_algebraMap, zero_add]]
      exact hc o
    have := mk_mem_maximalIdeal_of_ord_pos Q hmem hpos
    convert this using 1
    all_goals first | rfl | exact Subtype.ext rfl | (apply Subtype.ext; simp)
  have h3 := eval₂_sub_eval₂_mem f' (IsLocalRing.maximalIdeal O) c₀' c' h2 H
  rw [h1, sub_zero] at h3

  have h4 : MvPolynomial.eval₂ f' c₀' H = algebraMap K O (ι (MvPolynomial.eval c₀ H)) := by
    have hnat := MvPolynomial.eval₂_comp_left f' (RingHom.id A) c₀ H
    rw [RingHom.comp_id] at hnat
    rw [show c₀' = f' ∘ c₀ from funext fun o => rfl, ← hnat]
    rfl
  rw [h4] at h3
  exact eq_zero_of_algebraMap_mem_maximalIdeal Q h3

theorem ord_pow (x : F) (n : ℕ) : Q.ord (x ^ n) = n * Q.ord x := by
  rw [← zpow_natCast, Place.ord_zpow]

theorem mul_pow_mul_mem {f x y : F} {a b : ℤ} {m : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxo : Q.ord x = b) (hyo : Q.ord y = a) (hf : f = 0 ∨ -(a + (m : ℤ) * b) ≤ Q.ord f) :
    f * x ^ m * y ∈ Q.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul, zero_mul]; exact zero_mem _
  rcases hf with h | h
  · exact absurd h hf0
  refine mem_of_ord_nonneg Q (mul_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hx)) hy) ?_
  rw [Place.ord_mul Q (mul_ne_zero hf0 (pow_ne_zero _ hx)) hy, Place.ord_mul Q hf0 (pow_ne_zero _ hx), ord_pow, hxo, hyo]
  linarith

theorem mem_and_inv_mem_of_ord_eq_zero {x : F} (hx : x ≠ 0) (h : Q.ord x = 0) :
    x ∈ Q.toValuationSubring ∧ x⁻¹ ∈ Q.toValuationSubring :=
  ⟨mem_of_ord_nonneg Q hx h.ge, mem_of_ord_nonneg Q (inv_ne_zero hx) (by rw [Place.ord_inv, h, neg_zero])⟩

end PlaceAlg

namespace SeamSnd

open MvPolynomial

theorem hasValue_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    {y : F} {b : K} (h : 0 < Q.ord (y - algebraMap K F b)) : Q.HasValue y b := by
  have hmem : y - algebraMap K F b ∈ Q.toValuationSubring := by
    by_cases h0 : y - algebraMap K F b = 0
    · rw [h0]; exact zero_mem _
    · exact PlaceAlg.mem_of_ord_nonneg Q h0 h.le
  have hy : y ∈ Q.toValuationSubring := by
    have := add_mem hmem (Q.algebraMap_mem' b)
    rwa [sub_add_cancel] at this
  refine ⟨hy, ?_⟩
  have hmax := PlaceAlg.mk_mem_maximalIdeal_of_ord_pos Q hmem h
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

theorem evalBar_emp {A : ValuationSubring (AlgebraicClosure ℚ)} (N q : ℕ) [NeZero N] [Fact q.Prime]
    (c : Option (Fin 2) → ↥(modularFunctionFieldBar (N * q))) (a b : Option (Fin 2)) (Φ : Polynomial (Polynomial ℤ)) :
    PlaceSpecialization.evalBar N q c (EMPAlg.emp (X a) (X b) Φ : MvPolynomial (Option (Fin 2)) A)
      = evalModularPair (c a) (c b) Φ := by
  unfold PlaceSpecialization.evalBar
  rw [← MvPolynomial.coe_eval₂Hom, EMPAlg.emp_hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
  rfl

theorem evalModularPair_swapBivar {R' : Type*} [CommRing R'] (x y : R') (Φ : Polynomial (Polynomial ℤ)) :
    evalModularPair x y (swapBivar Φ) = evalModularPair y x Φ := by
  have h : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R') x) y).comp swapBivar
      = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R') y) x := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp [swapBivar_C_X]
    · simp [swapBivar_X]
  unfold evalModularPair
  exact RingHom.congr_fun h Φ

theorem coeff_zero_jet {A : Type*} [CommRing A] {m : ℕ} (w : Fin (m + 1) → A) :
    (∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w r')).coeff 0 = w 0 := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (0 : Fin (m + 1))]
  · simp [Polynomial.coeff_monomial]
  · intro r' _ hr'
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun h => hr' (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeff_zero_aeval {A : Type*} [CommRing A] {σ : Type*} (c : σ → Polynomial A) (H : MvPolynomial σ A) :
    (aeval c H).coeff 0 = MvPolynomial.eval (fun o => (c o).coeff 0) H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p o hp => simp [hp, Polynomial.mul_coeff_zero]

theorem core
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q) (hQ' : P.IsStrictSnd Q')
    (hQQ' : P.reduceSnd Q' = P.reduceSnd Q)
    (haff : IsAffineGeomPlace k N (P.reduceSnd Q))
    (hsm2 : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (m' : ℕ) {n : ℕ} (f : Fin n → ↥(modularFunctionFieldBar (N * q))) (hfI : ∀ l, f l ∈ R.R₂.integers)
    (hfd : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.IsStrictSnd V → P.reduceSnd V = P.reduceSnd Q →
      -((Finsupp.single Q' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V
          + (m' : ℤ) * ((Finsupp.single Q (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V))
        ≤ V.ord (f l))
    (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u τ : A) (w0 : Fin 2 → A) (G : Fin 2 → MvPolynomial (Option (Fin 2)) A)
    (htr : PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd Q) (red u) z y₁ y₂)
    (hz : 0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))))
    (hy : ∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w0 j : (AlgebraicClosure ℚ))))
    (hτ : 0 < Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))))
    (hτu : red τ = red u)
    (hzuI : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ)) ∈ R.R₂.integers)
    (hzτI : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ)) ∈ R.R₂.integers)
    (hdu : Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))) = 1)
    (hdu0 : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd V → P.reduceSnd V = P.reduceSnd Q → V ≠ Q →
      V.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))) = 0)
    (hdτ : Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))) = 1)
    (hdτ0 : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd V → P.reduceSnd V = P.reduceSnd Q → V ≠ Q' →
      V.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))) = 0)
    (hvars : (some 1 : Option (Fin 2)) ∉ (G 0).vars)
    (hrel : ∀ j : Fin 2, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (G j) = 0)
    (hder : ∀ j : Fin 2, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u w0)
        (MvPolynomial.pderiv (some j) (G j))) ≠ 0) :
    ∃ (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u τ : A) (w : Fin 2 → Fin (m' + 1) → A)
      (G : Fin 2 → MvPolynomial (Option (Fin 2)) A) (p s : Fin n → MvPolynomial (Option (Fin 2)) A)
      (σ : Fin n → Fin (m' + 1) → A),
      PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd Q) (red u) z y₁ y₂ ∧
      (∀ j : Fin 2, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (G j) = 0) ∧
      (some 1 : Option (Fin 2)) ∉ (G 0).vars ∧
      0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ∧
      (∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j 0 : AlgebraicClosure ℚ))) ∧
      0 < Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) ∧
      red τ = red u ∧
      (∀ l, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (p l) =
        f l * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ^ m' *
          (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) *
          PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (s l)) ∧
      (∀ l, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0)) (s l)) ≠ 0) ∧
      (∀ j : Fin 2, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0))
        (MvPolynomial.pderiv (some j) (G j))) ≠ 0) ∧
      (∀ (j : Fin 2) (r : Fin (m' + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0) ∧
      (∀ (l : Fin n) (r : Fin (m' + 1)),
        ((∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (σ l r')) *
            MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (s l) - 1).coeff r = 0) := by
  classical

  have hred : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A := fun a => by
    rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]
  have hunit : ∀ a : A, red a ≠ 0 → IsUnit a := fun a ha => by
    by_contra hna
    exact ha ((hred a).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hna))

  have hroot : ∀ j, MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u w0) (G j) = 0 := by
    intro j
    have hc : ∀ o : Option (Fin 2), 0 < Q.ord ((fun o : Option (Fin 2) => Option.elim o z ![y₁, y₂]) o
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (algebraMap A (AlgebraicClosure ℚ) ((fun o : Option (Fin 2) => Option.elim o u w0) o))) := by
      intro o; rcases o with _ | j'
      · exact hz
      · exact hy j'
    have h := PlaceAlg.map_eval_eq_zero_of_eval₂_eq_zero Q (algebraMap A (AlgebraicClosure ℚ)) _ _ hc (G j) (hrel j)
    rwa [show algebraMap A (AlgebraicClosure ℚ) (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u w0) (G j))
        = ((MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u w0) (G j) : A) : (AlgebraicClosure ℚ)) from rfl,
      ZeroMemClass.coe_eq_zero] at h

  have hderU : ∀ j, IsUnit (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u w0)
      (MvPolynomial.pderiv (some j) (G j))) := fun j => hunit _ (hder j)
  obtain ⟨w, hw0, hwjet⟩ :=
    MvPolynomial.exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv m' u w0 G hvars hroot hderU
  have hw0f : (fun j => w j 0) = w0 := funext hw0

  have hzu0 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ)) ≠ 0 := fun h0 => by
    rw [h0, Place.ord_zero] at hdu; exact zero_ne_one hdu
  have hzτ0 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ)) ≠ 0 := fun h0 => by
    rw [h0, Place.ord_zero] at hdτ; exact zero_ne_one hdτ
  have hsec : ∀ l, ∃ p s : MvPolynomial (Option (Fin 2)) A,
      PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) p =
        f l * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))) ^ m' *
          (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))) *
          PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) s ∧
      red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0)) s) ≠ 0 := by
    intro l
    have hmem : f l * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))) ^ m' *
        (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))) ∈ R.smoothLocalRingSnd (P.reduceSnd Q) := by
      rw [ProlongationTuple.mem_smoothLocalRingSnd_iff]
      refine ⟨mul_mem (mul_mem (hfI l) (pow_mem hzuI m')) hzτI, fun V hV hVr => ?_⟩
      have hxu : V.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ)))
          = (Finsupp.single Q (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V := by
        by_cases hVQ : V = Q
        · rw [hVQ, Finsupp.single_eq_same]; exact hdu
        · rw [Finsupp.single_apply, if_neg (fun h => hVQ h.symm)]; exact hdu0 V hV hVr hVQ
      have hxτ : V.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ)))
          = (Finsupp.single Q' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V := by
        by_cases hVQ : V = Q'
        · rw [hVQ, Finsupp.single_eq_same]; exact hdτ
        · rw [Finsupp.single_apply, if_neg (fun h => hVQ h.symm)]; exact hdτ0 V hV hVr hVQ
      exact PlaceAlg.mul_pow_mul_mem V hzu0 hzτ0 hxu hxτ (Or.inr (hfd l V hV hVr))
    exact ProlongationTuple.IsModel.exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd P hqN hW R hR hRL hNV hO
      Q hQ haff hsm2 hgen z y₁ y₂ u (fun j => w j 0) htr hz (fun j => by beta_reduce; rw [hw0]; exact hy j) _ hmem
  choose p s hps hs using hsec

  have hinv : ∀ l, ∃ σl : Fin (m' + 1) → A, ∀ r : Fin (m' + 1),
      ((∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (σl r')) *
          MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (s l) - 1).coeff r = 0 := by
    intro l
    apply Polynomial.exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero
    rw [coeff_zero_aeval]
    have hpt : (fun o : Option (Fin 2) => ((fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
        (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) o).coeff 0)
        = fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0) := by
      funext o; rcases o with _ | j
      · simp
      · simp only [Option.elim]
        exact coeff_zero_jet (w j)
    rw [hpt]
    exact hunit _ (hs l)
  choose σ hσ using hinv

  refine ⟨z, y₁, y₂, u, τ, w, G, p, s, σ, htr, hrel, hvars, hz, fun j => ?_, hτ, hτu, hps, hs, fun j => ?_, hwjet, hσ⟩
  · rw [hw0]; exact hy j
  · rw [hw0f]; exact hder j

end SeamSnd

open MvPolynomial in

theorem solution

    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q) (hQ' : P.IsStrictSnd Q')
    (hQQ' : P.reduceSnd Q' = P.reduceSnd Q)
    (haff : IsAffineGeomPlace k N (P.reduceSnd Q))
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q) ∧
      ((P.reduceSnd Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        (P.reduceSnd Q).ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (m' : ℕ) {n : ℕ} (f : Fin n → ↥(modularFunctionFieldBar (N * q))) (hfI : ∀ l, f l ∈ R.R₂.integers)
    (hfd : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.IsStrictSnd V → P.reduceSnd V = P.reduceSnd Q →
      -((Finsupp.single Q' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V
          + (m' : ℤ) * ((Finsupp.single Q (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V))
        ≤ V.ord (f l)) :
    ∃ (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u τ : A) (w : Fin 2 → Fin (m' + 1) → A)
      (G : Fin 2 → MvPolynomial (Option (Fin 2)) A) (p s : Fin n → MvPolynomial (Option (Fin 2)) A)
      (σ : Fin n → Fin (m' + 1) → A),
      PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd Q) (red u) z y₁ y₂ ∧
      (∀ j : Fin 2, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (G j) = 0) ∧
      (some 1 : Option (Fin 2)) ∉ (G 0).vars ∧
      0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ∧
      (∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j 0 : AlgebraicClosure ℚ))) ∧
      0 < Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) ∧
      red τ = red u ∧
      (∀ l, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (p l) =
        f l * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ^ m' *
          (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) *
          PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (s l)) ∧
      (∀ l, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0)) (s l)) ≠ 0) ∧
      (∀ j : Fin 2, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0))
        (MvPolynomial.pderiv (some j) (G j))) ≠ 0) ∧
      (∀ (j : Fin 2) (r : Fin (m' + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0) ∧
      (∀ (l : Fin n) (r : Fin (m' + 1)),
        ((∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (σ l r')) *
            MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (s l) - 1).coeff r = 0) := by
  classical
  obtain ⟨c, hcen, huniq, hor⟩ := hsm
  have hsm2 : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q := ⟨c, hcen, huniq⟩
  have hc1 : (P.reduceSnd Q).evalAt (jGeomGen k N) = c.1 := hcen.evalAt_jGeomGen
  have hfst : P.reduceFst Q = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd Q) := hQ.1
  have hcenF : IsCentreOf k N (c.1 ^ q, c.2 ^ q) (P.reduceFst Q) := by
    rw [hfst]; exact hcen.frobOnPlacesGeomLevel data hKr
  have haff1 : IsAffineGeomPlace k N (P.reduceFst Q) := hcenF.isAffineGeomPlace
  have haffQ' : IsAffineGeomPlace k N (P.reduceSnd Q') := by rw [hQQ']; exact haff
  have hgen1 : c.1 ^ (q ^ 2) ≠ c.1 := by rw [← hc1]; exact hgen.1
  obtain ⟨dataN⟩ := nonempty_modularPolynomialData N
  obtain ⟨-, hΦN2, hΦq1, -⟩ := ModularCurve.evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero N q dataN data

  obtain ⟨aJQ, haJQ, haJQv⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Q haff
  obtain ⟨aNQ, haNQ, haNQv⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Q haff
  obtain ⟨aJ, haJ, haJv⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst Q haff1
  have hrJQ : red aJQ = c.1 := SeamSnd.eq_of_ord_sub_pos _ haJQv hcen.1
  have hrNQ : red aNQ = c.2 := SeamSnd.eq_of_ord_sub_pos _ haNQv hcen.2
  have hrJ : red aJ = c.1 ^ q := SeamSnd.eq_of_ord_sub_pos _ haJv hcenF.1

  have KJQ : ∀ a : A, ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : (AlgebraicClosure ℚ)) ∈ R.R₂.integers := fun a => by
    obtain ⟨-, -, -, h₄, -⟩ := R.residue_jFun_sub_jQFun_sub hqN a
    exact h₄
  have KNQ : ∀ a : A, PlaceSpecialization.jNQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : (AlgebraicClosure ℚ)) ∈ R.R₂.integers := fun a => by
    obtain ⟨-, -, -, h₄, -⟩ := R.residue_jNFun_sub_jNQFun_sub hqN a
    exact h₄
  rcases hor with hordJ | hordN
  ·
    obtain ⟨aJQ', haJQ', haJQ'v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Q' haffQ'
    rw [hQQ'] at haJQ'v
    have hrJQ' : red aJQ' = c.1 := SeamSnd.eq_of_ord_sub_pos _ haJQ'v hcen.1
    obtain ⟨Q₀, ⟨-, -, hQ₀o⟩, hQ₀u⟩ :=
      ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one P hqN R hR (P.reduceSnd Q) hQ.2 haff
        c.1 hordJ aJQ hrJQ
    have hQQ₀ : Q = Q₀ := by
      by_contra hne
      have h0 := hQ₀u Q hQ rfl hne
      rw [h0] at haJQ; exact lt_irrefl _ haJQ
    obtain ⟨Q₁, ⟨-, -, hQ₁o⟩, hQ₁u⟩ :=
      ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one P hqN R hR (P.reduceSnd Q) hQ.2 haff
        c.1 hordJ aJQ' hrJQ'
    have hQQ₁ : Q' = Q₁ := by
      by_contra hne
      have h0 := hQ₁u Q' hQ' hQQ' hne
      rw [h0] at haJQ'; exact lt_irrefl _ haJQ'
    refine SeamSnd.core P hqN hW R hR hRL hNV hO Q Q' hQ hQ' hQQ' haff hsm2 hgen m' f hfI hfd
      (ProlongationTuple.jQFun N q) (PlaceSpecialization.jNQFun N q) (ProlongationTuple.jFun N q) aJQ aJQ' ![aNQ, aJ]
      ![EMPAlg.emp (X none) (X (some 0)) dataN.Φ, EMPAlg.emp (X none) (X (some 1)) (swapBivar data.Φ)]
      (Or.inl ⟨rfl, rfl, rfl, by rw [hrJQ]; exact hordJ⟩) haJQ ?_ haJQ' (by rw [hrJQ, hrJQ']) (KJQ aJQ) (KJQ aJQ')
      (by rw [hQQ₀]; exact hQ₀o) (fun V hV hVr hVQ => hQ₀u V hV hVr (by rw [← hQQ₀]; exact hVQ))
      (by rw [hQQ₁]; exact hQ₁o) (fun V hV hVr hVQ => hQ₁u V hV hVr (by rw [← hQQ₁]; exact hVQ))
      ?_ ?_ ?_
    · intro j; fin_cases j
      · simpa using haNQ
      · simpa using haJ
    · simp only [Matrix.cons_val_zero]
      exact EMPAlg.not_mem_vars_emp none (some 0) (some 1) (by decide) (by decide) _
    · intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [SeamSnd.evalBar_emp]
        simpa using hΦN2
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [SeamSnd.evalBar_emp, SeamSnd.evalModularPair_swapBivar]
        simpa using hΦq1
    · intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [EMPAlg.eval_pderiv_emp _ none (some 0) (by decide), EMPAlg.hom_evalEval_derivative_intMap red]
        simp only [Option.elim, Matrix.cons_val_zero, hrJQ, hrNQ]
        exact ModularCurve.derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one q k N hqN dataN
          (P.reduceSnd Q) c hcen huniq hordJ
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [EMPAlg.eval_pderiv_emp _ none (some 1) (by decide), EMPAlg.hom_evalEval_derivative_intMap red]
        simp only [Option.elim, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hrJQ, hrJ]
        exact (ModularCurve.derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne q data hKr k c.1 hgen1).2
  ·
    obtain ⟨aNQ', haNQ', haNQ'v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Q' haffQ'
    rw [hQQ'] at haNQ'v
    have hrNQ' : red aNQ' = c.2 := SeamSnd.eq_of_ord_sub_pos _ haNQ'v hcen.2
    obtain ⟨Q₀, ⟨-, -, hQ₀o⟩, hQ₀u⟩ :=
      ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one P hqN R hR (P.reduceSnd Q) hQ.2 haff
        c.2 hordN aNQ hrNQ
    have hQQ₀ : Q = Q₀ := by
      by_contra hne
      have h0 := hQ₀u Q hQ rfl hne
      rw [h0] at haNQ; exact lt_irrefl _ haNQ
    obtain ⟨Q₁, ⟨-, -, hQ₁o⟩, hQ₁u⟩ :=
      ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one P hqN R hR (P.reduceSnd Q) hQ.2 haff
        c.2 hordN aNQ' hrNQ'
    have hQQ₁ : Q' = Q₁ := by
      by_contra hne
      have h0 := hQ₁u Q' hQ' hQQ' hne
      rw [h0] at haNQ'; exact lt_irrefl _ haNQ'
    refine SeamSnd.core P hqN hW R hR hRL hNV hO Q Q' hQ hQ' hQQ' haff hsm2 hgen m' f hfI hfd
      (PlaceSpecialization.jNQFun N q) (ProlongationTuple.jQFun N q) (ProlongationTuple.jFun N q) aNQ aNQ' ![aJQ, aJ]
      ![EMPAlg.emp (X none) (X (some 0)) (swapBivar dataN.Φ), EMPAlg.emp (X (some 0)) (X (some 1)) (swapBivar data.Φ)]
      (Or.inr ⟨rfl, rfl, rfl, by rw [hrNQ]; exact hordN⟩) haNQ ?_ haNQ' (by rw [hrNQ, hrNQ']) (KNQ aNQ) (KNQ aNQ')
      (by rw [hQQ₀]; exact hQ₀o) (fun V hV hVr hVQ => hQ₀u V hV hVr (by rw [← hQQ₀]; exact hVQ))
      (by rw [hQQ₁]; exact hQ₁o) (fun V hV hVr hVQ => hQ₁u V hV hVr (by rw [← hQQ₁]; exact hVQ))
      ?_ ?_ ?_
    · intro j; fin_cases j
      · simpa using haJQ
      · simpa using haJ
    · simp only [Matrix.cons_val_zero]
      exact EMPAlg.not_mem_vars_emp none (some 0) (some 1) (by decide) (by decide) _
    · intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [SeamSnd.evalBar_emp, SeamSnd.evalModularPair_swapBivar]
        simpa using hΦN2
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [SeamSnd.evalBar_emp, SeamSnd.evalModularPair_swapBivar]
        simpa using hΦq1
    · intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [EMPAlg.eval_pderiv_emp _ none (some 0) (by decide), EMPAlg.hom_evalEval_derivative_intMap red]
        simp only [Option.elim, Matrix.cons_val_zero, hrNQ, hrJQ]
        exact ModularCurve.derivative_swapBivar_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jNGeomGen_sub_eq_one q k N hqN
          dataN (P.reduceSnd Q) c hcen huniq hordN
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [EMPAlg.eval_pderiv_emp _ (some 0) (some 1) (by decide), EMPAlg.hom_evalEval_derivative_intMap red]
        simp only [Option.elim, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hrJQ, hrJ]
        exact (ModularCurve.derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne q data hKr k c.1 hgen1).2

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictSnd
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictSnd (solution)
