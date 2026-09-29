-- Prove2me | solution 1 for ModularCurve.kroneckerPairIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a1a823ff-7f8b-5ea8-9101-2b7603e8d2ce

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Theorems.Thm_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_phiIrreducible_all
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Theorems.Thm_ModularCurve_transcendental_jq
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.Group.Int.Units
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kroneckerPairIntegral
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_congr qExpand_qExpand jq jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData modularFunctionField jGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin modularFunctionFieldFull coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand PhiGen.IntCoeffs PhiGen.splits_prime_at_slot coeffEmb_jq coeffEmb_qExpand coeffMap_qExpand coeff_jqModC_neg_one coeff_jqModC_pow_of_lt exists_phiIrreducible PhiGen.aeval_jq_intCoeffs_descent finrank_adjoin_jqN_eq_dedekindPsi functionFieldGeneration functionFieldGeneration_iff_full_eq minpoly_jqN_eq_toAdjoin minpoly_jqN_map_eq_prod_slots phiIrreducible_all pow_char_eq_map_frobenius_qExpand transcendental_jq"
p2m_open "ModularCurve"

private def jqZ : Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)) :=
  ⟨jq, Algebra.subset_adjoin (Set.mem_singleton jq)⟩

private def evalAtJZ : Polynomial ℤ →+* Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)) :=
  (Polynomial.aeval jqZ).toRingHom

private theorem algebraMap_comp_evalAtJZ :
    (algebraMap (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)).comp
        evalAtJZ = evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show algebraMap (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)
      (evalAtJZ X) = evalAtJ X
  rw [evalAtJ_X]
  show algebraMap (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)
      (Polynomial.aeval jqZ X) = jq
  rw [Polynomial.aeval_X]
  rfl

private theorem isIntegral_adjoin_jq_of_monic_eval₂ {y : LaurentSeries ℚ}
    (Q : Polynomial (Polynomial ℤ)) (hQ : Q.Monic) (h0 : Q.eval₂ evalAtJ y = 0) :
    IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ))) y := by
  refine ⟨Q.map evalAtJZ, hQ.map evalAtJZ, ?_⟩
  rw [Polynomial.eval₂_map, algebraMap_comp_evalAtJZ, h0]

private theorem isIntegral_adjoin_jq_inv_mul_of_annihilator (ℓ : ℕ) [NeZero ℓ]
    {C : LaurentSeries ℚ} (Q : Polynomial (Polynomial ℤ)) (hQ : Q.Monic)
    (hdvd : ∀ i < Q.natDegree, ((ℓ : Polynomial ℤ)) ^ (Q.natDegree - i) ∣ Q.coeff i)
    (h0 : Q.eval₂ evalAtJ C = 0) :
    IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
      ((ℓ : LaurentSeries ℚ)⁻¹ * C) := by
  have hℓA : ((ℓ : LaurentSeries ℚ)) ≠ 0 := by
    haveI : CharZero (LaurentSeries ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (LaurentSeries ℚ)).injective
    exact Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  by_cases hM0 : Q.natDegree = 0
  · exfalso
    have hQ1 : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hM0
    have hone : Q.coeff 0 = 1 := by
      have := hQ.coeff_natDegree
      rwa [hM0] at this
    rw [hQ1, hone, Polynomial.eval₂_C, map_one] at h0
    exact one_ne_zero h0
  · have hdvd' : ∀ i, ∃ s : Polynomial ℤ,
        i < Q.natDegree → Q.coeff i = ((ℓ : Polynomial ℤ)) ^ (Q.natDegree - i) * s := by
      intro i
      by_cases hi : i < Q.natDegree
      · obtain ⟨s, hs⟩ := hdvd i hi
        exact ⟨s, fun _ => hs⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose S hS using hdvd'
    set Q' : Polynomial (Polynomial ℤ) :=
      X ^ Q.natDegree + ∑ i ∈ Finset.range Q.natDegree, monomial i (S i) with hQ'def
    have hdegsum : (∑ i ∈ Finset.range Q.natDegree, monomial i (S i)).degree
        < ((Q.natDegree : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      exact (Finset.sup_lt_iff (WithBot.bot_lt_coe Q.natDegree)).mpr fun i hi =>
        lt_of_le_of_lt (Polynomial.degree_monomial_le i (S i))
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
    have hQ'monic : Q'.Monic := Polynomial.monic_X_pow_add hdegsum
    have hdegQ' : Q'.degree = ((Q.natDegree : ℕ) : WithBot ℕ) := by
      rw [hQ'def, Polynomial.degree_add_eq_left_of_degree_lt
        (by rwa [Polynomial.degree_X_pow]), Polynomial.degree_X_pow]
    have hQ'deg : Q'.natDegree = Q.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq_some hdegQ'
    have hQ'coeff : ∀ k, Q'.coeff k =
        (if k = Q.natDegree then 1 else 0)
          + (if k ∈ Finset.range Q.natDegree then S k else 0) := by
      intro k
      rw [hQ'def, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.finsetSum_coeff]
      congr 1
      rw [Finset.sum_congr rfl fun i _ => Polynomial.coeff_monomial]
      exact Finset.sum_ite_eq' _ _ _
    have hQQ' : Q'.scaleRoots ((ℓ : Polynomial ℤ)) = Q := by
      refine Polynomial.ext fun k => ?_
      rw [Polynomial.coeff_scaleRoots, hQ'deg, hQ'coeff]
      rcases lt_trichotomy k Q.natDegree with hk | hk | hk
      · rw [if_neg (ne_of_lt hk), if_pos (Finset.mem_range.mpr hk), zero_add,
          hS k hk, mul_comm]
      · subst hk
        rw [if_pos rfl, if_neg (by simp), add_zero, Nat.sub_self, pow_zero, mul_one,
          hQ.coeff_natDegree]
      · rw [if_neg (ne_of_gt hk), if_neg (by simp [Nat.not_lt.mpr (le_of_lt hk)]),
          add_zero, zero_mul]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt hk).symm
    have htrans := Polynomial.scaleRoots_eval₂_mul (p := Q') evalAtJ
      ((ℓ : LaurentSeries ℚ)⁻¹ * C) ((ℓ : Polynomial ℤ))
    rw [map_natCast, hQQ', hQ'deg, mul_inv_cancel_left₀ hℓA, h0] at htrans
    have heval' : Q'.eval₂ evalAtJ ((ℓ : LaurentSeries ℚ)⁻¹ * C) = 0 := by
      rcases mul_eq_zero.mp htrans.symm with h | h
      · exact absurd h (pow_ne_zero Q.natDegree hℓA)
      · exact h
    exact isIntegral_adjoin_jq_of_monic_eval₂ Q' hQ'monic heval'

private theorem exists_aeval_eq_of_mem_adjoin_rat_of_isIntegral {e : LaurentSeries ℚ}
    (he : e ∈ ℚ⟮jq⟯)
    (hint : IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) e) :
    ∃ P : Polynomial ℚ, e = Polynomial.aeval jq P := by
  have hinj : Function.Injective (Polynomial.aeval jq : Polynomial ℚ →ₐ[ℚ] LaurentSeries ℚ) :=
    transcendental_iff_injective.mp transcendental_jq
  have hinjR : Function.Injective
      ((Polynomial.aeval jq : Polynomial ℚ →ₐ[ℚ] LaurentSeries ℚ).toRingHom) := hinj
  set ψ : FractionRing (Polynomial ℚ) →+* LaurentSeries ℚ :=
    IsFractionRing.lift hinjR with hψdef
  have hQmem : ∀ c : ℚ, algebraMap ℚ (LaurentSeries ℚ) c ∈ ψ.fieldRange := by
    intro c
    refine RingHom.mem_fieldRange.mpr ⟨algebraMap (Polynomial ℚ) _ (Polynomial.C c), ?_⟩
    rw [hψdef, IsFractionRing.lift_algebraMap]
    simp
  have hjqmem : jq ∈ (ψ.fieldRange).toIntermediateField hQmem := by
    refine RingHom.mem_fieldRange.mpr ⟨algebraMap (Polynomial ℚ) _ Polynomial.X, ?_⟩
    rw [hψdef, IsFractionRing.lift_algebraMap]
    simp
  have hle : ℚ⟮jq⟯ ≤ (ψ.fieldRange).toIntermediateField hQmem :=
    IntermediateField.adjoin_simple_le_iff.mpr hjqmem
  obtain ⟨r, hr⟩ : ∃ r, ψ r = e := RingHom.mem_fieldRange.mp (hle he)
  obtain ⟨p, hpm, hp0⟩ := hint
  have hEq : Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))
      = (Polynomial.aeval jq : Polynomial ℚ →ₐ[ℚ] LaurentSeries ℚ).range :=
    Algebra.adjoin_singleton_eq_range_aeval ℚ jq
  set χ : ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ≃ₐ[ℚ] Polynomial ℚ :=
    (Subalgebra.equivOfEq _ _ hEq).trans
      (AlgEquiv.ofInjective (Polynomial.aeval jq) hinj).symm with hχdef
  have hχ : ∀ s, Polynomial.aeval jq (χ s) = (s : LaurentSeries ℚ) := by
    intro s
    rw [hχdef]
    simp only [AlgEquiv.trans_apply]
    rw [← AlgEquiv.ofInjective_apply (Polynomial.aeval jq) hinj, AlgEquiv.apply_symm_apply]
    rfl
  have hcomp : (ψ.comp (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).comp
        (χ.toAlgHom.toRingHom)
      = algebraMap ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ) := by
    refine RingHom.ext fun s => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, hψdef, IsFractionRing.lift_algebraMap]
    exact hχ s
  have heval' : (p.map χ.toAlgHom.toRingHom).eval₂
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) r = 0 := by
    refine RingHom.injective ψ ?_
    rw [map_zero, Polynomial.hom_eval₂, hr, Polynomial.eval₂_map, hcomp]
    exact hp0
  have hrint : IsIntegral (Polynomial ℚ) r :=
    ⟨p.map χ.toAlgHom.toRingHom, hpm.map _, heval'⟩
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrint
  refine ⟨P, ?_⟩
  rw [← hr, ← hP, hψdef, IsFractionRing.lift_algebraMap]
  rfl

private theorem exists_multiset_minpoly_map_eq_prod_of_mem_adjoin
    {k L Ω : Type*} [Field k] [Field L] [Field Ω] [Algebra k L] [Algebra k Ω]
    {θ : L} (hθ : IsIntegral k θ)
    (hsplits : ((minpoly k θ).map (algebraMap k Ω)).Splits)
    {C : L} (hC : C ∈ IntermediateField.adjoin k ({θ} : Set L)) :
    ∃ m : Multiset Ω,
      (minpoly k C).map (algebraMap k Ω)
          = (m.map fun v => Polynomial.X - Polynomial.C v).prod
        ∧ ∀ v ∈ m, ∃ τ : IntermediateField.adjoin k ({θ} : Set L) →ₐ[k] Ω,
            τ ⟨C, hC⟩ = v := by
  classical
  have hK : ∀ s ∈ ({θ} : Set L), IsIntegral k s
      ∧ ((minpoly k s).map (algebraMap k Ω)).Splits := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨hθ, hsplits⟩
  have halg : Algebra.IsAlgebraic k (IntermediateField.adjoin k ({θ} : Set L)) :=
    IntermediateField.isAlgebraic_adjoin fun s hs => (hK s hs).1
  have hCint : IsIntegral k C := by
    have h1 : IsAlgebraic k (⟨C, hC⟩ : IntermediateField.adjoin k ({θ} : Set L)) :=
      halg.isAlgebraic _
    have h3 := h1.isIntegral.map (IntermediateField.adjoin k ({θ} : Set L)).val
    simpa using h3
  have hCsplits : ((minpoly k C).map (algebraMap k Ω)).Splits :=
    IntermediateField.splits_of_mem_adjoin k L hK hC
  have hmono : ((minpoly k C).map (algebraMap k Ω)).Monic :=
    (minpoly.monic hCint).map _
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hCsplits
  rw [hmono.leadingCoeff, Polynomial.C_1, one_mul] at hm
  refine ⟨m, hm, fun v hv => ?_⟩
  have hroot : Polynomial.aeval v (minpoly k C) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hm,
      Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero
      (Multiset.mem_map.mpr ⟨Polynomial.X - Polynomial.C v,
        Multiset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩)
    simp
  exact IntermediateField.exists_algHom_adjoin_of_splits_of_aeval hK hC hroot

private theorem dvd_multiset_sum {R : Type*} [CommRing R] {r : R} {s : Multiset R}
    (h : ∀ x ∈ s, r ∣ x) : r ∣ s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.sum_cons]
      exact dvd_add (h a (Multiset.mem_cons_self a t))
        (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

private theorem coeff_multiset_sum {R : Type*} [CommRing R]
    (s : Multiset (LaurentSeries R)) (k : ℤ) :
    s.sum.coeff k = (s.map fun A => A.coeff k).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih => simp [Multiset.sum_cons, HahnSeries.coeff_add, ih]

private theorem pow_card_dvd_coeff_multiset_prod {R : Type*} [CommRing R] {r : R}
    {t : Multiset (LaurentSeries R)} (h : ∀ A ∈ t, ∀ k : ℤ, r ∣ A.coeff k) (k : ℤ) :
    r ^ Multiset.card t ∣ t.prod.coeff k := by
  induction t using Multiset.induction generalizing k with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, Multiset.card_cons, pow_succ', HahnSeries.coeff_mul]
      refine Finset.dvd_sum fun ij _ => ?_
      exact mul_dvd_mul (h a (Multiset.mem_cons_self a s) ij.1)
        (ih (fun A hA k' => h A (Multiset.mem_cons_of_mem hA) k') ij.2)

private theorem pow_dvd_coeff_esymm {R : Type*} [CommRing R] {r : R}
    {s : Multiset (LaurentSeries R)} (h : ∀ A ∈ s, ∀ k : ℤ, r ∣ A.coeff k) (j : ℕ)
    (k : ℤ) : r ^ j ∣ (s.esymm j).coeff k := by
  rw [Multiset.esymm, coeff_multiset_sum]
  refine dvd_multiset_sum fun x hx => ?_
  obtain ⟨B, hB, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hB
  obtain ⟨hts, htcard⟩ := (Multiset.mem_powersetCard).mp ht
  rw [← htcard]
  exact pow_card_dvd_coeff_multiset_prod
    (fun A hA k' => h A (Multiset.mem_of_le hts hA) k') k

private theorem exists_intCast_of_algebraMap_eq_of_isIntegral {K : Type*} [Field K]
    [Algebra ℚ K] {s : K} (hs : IsIntegral ℤ s) {q : ℚ}
    (h : algebraMap ℚ K q = s) : ∃ z : ℤ, q = (z : ℚ) := by
  have h1 : IsIntegral ℤ (algebraMap ℚ K q) := h ▸ hs
  have h2 : IsIntegral ℤ q := by
    have h1' : IsIntegral ℤ ((IsScalarTower.toAlgHom ℤ ℚ K) q) := h1
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K)
      (algebraMap ℚ K).injective).mp h1'
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨z, by rw [← hz, eq_intCast]⟩

private def jqQ : Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) :=
  ⟨jq, Algebra.subset_adjoin (Set.mem_singleton jq)⟩

private def evalAtJQZ : Polynomial ℤ →+* Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) :=
  (Polynomial.aeval (R := ℤ) jqQ).toRingHom

private theorem algebraMap_comp_evalAtJQZ :
    (algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)).comp
        evalAtJQZ = evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)
      (evalAtJQZ X) = evalAtJ X
  rw [evalAtJ_X]
  show algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)
      (Polynomial.aeval (R := ℤ) jqQ X) = jq
  rw [Polynomial.aeval_X]
  rfl

private theorem isIntegral_adjoin_rat_of_monic_eval₂ {y : LaurentSeries ℚ}
    (Q : Polynomial (Polynomial ℤ)) (hQ : Q.Monic) (h0 : Q.eval₂ evalAtJ y = 0) :
    IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) y := by
  refine ⟨Q.map evalAtJQZ, hQ.map evalAtJQZ, ?_⟩
  rw [Polynomial.eval₂_map, algebraMap_comp_evalAtJQZ, h0]

private theorem isIntegral_adjoin_rat_jqN (M : ℕ) [NeZero M] :
    IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M) := by
  obtain ⟨data, -⟩ := exists_phiIrreducible M
  exact isIntegral_adjoin_rat_of_monic_eval₂ data.Φ data.monic data.eval_eq_zero

private theorem isIntegral_adjoin_rat_jq :
    IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) jq := by
  have h : jq = algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (LaurentSeries ℚ) jqQ := rfl
  rw [h]
  exact isIntegral_algebraMap

private theorem isIntegral_adjoin_field_jqN (M : ℕ) [NeZero M] :
    IsIntegral (↥ℚ⟮jq⟯) (jqN M) := by
  obtain ⟨data, -⟩ := exists_phiIrreducible M
  refine ⟨data.toAdjoin, data.toAdjoin_monic, ?_⟩
  simp only [ModularPolynomialData.toAdjoin]
  rw [Polynomial.eval₂_map, algebraMap_comp_evalAtJGen, data.eval_eq_zero]

private theorem isIntegral_adjoin_rat_mixedProd₁ (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      ((jqN ℓ - jq ^ ℓ) * (jqN N - jqN (N * ℓ) ^ ℓ)) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  exact ((isIntegral_adjoin_rat_jqN ℓ).sub (isIntegral_adjoin_rat_jq.pow ℓ)).mul
    ((isIntegral_adjoin_rat_jqN N).sub ((isIntegral_adjoin_rat_jqN (N * ℓ)).pow ℓ))

private theorem isIntegral_adjoin_rat_mixedProd₂ (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      ((jq - jqN ℓ ^ ℓ) * (jqN (N * ℓ) - jqN N ^ ℓ)) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  exact (isIntegral_adjoin_rat_jq.sub ((isIntegral_adjoin_rat_jqN ℓ).pow ℓ)).mul
    ((isIntegral_adjoin_rat_jqN (N * ℓ)).sub ((isIntegral_adjoin_rat_jqN N).pow ℓ))

private theorem qExpand_mixed₁ (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    qExpand ℚ N (jq - jqN ℓ ^ ℓ) = jqN N - jqN (N * ℓ) ^ ℓ := by
  simp only [jqN, map_sub, map_pow, qExpand_qExpand]

private theorem qExpand_mixed₂ (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    qExpand ℚ N (jqN ℓ - jq ^ ℓ) = jqN (N * ℓ) - jqN N ^ ℓ := by
  simp only [jqN, map_sub, map_pow, qExpand_qExpand]

private theorem exists_primitiveRoot_unit (n : ℕ) [NeZero n] :
    ∃ ξ : (CyclotomicField n ℚ)ˣ, IsPrimitiveRoot (ξ : CyclotomicField n ℚ) n := by
  haveI : NeZero ((n : ℚ)) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  haveI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have hu := hζ.isUnit (NeZero.ne n)
  exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hζ⟩

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

private theorem coeffMap_qTwist (u : Rˣ) (x : LaurentSeries R) :
    coeffMap f (qTwist u x) = qTwist (Units.map (f : R →* S) u) (coeffMap f x) := by
  ext k
  have h : f ((u ^ k : Rˣ) : R) = (((Units.map (f : R →* S) u) ^ k : Sˣ) : S) := by
    rw [← map_zpow, Units.coe_map, MonoidHom.coe_coe]
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul, h]

private theorem coeffMap_jqModC : coeffMap f (jqModC R) = jqModC S := by
  show (jqModC R).map f = jqModC S
  exact map_jqModC f

private theorem coeffMap_slot (w : Rˣ) (m : ℕ) [NeZero m] :
    coeffMap f (qExpand R m (qTwist w (jqModC R)))
      = qExpand S m (qTwist (Units.map (f : R →* S) w) (jqModC S)) := by
  rw [coeffMap_qExpand, coeffMap_qTwist, coeffMap_jqModC]

end Transport

section CharL

variable (F : Type*) [CommRing F] (ℓ : ℕ) [Fact ℓ.Prime] [CharP F ℓ]

private theorem frobenius_coeff_jqModC (k : ℤ) :
    frobenius F ℓ ((jqModC F).coeff k) = (jqModC F).coeff k := by
  rw [jqModC_eq_map_intCast F, HahnSeries.map_coeff]
  exact map_intCast (frobenius F ℓ) _

private theorem qTwist_jqModC_pow_char (u : Fˣ) :
    (qTwist u (jqModC F)) ^ ℓ = qExpand F ℓ (qTwist (u ^ ℓ) (jqModC F)) := by
  rw [pow_char_eq_map_frobenius_qExpand ℓ (qTwist u (jqModC F))]
  ext k
  rw [HahnSeries.map_coeff]
  by_cases hk : (ℓ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, qTwist_coeff, qTwist_coeff, map_mul,
      frobenius_coeff_jqModC, frobenius_def, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
      ← zpow_mul, ← zpow_natCast u ℓ, ← zpow_mul, mul_comm (m : ℤ) (ℓ : ℤ)]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hk, qExpand_coeff_of_not_dvd ℓ _ hk, map_zero]

private theorem slot_pow_char (u : Fˣ) (m : ℕ) [NeZero m] :
    (qExpand F m (qTwist u (jqModC F))) ^ ℓ
      = qExpand F (m * ℓ) (qTwist (u ^ ℓ) (jqModC F)) := by
  rw [← map_pow, qTwist_jqModC_pow_char, qExpand_qExpand]

private theorem liftDiff_eq_zero (u : Fˣ) (m : ℕ) [NeZero m] :
    qExpand F (m * ℓ) (qTwist (u ^ ℓ) (jqModC F)) - (qExpand F m (qTwist u (jqModC F))) ^ ℓ
      = 0 := by
  rw [slot_pow_char, sub_self]

end CharL

section Integral

variable {R F : Type*} [CommRing R] [CommRing F] (ℓ : ℕ) [Fact ℓ.Prime] [CharP F ℓ]
  (π : R →+* F)

private theorem coeffMap_liftDiff_eq_zero (w : Rˣ) (m : ℕ) [NeZero m] :
    coeffMap π (qExpand R (m * ℓ) (qTwist (w ^ ℓ) (jqModC R))
        - (qExpand R m (qTwist w (jqModC R))) ^ ℓ) = 0 := by
  rw [map_sub, map_pow, coeffMap_slot, coeffMap_slot, map_pow]
  exact liftDiff_eq_zero F ℓ (Units.map (π : R →* F) w) m

private theorem coeffMap_liftDiff_mul_eq_zero (w : Rˣ) (m : ℕ) [NeZero m] (y : LaurentSeries R) :
    coeffMap π ((qExpand R (m * ℓ) (qTwist (w ^ ℓ) (jqModC R))
        - (qExpand R m (qTwist w (jqModC R))) ^ ℓ) * y) = 0 := by
  rw [map_mul, coeffMap_liftDiff_eq_zero, zero_mul]

private theorem coeffMap_mul_liftDiff_eq_zero (w : Rˣ) (m : ℕ) [NeZero m] (y : LaurentSeries R) :
    coeffMap π (y * (qExpand R (m * ℓ) (qTwist (w ^ ℓ) (jqModC R))
        - (qExpand R m (qTwist w (jqModC R))) ^ ℓ)) = 0 := by
  rw [map_mul, coeffMap_liftDiff_eq_zero, mul_zero]

private theorem coeff_liftDiff_mem_ker (w : Rˣ) (m : ℕ) [NeZero m] (k : ℤ) :
    (qExpand R (m * ℓ) (qTwist (w ^ ℓ) (jqModC R))
        - (qExpand R m (qTwist w (jqModC R))) ^ ℓ).coeff k ∈ RingHom.ker π := by
  rw [RingHom.mem_ker, ← coeffMap_coeff, coeffMap_liftDiff_eq_zero, HahnSeries.coeff_zero]

end Integral

section TransportRel

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem aeval_int_toRingHom_eq {L : Type*} [CommRing L] {inst : Algebra ℤ L} (x : L) :
    (@Polynomial.aeval ℤ L _ _ inst x).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom L) x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

private theorem evalAtJ_eq_eval₂RingHom :
    evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

private theorem eval₂_intRel_map_ringHom (τ : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (x y : A)
    (h : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom A) x) y = 0) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom B) (τ x)) (τ y) = 0 := by
  have hcomp : τ.comp (Polynomial.eval₂RingHom (Int.castRingHom A) x)
      = Polynomial.eval₂RingHom (Int.castRingHom B) (τ x) :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  rw [← hcomp, ← Polynomial.hom_eval₂, h, map_zero]

end TransportRel

section Slots

variable {K : Type*} [Field K]

private theorem coeff_slot_neg (w : Kˣ) (m : ℕ) [NeZero m] :
    (qExpand K m (qTwist w (jqModC K))).coeff (-(m : ℤ)) = ((w ^ (-1 : ℤ) : Kˣ) : K) := by
  rw [show (-(m : ℤ)) = (m : ℤ) * (-1) by ring, qExpand_coeff_mul, qTwist_coeff,
    coeff_jqModC_neg_one, mul_one]

private theorem coeff_slot_of_lt (w : Kˣ) (m : ℕ) [NeZero m] {k : ℤ} (hk : k < -(m : ℤ)) :
    (qExpand K m (qTwist w (jqModC K))).coeff k = 0 := by
  by_cases hmk : (m : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hmk
    have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    rcases lt_or_ge n (-1) with hn | hn
    · rw [qExpand_coeff_mul, qTwist_coeff, ← pow_one (jqModC K),
        coeff_jqModC_pow_of_lt K (b := 1) (by exact_mod_cast hn), mul_zero]
    · exfalso
      have : (m : ℤ) * (-1) ≤ (m : ℤ) * n := mul_le_mul_of_nonneg_left hn hm.le
      omega
  · exact qExpand_coeff_of_not_dvd m _ hmk

private theorem slot_pole_injective {w w' : Kˣ} {m m' : ℕ} [NeZero m] [NeZero m']
    (h : qExpand K m (qTwist w (jqModC K)) = qExpand K m' (qTwist w' (jqModC K))) :
    m = m' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := congrArg (fun f => HahnSeries.coeff f (-(m' : ℤ))) h
    rw [coeff_slot_of_lt w m (by omega), coeff_slot_neg] at h1
    exact (w' ^ (-1 : ℤ)).ne_zero h1.symm
  · have h1 := congrArg (fun f => HahnSeries.coeff f (-(m : ℤ))) h
    rw [coeff_slot_of_lt w' m' (by omega), coeff_slot_neg] at h1
    exact (w ^ (-1 : ℤ)).ne_zero h1

private theorem qTwist_slot (v w : Kˣ) (a : ℕ) [NeZero a] :
    qTwist v (qExpand K a (qTwist w (jqModC K)))
      = qExpand K a (qTwist (v ^ a * w) (jqModC K)) := by
  rw [qTwist_qExpand, qTwist_qTwist, zpow_natCast]

private theorem qExpand_slot (m : ℕ) [NeZero m] (w : Kˣ) (a : ℕ) [NeZero a] :
    qExpand K m (qExpand K a (qTwist w (jqModC K)))
      = qExpand K (m * a) (qTwist w (jqModC K)) :=
  qExpand_qExpand a m _

variable (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime] (ξ : Kˣ)
  (hξ : IsPrimitiveRoot (ξ : K) (N * ℓ))

include hξ in

private theorem isPrimitiveRoot_pow_ell : IsPrimitiveRoot ((ξ ^ ℓ : Kˣ) : K) N := by
  rw [Units.val_pow_eq_pow_val]
  exact hξ.pow (Nat.pos_of_ne_zero (NeZero.ne (N * ℓ))) (mul_comm N ℓ)

variable [Algebra ℚ K]

include hξ in

private theorem root_phiEll (dataℓ : ModularPolynomialData ℓ) (e : ℕ) [NeZero e] (u : Kˣ)
    {y : LaurentSeries K}
    (hy : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (ℓ * e) (qTwist (u ^ ℓ) (jqModC K)))) y = 0) :
    y = qExpand K (ℓ * (ℓ * e)) (qTwist (u ^ (ℓ * ℓ)) (jqModC K)) ∨
      ∃ b : ℕ, y = qExpand K e (qTwist (u * ξ ^ (b * N)) (jqModC K)) := by
  have hsplit := PhiGen.splits_prime_at_slot (N * ℓ) ξ hξ ℓ (dvd_mul_left ℓ N) dataℓ e u
  rw [coeffEmb_jq, Nat.mul_div_cancel N hℓ.out.pos] at hsplit
  have hy' : (dataℓ.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (ℓ * e) (qTwist (u ^ ℓ) (jqModC K))))).eval y = 0 := by
    rw [Polynomial.eval_map, hy]
  rw [hsplit, Polynomial.eval_mul, mul_eq_zero] at hy'
  rcases hy' with h0 | hprod
  · left
    rwa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h0
  · right
    rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, -, hb⟩ := hprod
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hb
    exact ⟨b, hb⟩

include hξ in

private theorem phiN_map_eq_prod_slots (dataN : ModularPolynomialData N) :
    dataN.Φ.map (((coeffEmb K).comp (qExpand ℚ N)).comp evalAtJ)
      = ∏ a ∈ N.divisors, ∏ b ∈ (Finset.range (N / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
          (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
            letI : NeZero a := ⟨h⟩
            qExpand K (a * a) (qTwist ((ξ ^ ℓ) ^ (b * a)) (coeffEmb K jq)))) := by
  have hall : ∀ d : ℕ, d ∣ N → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d ∧
        modularFunctionField d = modularFunctionFieldFull d :=
    fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d,
      ((functionFieldGeneration_iff_full_eq d).mp (functionFieldGeneration d)).symm⟩
  have h := minpoly_jqN_map_eq_prod_slots (K := K) N (ξ ^ ℓ)
    (isPrimitiveRoot_pow_ell N ℓ ξ hξ) hall
  rw [minpoly_jqN_eq_toAdjoin dataN (phiIrreducible_all N dataN), ModularPolynomialData.toAdjoin,
    Polynomial.map_map, RingHom.comp_assoc, algebraMap_comp_evalAtJGen] at h
  exact h

include hξ in

private theorem root_phiN (dataN : ModularPolynomialData N) (m' : ℕ) [NeZero m'] (w' : Kˣ)
    {y : LaurentSeries K}
    (hy : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (m' * N) (qTwist (w' ^ N) (jqModC K)))) y = 0) :
    ∃ a b : ℕ, a ∣ N ∧ ∃ _ : NeZero a,
      y = qExpand K (m' * (a * a)) (qTwist (w' ^ (a * a) * (ξ ^ ℓ) ^ (b * a)) (jqModC K)) := by
  set θ : LaurentSeries K →+* LaurentSeries K := (qExpand K m').comp (qTwist w') with hθ
  have hprod := congrArg (Polynomial.map θ) (phiN_map_eq_prod_slots N ℓ ξ hξ dataN)
  rw [Polynomial.map_map] at hprod
  have hring : θ.comp (((coeffEmb K).comp (qExpand ℚ N)).comp evalAtJ)
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (qExpand K (m' * N) (qTwist (w' ^ N) (jqModC K))) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [coeffEmb_qExpand, coeffEmb_jq, hθ, RingHom.comp_apply, qTwist_qExpand, zpow_natCast,
      qExpand_qExpand]
  rw [hring] at hprod
  have hy' : (dataN.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (m' * N) (qTwist (w' ^ N) (jqModC K))))).eval y = 0 := by
    rw [Polynomial.eval_map, hy]
  rw [hprod, Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hy'
  obtain ⟨a, ha, hy'⟩ := hy'
  rw [Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hy'
  obtain ⟨b, -, hy'⟩ := hy'
  have ha0 : a ≠ 0 := (Nat.pos_of_mem_divisors ha).ne'
  refine ⟨a, b, Nat.dvd_of_mem_divisors ha, ⟨ha0⟩, ?_⟩
  rw [dif_neg ha0, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hy'
  rw [hy', hθ, RingHom.comp_apply, coeffEmb_jq, qTwist_slot, qExpand_slot]

include hξ in

private theorem liftPair_coupling (hℓN : ¬ ℓ ∣ N) (dataℓ : ModularPolynomialData ℓ)
    (dataN : ModularPolynomialData N) (xℓ xN xNℓ : LaurentSeries K)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (N * ℓ) (jqModC K))) xℓ = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (N * ℓ) (jqModC K))) xN = 0)
    (h₃ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) xN) xNℓ = 0)
    (h₄ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) xℓ) xNℓ = 0) :
    (xℓ = qExpand K (N * ℓ * ℓ) (jqModC K) ∧
        ∃ (e m : ℕ) (_ : NeZero m), xN = qExpand K m (qTwist (ξ ^ e) (jqModC K)) ∧
          xNℓ = qExpand K (m * ℓ) (qTwist ((ξ ^ e) ^ ℓ) (jqModC K))) ∨
    ((∃ e : ℕ, (ξ ^ e) ^ ℓ = 1 ∧ xℓ = qExpand K N (qTwist (ξ ^ e) (jqModC K))) ∧
        ∃ (e m : ℕ) (_ : NeZero m), xNℓ = qExpand K m (qTwist (ξ ^ e) (jqModC K)) ∧
          xN = qExpand K (m * ℓ) (qTwist ((ξ ^ e) ^ ℓ) (jqModC K))) := by
  have hξ1 : ξ ^ (N * ℓ) = 1 := Units.val_eq_one.mp (by rw [Units.val_pow_eq_pow_val, hξ.pow_eq_one])

  have hjℓ : qExpand K (N * ℓ) (jqModC K) = qExpand K (ℓ * N) (qTwist ((1 : Kˣ) ^ ℓ) (jqModC K)) := by
    rw [one_pow, qTwist_one_apply, qExpand_congr (mul_comm N ℓ)]
  have hjN : qExpand K (N * ℓ) (jqModC K) = qExpand K (ℓ * N) (qTwist ((1 : Kˣ) ^ N) (jqModC K)) := by
    rw [one_pow, qTwist_one_apply, qExpand_congr (mul_comm N ℓ)]

  rw [hjℓ] at h₁
  have Hℓ := root_phiEll N ℓ ξ hξ dataℓ N 1 h₁
  simp only [one_pow, one_mul] at Hℓ

  rw [hjN] at h₂
  obtain ⟨a', b', ha'N, _, hxN⟩ := root_phiN N ℓ ξ hξ dataN ℓ 1 h₂
  simp only [one_pow, one_mul] at hxN
  have hu : (ξ ^ ℓ) ^ (b' * a') = (ξ ^ (b' * a')) ^ ℓ := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hu] at hxN

  rw [hxN] at h₃
  have HN := root_phiEll N ℓ ξ hξ dataℓ (a' * a') (ξ ^ (b' * a')) h₃
  have hℓa' : ¬ ℓ ∣ a' := fun h => hℓN (h.trans ha'N)
  rcases Hℓ with hF | ⟨β, hV⟩
  ·
    rcases HN with hNF | ⟨b, hNV⟩
    ·
      refine Or.inl ⟨?_, b' * a' * ℓ, ℓ * (a' * a'), inferInstance, ?_, ?_⟩
      · rw [hF, qTwist_one_apply, qExpand_congr (show ℓ * (ℓ * N) = N * ℓ * ℓ by ring)]
      · rw [hxN, ← pow_mul]
      · rw [hNF, ← pow_mul, ← pow_mul,
          qExpand_congr (show ℓ * (ℓ * (a' * a')) = ℓ * (a' * a') * ℓ by ring),
          show b' * a' * (ℓ * ℓ) = b' * a' * ℓ * ℓ by ring]
    ·
      exfalso
      rw [hF, qTwist_one_apply,
        qExpand_congr (show ℓ * (ℓ * N) = ℓ * ℓ * N by ring),
        show qExpand K (ℓ * ℓ * N) (jqModC K)
          = qExpand K (ℓ * ℓ * N) (qTwist ((1 : Kˣ) ^ N) (jqModC K)) by
            rw [one_pow, qTwist_one_apply]] at h₄
      obtain ⟨a, b₀, haN, _, hroot⟩ := root_phiN N ℓ ξ hξ dataN (ℓ * ℓ) 1 h₄
      rw [hNV] at hroot
      have hm := slot_pole_injective hroot
      have : ℓ ∣ a' * a' := ⟨ℓ * (a * a), by rw [hm]; ring⟩
      exact hℓa' ((Nat.Prime.dvd_mul hℓ.out).mp this |>.elim id id)
  ·
    rcases HN with hNF | ⟨b, hNV⟩
    ·
      exfalso
      rw [hV, show qExpand K N (qTwist (ξ ^ (β * N)) (jqModC K))
          = qExpand K (1 * N) (qTwist ((ξ ^ β) ^ N) (jqModC K)) by
            rw [← pow_mul, qExpand_congr (one_mul N)]] at h₄
      obtain ⟨a, b₀, haN, _, hroot⟩ := root_phiN N ℓ ξ hξ dataN 1 (ξ ^ β) h₄
      rw [hNF] at hroot
      have hm := slot_pole_injective hroot
      have hℓa : ¬ ℓ ∣ a := fun h => hℓN (h.trans haN)
      rw [one_mul] at hm
      have : ℓ ∣ a * a := ⟨ℓ * (a' * a'), hm.symm⟩
      exact hℓa ((Nat.Prime.dvd_mul hℓ.out).mp this |>.elim id id)
    ·
      refine Or.inr ⟨⟨β * N, ?_, hV⟩, b' * a' + b * N, a' * a', inferInstance, ?_, ?_⟩
      · rw [← pow_mul, show β * N * ℓ = N * ℓ * β by ring, pow_mul, hξ1, one_pow]
      · rw [hNV, pow_add]
      · rw [hxN, qExpand_congr (mul_comm ℓ (a' * a')), pow_add, mul_pow, ← pow_mul ξ (b * N) ℓ,
          show b * N * ℓ = N * ℓ * b by ring, pow_mul ξ (N * ℓ) b, hξ1, one_pow, mul_one]

end Slots

section Pullback

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem eval₂_intRel_of_injective (f : A →+* B) (hf : Function.Injective f)
    (Φ : Polynomial (Polynomial ℤ)) (x y : A)
    (h : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom B) (f x)) (f y) = 0) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom A) x) y = 0 := by
  have hcomp : f.comp (Polynomial.eval₂RingHom (Int.castRingHom A) x)
      = Polynomial.eval₂RingHom (Int.castRingHom B) (f x) :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  apply hf
  rw [map_zero, Polynomial.hom_eval₂, hcomp, h]

end Pullback

section Payload

variable {K : Type*} [Field K] [Algebra ℚ K] (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]
  (ξ : Kˣ) (hξ : IsPrimitiveRoot (ξ : K) (N * ℓ))
  {R F : Type*} [CommRing R] [CommRing F] [CharP F ℓ]
  (ι : R →+* K) (π : R →+* F) (ξR : Rˣ) (hξR : Units.map (ι : R →* K) ξR = ξ)

include hξ hξR in

private theorem perConjugate_payload (hℓN : ¬ ℓ ∣ N) (dataℓ : ModularPolynomialData ℓ)
    (dataN : ModularPolynomialData N) (xℓ xN xNℓ : LaurentSeries K)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (N * ℓ) (jqModC K))) xℓ = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (N * ℓ) (jqModC K))) xN = 0)
    (h₃ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) xN) xNℓ = 0)
    (h₄ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) xℓ) xNℓ = 0) :
    (∃ A : LaurentSeries R,
        coeffMap ι A = (xℓ - (qExpand K (N * ℓ) (jqModC K)) ^ ℓ) * (xN - xNℓ ^ ℓ) ∧
        coeffMap π A = 0) ∧
    (∃ A : LaurentSeries R,
        coeffMap ι A = (qExpand K (N * ℓ) (jqModC K) - xℓ ^ ℓ) * (xNℓ - xN ^ ℓ) ∧
        coeffMap π A = 0) := by

  have slotK : ∀ (w : Rˣ) (m : ℕ) [NeZero m],
      coeffMap ι (qExpand R m (qTwist w (jqModC R)))
        = qExpand K m (qTwist (Units.map (ι : R →* K) w) (jqModC K)) :=
    fun w m _ => coeffMap_slot ι w m
  rcases liftPair_coupling N ℓ ξ hξ hℓN dataℓ dataN xℓ xN xNℓ h₁ h₂ h₃ h₄ with
    ⟨hF, e, m, _, hxN, hxNℓ⟩ | ⟨⟨e₀, he₀, hV⟩, e, m, _, hxNℓ, hxN⟩
  ·
    refine ⟨⟨(qExpand R (N * ℓ * ℓ) (qTwist ((1 : Rˣ) ^ ℓ) (jqModC R))
        - (qExpand R (N * ℓ) (qTwist (1 : Rˣ) (jqModC R))) ^ ℓ)
        * (qExpand R m (qTwist (ξR ^ e) (jqModC R))
          - (qExpand R (m * ℓ) (qTwist ((ξR ^ e) ^ ℓ) (jqModC R))) ^ ℓ), ?_,
        coeffMap_liftDiff_mul_eq_zero ℓ π 1 (N * ℓ) _⟩,
      ⟨(qExpand R (N * ℓ) (qTwist (1 : Rˣ) (jqModC R))
        - (qExpand R (N * ℓ * ℓ) (qTwist ((1 : Rˣ) ^ ℓ) (jqModC R))) ^ ℓ)
        * (qExpand R (m * ℓ) (qTwist ((ξR ^ e) ^ ℓ) (jqModC R))
          - (qExpand R m (qTwist (ξR ^ e) (jqModC R))) ^ ℓ), ?_,
        coeffMap_mul_liftDiff_eq_zero ℓ π (ξR ^ e) m _⟩⟩
    · rw [hF, hxN, hxNℓ]
      simp only [map_mul, map_sub, map_pow, slotK, hξR, one_pow, qTwist_one_apply, coeffMap_qExpand,
        coeffMap_jqModC]
    · rw [hF, hxN, hxNℓ]
      simp only [map_mul, map_sub, map_pow, slotK, hξR, one_pow, qTwist_one_apply, coeffMap_qExpand,
        coeffMap_jqModC]
  ·
    refine ⟨⟨(qExpand R N (qTwist (ξR ^ e₀) (jqModC R))
        - (qExpand R (N * ℓ) (qTwist ((ξR ^ e₀) ^ ℓ) (jqModC R))) ^ ℓ)
        * (qExpand R (m * ℓ) (qTwist ((ξR ^ e) ^ ℓ) (jqModC R))
          - (qExpand R m (qTwist (ξR ^ e) (jqModC R))) ^ ℓ), ?_,
        coeffMap_mul_liftDiff_eq_zero ℓ π (ξR ^ e) m _⟩,
      ⟨(qExpand R (N * ℓ) (qTwist ((ξR ^ e₀) ^ ℓ) (jqModC R))
        - (qExpand R N (qTwist (ξR ^ e₀) (jqModC R))) ^ ℓ)
        * (qExpand R m (qTwist (ξR ^ e) (jqModC R))
          - (qExpand R (m * ℓ) (qTwist ((ξR ^ e) ^ ℓ) (jqModC R))) ^ ℓ), ?_,
        coeffMap_liftDiff_mul_eq_zero ℓ π (ξR ^ e₀) N _⟩⟩
    · rw [hV, hxN, hxNℓ]
      simp only [map_mul, map_sub, map_pow, slotK, hξR, he₀, qTwist_one_apply]
    · rw [hV, hxN, hxNℓ]
      simp only [map_mul, map_sub, map_pow, slotK, hξR, he₀, qTwist_one_apply]

end Payload

section Divide

variable {R : Type*} [CommRing R]

private theorem exists_eq_C_mul_of_coeffMap_mk_eq_zero (r : R) (A : LaurentSeries R)
    (h : coeffMap (Ideal.Quotient.mk (Ideal.span {r})) A = 0) :
    ∃ B : LaurentSeries R, A = HahnSeries.C r * B := by
  classical
  have hk : ∀ k : ℤ, ∃ b : R, b * r = A.coeff k := fun k =>
    Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp (by
      rw [← coeffMap_coeff, h, HahnSeries.coeff_zero]))
  choose b hb using hk
  refine ⟨⟨fun k => if A.coeff k = 0 then 0 else b k, A.isPWO_support.mono ?_⟩, ?_⟩
  · intro k hk
    rw [Function.mem_support] at hk
    rw [HahnSeries.mem_support]
    intro hA
    exact hk (if_pos hA)
  · ext k
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    show A.coeff k = r * (if A.coeff k = 0 then 0 else b k)
    split_ifs with h0
    · rw [h0, mul_zero]
    · rw [mul_comm, hb]

end Divide

section PayloadDiv

variable {K : Type*} [Field K] [Algebra ℚ K] (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]
  (ξ : Kˣ) (hξ : IsPrimitiveRoot (ξ : K) (N * ℓ))
  {R : Type*} [CommRing R] [CharP (R ⧸ Ideal.span {(ℓ : R)}) ℓ]
  (ι : R →+* K) (ξR : Rˣ) (hξR : Units.map (ι : R →* K) ξR = ξ)

include hξ hξR in

private theorem perConjugate_payload_div (hℓN : ¬ ℓ ∣ N) (dataℓ : ModularPolynomialData ℓ)
    (dataN : ModularPolynomialData N) (xℓ xN xNℓ : LaurentSeries K)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (N * ℓ) (jqModC K))) xℓ = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (N * ℓ) (jqModC K))) xN = 0)
    (h₃ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) xN) xNℓ = 0)
    (h₄ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) xℓ) xNℓ = 0) :
    (∃ B : LaurentSeries R,
        (xℓ - (qExpand K (N * ℓ) (jqModC K)) ^ ℓ) * (xN - xNℓ ^ ℓ)
          = (ℓ : LaurentSeries K) * coeffMap ι B) ∧
    (∃ B : LaurentSeries R,
        (qExpand K (N * ℓ) (jqModC K) - xℓ ^ ℓ) * (xNℓ - xN ^ ℓ)
          = (ℓ : LaurentSeries K) * coeffMap ι B) := by
  obtain ⟨⟨A₁, hA₁, hπ₁⟩, ⟨A₂, hA₂, hπ₂⟩⟩ := perConjugate_payload N ℓ ξ hξ ι
    (Ideal.Quotient.mk (Ideal.span {(ℓ : R)})) ξR hξR hℓN dataℓ dataN xℓ xN xNℓ h₁ h₂ h₃ h₄
  obtain ⟨B₁, rfl⟩ := exists_eq_C_mul_of_coeffMap_mk_eq_zero (ℓ : R) A₁ hπ₁
  obtain ⟨B₂, rfl⟩ := exists_eq_C_mul_of_coeffMap_mk_eq_zero (ℓ : R) A₂ hπ₂
  refine ⟨⟨B₁, ?_⟩, ⟨B₂, ?_⟩⟩
  · rw [← hA₁, map_mul, map_natCast (HahnSeries.C : R →+* LaurentSeries R) ℓ, map_natCast]
  · rw [← hA₂, map_mul, map_natCast (HahnSeries.C : R →+* LaurentSeries R) ℓ, map_natCast]

end PayloadDiv

section Hall

open scoped IntermediateField

private theorem jqN_mem_adjoin_adjoin_jq (M d : ℕ) [NeZero M] [NeZero d] (hd : d ∣ M) :
    jqN d ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
  have h := functionFieldGeneration M d hd ‹_›
  have hle : (IntermediateField.adjoin ℚ ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ))).toSubfield
      ≤ (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))).toSubfield := by
    refine IntermediateField.adjoin_le_subfield ℚ ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ)) ?_ ?_
    · rintro x ⟨q, rfl⟩
      rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) q]
      exact SubfieldClass.ratCast_mem _ q
    · rintro x (rfl | rfl)
      · exact (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))).algebraMap_mem jGen
      · exact IntermediateField.mem_adjoin_simple_self _ _
  exact hle h

private theorem jq_mem_adjoin_adjoin_jq (M : ℕ) [NeZero M] :
    jq ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) :=
  (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))).algebraMap_mem jGen

private theorem jqN_self_mem_adjoin_adjoin_jq (M : ℕ) [NeZero M] :
    jqN M ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) :=
  IntermediateField.mem_adjoin_simple_self _ _

private theorem jqN_left_mem_adjoin_adjoin_jq (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    jqN N ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)) :=
  jqN_mem_adjoin_adjoin_jq (N * ℓ) N (dvd_mul_right N ℓ)

private theorem jqN_right_mem_adjoin_adjoin_jq (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    jqN ℓ ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)) :=
  jqN_mem_adjoin_adjoin_jq (N * ℓ) ℓ (dvd_mul_left ℓ N)

private theorem mixedProd₁_mem_adjoin_adjoin_jq (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    (jqN ℓ - jq ^ ℓ) * (jqN N - jqN (N * ℓ) ^ ℓ)
      ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)) :=
  mul_mem (sub_mem (jqN_right_mem_adjoin_adjoin_jq N ℓ) (pow_mem (jq_mem_adjoin_adjoin_jq _) _))
    (sub_mem (jqN_left_mem_adjoin_adjoin_jq N ℓ) (pow_mem (jqN_self_mem_adjoin_adjoin_jq _) _))

private theorem mixedProd₂_mem_adjoin_adjoin_jq (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    (jq - jqN ℓ ^ ℓ) * (jqN (N * ℓ) - jqN N ^ ℓ)
      ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)) :=
  mul_mem (sub_mem (jq_mem_adjoin_adjoin_jq _) (pow_mem (jqN_right_mem_adjoin_adjoin_jq N ℓ) _))
    (sub_mem (jqN_self_mem_adjoin_adjoin_jq _) (pow_mem (jqN_left_mem_adjoin_adjoin_jq N ℓ) _))

end Hall

section AtAlgHom

open scoped IntermediateField

variable {K : Type*} [Field K] [Algebra ℚ K] (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]
  (ξ : Kˣ) (hξ : IsPrimitiveRoot (ξ : K) (N * ℓ))

private theorem eval₂_intRel_map_algHom {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] (τ : A →ₐ[F] B) (Φ : Polynomial (Polynomial ℤ)) (x y : A)
    (h : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom A) x) y = 0) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom B) (τ x)) (τ y) = 0 :=
  eval₂_intRel_map_ringHom τ.toRingHom Φ x y h

local notation "𝔼" => IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))

include hξ in

private theorem splits_minpoly_jqN_map :
    letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
      (((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
    ((minpoly ℚ⟮jq⟯ (jqN (N * ℓ))).map (algebraMap ℚ⟮jq⟯ (LaurentSeries K))).Splits := by
  letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
  have hall : ∀ d : ℕ, d ∣ N * ℓ → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d ∧
        modularFunctionField d = modularFunctionFieldFull d :=
    fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d,
      ((functionFieldGeneration_iff_full_eq d).mp (functionFieldGeneration d)).symm⟩
  show ((minpoly ℚ⟮jq⟯ (jqN (N * ℓ))).map (((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp
    (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).Splits
  rw [minpoly_jqN_map_eq_prod_slots (K := K) (N * ℓ) ξ hξ hall]
  exact Polynomial.Splits.prod fun a _ => Polynomial.Splits.prod fun b _ =>
    Polynomial.Splits.X_sub_C _

include hξ in

private theorem payload_div_at_algHom {R : Type*} [CommRing R] [CharP (R ⧸ Ideal.span {(ℓ : R)}) ℓ]
    (ιR : R →+* K) (ξR : Rˣ) (hξR : Units.map (ιR : R →* K) ξR = ξ) (hℓN : ¬ ℓ ∣ N)
    (dataℓ : ModularPolynomialData ℓ) (dataN : ModularPolynomialData N)
    (hC₁ : (jqN ℓ - jq ^ ℓ) * (jqN N - jqN (N * ℓ) ^ ℓ)
      ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)))
    (hC₂ : (jq - jqN ℓ ^ ℓ) * (jqN (N * ℓ) - jqN N ^ ℓ)
      ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))) :
    letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
      (((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
    ∀ τ : IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))
        →ₐ[ℚ⟮jq⟯] LaurentSeries K,
      (∃ B : LaurentSeries R, τ ⟨_, hC₁⟩ = (ℓ : LaurentSeries K) * coeffMap ιR B) ∧
      (∃ B : LaurentSeries R, τ ⟨_, hC₂⟩ = (ℓ : LaurentSeries K) * coeffMap ιR B) := by
  letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
  intro τ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

  have hj : jq ∈ 𝔼 := jq_mem_adjoin_adjoin_jq (N * ℓ)
  have hℓ' : jqN ℓ ∈ 𝔼 := jqN_right_mem_adjoin_adjoin_jq N ℓ
  have hN' : jqN N ∈ 𝔼 := jqN_left_mem_adjoin_adjoin_jq N ℓ
  have hNℓ' : jqN (N * ℓ) ∈ 𝔼 := jqN_self_mem_adjoin_adjoin_jq _

  have hτj : τ ⟨jq, hj⟩ = qExpand K (N * ℓ) (jqModC K) := by
    have hgen : (⟨jq, hj⟩ : 𝔼) = algebraMap ℚ⟮jq⟯ 𝔼 jGen := Subtype.ext rfl
    rw [hgen, AlgHom.commutes]
    show coeffEmb K (qExpand ℚ (N * ℓ) jq) = _
    rw [coeffEmb_qExpand, coeffEmb_jq]

  have inj : Function.Injective (algebraMap 𝔼 (LaurentSeries ℚ)) :=
    (algebraMap 𝔼 (LaurentSeries ℚ)).injective
  have s₁ := dataℓ.eval_eq_zero
  have s₂ := dataN.eval_eq_zero
  rw [evalAtJ_eq_eval₂RingHom] at s₁ s₂
  have s₃ := dataℓ.eval_jqNModC_mul_eq_zero ℚ N
  rw [aeval_int_toRingHom_eq] at s₃
  have s₄ := dataN.eval_jqNModC_mul_eq_zero ℚ ℓ
  rw [aeval_int_toRingHom_eq,
    show jqNModC ℚ (ℓ * N) = jqN (N * ℓ) from qExpand_congr (mul_comm ℓ N) _] at s₄
  have r₁ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom 𝔼) ⟨jq, hj⟩)
      ⟨jqN ℓ, hℓ'⟩ = 0 :=
    eval₂_intRel_of_injective _ inj _ _ _ s₁
  have r₂ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom 𝔼) ⟨jq, hj⟩)
      ⟨jqN N, hN'⟩ = 0 :=
    eval₂_intRel_of_injective _ inj _ _ _ s₂
  have r₃ : dataℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom 𝔼) ⟨jqN N, hN'⟩)
      ⟨jqN (N * ℓ), hNℓ'⟩ = 0 :=
    eval₂_intRel_of_injective _ inj _ _ _ s₃
  have r₄ : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom 𝔼) ⟨jqN ℓ, hℓ'⟩)
      ⟨jqN (N * ℓ), hNℓ'⟩ = 0 :=
    eval₂_intRel_of_injective _ inj _ _ _ s₄
  have t₁ := eval₂_intRel_map_algHom τ _ _ _ r₁
  have t₂ := eval₂_intRel_map_algHom τ _ _ _ r₂
  have t₃ := eval₂_intRel_map_algHom τ _ _ _ r₃
  have t₄ := eval₂_intRel_map_algHom τ _ _ _ r₄
  rw [hτj] at t₁ t₂
  obtain ⟨⟨B₁, h1⟩, ⟨B₂, h2⟩⟩ := perConjugate_payload_div N ℓ ξ hξ ιR ξR hξR hℓN dataℓ dataN
    (τ ⟨jqN ℓ, hℓ'⟩) (τ ⟨jqN N, hN'⟩) (τ ⟨jqN (N * ℓ), hNℓ'⟩) t₁ t₂ t₃ t₄
  have e₁ : (⟨_, hC₁⟩ : 𝔼)
      = (⟨jqN ℓ, hℓ'⟩ - ⟨jq, hj⟩ ^ ℓ) * (⟨jqN N, hN'⟩ - ⟨jqN (N * ℓ), hNℓ'⟩ ^ ℓ) :=
    Subtype.ext (by simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
      SubmonoidClass.coe_pow])
  have e₂ : (⟨_, hC₂⟩ : 𝔼)
      = (⟨jq, hj⟩ - ⟨jqN ℓ, hℓ'⟩ ^ ℓ) * (⟨jqN (N * ℓ), hNℓ'⟩ - ⟨jqN N, hN'⟩ ^ ℓ) :=
    Subtype.ext (by simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
      SubmonoidClass.coe_pow])
  refine ⟨⟨B₁, ?_⟩, ⟨B₂, ?_⟩⟩
  · rw [e₁, map_mul, map_sub, map_sub, map_pow, map_pow, hτj]
    exact h1
  · rw [e₂, map_mul, map_sub, map_sub, map_pow, map_pow, hτj]
    exact h2

end AtAlgHom

section RPackage

variable {K : Type*} [Field K] {n : ℕ} (ξ : Kˣ)
  (hξ : IsPrimitiveRoot (ξ : K) n) (hn : n ≠ 0)

include hξ hn in

private theorem isIntegral_int_root : IsIntegral ℤ (ξ : K) :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn,
    by simp [hξ.pow_eq_one]⟩

include hξ hn in

private theorem isIntegral_of_mem_adjoin_root {x : K}
    (hx : x ∈ Algebra.adjoin ℤ ({(ξ : K)} : Set K)) : IsIntegral ℤ x :=
  adjoin_le_integralClosure (isIntegral_int_root ξ hξ hn) hx

include hξ hn in

private theorem exists_unit_adjoin_map_eq :
    ∃ ξR : (Algebra.adjoin ℤ ({(ξ : K)} : Set K))ˣ,
      Units.map (algebraMap (Algebra.adjoin ℤ ({(ξ : K)} : Set K)) K :
        Algebra.adjoin ℤ ({(ξ : K)} : Set K) →* K) ξR = ξ := by
  refine ⟨Units.ofPowEqOne ⟨(ξ : K), Algebra.subset_adjoin (Set.mem_singleton _)⟩ n
    (Subtype.ext ?_) hn, Units.ext ?_⟩
  · simp [hξ.pow_eq_one]
  · rfl

private theorem algebraMap_adjoin_injective :
    Function.Injective (algebraMap (Algebra.adjoin ℤ ({(ξ : K)} : Set K)) K) :=
  fun _ _ h => Subtype.ext h

include hξ hn in

private theorem natCast_mem_nonunits_adjoin [Algebra ℚ K] (ℓ : ℕ) (hℓ : 1 < ℓ) :
    ((ℓ : Algebra.adjoin ℤ ({(ξ : K)} : Set K)) ∈ nonunits (Algebra.adjoin ℤ ({(ξ : K)} : Set K))) := by
  rw [mem_nonunits_iff]
  rintro ⟨u, hu⟩
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective

  have hs : (ℓ : K) * ((u⁻¹ : (Algebra.adjoin ℤ ({(ξ : K)} : Set K))ˣ) :
      Algebra.adjoin ℤ ({(ξ : K)} : Set K)) = 1 := by
    have h := congrArg (fun x : Algebra.adjoin ℤ ({(ξ : K)} : Set K) => (x : K)) (u.mul_inv)
    simpa [hu] using h
  have hint : IsIntegral ℤ (algebraMap ℚ K ((ℓ : ℚ)⁻¹)) := by
    rw [map_inv₀, map_natCast, ← eq_inv_of_mul_eq_one_right hs]
    exact isIntegral_of_mem_adjoin_root ξ hξ hn (u⁻¹).1.2
  have hint' : IsIntegral ℤ ((ℓ : ℚ)⁻¹) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K) (algebraMap ℚ K).injective).mp hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hz1 : (z : ℚ) * ℓ = 1 := by
    rw [eq_intCast] at hz
    rw [hz, inv_mul_cancel₀ (by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne')]
  have hzℓ : (ℓ : ℤ) * z = 1 := by rw [mul_comm]; exact_mod_cast hz1
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one z hzℓ) with h1 | h1 <;> omega

include hξ hn in

private theorem charP_quotient_adjoin_span_natCast [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    CharP (Algebra.adjoin ℤ ({(ξ : K)} : Set K) ⧸
      Ideal.span {(ℓ : Algebra.adjoin ℤ ({(ξ : K)} : Set K))}) ℓ :=
  CharP.quotient _ ℓ (natCast_mem_nonunits_adjoin ξ hξ hn ℓ hℓ.out.one_lt)

end RPackage

section Instantiated

open scoped IntermediateField

variable {K : Type*} [Field K] (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]
  (ξ : Kˣ) (hξ : IsPrimitiveRoot (ξ : K) (N * ℓ))

include hξ in

private theorem isIntegral_algebraMap_adjoin_root (r : Algebra.adjoin ℤ ({(ξ : K)} : Set K)) :
    IsIntegral ℤ (algebraMap (Algebra.adjoin ℤ ({(ξ : K)} : Set K)) K r) :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  isIntegral_of_mem_adjoin_root ξ hξ (NeZero.ne (N * ℓ)) r.2

variable [Algebra ℚ K]

include hξ in

private theorem payload_div_at_algHom_adjoin (hℓN : ¬ ℓ ∣ N) (dataℓ : ModularPolynomialData ℓ)
    (dataN : ModularPolynomialData N)
    (hC₁ : (jqN ℓ - jq ^ ℓ) * (jqN N - jqN (N * ℓ) ^ ℓ)
      ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)))
    (hC₂ : (jq - jqN ℓ ^ ℓ) * (jqN (N * ℓ) - jqN N ^ ℓ)
      ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))) :
    letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
      (((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
    ∀ τ : IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))
        →ₐ[ℚ⟮jq⟯] LaurentSeries K,
      (∃ B : LaurentSeries (Algebra.adjoin ℤ ({(ξ : K)} : Set K)),
          τ ⟨_, hC₁⟩ = (ℓ : LaurentSeries K) *
            coeffMap (algebraMap (Algebra.adjoin ℤ ({(ξ : K)} : Set K)) K) B) ∧
      (∃ B : LaurentSeries (Algebra.adjoin ℤ ({(ξ : K)} : Set K)),
          τ ⟨_, hC₂⟩ = (ℓ : LaurentSeries K) *
            coeffMap (algebraMap (Algebra.adjoin ℤ ({(ξ : K)} : Set K)) K) B) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  obtain ⟨ξR, hξR⟩ := exists_unit_adjoin_map_eq ξ hξ (NeZero.ne (N * ℓ))
  haveI := charP_quotient_adjoin_span_natCast ξ hξ (NeZero.ne (N * ℓ)) ℓ
  exact payload_div_at_algHom N ℓ ξ hξ (algebraMap (Algebra.adjoin ℤ ({(ξ : K)} : Set K)) K)
    ξR hξR hℓN dataℓ dataN hC₁ hC₂

end Instantiated

section SubMaster

variable {N ℓ : ℕ} [NeZero N] [NeZero ℓ] [Fact ℓ.Prime]
variable {K : Type*} [Field K] [Algebra ℚ K]
variable [Algebra (↥ℚ⟮jq⟯) (LaurentSeries K)]
variable {R : Type*} [CommRing R] (ιR : R →+* K)

omit [Fact (Nat.Prime ℓ)] in
private theorem subMaster

    (hι : algebraMap (↥ℚ⟮jq⟯) (LaurentSeries K)
        = ((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp
            (algebraMap (↥ℚ⟮jq⟯) (LaurentSeries ℚ)))

    (hθint : IsIntegral (↥ℚ⟮jq⟯) (jqN (N * ℓ)))

    {C : LaurentSeries ℚ}
    (hC : C ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)))
    (hCA : IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) C)

    (hpay : ∀ τ : IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))
          →ₐ[↥ℚ⟮jq⟯] LaurentSeries K,
        ∃ B : LaurentSeries R, τ ⟨C, hC⟩ = (ℓ : LaurentSeries K) * coeffMap ιR B)

    (hR : ∀ r : R, IsIntegral ℤ (ιR r))

    (S2 : ∀ {C' : LaurentSeries ℚ}
        (hC' : C' ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))),
        ∃ m : Multiset (LaurentSeries K),
          (minpoly (↥ℚ⟮jq⟯) C').map (algebraMap (↥ℚ⟮jq⟯) (LaurentSeries K))
              = (m.map fun v => Polynomial.X - Polynomial.C v).prod
            ∧ ∀ v ∈ m, ∃ τ : IntermediateField.adjoin ℚ⟮jq⟯
                  ({jqN (N * ℓ)} : Set (LaurentSeries ℚ)) →ₐ[↥ℚ⟮jq⟯] LaurentSeries K,
                τ ⟨C', hC'⟩ = v)
    (MLEM : ∀ {e : LaurentSeries ℚ}, e ∈ ℚ⟮jq⟯ →
        IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) e →
        ∃ P : Polynomial ℚ, e = Polynomial.aeval jq P)
    (DESC : ∀ (P : Polynomial ℚ), PhiGen.IntCoeffs (Polynomial.aeval jq P) →
        ∀ n : ℕ, ∃ z : ℤ, P.coeff n = (z : ℚ))
    (D2 : ∀ {s : K}, IsIntegral ℤ s → ∀ {q : ℚ}, algebraMap ℚ K q = s →
        ∃ z : ℤ, q = (z : ℚ))
    (G1 : ∀ {C' : LaurentSeries ℚ} (Q : Polynomial (Polynomial ℤ)), Q.Monic →
        (∀ i < Q.natDegree, ((ℓ : Polynomial ℤ)) ^ (Q.natDegree - i) ∣ Q.coeff i) →
        Q.eval₂ evalAtJ C' = 0 →
        IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
          ((ℓ : LaurentSeries ℚ)⁻¹ * C')) :
    IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
      ((ℓ : LaurentSeries ℚ)⁻¹ * C) := by
  classical

  have halg : Algebra.IsAlgebraic (↥ℚ⟮jq⟯)
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))) :=
    IntermediateField.isAlgebraic_adjoin fun s hs => by
      rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hθint
  have hkC : IsIntegral (↥ℚ⟮jq⟯) C := by
    have h1 := (halg.isAlgebraic ⟨C, hC⟩).isIntegral.map
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))).val
    simpa using h1
  set d := (minpoly (↥ℚ⟮jq⟯) C).natDegree with hd

  obtain ⟨m, hfac, hτs⟩ := S2 hC
  have hcard : Multiset.card m = d := by
    have h1 : ((minpoly (↥ℚ⟮jq⟯) C).map
        (algebraMap (↥ℚ⟮jq⟯) (LaurentSeries K))).natDegree = d :=
      (minpoly.monic hkC).natDegree_map _
    rw [hfac] at h1
    rwa [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1

  have hmB : ∀ v ∈ m, ∃ B : LaurentSeries R,
      v = (ℓ : LaurentSeries K) * coeffMap ιR B := by
    intro v hv
    obtain ⟨τ, hτ⟩ := hτs v hv
    obtain ⟨B, hB⟩ := hpay τ
    exact ⟨B, by rw [← hτ, hB]⟩

  obtain ⟨mB, hmBeq⟩ : ∃ mB : Multiset (LaurentSeries R),
      m = mB.map fun B => (ℓ : LaurentSeries K) * coeffMap ιR B := by
    have key : ∀ s : Multiset (LaurentSeries K),
        (∀ v ∈ s, ∃ B : LaurentSeries R, v = (ℓ : LaurentSeries K) * coeffMap ιR B) →
        ∃ mB : Multiset (LaurentSeries R),
          s = mB.map fun B => (ℓ : LaurentSeries K) * coeffMap ιR B := by
      intro s
      induction s using Multiset.induction with
      | empty => intro _; exact ⟨0, rfl⟩
      | cons a t ih =>
          intro h
          obtain ⟨B, hB⟩ := h a (Multiset.mem_cons_self a t)
          obtain ⟨mB, hmB2⟩ := ih fun v hv => h v (Multiset.mem_cons_of_mem hv)
          exact ⟨B ::ₘ mB, by rw [Multiset.map_cons, ← hB, ← hmB2]⟩
    exact key m hmB

  have hvieta : ∀ i, i < d →
      algebraMap (↥ℚ⟮jq⟯) (LaurentSeries K) ((minpoly (↥ℚ⟮jq⟯) C).coeff i)
        = (-1 : LaurentSeries K) ^ (d - i) * Multiset.esymm m (d - i) := by
    intro i hi
    have h2 : algebraMap (↥ℚ⟮jq⟯) (LaurentSeries K) ((minpoly (↥ℚ⟮jq⟯) C).coeff i)
        = ((minpoly (↥ℚ⟮jq⟯) C).map
            (algebraMap (↥ℚ⟮jq⟯) (LaurentSeries K))).coeff i :=
      (Polynomial.coeff_map _ _).symm
    rw [h2, hfac, Multiset.prod_X_sub_C_coeff m (by rw [hcard]; exact le_of_lt hi),
      hcard]

  have hscale : ∀ j : ℕ, Multiset.esymm m j
      = (ℓ : LaurentSeries K) ^ j * coeffMap ιR (Multiset.esymm mB j) := by
    intro j
    rw [hmBeq, Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map,
      Multiset.map_map]
    rw [map_multiset_sum (coeffMap ιR), Multiset.map_map,
      ← Multiset.sum_map_mul_left]
    refine congr_arg Multiset.sum (Multiset.map_congr rfl ?_)
    intro t ht
    simp only [Function.comp_apply]
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      (Multiset.mem_powersetCard.mp ht).2, ← map_multiset_prod (coeffMap ιR)]

  have hCmul : ∀ (c : K) (A : LaurentSeries K) (a : ℤ),
      (algebraMap K (LaurentSeries K) c * A).coeff a = c * A.coeff a := by
    intro c A a
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

  have hint_coeff : ∀ i : ℕ,
      IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (((minpoly (↥ℚ⟮jq⟯) C).coeff i : ↥ℚ⟮jq⟯) : LaurentSeries ℚ) := by

    letI : Algebra (↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))))
        (LaurentSeries K) :=
      (((coeffEmb K).comp (qExpand ℚ (N * ℓ))).comp
        ((Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))).val.toRingHom)).toAlgebra

    have hle : ∀ a : ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))),
        (a : LaurentSeries ℚ) ∈ ℚ⟮jq⟯ := by
      intro a
      have h1 : Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ ℚ⟮jq⟯.toSubalgebra :=
        Algebra.adjoin_le fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          exact IntermediateField.subset_adjoin ℚ {jq} (Set.mem_singleton jq)
      exact h1 a.2
    let incl : ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) →+* ↥ℚ⟮jq⟯ :=
      { toFun := fun a => ⟨(a : LaurentSeries ℚ), hle a⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let f₀ : ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        →+* ↥(IntermediateField.adjoin ℚ⟮jq⟯ ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))) :=
      (algebraMap (↥ℚ⟮jq⟯)
        (↥(IntermediateField.adjoin ℚ⟮jq⟯
          ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))))).comp incl

    obtain ⟨p₀, hp₀m, hp₀e⟩ := hCA
    have hvalcomp : (IntermediateField.adjoin ℚ⟮jq⟯
        ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))).val.toRingHom.comp f₀
        = algebraMap (↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))))
            (LaurentSeries ℚ) :=
      RingHom.ext fun a => rfl
    have hE0 : Polynomial.eval₂ f₀ ⟨C, hC⟩ p₀ = 0 := by
      apply RingHom.injective (IntermediateField.adjoin ℚ⟮jq⟯
        ({jqN (N * ℓ)} : Set (LaurentSeries ℚ))).val.toRingHom
      rw [map_zero, Polynomial.hom_eval₂, hvalcomp]
      exact hp₀e

    have hvint : ∀ v ∈ m, IsIntegral
        (↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) v := by
      intro v hv
      obtain ⟨τ, hτ⟩ := hτs v hv
      have hτcomp : τ.toRingHom.comp f₀
          = algebraMap (↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))))
              (LaurentSeries K) := by
        refine RingHom.ext fun a => ?_
        show τ (algebraMap (↥ℚ⟮jq⟯) _ (incl a)) = _
        rw [AlgHom.commutes, hι]
        rfl
      have h2 := congrArg τ.toRingHom hE0
      rw [map_zero] at h2
      rw [Polynomial.hom_eval₂] at h2
      rw [hτcomp] at h2
      have h5 : (τ.toRingHom) ⟨C, hC⟩ = v := hτ
      rw [h5] at h2
      exact ⟨p₀, hp₀m, h2⟩

    have hesym : ∀ j : ℕ, Multiset.esymm m j
        ∈ integralClosure (↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))))
          (LaurentSeries K) := by
      intro j
      rw [Multiset.esymm]
      refine Subalgebra.multiset_sum_mem _ fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
      refine Subalgebra.multiset_prod_mem _ fun v hv => ?_
      exact hvint v (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hv)

    let φL : LaurentSeries ℚ
        →ₐ[↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))] LaurentSeries K :=
      { toRingHom := (coeffEmb K).comp (qExpand ℚ (N * ℓ))
        commutes' := fun a => rfl }
    have hφLinj : Function.Injective φL := by
      intro x y hxy
      apply qExpand_injective (R := ℚ) (N := N * ℓ)
      have hcoeff : ∀ a : ℤ, (qExpand ℚ (N * ℓ) x).coeff a
          = (qExpand ℚ (N * ℓ) y).coeff a := by
        intro a
        have h4 := congrArg (fun t : LaurentSeries K => t.coeff a) hxy
        exact (algebraMap ℚ K).injective h4
      exact HahnSeries.coeff_inj.mp (funext hcoeff)
    intro i
    rcases lt_trichotomy i d with hi | hi | hi
    · have hφeq : φL (((minpoly (↥ℚ⟮jq⟯) C).coeff i : ↥ℚ⟮jq⟯) : LaurentSeries ℚ)
          = algebraMap (↥ℚ⟮jq⟯) (LaurentSeries K)
              ((minpoly (↥ℚ⟮jq⟯) C).coeff i) := by
        rw [hι]
        rfl
      have hΩ : IsIntegral (↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))))
          (φL (((minpoly (↥ℚ⟮jq⟯) C).coeff i : ↥ℚ⟮jq⟯) : LaurentSeries ℚ)) := by
        rw [hφeq, hvieta i hi]
        exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (hesym (d - i))
      exact (isIntegral_algHom_iff φL hφLinj).mp hΩ
    · have h1 : (minpoly (↥ℚ⟮jq⟯) C).coeff i = 1 := by
        have h2 := (minpoly.monic hkC).coeff_natDegree
        rwa [← hd, ← hi] at h2
      rw [h1]
      simpa using isIntegral_one
    · have h0' : (minpoly (↥ℚ⟮jq⟯) C).coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [hd] at hi)
      rw [h0']
      simpa using isIntegral_zero

  have hdvd_coeff : ∀ i < d, ∀ g : ℤ,
      ∃ z : ℤ, (((minpoly (↥ℚ⟮jq⟯) C).coeff i : ↥ℚ⟮jq⟯) : LaurentSeries ℚ).coeff g
        = ((-1 : ℚ) ^ (d - i) * (ℓ : ℚ) ^ (d - i)) * (z : ℚ) := by
    intro i hi g
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    have hcK0 : ((-1 : K) ^ (d - i) * (ℓ : K) ^ (d - i)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ)))
    have hcQ0 : ((-1 : ℚ) ^ (d - i) * (ℓ : ℚ) ^ (d - i)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ)))
    have hconsts : ∀ X' : LaurentSeries K,
        (-1 : LaurentSeries K) ^ (d - i) * ((ℓ : LaurentSeries K) ^ (d - i) * X')
          = algebraMap K (LaurentSeries K) ((-1 : K) ^ (d - i) * (ℓ : K) ^ (d - i))
              * X' := by
      intro X'
      rw [map_mul, map_pow, map_pow, map_neg, map_one, map_natCast]
      ring
    have h2 := hvieta i hi
    rw [hscale (d - i), ← mul_assoc, mul_assoc, hconsts, hι] at h2
    have h3 := congrArg
      (fun x : LaurentSeries K => x.coeff (((N * ℓ : ℕ) : ℤ) * g)) h2
    simp only [RingHom.comp_apply] at h3
    rw [coeffEmb_coeff, qExpand_coeff_mul, hCmul, coeffMap_coeff] at h3
    have h3' : algebraMap ℚ K
        ((((minpoly (↥ℚ⟮jq⟯) C).coeff i : ↥ℚ⟮jq⟯) : LaurentSeries ℚ).coeff g)
        = ((-1 : K) ^ (d - i) * (ℓ : K) ^ (d - i))
            * ιR ((Multiset.esymm mB (d - i)).coeff (((N * ℓ : ℕ) : ℤ) * g)) := h3
    have hs : IsIntegral ℤ
        (ιR ((Multiset.esymm mB (d - i)).coeff (((N * ℓ : ℕ) : ℤ) * g))) := hR _
    have hq : algebraMap ℚ K
        (((-1 : ℚ) ^ (d - i) * (ℓ : ℚ) ^ (d - i))⁻¹
          * (((minpoly (↥ℚ⟮jq⟯) C).coeff i : ↥ℚ⟮jq⟯) : LaurentSeries ℚ).coeff g)
        = ιR ((Multiset.esymm mB (d - i)).coeff (((N * ℓ : ℕ) : ℤ) * g)) := by
      rw [map_mul, h3', map_inv₀, map_mul, map_pow, map_pow, map_neg, map_one,
        map_natCast]
      exact inv_mul_cancel_left₀ hcK0 _
    obtain ⟨z, hz⟩ := D2 hs hq
    refine ⟨z, ?_⟩
    have h4 := congrArg
      (fun t : ℚ => ((-1 : ℚ) ^ (d - i) * (ℓ : ℚ) ^ (d - i)) * t) hz
    rwa [← mul_assoc, mul_inv_cancel₀ hcQ0, one_mul] at h4

  choose P hP using fun i => MLEM ((minpoly (↥ℚ⟮jq⟯) C).coeff i).2 (hint_coeff i)
  have hevalcast : ∀ T : Polynomial ℤ,
      Polynomial.aeval jq (T.map (Int.castRingHom ℚ)) = evalAtJ T := by
    intro T
    have hcomp : (Polynomial.aeval (R := ℚ) jq).toRingHom.comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = evalAtJ := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      show Polynomial.aeval jq ((Polynomial.X : Polynomial ℤ).map (Int.castRingHom ℚ))
          = evalAtJ Polynomial.X
      rw [Polynomial.map_X, Polynomial.aeval_X, evalAtJ_X]
    exact DFunLike.congr_fun hcomp T
  have hlift : ∀ T : Polynomial ℚ, (∀ n, ∃ z : ℤ, T.coeff n = (z : ℚ)) →
      ∃ Sz : Polynomial ℤ, Sz.map (Int.castRingHom ℚ) = T := by
    intro T hT
    choose z hz using hT
    refine ⟨∑ n ∈ T.support, Polynomial.monomial n (z n), ?_⟩
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff,
      Finset.sum_congr rfl fun n _ => Polynomial.coeff_monomial,
      Finset.sum_ite_eq' T.support k z]
    by_cases hk : k ∈ T.support
    · rw [if_pos hk]; exact (hz k).symm
    · rw [if_neg hk, map_zero,
        (Polynomial.notMem_support_iff.mp hk)]
  have hSex : ∀ i, ∃ Sz : Polynomial ℤ, i < d →
      P i = Polynomial.C ((-1 : ℚ) ^ (d - i) * (ℓ : ℚ) ^ (d - i))
          * Sz.map (Int.castRingHom ℚ) := by
    intro i
    by_cases hi : i < d
    · have hℓ0 : ((ℓ : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
      have hc0 : ((-1 : ℚ) ^ (d - i) * (ℓ : ℚ) ^ (d - i)) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hℓ0)
      have hTint : ∀ n, ∃ z : ℤ,
          (Polynomial.C ((-1 : ℚ) ^ (d - i) * (ℓ : ℚ) ^ (d - i))⁻¹ * P i).coeff n
            = (z : ℚ) := by
        refine DESC _ ?_
        intro g
        obtain ⟨z, hz⟩ := hdvd_coeff i hi g
        refine ⟨z, ?_⟩
        rw [map_mul, Polynomial.aeval_C]
        rw [algebraMap_laurentSeries_eq_single]
        rw [HahnSeries.coeff_single_zero_mul]
        rw [← hP i, hz]
        field_simp
      obtain ⟨Sz, hSz⟩ := hlift _ hTint
      refine ⟨Sz, fun _ => ?_⟩
      rw [hSz]
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc0, Polynomial.C_1, one_mul]
    · exact ⟨0, fun h => absurd h hi⟩
  choose Sz hSz using hSex
  set Q : Polynomial (Polynomial ℤ) := Polynomial.X ^ d
      + ∑ i ∈ Finset.range d, Polynomial.monomial i
          ((-1 : Polynomial ℤ) ^ (d - i) * (ℓ : Polynomial ℤ) ^ (d - i) * Sz i)
    with hQdef
  have hdegsum : (∑ i ∈ Finset.range d, Polynomial.monomial i
      ((-1 : Polynomial ℤ) ^ (d - i) * (ℓ : Polynomial ℤ) ^ (d - i) * Sz i)).degree
      < ((d : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    have hd0 : 0 < d := minpoly.natDegree_pos hkC
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun i hi =>
      lt_of_le_of_lt (Polynomial.degree_monomial_le i _)
        (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
  have hQmonic : Q.Monic := Polynomial.monic_X_pow_add hdegsum
  have hdegQ : Q.degree = ((d : ℕ) : WithBot ℕ) := by
    rw [hQdef, Polynomial.degree_add_eq_left_of_degree_lt
      (by rwa [Polynomial.degree_X_pow]), Polynomial.degree_X_pow]
  have hQdeg : Q.natDegree = d := Polynomial.natDegree_eq_of_degree_eq_some hdegQ
  have hQcoeff : ∀ k, Q.coeff k =
      (if k = d then 1 else 0)
        + (if k ∈ Finset.range d
            then (-1 : Polynomial ℤ) ^ (d - k) * (ℓ : Polynomial ℤ) ^ (d - k) * Sz k
            else 0) := by
    intro k
    rw [hQdef, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.finsetSum_coeff]
    congr 1
    rw [Finset.sum_congr rfl fun i _ => Polynomial.coeff_monomial]
    exact Finset.sum_ite_eq' _ _ _
  have hQdvd : ∀ i < Q.natDegree,
      ((ℓ : Polynomial ℤ)) ^ (Q.natDegree - i) ∣ Q.coeff i := by
    intro i hi
    rw [hQdeg] at hi
    rw [hQcoeff i, if_neg (ne_of_lt hi), if_pos (Finset.mem_range.mpr hi), zero_add,
      hQdeg]
    exact ⟨(-1 : Polynomial ℤ) ^ (d - i) * Sz i, by ring⟩
  have hQmap : Q.map evalAtJ
      = (minpoly (↥ℚ⟮jq⟯) C).map (algebraMap (↥ℚ⟮jq⟯) (LaurentSeries ℚ)) := by
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hQcoeff k]
    rcases lt_trichotomy k d with hk | hk | hk
    · rw [if_neg (ne_of_lt hk), if_pos (Finset.mem_range.mpr hk), zero_add]
      have hval : algebraMap (↥ℚ⟮jq⟯) (LaurentSeries ℚ) ((minpoly (↥ℚ⟮jq⟯) C).coeff k)
          = (((minpoly (↥ℚ⟮jq⟯) C).coeff k : ↥ℚ⟮jq⟯) : LaurentSeries ℚ) := rfl
      have hrhs : Polynomial.aeval jq (Polynomial.C ((-1 : ℚ) ^ (d - k) * (ℓ : ℚ) ^ (d - k))
          * (Sz k).map (Int.castRingHom ℚ))
          = algebraMap ℚ (LaurentSeries ℚ) ((-1 : ℚ) ^ (d - k) * (ℓ : ℚ) ^ (d - k))
              * evalAtJ (Sz k) := by
        rw [map_mul, Polynomial.aeval_C, hevalcast]
      rw [hval, hP k, hSz k hk, hrhs]
      simp [map_mul, map_pow]
    · rw [if_pos hk, if_neg (by simp [hk]), add_zero, map_one]
      have h1 : (minpoly (↥ℚ⟮jq⟯) C).coeff k = 1 := by
        have h2 := (minpoly.monic hkC).coeff_natDegree
        rwa [← hd, ← hk] at h2
      rw [h1, map_one]
    · rw [if_neg (ne_of_gt hk), if_neg (by simp [Nat.not_lt.mpr (le_of_lt hk)]),
        add_zero, map_zero,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [hd] at hk), map_zero]
  have h0 : Q.eval₂ evalAtJ C = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, hQmap, ← Polynomial.eval₂_eq_eval_map]
    have := minpoly.aeval (↥ℚ⟮jq⟯) C
    rwa [Polynomial.aeval_def] at this
  exact G1 Q hQmonic hQdvd h0

end SubMaster

theorem _root_.P2MW.S_ModularCurve_kroneckerPairIntegral.solution (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) :
    IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jqN ℓ - jq ^ ℓ) * qExpand ℚ N (jq - (jqN ℓ) ^ ℓ)))
      ∧ IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jq - (jqN ℓ) ^ ℓ) * qExpand ℚ N (jqN ℓ - jq ^ ℓ))) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  obtain ⟨ξ, hξ⟩ := exists_primitiveRoot_unit (N * ℓ)
  letI : Algebra (↥ℚ⟮jq⟯) (LaurentSeries (CyclotomicField (N * ℓ) ℚ)) :=
    (((coeffEmb (CyclotomicField (N * ℓ) ℚ)).comp (qExpand ℚ (N * ℓ))).comp
      (algebraMap (↥ℚ⟮jq⟯) (LaurentSeries ℚ))).toAlgebra
  obtain ⟨dataℓ, -⟩ := exists_phiIrreducible ℓ
  obtain ⟨dataN, -⟩ := exists_phiIrreducible N
  have hC₁ := mixedProd₁_mem_adjoin_adjoin_jq N ℓ
  have hC₂ := mixedProd₂_mem_adjoin_adjoin_jq N ℓ
  have hpay := payload_div_at_algHom_adjoin N ℓ ξ hξ hℓN dataℓ dataN hC₁ hC₂
  have hsp := splits_minpoly_jqN_map N ℓ ξ hξ
  have hθ := isIntegral_adjoin_field_jqN (N * ℓ)
  rw [qExpand_mixed₁ N ℓ, qExpand_mixed₂ N ℓ]
  refine ⟨?_, ?_⟩
  · exact subMaster
      (algebraMap (Algebra.adjoin ℤ ({(ξ : CyclotomicField (N * ℓ) ℚ)} :
        Set (CyclotomicField (N * ℓ) ℚ))) (CyclotomicField (N * ℓ) ℚ))
      rfl hθ hC₁ (isIntegral_adjoin_rat_mixedProd₁ N ℓ) (fun τ => (hpay τ).1)
      (isIntegral_algebraMap_adjoin_root N ℓ ξ hξ)
      (fun {C'} hC' => exists_multiset_minpoly_map_eq_prod_of_mem_adjoin hθ hsp hC')
      (fun {e} he hint => exists_aeval_eq_of_mem_adjoin_rat_of_isIntegral he hint)
      (fun P hP n => PhiGen.aeval_jq_intCoeffs_descent P hP n)
      (fun {s} hs {q} h => exists_intCast_of_algebraMap_eq_of_isIntegral hs h)
      (fun {C'} Q hm hd h0 => isIntegral_adjoin_jq_inv_mul_of_annihilator ℓ Q hm hd h0)
  · exact subMaster
      (algebraMap (Algebra.adjoin ℤ ({(ξ : CyclotomicField (N * ℓ) ℚ)} :
        Set (CyclotomicField (N * ℓ) ℚ))) (CyclotomicField (N * ℓ) ℚ))
      rfl hθ hC₂ (isIntegral_adjoin_rat_mixedProd₂ N ℓ) (fun τ => (hpay τ).2)
      (isIntegral_algebraMap_adjoin_root N ℓ ξ hξ)
      (fun {C'} hC' => exists_multiset_minpoly_map_eq_prod_of_mem_adjoin hθ hsp hC')
      (fun {e} he hint => exists_aeval_eq_of_mem_adjoin_rat_of_isIntegral he hint)
      (fun P hP n => PhiGen.aeval_jq_intCoeffs_descent P hP n)
      (fun {s} hs {q} h => exists_intCast_of_algebraMap_eq_of_isIntegral hs h)
      (fun {C'} Q hm hd h0 => isIntegral_adjoin_jq_inv_mul_of_annihilator ℓ Q hm hd h0)

example (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jqN ℓ - jq ^ ℓ) * qExpand ℚ N (jq - (jqN ℓ) ^ ℓ)))
      ∧ IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jq - (jqN ℓ) ^ ℓ) * qExpand ℚ N (jqN ℓ - jq ^ ℓ))) :=
  solution N ℓ hℓN

end ModularCurve

end
end S_ModularCurve_kroneckerPairIntegral
end P2MW
export P2MW.S_ModularCurve_kroneckerPairIntegral (solution)
