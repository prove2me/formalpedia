-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_finset_isStrict_and_kind_of_mem_support_heckeDivBar_single_of_reduce_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fdb1a97a-c4f4-594c-895b-8de20082f457

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Finite.Basic
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_isStrict_and_kind_of_mem_support_heckeDivBar_single_of_reduce_notMem
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply"

noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_qExpand ModularCurve.PlaceSpecialization"

namespace KindRespectingMoving

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem exists_of_mem_support_correspondence_single [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (v v' : Place K F) (n : ℤ)
    (h : v' ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n)).support) :
    ∃ R ∈ Place.fiberAlong φ hφ v, R.restrictAlong ψ hψ = v' := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum] at h
  obtain ⟨R, hR, hR'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
  rw [Divisor.pushforwardAlong_single] at hR'
  exact ⟨R, hR, (Finset.mem_singleton.mp (Finsupp.support_single_subset hR')).symm⟩

private theorem aeval_toRingHom_eq {R : Type*} [CommRing R] {inst : Algebra ℤ R} (x : R) :
    (@Polynomial.aeval ℤ R _ _ inst x).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom R) x :=
  Polynomial.ringHom_ext (fun n => by simp) (by simp)

private theorem map_eval₂_aeval {R S G : Type*} [CommRing R] [CommRing S] [FunLike G R S]
    [RingHomClass G R S] (f : G) (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    f (Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y)
      = Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) (f x)) (f y) := by
  have h := Polynomial.hom_eval₂ Φ (Polynomial.eval₂RingHom (Int.castRingHom R) x) (f : R →+* S) y
  rw [RingHom.coe_coe] at h
  rw [h]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp
  · simp

private theorem eval₂_aeval_eq_zero_of_map {R S G : Type*} [CommRing R] [CommRing S] [FunLike G R S]
    [RingHomClass G R S] (f : G) (hf : Function.Injective f) (Φ : Polynomial (Polynomial ℤ))
    (x y : R) (h : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) (f x)) (f y) = 0) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y = 0 :=
  hf (by rw [map_eval₂_aeval, map_zero]; exact h)

private theorem ne_zero_of_ord_pos (w : Place K F) {f : F} (h : 0 < w.ord f) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl _ h

private theorem mem_of_ord_pos' (w : Place K F) {f : F} (h : 0 < w.ord f) :
    f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := ne_zero_of_ord_pos w h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

private theorem ord_algebraMap' (w : Place K F) {c : K} (hc : c ≠ 0) :
    w.ord (algebraMap K F c) = 0 := by
  have hu : IsUnit (⟨algebraMap K F c, w.algebraMap_mem' c⟩ : w.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, w.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, w.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := w.ord_coe_unit u
  rwa [hu] at this

private theorem eq_of_ord_sub_algebraMap_pos (w : Place K F) (f : F) {c₁ c₂ : K}
    (h₁ : 0 < w.ord (f - algebraMap K F c₁)) (h₂ : 0 < w.ord (f - algebraMap K F c₂)) :
    c₁ = c₂ := by
  by_contra hne
  have hm₁ := (w.mem_maximalIdeal_iff_ord_pos (ne_zero_of_ord_pos w h₁)
    (mem_of_ord_pos' w h₁)).mpr h₁
  have hm₂ := (w.mem_maximalIdeal_iff_ord_pos (ne_zero_of_ord_pos w h₂)
    (mem_of_ord_pos' w h₂)).mpr h₂
  have hsub := Ideal.sub_mem _ hm₂ hm₁
  have hc : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  have hval : ((⟨f - algebraMap K F c₂, mem_of_ord_pos' w h₂⟩ : w.toValuationSubring)
        - ⟨f - algebraMap K F c₁, mem_of_ord_pos' w h₁⟩)
      = ⟨algebraMap K F (c₁ - c₂), w.algebraMap_mem' (c₁ - c₂)⟩ := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, map_sub]
    ring
  rw [hval] at hsub
  have hunit : IsUnit (⟨algebraMap K F (c₁ - c₂), w.algebraMap_mem' (c₁ - c₂)⟩ :
      w.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F (c₁ - c₂), w.algebraMap_mem' _⟩, ⟨algebraMap K F (c₁ - c₂)⁻¹, w.algebraMap_mem' _⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc))⟩, rfl⟩
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hsub)) hunit

private theorem ord_pos_iff_ord_restrictAlong_pos (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    0 < w.ord (φ f) ↔ 0 < (w.restrictAlong φ hφ).ord f := by
  have he : 0 < Place.ramificationIndexAlong φ w := by
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI := isIntegral_along φ hφ
    exact w.ramificationIndex_pos (F := F)
  rw [Place.ord_restrictAlong φ hφ w f]
  exact mul_pos_iff_of_pos_left (by exact_mod_cast he)

private theorem mem_of_eval₂_eq_zero (U : Place K F) (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    {x y : F} (hx : x ∈ U.toValuationSubring)
    (h : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom F) x) y = 0) : y ∈ U.toValuationSubring := by
  refine U.mem_of_eval_monic_eq_zero (P := Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x))
    (hΦ.map _) (fun i => ?_) (by rw [Polynomial.eval_map]; exact h)
  rw [Polynomial.coeff_map, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun k _ => mul_mem (intCast_mem _ _) (pow_mem hx _)

private theorem eval₂_eq_zero_of_residue_eq (U : Place K F) (Φ : Polynomial (Polynomial ℤ))
    {u w : F} (hu : u ∈ U.toValuationSubring) (hw : w ∈ U.toValuationSubring) {c d : K}
    (hc : IsLocalRing.residue U.toValuationSubring ⟨u, hu⟩ = algebraMap K U.ResidueField c)
    (hd : IsLocalRing.residue U.toValuationSubring ⟨w, hw⟩ = algebraMap K U.ResidueField d)
    (huw : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom F) u) w = 0) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom K) c) d = 0 := by
  have h0 : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom U.toValuationSubring)
      (⟨u, hu⟩ : U.toValuationSubring)) ⟨w, hw⟩ = 0 := by
    apply Subtype.val_injective
    have h := map_eval₂_aeval (algebraMap U.toValuationSubring F) Φ ⟨u, hu⟩ ⟨w, hw⟩
    simp only [ValuationSubring.algebraMap_apply] at h
    rw [huw] at h
    exact h
  have h1 := congrArg (IsLocalRing.residue U.toValuationSubring) h0
  rw [map_eval₂_aeval, map_zero, hc, hd, ← map_eval₂_aeval (algebraMap K U.ResidueField) Φ c d] at h1
  exact (map_eq_zero_iff _ (algebraMap K U.ResidueField).injective).mp h1

private theorem mem_valuationSubring_of_eval₂_eq_zero {L : Type*} [Field L] (A : ValuationSubring L)
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a : A) {b : L}
    (h : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom L) (a : L)) b = 0) : b ∈ A := by
  have hint : IsIntegral A b := by
    refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) a), hΦ.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap A L).comp (Polynomial.eval₂RingHom (Int.castRingHom A) a)
        = Polynomial.eval₂RingHom (Int.castRingHom L) (a : L) :=
      Polynomial.ringHom_ext (fun n => by simp) (by simp [ValuationSubring.algebraMap_apply])
    rw [hcomp]
    exact h
  obtain ⟨b', hb'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A)).mp hint
  rw [← hb']
  exact b'.2

end Generic

section Exceptional

open Polynomial

variable (κ : Type*) [Field κ]

private def phiBar (Φ : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial κ) :=
  Φ.map (mapRingHom (Int.castRingHom κ))

private def phiBarExpand (Φ : Polynomial (Polynomial ℤ)) (m : ℕ) : Polynomial (Polynomial κ) :=
  (phiBar κ Φ).map (expand κ m).toRingHom

private def resPoly (Φ : Polynomial (Polynomial ℤ)) (m : ℕ) : Polynomial κ :=
  resultant (phiBar κ Φ) (phiBarExpand κ Φ m) (phiBar κ Φ).natDegree
    (phiBarExpand κ Φ m).natDegree

variable {κ}

private theorem evalRingHom_comp_mapRingHom_intCast (a : κ) :
    (evalRingHom a).comp (mapRingHom (Int.castRingHom κ))
      = eval₂RingHom (Int.castRingHom κ) a :=
  Polynomial.ringHom_ext (fun n => by simp) (by simp)

private theorem evalRingHom_comp_expand (a : κ) (m : ℕ) :
    (evalRingHom a).comp (expand κ m).toRingHom = evalRingHom (a ^ m) :=
  Polynomial.ringHom_ext (fun c => by simp) (by simp [expand_X])

private theorem eval_map_phiBar (Φ : Polynomial (Polynomial ℤ)) (a b : κ) :
    ((phiBar κ Φ).map (evalRingHom a)).eval b = Φ.eval₂ (eval₂RingHom (Int.castRingHom _) a) b := by
  rw [phiBar, Polynomial.map_map, eval_map, evalRingHom_comp_mapRingHom_intCast]

private theorem eval_map_phiBarExpand (Φ : Polynomial (Polynomial ℤ)) (m : ℕ) (a b : κ) :
    ((phiBarExpand κ Φ m).map (evalRingHom a)).eval b
      = Φ.eval₂ (eval₂RingHom (Int.castRingHom _) (a ^ m)) b := by
  rw [phiBarExpand, Polynomial.map_map, evalRingHom_comp_expand, eval_map_phiBar]

private theorem phiBar_monic {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) : (phiBar κ Φ).Monic :=
  hΦ.map _

private theorem phiBarExpand_monic {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (m : ℕ) :
    (phiBarExpand κ Φ m).Monic :=
  (phiBar_monic hΦ).map _

private theorem resPoly_eval_eq_zero {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (m : ℕ)
    {a b : κ} (hab : Φ.eval₂ (eval₂RingHom (Int.castRingHom _) a) b = 0)
    (hab' : Φ.eval₂ (eval₂RingHom (Int.castRingHom _) (a ^ m)) b = 0) :
    (resPoly κ Φ m).eval a = 0 := by
  have hF0 : (phiBar κ Φ).map (evalRingHom a) ≠ 0 := ((phiBar_monic hΦ).map _).ne_zero
  have hncop : ¬ IsCoprime ((phiBar κ Φ).map (evalRingHom a))
      ((phiBarExpand κ Φ m).map (evalRingHom a)) := by
    rintro ⟨u, v, huv⟩
    have h := congrArg (Polynomial.eval b) huv
    rw [eval_add, eval_mul, eval_mul, eval_map_phiBar, eval_map_phiBarExpand, hab, hab',
      mul_zero, mul_zero, add_zero, eval_one] at h
    exact zero_ne_one h
  have h := resultant_eq_zero_iff.mpr ⟨Or.inl hF0, hncop⟩
  rw [((phiBar_monic (κ := κ) hΦ)).natDegree_map, (phiBarExpand_monic (κ := κ) hΦ m).natDegree_map,
    resultant_map_map] at h
  exact h

private theorem exists_natDegree_coeff_ne_zero [IsAlgClosed κ] {Φ : Polynomial (Polynomial ℤ)}
    (hΦ : Φ.Monic) (h2 : 2 ≤ Φ.natDegree)
    (hirr : Irreducible ((phiBar κ Φ).map (algebraMap (Polynomial κ) (RatFunc κ)))) :
    ∃ i, ((phiBar κ Φ).coeff i).natDegree ≠ 0 := by
  by_contra hall
  push Not at hall

  set p₀ : Polynomial κ := (phiBar κ Φ).map (evalRingHom 0) with hp₀
  have hF : phiBar κ Φ = p₀.map (C : κ →+* Polynomial κ) := by
    ext i : 1
    rw [coeff_map, coeff_map, coe_evalRingHom, ← coeff_zero_eq_eval_zero]
    exact eq_C_of_natDegree_eq_zero (hall i)
  have hp₀m : p₀.Monic := (phiBar_monic hΦ).map _
  have hdeg : p₀.natDegree = Φ.natDegree := by
    rw [hp₀, (phiBar_monic (κ := κ) hΦ).natDegree_map, phiBar, hΦ.natDegree_map]

  have hp₀0 : p₀.degree ≠ 0 := by
    rw [degree_eq_natDegree hp₀m.ne_zero, hdeg]
    exact_mod_cast (show Φ.natDegree ≠ 0 by omega)
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_root p₀ hp₀0
  set g : κ →+* RatFunc κ := (algebraMap (Polynomial κ) (RatFunc κ)).comp C with hg
  have hmap : (phiBar κ Φ).map (algebraMap (Polynomial κ) (RatFunc κ)) = p₀.map g := by
    rw [hF, Polynomial.map_map]
  rw [hmap] at hirr
  have h1 : (p₀.map g).natDegree = 1 :=
    natDegree_eq_of_degree_eq_some (n := 1) (degree_eq_one_of_irreducible_of_root hirr (hρ.map (f := g)))
  rw [hp₀m.natDegree_map, hdeg] at h1
  omega

private theorem resPoly_ne_zero [IsAlgClosed κ] {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    (h2 : 2 ≤ Φ.natDegree) {m : ℕ} (hm : 1 < m)
    (hirr : Irreducible ((phiBar κ Φ).map (algebraMap (Polynomial κ) (RatFunc κ)))) :
    resPoly κ Φ m ≠ 0 := by
  intro hr
  have hinj : Function.Injective (algebraMap (Polynomial κ) (RatFunc κ)) :=
    IsFractionRing.injective (Polynomial κ) (RatFunc κ)
  have hFm : (phiBar κ Φ).Monic := phiBar_monic hΦ
  have hGm : (phiBarExpand κ Φ m).Monic := phiBarExpand_monic hΦ m

  have hne : phiBar κ Φ ≠ phiBarExpand κ Φ m := by
    intro h
    obtain ⟨i, hi⟩ := exists_natDegree_coeff_ne_zero hΦ h2 hirr
    have hc := congrArg (fun p : Polynomial (Polynomial κ) => (p.coeff i).natDegree) h
    simp only [phiBarExpand, coeff_map] at hc
    rw [show (expand κ m).toRingHom ((phiBar κ Φ).coeff i) = expand κ m ((phiBar κ Φ).coeff i) from rfl,
      natDegree_expand] at hc
    exact hi (eq_zero_of_mul_eq_self_right hm.ne' hc.symm)
  have hne' : (phiBar κ Φ).map (algebraMap _ (RatFunc κ))
      ≠ (phiBarExpand κ Φ m).map (algebraMap _ (RatFunc κ)) :=
    fun h => hne (map_injective _ hinj h)
  have hndvd : ¬ (phiBar κ Φ).map (algebraMap _ (RatFunc κ))
      ∣ (phiBarExpand κ Φ m).map (algebraMap _ (RatFunc κ)) := fun hd =>
    hne' (eq_of_monic_of_dvd_of_natDegree_le (hFm.map _) (hGm.map _) hd (by
      rw [hGm.natDegree_map, hFm.natDegree_map]
      unfold phiBarExpand
      rw [hFm.natDegree_map])).symm
  have hcop := (hirr.coprime_iff_not_dvd).mpr hndvd
  have hres := resultant_ne_zero _ _ hcop
  rw [hFm.natDegree_map (algebraMap _ (RatFunc κ)), hGm.natDegree_map (algebraMap _ (RatFunc κ)),
    resultant_map_map] at hres
  unfold resPoly at hr
  rw [hr, map_zero] at hres
  exact hres rfl

end Exceptional

private abbrev jBar (M : ℕ) [NeZero M] : modularFunctionFieldBar M :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M (jq_mem M))⟩

private theorem jBar_coe (M : ℕ) [NeZero M] :
    ((jBar M : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) jq := rfl

private theorem heckeAlphaBar_jBar (M ℓ : ℕ) [NeZero M] [NeZero ℓ] :
    heckeAlphaBar (AlgebraicClosure ℚ) M ℓ (jBar M) = jBar (M * ℓ) :=
  Subtype.ext (by simp)

private theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

private theorem qExpand_comm {R : Type*} [CommRing R] (a b : ℕ) [NeZero a] [NeZero b]
    (f : LaurentSeries R) : qExpand R a (qExpand R b f) = qExpand R b (qExpand R a f) := by
  rw [qExpand_qExpand, qExpand_qExpand]
  have key : ∀ (m m' : ℕ) (_ : NeZero m) (_ : NeZero m'), m = m' → qExpand R m f = qExpand R m' f := by
    rintro m m' _ _ rfl
    rfl
  exact key _ _ _ _ (mul_comm a b)

private theorem modular_relations_series (ℓ : ℕ) [NeZero ℓ] (dℓ : ModularPolynomialData ℓ)
    (hsym : EvalSymm dℓ.Φ) (n : ℕ) [NeZero n] :
    let x := qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) jq)
    dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (qExpand (AlgebraicClosure ℚ) ℓ x)) x = 0 ∧
      dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) x) (qExpand (AlgebraicClosure ℚ) ℓ x)
        = 0 := by
  intro x

  have h0 : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) jq) (qExpand ℚ ℓ jq) = 0 := by
    have h := dℓ.eval_eq_zero
    rwa [show evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom _) jq from aeval_toRingHom_eq jq] at h
  have h0' : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (qExpand ℚ ℓ jq)) jq = 0 := by
    have h := hsym jq (qExpand ℚ ℓ jq)
    rw [aeval_toRingHom_eq, aeval_toRingHom_eq] at h
    exact h.symm.trans h0

  have h1 := congrArg (coeffEmb (AlgebraicClosure ℚ)) h0
  have h1' := congrArg (coeffEmb (AlgebraicClosure ℚ)) h0'
  rw [map_eval₂_aeval, map_zero, coeffEmb_qExpand] at h1 h1'

  have h2 := congrArg (qExpand (AlgebraicClosure ℚ) n) h1
  have h2' := congrArg (qExpand (AlgebraicClosure ℚ) n) h1'
  rw [map_eval₂_aeval, map_zero, qExpand_comm] at h2 h2'
  exact ⟨h2', h2⟩

private theorem modular_relations (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (dℓ : ModularPolynomialData ℓ)
    (hsym : EvalSymm dℓ.Φ) (n : ℕ) [NeZero n] (g : modularFunctionFieldBar M)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ))
      = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) jq)) :
    dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (heckeBetaBar (AlgebraicClosure ℚ) M ℓ g))
        (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ g) = 0 ∧
      dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ g))
        (heckeBetaBar (AlgebraicClosure ℚ) M ℓ g) = 0 := by
  obtain ⟨h, h'⟩ := modular_relations_series ℓ dℓ hsym n
  refine ⟨eval₂_aeval_eq_zero_of_map (modularFunctionFieldBar (M * ℓ)).val.toRingHom
      (RingHom.injective _) dℓ.Φ _ _ ?_,
    eval₂_aeval_eq_zero_of_map (modularFunctionFieldBar (M * ℓ)).val.toRingHom
      (RingHom.injective _) dℓ.Φ _ _ ?_⟩
  · simpa [hg] using h
  · simpa [hg] using h'

private theorem exists_value_of_mem_support_heckeDivBar (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (dℓ : ModularPolynomialData ℓ)
    (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M ℓ)
    (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (M * ℓ))]
    (g : modularFunctionFieldBar M)
    (hrel : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _)
      (heckeBetaBar (AlgebraicClosure ℚ) M ℓ g)) (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ g)
        = 0)
    (hrel' : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _)
      (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ g)) (heckeBetaBar (AlgebraicClosure ℚ) M ℓ g)
        = 0)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (V V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (hV' : V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).support)
    (a : A) (ha : 0 < V.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) a)) :
    ∃ b : A, 0 < V'.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) b) ∧
      dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) a) b = 0 ∧
      dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) b) a = 0 := by
  classical

  obtain ⟨U, hU, hUV'⟩ := exists_of_mem_support_correspondence_single _ _ hβℓ hαℓ V V' 1 hV'
  have hUV : U.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) M ℓ) hβℓ = V :=
    Place.mem_fiberAlong.mp hU

  set x := heckeBetaBar (AlgebraicClosure ℚ) M ℓ g with hx_def
  set y := heckeAlphaBar (AlgebraicClosure ℚ) M ℓ g with hy_def

  have hx : 0 < U.ord (x - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) := by
    have h := (ord_pos_iff_ord_restrictAlong_pos (heckeBetaBar (AlgebraicClosure ℚ) M ℓ) hβℓ U
      (g - algebraMap _ _ (a : AlgebraicClosure ℚ))).mpr (hUV ▸ ha)
    rwa [map_sub, AlgHom.commutes] at h
  have hxmem : x ∈ U.toValuationSubring := by
    have h1 := mem_of_ord_pos' U hx
    have h2 : algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ∈ U.toValuationSubring :=
      U.algebraMap_mem' _
    simpa using add_mem h1 h2

  have hymem : y ∈ U.toValuationSubring := mem_of_eval₂_eq_zero U dℓ.Φ dℓ.monic hxmem hrel

  have hdeg : U.deg = 1 := deg_eq_one_modularFunctionFieldBar (M * ℓ) U
  haveI : Module.Finite (AlgebraicClosure ℚ) U.ResidueField :=
    Module.finite_of_finrank_eq_succ (n := 0)
      (hdeg : Module.finrank (AlgebraicClosure ℚ) U.ResidueField = 1)
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) U.ResidueField := Algebra.IsIntegral.of_finite _ _
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) U.ResidueField) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ)).2

  obtain ⟨b, ⟨hyb, hresb⟩, -⟩ := U.exists_hasValue_of_surjective hsurj hymem

  obtain ⟨h0a, hresa0⟩ := U.hasValue_algebraMap (a : AlgebraicClosure ℚ)
  have hresa : IsLocalRing.residue U.toValuationSubring ⟨x, hxmem⟩
      = algebraMap (AlgebraicClosure ℚ) U.ResidueField (a : AlgebraicClosure ℚ) := by
    rw [← hresa0, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (U.mem_maximalIdeal_iff_ord_pos (ne_zero_of_ord_pos U hx) (mem_of_ord_pos' U hx)).mpr hx

  have hab : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (a : AlgebraicClosure ℚ)) b = 0 :=
    eval₂_eq_zero_of_residue_eq U dℓ.Φ hxmem hyb hresa hresb hrel
  have hba : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) b) (a : AlgebraicClosure ℚ) = 0 :=
    eval₂_eq_zero_of_residue_eq U dℓ.Φ hyb hxmem hresb hresa hrel'

  have hbA : b ∈ A := mem_valuationSubring_of_eval₂_eq_zero A dℓ.Φ dℓ.monic a hab

  have hyb' : 0 < U.ord (y - algebraMap (AlgebraicClosure ℚ) _ b) := by
    obtain ⟨h0b, hresb0⟩ := U.hasValue_algebraMap b
    have hm : (⟨y, hyb⟩ : U.toValuationSubring) - ⟨_, h0b⟩
        ∈ IsLocalRing.maximalIdeal U.toValuationSubring := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hresb, hresb0, sub_self]
    have hne : y - algebraMap (AlgebraicClosure ℚ) _ b ≠ 0 := by
      intro h
      have hj : g = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) b := by
        have h' : heckeAlphaBar (AlgebraicClosure ℚ) M ℓ g
            = heckeAlphaBar (AlgebraicClosure ℚ) M ℓ (algebraMap _ _ b) := by
          rw [AlgHom.commutes]; exact sub_eq_zero.mp h
        exact (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ).toRingHom.injective h'
      rw [hj, ← map_sub] at ha
      rcases eq_or_ne (b - (a : AlgebraicClosure ℚ)) 0 with h0 | h0
      · rw [h0, map_zero, Place.ord_zero] at ha
        exact lt_irrefl _ ha
      · rw [ord_algebraMap' V h0] at ha
        exact lt_irrefl _ ha
    exact (U.mem_maximalIdeal_iff_ord_pos hne (sub_mem hyb h0b)).mp hm
  refine ⟨⟨b, hbA⟩, ?_, ?_, ?_⟩
  · have h := (ord_pos_iff_ord_restrictAlong_pos (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ) hαℓ U
      (g - algebraMap _ _ b)).mp (by rwa [map_sub, AlgHom.commutes])
    rwa [hUV'] at h
  · exact eval₂_aeval_eq_zero_of_map (algebraMap A (AlgebraicClosure ℚ)) Subtype.val_injective
      dℓ.Φ a ⟨b, hbA⟩ hab
  · exact eval₂_aeval_eq_zero_of_map (algebraMap A (AlgebraicClosure ℚ)) Subtype.val_injective
      dℓ.Φ ⟨b, hbA⟩ a hba

end KindRespectingMoving

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
open KindRespectingMoving in

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
          ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))],
          ∃ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
            ∀ V V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
              P.reduceFst V ∉ T → P.reduceSnd V ∉ T →
              V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V (1 : ℤ))).support →
                (P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
                (P.IsStrictFst V → P.IsStrictFst V') ∧
                (P.IsStrictSnd V → P.IsStrictSnd V') := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro data hKr hα hβ P ℓ hℓq
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  intro hαℓ hβℓ _
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hℓκ : ((ℓ : ℕ) : ResidueField A) ≠ 0 := by
    intro h
    have hd : q ∣ (ℓ : ℕ) := (CharP.cast_eq_zero_iff (ResidueField A) q _).mp h
    exact hℓq ((Nat.prime_dvd_prime_iff_eq hq ℓ.2).mp hd).symm
  have hq1 : 1 < q := hq.one_lt
  have hq2 : 1 < q ^ 2 := lt_of_lt_of_le hq1 (Nat.le_self_pow two_ne_zero q)

  haveI : HasPrincipalDivisors (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField (ResidueField A) N

  obtain ⟨dℓ, hsym⟩ := ModularCurve.exists_modularPolynomialData_evalSymm (ℓ : ℕ)
  have hpsi : 2 ≤ dℓ.Φ.natDegree := by
    rw [dℓ.natDegree_eq, dedekindPsi]
    refine le_trans (Nat.succ_le_of_lt ℓ.2.one_lt) ?_
    have h1 : (1 : ℕ) ∈ (Nat.divisors (ℓ : ℕ)).filter Squarefree :=
      Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr ℓ.2.ne_zero, squarefree_one⟩
    simpa using Finset.single_le_sum (f := fun d => (ℓ : ℕ) / d) (fun _ _ => Nat.zero_le _) h1
  have hrel₁ := modular_relations (N * q) ℓ dℓ hsym 1 (jBar (N * q)) (by
    rw [jBar_coe, qExpand_one_apply])
  have hrel₂ := modular_relations (N * q) ℓ dℓ hsym q
    (heckeBetaBar (AlgebraicClosure ℚ) N q (jBar N)) (by simp)
  classical

  obtain ⟨Rset, hRfix, hRexc, hRexc'⟩ : ∃ Rset : Finset (ResidueField A),
      (∀ a b : ResidueField A, b ^ (q ^ 2) = b →
        dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) b) a = 0 → a ∈ Rset) ∧
      (∀ a b : ResidueField A, dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) a) b = 0 →
        dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (a ^ (q ^ 2))) b = 0 → a ∈ Rset) ∧
      (∀ a b : ResidueField A, dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) a) b = 0 →
        dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (a ^ (q ^ 2))) b = 0 →
          a ^ (q ^ 2) ∈ Rset) := by
    have hirr := ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero
      (ResidueField A) (ℓ : ℕ) dℓ hℓκ
    have hres : resPoly (ResidueField A) dℓ.Φ (q ^ 2) ≠ 0 := resPoly_ne_zero dℓ.monic hpsi hq2 hirr
    have hE : ∀ a b : ResidueField A,
        dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) a) b = 0 →
        dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (a ^ (q ^ 2))) b = 0 →
          a ∈ (resPoly (ResidueField A) dℓ.Φ (q ^ 2)).roots.toFinset := fun a b hab hab' =>
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hres).mpr (resPoly_eval_eq_zero dℓ.monic _ hab hab'))
    refine ⟨((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial (ResidueField A)).roots.toFinset.biUnion
        fun b => ((phiBar (ResidueField A) dℓ.Φ).map (Polynomial.evalRingHom b)).roots.toFinset) ∪
      (resPoly (ResidueField A) dℓ.Φ (q ^ 2)).roots.toFinset ∪
      ((resPoly (ResidueField A) dℓ.Φ (q ^ 2)).roots.toFinset.image fun a => a ^ (q ^ 2)),
      fun a b hb hab => ?_, fun a b hab hab' => ?_, fun a b hab hab' => ?_⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨b, ?_, ?_⟩))
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_pow_sub_X_ne_zero
          (K' := ResidueField A) two_ne_zero hq1), Polynomial.IsRoot.def, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, hb, sub_self]
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots (((phiBar_monic dℓ.monic).map _).ne_zero),
          Polynomial.IsRoot.def, eval_map_phiBar, hab]
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hE a b hab hab'))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, hE a b hab hab', rfl⟩)

  obtain ⟨T, hTpole, hTval⟩ :
      ∃ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
        (∀ t, t.ord (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
            modularFunctionFieldC (ResidueField A) N) < 0 → t ∈ T) ∧
        (∀ t, ∀ a₀ ∈ Rset, 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
            modularFunctionFieldC (ResidueField A) N)
              - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) a₀) → t ∈ T) := by
    have hfin : ∀ f : modularFunctionFieldC (ResidueField A) N, f ≠ 0 →
        {t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) | t.ord f ≠ 0}.Finite :=
      fun f hf => by
        obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) f hf
        refine Df.support.finite_toSet.subset fun t ht => ?_
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hDf]
        exact ht
    have hj0 : (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
        modularFunctionFieldC (ResidueField A) N) ≠ 0 := by
      have h := jGeomGen_sub_algebraMap_ne_zero (ResidueField A) N 0
      rwa [map_zero, sub_zero] at h
    set S : Set (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) :=
      {t | t.ord (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N) ≠ 0} ∪
        ⋃ a₀ ∈ (Rset : Set (ResidueField A)),
          {t | t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
              modularFunctionFieldC (ResidueField A) N)
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) a₀) ≠ 0} with hS
    have hSfin : S.Finite :=
      (hfin _ hj0).union (Set.Finite.biUnion Rset.finite_toSet fun a₀ _ =>
        hfin _ (jGeomGen_sub_algebraMap_ne_zero (ResidueField A) N a₀))
    refine ⟨hSfin.toFinset, fun t ht => hSfin.mem_toFinset.mpr (Or.inl (ne_of_lt ht)),
      fun t a₀ ha₀ ht => hSfin.mem_toFinset.mpr (Or.inr ?_)⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr ha₀) (ne_of_gt ht)

  refine ⟨T, ?_⟩
  intro V V' hVT₁ hVT₂ hV'

  have hkind : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      frobOnPlacesGeomLevel (ResidueField A) N data hKr
          (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')) ≠ P.reduceFst V' →
        P.IsStrictFst V' ∨ P.IsStrictSnd V' := by
    intro V' hnf
    rcases P.d1 V' with h | h
    · right
      have h' : P.reduceFst V'
          = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V') := h
      refine ⟨h', fun hfix => hnf ?_⟩
      rw [h', hfix]
    · left
      exact ⟨h, hnf⟩

  have hval_frob : ∀ (t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
      (c : ResidueField A),
      0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
        - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) →
      0 < (frobOnPlacesGeomLevel (ResidueField A) N data hKr t).ord
          ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
              modularFunctionFieldC (ResidueField A) N)
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c ^ q)) := by
    intro t c ht
    have hs : arithFrobC q (ResidueField A) N •
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
            modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c)
        = (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
            modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c ^ q) := by
      rw [SemilinearAut.smul_def, map_sub, ← SemilinearAut.smul_def, ← SemilinearAut.smul_def,
        arithFrobC_smul_jq, SemilinearAut.smul_algebraMap, baseAut_arithFrobC_apply]
    have h := SemilinearAut.ord_smul (arithFrobC q (ResidueField A) N) t
      ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
        - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c)
    rw [hs, ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q (ResidueField A) N data hKr t]
      at h
    rw [h]
    exact ht

  have hvalV :
      (∃ a : A, 0 < (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) ∧
      (∃ c : A, 0 < (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c : AlgebraicClosure ℚ))) := by
    constructor
    · by_contra h
      push Not at h
      exact hVT₁ (hTpole _ (P.d0_j_pole _ h))
    · by_contra h
      push Not at h
      exact hVT₂ (hTpole _ (P.d0_j_pole _ h))

  have hlift : ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (a : A),
      0 < (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ↔
      0 < V.ord (jBar (N * q)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
    intro V a
    rw [← ord_pos_iff_ord_restrictAlong_pos (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V, map_sub,
      AlgHom.commutes, heckeAlphaBar_jBar]
  have hliftβ : ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (c : A),
      0 < (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c : AlgebraicClosure ℚ)) ↔
      0 < V.ord (heckeBetaBar (AlgebraicClosure ℚ) N q (jBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) := by
    intro V c
    rw [← ord_pos_iff_ord_restrictAlong_pos (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V, map_sub,
      AlgHom.commutes]

  have hredκ : ∀ u w : A, dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) u) w = 0 →
      dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (IsLocalRing.residue A u))
        (IsLocalRing.residue A w) = 0 := fun u w h => by
    have h' := congrArg (IsLocalRing.residue A) h
    rwa [map_eval₂_aeval, map_zero] at h'

  have hstep : frobOnPlacesGeomLevel (ResidueField A) N data hKr
      (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')) ≠ P.reduceFst V' := by
    intro hfix
    obtain ⟨⟨a, ha⟩, -⟩ := hvalV
    obtain ⟨b, hb, -, hba⟩ := exists_value_of_mem_support_heckeDivBar (N * q) ℓ dℓ hαℓ hβℓ
      (jBar (N * q)) hrel₁.1 hrel₁.2 A V V' hV' a ((hlift V a).mp ha)
    have hta : 0 < (P.reduceFst V).ord
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A a)) := P.d0_j _ a ha
    have htb : 0 < (P.reduceFst V').ord
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A b)) := P.d0_j _ b ((hlift V' b).mpr hb)

    have hfixval := hval_frob _ _ (hval_frob _ _ htb)
    rw [hfix] at hfixval
    have hbq : IsLocalRing.residue A b ^ (q ^ 2) = IsLocalRing.residue A b := by
      have h := eq_of_ord_sub_algebraMap_pos _ _ hfixval htb
      rwa [← pow_mul, ← sq] at h

    exact hVT₁ (hTval _ _ (hRfix _ _ hbq (hredκ _ _ hba)) hta)

  have hKT :
      (P.IsStrictFst V → (P.IsStrictFst V' ∨ P.IsStrictSnd V') → P.IsStrictFst V') ∧
      (P.IsStrictSnd V → (P.IsStrictFst V' ∨ P.IsStrictSnd V') → P.IsStrictSnd V') := by
    obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := hvalV
    obtain ⟨b, hb, hab, -⟩ := exists_value_of_mem_support_heckeDivBar (N * q) ℓ dℓ hαℓ hβℓ
      (jBar (N * q)) hrel₁.1 hrel₁.2 A V V' hV' a ((hlift V a).mp ha)
    obtain ⟨b', hb', hcb', -⟩ := exists_value_of_mem_support_heckeDivBar (N * q) ℓ dℓ hαℓ hβℓ
      (heckeBetaBar (AlgebraicClosure ℚ) N q (jBar N)) hrel₂.1 hrel₂.2 A V V' hV' c ((hliftβ V c).mp hc)

    have hta : 0 < (P.reduceFst V).ord
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A a)) := P.d0_j _ a ha
    have hsc : 0 < (P.reduceSnd V).ord
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c)) := P.d0_j _ c hc
    have htb : 0 < (P.reduceFst V').ord
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A b)) := P.d0_j _ b ((hlift V' b).mpr hb)
    have hsb' : 0 < (P.reduceSnd V').ord
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
          modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A b')) := P.d0_j _ b' ((hliftβ V' b').mpr hb')
    have habκ := hredκ _ _ hab
    have hcb'κ := hredκ _ _ hcb'
    refine ⟨fun hF hk => hk.elim id fun hS' => ?_, fun hS hk => hk.elim (fun hF' => ?_) id⟩
    ·
      exfalso
      have h1 := hval_frob _ _ hta
      rw [hF.1] at h1
      have hca : IsLocalRing.residue A c = IsLocalRing.residue A a ^ q :=
        eq_of_ord_sub_algebraMap_pos _ _ hsc h1
      have h2 := hval_frob _ _ hsb'
      rw [← hS'.1] at h2
      have hbb' : IsLocalRing.residue A b = IsLocalRing.residue A b' ^ q :=
        eq_of_ord_sub_algebraMap_pos _ _ htb h2
      have h3 := congrArg (frobenius (ResidueField A) q) hcb'κ
      rw [map_eval₂_aeval, map_zero, frobenius_def, frobenius_def, hca, ← hbb', ← pow_mul, ← sq] at h3
      exact hVT₁ (hTval _ _ (hRexc _ _ habκ h3) hta)
    ·

      exfalso
      have h1 := hval_frob _ _ hsc
      rw [← hS.1] at h1
      have hac : IsLocalRing.residue A a = IsLocalRing.residue A c ^ q :=
        eq_of_ord_sub_algebraMap_pos _ _ hta h1
      have h2 := hval_frob _ _ htb
      rw [hF'.1] at h2
      have hb'b : IsLocalRing.residue A b' = IsLocalRing.residue A b ^ q :=
        eq_of_ord_sub_algebraMap_pos _ _ hsb' h2
      have h3 := congrArg (frobenius (ResidueField A) q) hcb'κ
      rw [map_eval₂_aeval, map_zero, frobenius_def, frobenius_def, ← hac, hb'b, ← pow_mul, ← sq] at h3
      obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (IsLocalRing.residue A a) (pow_pos hq.pos 2)
      have h4 : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) ρ) (IsLocalRing.residue A b)
          = 0 := by
        apply iterateFrobenius_inj (ResidueField A) q 2
        rw [map_eval₂_aeval, map_zero, iterateFrobenius_def, iterateFrobenius_def, hρ]
        exact h3
      have h5 : dℓ.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (ρ ^ (q ^ 2)))
          (IsLocalRing.residue A b) = 0 := by
        rw [hρ]
        exact habκ
      have hmem := hRexc' _ _ h4 h5
      rw [hρ] at hmem
      exact hVT₁ (hTval _ _ hmem hta)
  have hstrict : P.IsStrictFst V' ∨ P.IsStrictSnd V' := hkind V' hstep
  exact ⟨hstrict, fun hF => hKT.1 hF hstrict, fun hS => hKT.2 hS hstrict⟩

#print axioms solution

end
end S_ModularCurve_PlaceSpecialization_exists_finset_isStrict_and_kind_of_mem_support_heckeDivBar_single_of_reduce_notMem
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_isStrict_and_kind_of_mem_support_heckeDivBar_single_of_reduce_notMem (solution)
