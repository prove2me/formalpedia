-- Prove2me | solution 1 for ModularCurve.kroneckerCoordinatewiseDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5d1fac22-9265-53ab-ab50-a6fc4463fd9e

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kroneckerCoordinatewiseDichotomy
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

namespace ModularCurve
p2m_export "ModularCurve" "heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr qExpand_qExpand jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange fibrePoly jqModC jqNModC jqNModC_one kroneckerCongruence_of_prime fibrePoly_eq_of_kroneckerCongruence exists_kroneckerCongruence_of_prime coeffEmb_jq coeffEmb_qExpand EvalSymm exists_modularPolynomialData_evalSymm"
p2m_open "ModularCurve"

open AlgebraicCurve Polynomial IsLocalRing

section VLayer

section ValueCalculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem mem_toValuationSubring_of_ord_pos {g : F} (h : 0 < v.ord g) :
    g ∈ v.toValuationSubring := by
  by_cases hg : g = 0
  · rw [hg]; exact zero_mem _
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hg hπ
    rw [hu]
    refine mul_mem (SetLike.coe_mem _) ?_
    rw [show ((π : F) ^ (v.ord g)) = ((π : F) ^ ((v.ord g).toNat)) by
      rw [← zpow_natCast, Int.toNat_of_nonneg h.le]]
    exact pow_mem (SetLike.coe_mem π) _

private theorem mem_maximalIdeal_of_ord_pos {g : F} (h : 0 < v.ord g)
    (hg : g ∈ v.toValuationSubring) :
    (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  have h0 := v.ord_coe_unit u
  rw [show ((u : v.toValuationSubring) : F) = g by rw [hu]] at h0
  omega

private theorem mem_toValuationSubring_of_ord_sub_pos {f : F} {c : K}
    (h : 0 < v.ord (f - algebraMap K F c)) : f ∈ v.toValuationSubring := by
  have hdiff := mem_toValuationSubring_of_ord_pos v h
  have := add_mem hdiff (v.algebraMap_mem' c)
  simpa using this

private theorem residue_eq_of_ord_sub_pos {f : F} {c : K}
    (h : 0 < v.ord (f - algebraMap K F c)) (hf : f ∈ v.toValuationSubring) :
    residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField c := by
  have hsub : f - algebraMap K F c ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' c)
  have hmax := mem_maximalIdeal_of_ord_pos v h hsub
  have hres : residue v.toValuationSubring ⟨f, hf⟩
      = residue v.toValuationSubring ⟨algebraMap K F c, v.algebraMap_mem' c⟩ := by
    rw [← sub_eq_zero, ← map_sub]
    have hel : (⟨f, hf⟩ - ⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
        = ⟨f - algebraMap K F c, hsub⟩ := rfl
    rw [hel]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmax
  rw [hres]
  rfl

private theorem eval₂_eq_zero_of_ord_sub_pos (Φ : Polynomial (Polynomial ℤ))
    {f g : F} {c d : K}
    (hf : 0 < v.ord (f - algebraMap K F c)) (hg : 0 < v.ord (g - algebraMap K F d))
    (hΦ : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom F) f) g = 0) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom K) c) d = 0 := by
  have hfm := mem_toValuationSubring_of_ord_sub_pos v hf
  have hgm := mem_toValuationSubring_of_ord_sub_pos v hg

  set fO : v.toValuationSubring := ⟨f, hfm⟩
  set gO : v.toValuationSubring := ⟨g, hgm⟩
  have hcoe : (v.toValuationSubring.subtype)
        (Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom v.toValuationSubring) fO) gO)
      = Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom F) f) g := by
    rw [Polynomial.hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [Polynomial.coe_eval₂RingHom, fO]
  have hO : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom v.toValuationSubring) fO) gO
      = 0 := by
    apply Subtype.ext
    simpa using hcoe.trans hΦ

  have hκ : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom v.ResidueField)
        (algebraMap K v.ResidueField c)) (algebraMap K v.ResidueField d) = 0 := by
    have := congrArg (residue v.toValuationSubring) hO
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [← residue_eq_of_ord_sub_pos v hf hfm, ← residue_eq_of_ord_sub_pos v hg hgm]
    rw [← this]
    congr 1
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [Polynomial.coe_eval₂RingHom, fO]

  apply (algebraMap K v.ResidueField).injective
  rw [map_zero, ← hκ, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp [Polynomial.coe_eval₂RingHom]

end ValueCalculus

section Dichotomy

private theorem kronecker_value_dichotomy {ℓ : ℕ} [Fact ℓ.Prime]
    (data : ModularPolynomialData ℓ)
    {k : Type*} [Field k] [CharP k ℓ]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k) {c d : A}
    (h : data.Φ.eval₂
        (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ))
          (c : AlgebraicClosure ℚ)) (d : AlgebraicClosure ℚ) = 0) :
    red c = red d ^ ℓ ∨ red c ^ ℓ = red d := by

  have hA : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom A) c) d = 0 := by
    have hcoe : (A.subtype) (data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom A) c) d)
        = data.Φ.eval₂
            (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ))
              (c : AlgebraicClosure ℚ)) (d : AlgebraicClosure ℚ) := by
      rw [Polynomial.hom_eval₂]
      congr 1
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp [Polynomial.coe_eval₂RingHom]
    refine Subtype.val_injective ?_
    rw [show ((0 : A) : AlgebraicClosure ℚ) = 0 from rfl]
    rw [← h, ← hcoe]
    rfl

  have hk : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom k) (red c)) (red d) = 0 := by
    have := congrArg red hA
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [← this]
    congr 1
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [Polynomial.coe_eval₂RingHom]

  have hfib : (fibrePoly data.Φ (red c)).eval (red d) = 0 := by
    rw [fibrePoly, Polynomial.eval_map]
    exact hk
  rw [fibrePoly_eq_of_kroneckerCongruence data (kroneckerCongruence_of_prime ℓ data) (red c)]
    at hfib
  have hfib2 : red c ^ ℓ - red d = 0 ∨ red c - red d ^ ℓ = 0 := by simpa using hfib
  rcases hfib2 with h1 | h1
  · right
    exact sub_eq_zero.mp h1
  · left
    exact sub_eq_zero.mp h1

end Dichotomy

section ValueTransfer

private theorem isIntegral_adjoin_of_eval₂_monic {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) {x y : A}
    (hxy : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    IsIntegral (Algebra.adjoin R {x}) y := by
  set x' : Algebra.adjoin R {x} := ⟨x, Algebra.self_mem_adjoin_singleton R x⟩ with hx'
  set φ : Polynomial ℤ →+* Algebra.adjoin R {x} := (Polynomial.aeval (R := ℤ) x').toRingHom
    with hφ
  refine ⟨Φ.map φ, hΦ.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (Algebra.adjoin R {x}) A).comp φ
      = (Polynomial.aeval (R := ℤ) x).toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [hφ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X]
    rfl
  rw [hcomp]
  exact hxy

variable {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  (v : Place (AlgebraicClosure ℚ) F)

private theorem exists_mem_A_residue_eq_of_eval₂_monic
    (A : ValuationSubring (AlgebraicClosure ℚ)) {x g : F} {a : A}
    {Φ : Polynomial (Polynomial ℤ)} (hΦm : Φ.Monic)
    (hrel : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom g = 0)
    (hx : 0 < v.ord (x - algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))) :
    ∃ (hgmem : g ∈ v.toValuationSubring) (b : A),
      residue v.toValuationSubring ⟨g, hgmem⟩
        = algebraMap (AlgebraicClosure ℚ) v.ResidueField (b : AlgebraicClosure ℚ) := by
  have hxm : x ∈ v.toValuationSubring := mem_toValuationSubring_of_ord_sub_pos v hx
  have hgK : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({x} : Set F)) g :=
    isIntegral_adjoin_of_eval₂_monic hΦm hrel
  have hgmem : g ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_isIntegral_adjoin hxm hgK
  refine ⟨hgmem, ?_⟩
  set ρ : v.toValuationSubring →+* v.ResidueField := residue v.toValuationSubring with hρ
  set Ta : Polynomial A := Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) a) with hTa
  set T : Polynomial (AlgebraicClosure ℚ) :=
    Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ))
      (a : AlgebraicClosure ℚ)) with hT
  have hTam : Ta.Monic := hΦm.map _
  have hTm : T.Monic := hΦm.map _
  have hTmap : Ta.map (algebraMap A (AlgebraicClosure ℚ)) = T := by
    rw [hTa, hT, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [Polynomial.coe_eval₂RingHom]

  have hOrel : Φ.eval₂ (Polynomial.aeval (R := ℤ)
      (⟨x, hxm⟩ : v.toValuationSubring)).toRingHom (⟨g, hgmem⟩ : v.toValuationSubring)
      = 0 := by
    have h2 := Polynomial.hom_eval₂ Φ
      (Polynomial.aeval (R := ℤ) (⟨x, hxm⟩ : v.toValuationSubring)).toRingHom
      v.toValuationSubring.subtype (⟨g, hgmem⟩ : v.toValuationSubring)
    have hcomp : v.toValuationSubring.subtype.comp
        (Polynomial.aeval (R := ℤ) (⟨x, hxm⟩ : v.toValuationSubring)).toRingHom
        = (Polynomial.aeval (R := ℤ) x).toRingHom := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp
    rw [hcomp] at h2
    exact Subtype.val_injective (by simpa using h2.trans hrel)

  have hhom : ρ.comp (Polynomial.aeval (R := ℤ)
      (⟨x, hxm⟩ : v.toValuationSubring)).toRingHom
      = Polynomial.eval₂RingHom (Int.castRingHom v.ResidueField)
          (algebraMap (AlgebraicClosure ℚ) v.ResidueField (a : AlgebraicClosure ℚ)) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    exact residue_eq_of_ord_sub_pos v hx hxm
  have hTκ : (T.map (algebraMap (AlgebraicClosure ℚ) v.ResidueField)).eval
      (ρ ⟨g, hgmem⟩) = 0 := by
    have hmm : T.map (algebraMap (AlgebraicClosure ℚ) v.ResidueField)
        = Φ.map (Polynomial.eval₂RingHom (Int.castRingHom v.ResidueField)
            (algebraMap (AlgebraicClosure ℚ) v.ResidueField (a : AlgebraicClosure ℚ))) := by
      rw [hT, Polynomial.map_map]
      congr 1
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp [Polynomial.coe_eval₂RingHom]
    rw [hmm, Polynomial.eval_map, ← hhom]
    have h3 := Polynomial.hom_eval₂ Φ
      (Polynomial.aeval (R := ℤ) (⟨x, hxm⟩ : v.toValuationSubring)).toRingHom ρ
      (⟨g, hgmem⟩ : v.toValuationSubring)
    rw [← h3, hOrel, map_zero]

  have hTfact : T = (T.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
    (IsAlgClosed.splits T).eq_prod_roots_of_monic hTm
  have hzero : (T.roots.map fun r =>
      ρ ⟨g, hgmem⟩ - algebraMap (AlgebraicClosure ℚ) v.ResidueField r).prod = 0 := by
    have h4 := hTκ
    rw [hTfact, Polynomial.map_multiset_prod] at h4
    simpa [Multiset.map_map, Function.comp, Polynomial.eval_multiset_prod] using h4
  have h0mem : (0 : v.ResidueField) ∈ T.roots.map fun r =>
      ρ ⟨g, hgmem⟩ - algebraMap (AlgebraicClosure ℚ) v.ResidueField r :=
    Multiset.prod_eq_zero_iff.mp hzero
  obtain ⟨r, hrmem, hr0⟩ := Multiset.mem_map.mp h0mem
  have hrval : ρ ⟨g, hgmem⟩ = algebraMap (AlgebraicClosure ℚ) v.ResidueField r :=
    sub_eq_zero.mp hr0

  have hreval : T.eval r = 0 := ((Polynomial.mem_roots hTm.ne_zero).mp hrmem)
  have hrint : IsIntegral A r := by
    refine ⟨Ta, hTam, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hTmap]
    exact hreval
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrint
  refine ⟨b, ?_⟩
  rw [hrval, show (b : AlgebraicClosure ℚ) = r from hb]

end ValueTransfer

end VLayer

section SLayer

section CaseSplit

private theorem coupled_of_dichotomies_of_mixed_products {k : Type*} [Field k] {ℓ : ℕ}
    {x y x' y' : k}
    (hx : x = x' ^ ℓ ∨ x ^ ℓ = x') (hy : y = y' ^ ℓ ∨ y ^ ℓ = y')
    (hR1 : (x' - x ^ ℓ) * (y - y' ^ ℓ) = 0)
    (hR2 : (x - x' ^ ℓ) * (y' - y ^ ℓ) = 0) :
    (x = x' ^ ℓ ∧ y = y' ^ ℓ) ∨ (x ^ ℓ = x' ∧ y ^ ℓ = y') := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact Or.inl ⟨hx, hy⟩
    · rcases mul_eq_zero.mp hR1 with h | h
      · exact Or.inr ⟨(sub_eq_zero.mp h).symm, hy⟩
      · exact Or.inl ⟨hx, sub_eq_zero.mp h⟩
  · rcases hy with hy | hy
    · rcases mul_eq_zero.mp hR2 with h | h
      · exact Or.inl ⟨sub_eq_zero.mp h, hy⟩
      · exact Or.inr ⟨hx, (sub_eq_zero.mp h).symm⟩
    · exact Or.inr ⟨hx, hy⟩

end CaseSplit

section Transport

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F']

private theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') : 0 < W.ramificationIndexAlong φ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos (F := F)

private theorem ord_pos_along_of_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') {f : F}
    (h : 0 < (W.restrictAlong φ hφ).ord f) : 0 < W.ord (φ f) := by
  rw [W.ord_restrictAlong φ hφ f]
  have := ramificationIndexAlong_pos φ hφ W
  positivity

end Transport

section Bivariate

private theorem exists_monic_bivariate_of_isIntegral_adjoin {B : Type*} [CommRing B] [Nontrivial B]
    {x₀ m : B} (h : IsIntegral (Algebra.adjoin ℤ ({x₀} : Set B)) m) :
    ∃ Ψ : Polynomial (Polynomial ℤ), Ψ.Monic
      ∧ Ψ.eval₂ (Polynomial.aeval (R := ℤ) x₀).toRingHom m = 0 := by
  obtain ⟨P, hPm, hPev⟩ := h

  set f : Polynomial ℤ →+* B := (Polynomial.aeval (R := ℤ) x₀).toRingHom with hf
  set Pb : Polynomial B := P.map (algebraMap (Algebra.adjoin ℤ ({x₀} : Set B)) B) with hPb
  have hPbm : Pb.Monic := hPm.map _
  have hlift : Pb ∈ Polynomial.lifts f := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hPb, Polynomial.coeff_map]
    have hmem : ((P.coeff n : Algebra.adjoin ℤ ({x₀} : Set B)) : B)
        ∈ Algebra.adjoin ℤ ({x₀} : Set B) := (P.coeff n).2
    have hmem2 : ((P.coeff n : Algebra.adjoin ℤ ({x₀} : Set B)) : B)
        ∈ (Polynomial.aeval (R := ℤ) x₀).range :=
      (le_of_eq (Algebra.adjoin_singleton_eq_range_aeval ℤ x₀)) hmem
    exact hmem2
  obtain ⟨Ψ, hΨmap, -, hΨm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hPbm
  refine ⟨Ψ, hΨm, ?_⟩
  have hev : Polynomial.eval₂ f m Ψ = Pb.eval m := by
    rw [← hΨmap, Polynomial.eval_map]
  rw [hev, hPb, Polynomial.eval_map]
  exact hPev

private theorem exists_monic_bivariate_of_isIntegral_adjoin_laurent
    {x₀ m : LaurentSeries ℚ}
    (h : IsIntegral (Algebra.adjoin ℤ ({x₀} : Set (LaurentSeries ℚ))) m) :
    ∃ Ψ : Polynomial (Polynomial ℤ), Ψ.Monic
      ∧ Ψ.eval₂ (Polynomial.aeval (R := ℤ) x₀).toRingHom m = 0 := by
  obtain ⟨P, hPm, hPev⟩ := h
  set f : Polynomial ℤ →+* LaurentSeries ℚ := (Polynomial.aeval (R := ℤ) x₀).toRingHom
    with hf
  set Pb : Polynomial (LaurentSeries ℚ) :=
    P.map (algebraMap (Algebra.adjoin ℤ ({x₀} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ))
    with hPb
  have hPbm : Pb.Monic := hPm.map _
  have hlift : Pb ∈ Polynomial.lifts f := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hPb, Polynomial.coeff_map]
    have hmem : ((P.coeff n : Algebra.adjoin ℤ ({x₀} : Set (LaurentSeries ℚ)))
        : LaurentSeries ℚ) ∈ Algebra.adjoin ℤ ({x₀} : Set (LaurentSeries ℚ)) :=
      (P.coeff n).2
    have hmem2 : ((P.coeff n : Algebra.adjoin ℤ ({x₀} : Set (LaurentSeries ℚ)))
        : LaurentSeries ℚ) ∈ (Polynomial.aeval (R := ℤ) x₀).range :=
      (le_of_eq (Algebra.adjoin_singleton_eq_range_aeval ℤ x₀)) hmem
    exact hmem2
  obtain ⟨Ψ, hΨmap, -, hΨm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hPbm
  refine ⟨Ψ, hΨm, ?_⟩
  have hev : Polynomial.eval₂ f m Ψ = Pb.eval m := by
    rw [← hΨmap, Polynomial.eval_map]
  rw [hev, hPb, Polynomial.eval_map]
  exact hPev

end Bivariate

end SLayer

section PhiLayer

section BarLevel

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

private theorem coeffEmb_qExpand_jq_eq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = jqNModC L d := by
  rw [coeffEmb_qExpand, coeffEmb_jq]; rfl

private theorem coeffEmb_jq_eq : coeffEmb L jq = jqNModC L 1 := by
  rw [coeffEmb_jq, jqNModC_one]

variable {L N ℓ}

private theorem coe_heckeAlphaBar_of_coe_eq {x : laurentBaseChange L (modularFunctionFieldFull N)}
    {d : ℕ} [NeZero d] (hx : (x : LaurentSeries L) = jqNModC L d) :
    ((heckeAlphaBar L N ℓ x : laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
      LaurentSeries L) = jqNModC L d := by
  rw [coe_heckeAlphaBar, hx]

omit [NeZero N] in

private theorem coe_heckeBetaBar_of_coe_eq {x : laurentBaseChange L (modularFunctionFieldFull N)}
    {d : ℕ} [NeZero d] (hx : (x : LaurentSeries L) = jqNModC L d) :
    ((heckeBetaBar L N ℓ x : laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
      LaurentSeries L) = jqNModC L (d * ℓ) := by
  rw [coe_heckeBetaBar, hx]
  show qExpand L ℓ (qExpand L d (jqModC L)) = qExpand L (d * ℓ) (jqModC L)
  rw [qExpand_qExpand, qExpand_congr (mul_comm ℓ d)]

omit [Algebra ℚ L] in

private theorem coe_eval₂_aeval (E : IntermediateField L (LaurentSeries L))
    (Φ : Polynomial (Polynomial ℤ)) (y z : E) :
    ((Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom z : E) : LaurentSeries L)
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (y : LaurentSeries L)).toRingHom
          (z : LaurentSeries L) := by
  set ι : E →+* LaurentSeries L := (IntermediateField.val _).toRingHom with hι
  have hιy : ∀ w, ι w = (w : LaurentSeries L) := fun _ => rfl
  rw [← hιy, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Polynomial.aeval_X, hιy]

namespace ModularPolynomialData p2m_export "ModularCurve.ModularPolynomialData" "monic Φ eval_jqNModC_mul_eq_zero eval_jqNModC_of_mul_eq_zero" end ModularPolynomialData
namespace ModularPolynomialData
p2m_open_scoped "ModularCurve.ModularPolynomialData" in

private theorem _root_.ModularCurve.ModularPolynomialData.eval₂_heckeAlphaBar_heckeBetaBar_eq_zero
    (data : ModularPolynomialData ℓ) {d : ℕ} [NeZero d]
    (x : laurentBaseChange L (modularFunctionFieldFull N))
    (hx : (x : LaurentSeries L) = jqNModC L d) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (heckeAlphaBar L N ℓ x)).toRingHom
      (heckeBetaBar L N ℓ x) = 0 := by
  apply Subtype.val_injective
  rw [coe_eval₂_aeval, coe_heckeAlphaBar_of_coe_eq hx, coe_heckeBetaBar_of_coe_eq hx]
  exact data.eval_jqNModC_mul_eq_zero L d

end ModularPolynomialData
p2m_export "ModularCurve" "ModularPolynomialData.eval₂_heckeAlphaBar_heckeBetaBar_eq_zero"
end BarLevel

section Generators

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

omit [NeZero N] in

private theorem coe_jBar_eq (h : coeffEmb L jq ∈ laurentBaseChange L (modularFunctionFieldFull N)) :
    ((⟨coeffEmb L jq, h⟩ : laurentBaseChange L (modularFunctionFieldFull N)) : LaurentSeries L)
      = jqNModC L 1 :=
  coeffEmb_jq_eq L

private theorem coe_jNBar_eq
    (h : coeffEmb L (qExpand ℚ N jq) ∈ laurentBaseChange L (modularFunctionFieldFull N)) :
    ((⟨coeffEmb L (qExpand ℚ N jq), h⟩ : laurentBaseChange L (modularFunctionFieldFull N)) :
        LaurentSeries L) = jqNModC L N :=
  coeffEmb_qExpand_jq_eq L N

end Generators

end PhiLayer

section CuspSupport

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_sub_algebraMap_nonpos (v : Place K F) (c b : K) :
    v.ord (algebraMap K F c - algebraMap K F b) ≤ 0 := by
  rw [← map_sub, v.ord_algebraMap]

private theorem ord_pos_restrictAlong_of_along {F' : Type*} [Field F'] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (W : Place K F') {f : F}
    (h : 0 < W.ord (φ f)) : 0 < (W.restrictAlong φ hφ).ord f := by
  rw [W.ord_restrictAlong φ hφ f] at h
  by_contra hle
  push Not at hle
  have hepos := ramificationIndexAlong_pos φ hφ W
  nlinarith [mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℤ) ≤ (W.ramificationIndexAlong φ : ℤ) by positivity) hle]

private theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {g : F}
    (hg : g ∈ v.toValuationSubring) (hgne : g ≠ 0)
    (hm : (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring) :
    0 < v.ord g := by
  by_contra hle
  push Not at hle
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hgne hπ
  have hπF : ((π : F)) ≠ 0 := by
    simpa using (fun h0 => hπ.ne_zero (Subtype.ext h0))

  have hmem_pow : (π : F) ^ (-(v.ord g)) ∈ v.toValuationSubring := by
    rw [show ((π : F) ^ (-(v.ord g))) = ((π : F) ^ ((-(v.ord g)).toNat)) by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]]
    exact pow_mem (SetLike.coe_mem π) _

  have hF : g * (π : F) ^ (-(v.ord g)) = ((u : v.toValuationSubringˣ) : F) := by
    have h1 : g * (π : F) ^ (-(v.ord g))
        = (((u : v.toValuationSubringˣ) : v.toValuationSubring) : F)
          * ((π : F) ^ (v.ord g) * (π : F) ^ (-(v.ord g))) :=
      (congrArg (· * (π : F) ^ (-(v.ord g))) hu).trans (mul_assoc _ _ _)
    rw [h1, ← zpow_add₀ hπF, add_neg_cancel, zpow_zero, mul_one]
  have hO : (⟨g, hg⟩ : v.toValuationSubring) * ⟨(π : F) ^ (-(v.ord g)), hmem_pow⟩
      = ((u : v.toValuationSubringˣ) : v.toValuationSubring) := by
    apply Subtype.ext
    push_cast
    exact hF
  have humem : ((u : v.toValuationSubringˣ) : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
    rw [← hO]
    exact Ideal.mul_mem_right _ _ hm
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at humem
  exact humem u.isUnit

private theorem ord_sub_pos_of_residue_eq {v : Place K F} {g : F} {c : K}
    (hgmem : g ∈ v.toValuationSubring)
    (hres : IsLocalRing.residue v.toValuationSubring ⟨g, hgmem⟩
      = algebraMap K v.ResidueField c)
    (hne : g ≠ algebraMap K F c) : 0 < v.ord (g - algebraMap K F c) := by
  have hcmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hdmem : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hgmem hcmem
  have hdm : (⟨g - algebraMap K F c, hdmem⟩ : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
    have hsplit : (⟨g - algebraMap K F c, hdmem⟩ : v.toValuationSubring)
        = ⟨g, hgmem⟩ - ⟨algebraMap K F c, hcmem⟩ := rfl
    have hres2 : IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, hcmem⟩
        = algebraMap K v.ResidueField c := rfl
    have h0 : IsLocalRing.residue v.toValuationSubring
        (⟨g - algebraMap K F c, hdmem⟩ : v.toValuationSubring) = 0 := by
      rw [hsplit, map_sub, hres, hres2, sub_self]
    rw [← IsLocalRing.ker_residue]
    exact RingHom.mem_ker.mpr h0
  exact ord_pos_of_mem_maximalIdeal v hdmem (sub_ne_zero.mpr hne) hdm

end CuspSupport

section AssemblyCoord

section TransposeFold

variable {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ]

p2m_open_scoped "ModularCurve.ModularPolynomialData" in

private theorem ModularPolynomialData.eval₂_heckeBetaBar_heckeAlphaBar_eq_zero
    (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ) {d : ℕ} [NeZero d]
    (x : laurentBaseChange L (modularFunctionFieldFull N))
    (hx : (x : LaurentSeries L) = jqNModC L d) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (heckeBetaBar L N ℓ x)).toRingHom
      (heckeAlphaBar L N ℓ x) = 0 := by
  apply Subtype.val_injective
  rw [coe_eval₂_aeval, coe_heckeAlphaBar_of_coe_eq hx, coe_heckeBetaBar_of_coe_eq hx]
  exact data.eval_jqNModC_of_mul_eq_zero hsymm L d

end TransposeFold

private theorem aeval_toRingHom_eq {F : Type*} [CommRing F] (f : F) :
    (Polynomial.aeval (R := ℤ) f).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom F) f := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp [Polynomial.coe_eval₂RingHom]

private theorem exists_algebraMap_eq_of_eval₂_const {N ℓ : ℕ} [NeZero N] [NeZero ℓ]
    {Φ : Polynomial (Polynomial ℤ)} (hm : Φ.Monic) {c : AlgebraicClosure ℚ}
    {g : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))}
    (hrel : Φ.eval₂ (Polynomial.aeval (R := ℤ)
        (algebraMap (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))) c)).toRingHom
        g = 0) :
    ∃ r : AlgebraicClosure ℚ,
      g = algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))) r := by
  set T : Polynomial (AlgebraicClosure ℚ) :=
    Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) c) with hT
  have hTm : T.Monic := hm.map _
  have hev : (T.map (algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))).eval g
      = 0 := by
    have hmm : T.map (algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
        = Φ.map (Polynomial.eval₂RingHom (Int.castRingHom
            (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
          (algebraMap (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))) c)) := by
      rw [hT, Polynomial.map_map]
      congr 1
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp [Polynomial.coe_eval₂RingHom]
    rw [hmm, Polynomial.eval_map, ← aeval_toRingHom_eq]
    exact hrel
  have hTfact : T = (T.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
    (IsAlgClosed.splits T).eq_prod_roots_of_monic hTm
  have hzero : (T.roots.map fun r => g - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))) r).prod
      = 0 := by
    have h4 := hev
    rw [hTfact, Polynomial.map_multiset_prod] at h4
    simpa [Multiset.map_map, Function.comp, Polynomial.eval_multiset_prod] using h4
  have h0mem : (0 : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * ℓ))) ∈ T.roots.map fun r =>
      g - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))) r :=
    Multiset.prod_eq_zero_iff.mp hzero
  obtain ⟨r, -, hr0⟩ := Multiset.mem_map.mp h0mem
  exact ⟨r, (sub_eq_zero.mp hr0)⟩

private theorem value_transfers {N ℓ : ℕ} [NeZero N] [NeZero ℓ]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
    {Φ Φ' : Polynomial (Polynomial ℤ)} (hm : Φ.Monic) (hm' : Φ'.Monic)
    {u w : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))}
    (hrel : Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom w = 0)
    (hrel' : Φ'.eval₂ (Polynomial.aeval (R := ℤ) w).toRingHom u = 0)
    {b : A} (hu : 0 < W.ord (u - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
      (b : AlgebraicClosure ℚ))) :
    ∃ a : A, 0 < W.ord (w - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
      (a : AlgebraicClosure ℚ)) := by
  obtain ⟨hwmem, a, hres⟩ := exists_mem_A_residue_eq_of_eval₂_monic W A hm hrel hu
  by_cases hconst : w = algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
      (a : AlgebraicClosure ℚ)
  · rw [hconst] at hrel'
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_eval₂_const hm' hrel'
    rw [hr] at hu
    exact absurd hu (not_lt.mpr (ord_sub_algebraMap_nonpos W r _))
  · exact ⟨a, ord_sub_pos_of_residue_eq hwmem hres hconst⟩

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in

theorem _root_.P2MW.S_ModularCurve_kroneckerCoordinatewiseDichotomy.solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))) :
    (∀ aj aN bj bN : A,
      0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (aj : AlgebraicClosure ℚ)) →
      0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (aN : AlgebraicClosure ℚ)) →
      0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (bj : AlgebraicClosure ℚ)) →
      0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (bN : AlgebraicClosure ℚ)) →
        (red aj = red bj ^ ℓ ∨ red aj ^ ℓ = red bj)
      ∧ (red aN = red bN ^ ℓ ∨ red aN ^ ℓ = red bN))
    ∧ ((∀ a : A, (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0)
      ↔ (∀ b : A, (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (b : AlgebraicClosure ℚ)) ≤ 0))
    ∧ ((∀ a : A, (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0)
      ↔ (∀ b : A, (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (b : AlgebraicClosure ℚ)) ≤ 0)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    intro aj aN bj bN haj haN hbj hbN
    set xj : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
      ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ with hxj
    set xN : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full N (dvd_refl N))⟩ with hxN
    have hxjc : (xj : LaurentSeries (AlgebraicClosure ℚ))
        = jqNModC (AlgebraicClosure ℚ) 1 := coe_jBar_eq _ _ _
    have hxNc : (xN : LaurentSeries (AlgebraicClosure ℚ))
        = jqNModC (AlgebraicClosure ℚ) N := coe_jNBar_eq _ _ _
    have Haj : 0 < W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ xj
        - algebraMap (AlgebraicClosure ℚ) _ (aj : AlgebraicClosure ℚ)) := by
      have h := ord_pos_along_of_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W haj
      rwa [map_sub, AlgHom.commutes] at h
    have HaN : 0 < W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ xN
        - algebraMap (AlgebraicClosure ℚ) _ (aN : AlgebraicClosure ℚ)) := by
      have h := ord_pos_along_of_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W haN
      rwa [map_sub, AlgHom.commutes] at h
    have Hbj : 0 < W.ord (heckeBetaBar (AlgebraicClosure ℚ) N ℓ xj
        - algebraMap (AlgebraicClosure ℚ) _ (bj : AlgebraicClosure ℚ)) := by
      have h := ord_pos_along_of_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ W hbj
      rwa [map_sub, AlgHom.commutes] at h
    have HbN : 0 < W.ord (heckeBetaBar (AlgebraicClosure ℚ) N ℓ xN
        - algebraMap (AlgebraicClosure ℚ) _ (bN : AlgebraicClosure ℚ)) := by
      have h := ord_pos_along_of_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ W hbN
      rwa [map_sub, AlgHom.commutes] at h
    obtain ⟨data, -⟩ := exists_kroneckerCongruence_of_prime ℓ
    have hid1 := data.eval₂_heckeAlphaBar_heckeBetaBar_eq_zero (ℓ := ℓ) xj hxjc
    have hid2 := data.eval₂_heckeAlphaBar_heckeBetaBar_eq_zero (ℓ := ℓ) xN hxNc
    rw [aeval_toRingHom_eq] at hid1 hid2
    exact ⟨kronecker_value_dichotomy data A red
        (eval₂_eq_zero_of_ord_sub_pos W data.Φ Haj Hbj hid1),
      kronecker_value_dichotomy data A red
        (eval₂_eq_zero_of_ord_sub_pos W data.Φ HaN HbN hid2)⟩
  ·
    obtain ⟨dataS, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
    set x₀ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
      ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ with hx₀
    have hx₀c : (x₀ : LaurentSeries (AlgebraicClosure ℚ))
        = jqNModC (AlgebraicClosure ℚ) 1 := coe_jBar_eq _ _ _
    have hfwd := dataS.eval₂_heckeAlphaBar_heckeBetaBar_eq_zero (ℓ := ℓ) x₀ hx₀c
    have hbwd := ModularPolynomialData.eval₂_heckeBetaBar_heckeAlphaBar_eq_zero
      dataS hsymm x₀ hx₀c
    constructor
    · intro h b
      by_contra hpos
      push Not at hpos
      have Hu : 0 < W.ord (heckeBetaBar (AlgebraicClosure ℚ) N ℓ x₀
          - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) := by
        have h2 := ord_pos_along_of_restrictAlong
          (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ W hpos
        rwa [map_sub, AlgHom.commutes] at h2
      obtain ⟨a, ha⟩ := value_transfers A W dataS.monic dataS.monic hbwd hfwd Hu
      have hsh : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ
          (x₀ - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ))
          = heckeAlphaBar (AlgebraicClosure ℚ) N ℓ x₀
            - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := by
        rw [map_sub, AlgHom.commutes]
      have hdown := ord_pos_restrictAlong_of_along
        (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W (by rw [hsh]; exact ha)
      exact absurd hdown (not_lt.mpr (h a))
    · intro h a
      by_contra hpos
      push Not at hpos
      have Hu : 0 < W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ x₀
          - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) := by
        have h2 := ord_pos_along_of_restrictAlong
          (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W hpos
        rwa [map_sub, AlgHom.commutes] at h2
      obtain ⟨b, hb⟩ := value_transfers A W dataS.monic dataS.monic hfwd hbwd Hu
      have hsh : heckeBetaBar (AlgebraicClosure ℚ) N ℓ
          (x₀ - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ))
          = heckeBetaBar (AlgebraicClosure ℚ) N ℓ x₀
            - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ) := by
        rw [map_sub, AlgHom.commutes]
      have hdown := ord_pos_restrictAlong_of_along
        (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ W (by rw [hsh]; exact hb)
      exact absurd hdown (not_lt.mpr (h b))
  ·
    obtain ⟨dataS, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
    set x₀ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full N (dvd_refl N))⟩ with hx₀
    have hx₀c : (x₀ : LaurentSeries (AlgebraicClosure ℚ))
        = jqNModC (AlgebraicClosure ℚ) N := coe_jNBar_eq _ _ _
    have hfwd := dataS.eval₂_heckeAlphaBar_heckeBetaBar_eq_zero (ℓ := ℓ) x₀ hx₀c
    have hbwd := ModularPolynomialData.eval₂_heckeBetaBar_heckeAlphaBar_eq_zero
      dataS hsymm x₀ hx₀c
    constructor
    · intro h b
      by_contra hpos
      push Not at hpos
      have Hu : 0 < W.ord (heckeBetaBar (AlgebraicClosure ℚ) N ℓ x₀
          - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) := by
        have h2 := ord_pos_along_of_restrictAlong
          (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ W hpos
        rwa [map_sub, AlgHom.commutes] at h2
      obtain ⟨a, ha⟩ := value_transfers A W dataS.monic dataS.monic hbwd hfwd Hu
      have hsh : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ
          (x₀ - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ))
          = heckeAlphaBar (AlgebraicClosure ℚ) N ℓ x₀
            - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := by
        rw [map_sub, AlgHom.commutes]
      have hdown := ord_pos_restrictAlong_of_along
        (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W (by rw [hsh]; exact ha)
      exact absurd hdown (not_lt.mpr (h a))
    · intro h a
      by_contra hpos
      push Not at hpos
      have Hu : 0 < W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ x₀
          - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) := by
        have h2 := ord_pos_along_of_restrictAlong
          (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W hpos
        rwa [map_sub, AlgHom.commutes] at h2
      obtain ⟨b, hb⟩ := value_transfers A W dataS.monic dataS.monic hfwd hbwd Hu
      have hsh : heckeBetaBar (AlgebraicClosure ℚ) N ℓ
          (x₀ - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ))
          = heckeBetaBar (AlgebraicClosure ℚ) N ℓ x₀
            - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ) := by
        rw [map_sub, AlgHom.commutes]
      have hdown := ord_pos_restrictAlong_of_along
        (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ W (by rw [hsh]; exact hb)
      exact absurd hdown (not_lt.mpr (h b))

end AssemblyCoord

end ModularCurve

end S_ModularCurve_kroneckerCoordinatewiseDichotomy
end P2MW
export P2MW.S_ModularCurve_kroneckerCoordinatewiseDichotomy (solution)
