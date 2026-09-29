-- Prove2me | solution 1 for ModularCurve.kroneckerCentreDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b01ba5b8-f166-5b4b-bf00-619fed66543c

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kroneckerCentreDichotomy
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr qExpand_qExpand jq jqN ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange fibrePoly jqModC jqNModC jqNModC_one kroneckerCongruence_of_prime fibrePoly_eq_of_kroneckerCongruence exists_kroneckerCongruence_of_prime coeffEmb_jq coeffEmb_qExpand"
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

namespace ModularPolynomialData p2m_export "ModularCurve.ModularPolynomialData" "monic Φ eval_jqNModC_mul_eq_zero" end ModularPolynomialData
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

section Assembly

private theorem aeval_toRingHom_eq {F : Type*} [CommRing F] (f : F) :
    (Polynomial.aeval (R := ℤ) f).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom F) f := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp [Polynomial.coe_eval₂RingHom]

private theorem eval₂_aeval_coeffEmb_of_eval₂_aeval {x m : LaurentSeries ℚ}
    {Ψ : Polynomial (Polynomial ℤ)}
    (h : Ψ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom m = 0) :
    Ψ.eval₂ (Polynomial.aeval (R := ℤ)
        (coeffEmb (AlgebraicClosure ℚ) x)).toRingHom
      (coeffEmb (AlgebraicClosure ℚ) m) = 0 := by
  have h2 := Polynomial.hom_eval₂ Ψ (Polynomial.aeval (R := ℤ) x).toRingHom
    (coeffEmb (AlgebraicClosure ℚ)) m
  have hcomp : (coeffEmb (AlgebraicClosure ℚ)).comp (Polynomial.aeval (R := ℤ) x).toRingHom
      = (Polynomial.aeval (R := ℤ) (coeffEmb (AlgebraicClosure ℚ) x)).toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp
  rw [hcomp] at h2
  rw [← h2, h, map_zero]

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in

theorem _root_.P2MW.S_ModularCurve_kroneckerCentreDichotomy.solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hKR : IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jqN ℓ - jq ^ ℓ) * qExpand ℚ N (jq - (jqN ℓ) ^ ℓ)))
      ∧ IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jq - (jqN ℓ) ^ ℓ) * qExpand ℚ N (jqN ℓ - jq ^ ℓ))))
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
    (aj aN bj bN : A)
    (haj : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (aj : AlgebraicClosure ℚ)))
    (haN : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (aN : AlgebraicClosure ℚ)))
    (hbj : 0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (bj : AlgebraicClosure ℚ)))
    (hbN : 0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (bN : AlgebraicClosure ℚ))) :
    (red aj = red bj ^ ℓ ∧ red aN = red bN ^ ℓ)
      ∨ (red aj ^ ℓ = red bj ∧ red aN ^ ℓ = red bN) := by
  obtain ⟨Ψ₁, hΨ₁m, hΨ₁rel⟩ := exists_monic_bivariate_of_isIntegral_adjoin_laurent hKR.1
  obtain ⟨Ψ₂, hΨ₂m, hΨ₂rel⟩ := exists_monic_bivariate_of_isIntegral_adjoin_laurent hKR.2
  classical
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
  have hdj := kronecker_value_dichotomy data A red
    (eval₂_eq_zero_of_ord_sub_pos W data.Φ Haj Hbj hid1)
  have hdN := kronecker_value_dichotomy data A red
    (eval₂_eq_zero_of_ord_sub_pos W data.Φ HaN HbN hid2)

  set αj := heckeAlphaBar (AlgebraicClosure ℚ) N ℓ xj with hαj
  set βj := heckeBetaBar (AlgebraicClosure ℚ) N ℓ xj with hβj
  set αN := heckeAlphaBar (AlgebraicClosure ℚ) N ℓ xN with hαN
  set βN := heckeBetaBar (AlgebraicClosure ℚ) N ℓ xN with hβN
  have hℓ0 : ((ℓ : ℕ) : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * ℓ))) ≠ 0 := by
    have h2 : ((ℓ : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out (p := ℓ.Prime)).ne_zero
    intro h0
    apply h2
    apply (algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * ℓ)))).injective
    rw [map_natCast, h0, map_zero]
  set M₁ := ((ℓ : ℕ) : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * ℓ)))⁻¹ * ((βj - αj ^ ℓ) * (αN - βN ^ ℓ)) with hM₁
  set M₂ := ((ℓ : ℕ) : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * ℓ)))⁻¹ * ((αj - βj ^ ℓ) * (βN - αN ^ ℓ)) with hM₂

  have hαjc : (αj : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) 1 :=
    coe_heckeAlphaBar_of_coe_eq hxjc
  have hβjc : (βj : LaurentSeries (AlgebraicClosure ℚ))
      = jqNModC (AlgebraicClosure ℚ) (1 * ℓ) := coe_heckeBetaBar_of_coe_eq hxjc
  have hαNc : (αN : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) N :=
    coe_heckeAlphaBar_of_coe_eq hxNc
  have hβNc : (βN : LaurentSeries (AlgebraicClosure ℚ))
      = jqNModC (AlgebraicClosure ℚ) (N * ℓ) := coe_heckeBetaBar_of_coe_eq hxNc

  have hcjq : coeffEmb (AlgebraicClosure ℚ) jq = jqNModC (AlgebraicClosure ℚ) 1 :=
    coeffEmb_jq_eq _
  haveI : NeZero (N * ℓ) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out (p := ℓ.Prime)).ne_zero⟩
  have hjqN_ℓ : jqN ℓ = qExpand ℚ ℓ jq := rfl
  have hM₁c : (M₁ : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ)
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jqN ℓ - jq ^ ℓ) * qExpand ℚ N (jq - (jqN ℓ) ^ ℓ))) := by
    rw [hM₁]
    push_cast
    simp only [map_mul, map_inv₀, map_natCast, map_sub, map_pow, hjqN_ℓ, qExpand_qExpand,
      coeffEmb_qExpand_jq_eq, hcjq, hβjc, hαjc, hαNc, hβNc, one_mul]
  have hM₂c : (M₂ : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ)
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jq - (jqN ℓ) ^ ℓ) * qExpand ℚ N (jqN ℓ - jq ^ ℓ))) := by
    rw [hM₂]
    push_cast
    simp only [map_mul, map_inv₀, map_natCast, map_sub, map_pow, hjqN_ℓ, qExpand_qExpand,
      coeffEmb_qExpand_jq_eq, hcjq, hβjc, hαjc, hαNc, hβNc, one_mul]

  have hup₁ := eval₂_aeval_coeffEmb_of_eval₂_aeval hΨ₁rel
  have hup₂ := eval₂_aeval_coeffEmb_of_eval₂_aeval hΨ₂rel
  have hsαj : ((αj : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * ℓ))) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) jq := hαjc.trans hcjq.symm
  have hz : ((0 : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * ℓ))) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := rfl
  have hrel₁ : Ψ₁.eval₂ (Polynomial.aeval (R := ℤ) αj).toRingHom M₁ = 0 :=
    Subtype.val_injective (((coe_eval₂_aeval _ Ψ₁ αj M₁).trans
      (congrArg₂ (fun (s t : LaurentSeries (AlgebraicClosure ℚ)) =>
          Ψ₁.eval₂ (Polynomial.aeval (R := ℤ) s).toRingHom t) hsαj hM₁c)).trans
      (hup₁.trans hz.symm))
  have hrel₂ : Ψ₂.eval₂ (Polynomial.aeval (R := ℤ) αj).toRingHom M₂ = 0 :=
    Subtype.val_injective (((coe_eval₂_aeval _ Ψ₂ αj M₂).trans
      (congrArg₂ (fun (s t : LaurentSeries (AlgebraicClosure ℚ)) =>
          Ψ₂.eval₂ (Polynomial.aeval (R := ℤ) s).toRingHom t) hsαj hM₂c)).trans
      (hup₂.trans hz.symm))

  obtain ⟨hM₁mem, r₁, hr₁⟩ := exists_mem_A_residue_eq_of_eval₂_monic W A hΨ₁m hrel₁ Haj
  obtain ⟨hM₂mem, r₂, hr₂⟩ := exists_mem_A_residue_eq_of_eval₂_monic W A hΨ₂m hrel₂ Haj

  have hmem_αj := mem_toValuationSubring_of_ord_sub_pos W Haj
  have hmem_βj := mem_toValuationSubring_of_ord_sub_pos W Hbj
  have hmem_αN := mem_toValuationSubring_of_ord_sub_pos W HaN
  have hmem_βN := mem_toValuationSubring_of_ord_sub_pos W HbN
  have hres_αj := residue_eq_of_ord_sub_pos W Haj hmem_αj
  have hres_βj := residue_eq_of_ord_sub_pos W Hbj hmem_βj
  have hres_αN := residue_eq_of_ord_sub_pos W HaN hmem_αN
  have hres_βN := residue_eq_of_ord_sub_pos W HbN hmem_βN

  have hP₁ : (βj - αj ^ ℓ) * (αN - βN ^ ℓ)
      = ((ℓ : ℕ) : laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull (N * ℓ))) * M₁ := by
    rw [hM₁, ← mul_assoc, mul_inv_cancel₀ hℓ0, one_mul]
  have hP₂ : (αj - βj ^ ℓ) * (βN - αN ^ ℓ)
      = ((ℓ : ℕ) : laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull (N * ℓ))) * M₂ := by
    rw [hM₂, ← mul_assoc, mul_inv_cancel₀ hℓ0, one_mul]
  have hmem_P₁ : (βj - αj ^ ℓ) * (αN - βN ^ ℓ) ∈ W.toValuationSubring :=
    mul_mem (sub_mem hmem_βj (pow_mem hmem_αj ℓ)) (sub_mem hmem_αN (pow_mem hmem_βN ℓ))
  have hmem_P₂ : (αj - βj ^ ℓ) * (βN - αN ^ ℓ) ∈ W.toValuationSubring :=
    mul_mem (sub_mem hmem_αj (pow_mem hmem_βj ℓ)) (sub_mem hmem_βN (pow_mem hmem_αN ℓ))

  have hres_P₁ : residue W.toValuationSubring ⟨(βj - αj ^ ℓ) * (αN - βN ^ ℓ), hmem_P₁⟩
      = algebraMap (AlgebraicClosure ℚ) W.ResidueField
        (((bj : AlgebraicClosure ℚ) - (aj : AlgebraicClosure ℚ) ^ ℓ)
          * ((aN : AlgebraicClosure ℚ) - (bN : AlgebraicClosure ℚ) ^ ℓ)) := by
    have hsp : (⟨(βj - αj ^ ℓ) * (αN - βN ^ ℓ), hmem_P₁⟩ : W.toValuationSubring)
        = (⟨βj, hmem_βj⟩ - ⟨αj, hmem_αj⟩ ^ ℓ) * (⟨αN, hmem_αN⟩ - ⟨βN, hmem_βN⟩ ^ ℓ) := rfl
    have eL : residue W.toValuationSubring (⟨βj, hmem_βj⟩ - ⟨αj, hmem_αj⟩ ^ ℓ)
        = algebraMap (AlgebraicClosure ℚ) W.ResidueField
          ((bj : AlgebraicClosure ℚ) - (aj : AlgebraicClosure ℚ) ^ ℓ) :=
      ((map_sub _ _ _).trans (congrArg₂ HSub.hSub hres_βj
          ((map_pow _ _ _).trans (congrArg (· ^ ℓ) hres_αj)))).trans
        ((congrArg₂ HSub.hSub rfl (map_pow _ _ _).symm).trans (map_sub _ _ _).symm)
    have eR : residue W.toValuationSubring (⟨αN, hmem_αN⟩ - ⟨βN, hmem_βN⟩ ^ ℓ)
        = algebraMap (AlgebraicClosure ℚ) W.ResidueField
          ((aN : AlgebraicClosure ℚ) - (bN : AlgebraicClosure ℚ) ^ ℓ) :=
      ((map_sub _ _ _).trans (congrArg₂ HSub.hSub hres_αN
          ((map_pow _ _ _).trans (congrArg (· ^ ℓ) hres_βN)))).trans
        ((congrArg₂ HSub.hSub rfl (map_pow _ _ _).symm).trans (map_sub _ _ _).symm)
    exact ((congrArg (residue W.toValuationSubring) hsp).trans
      ((map_mul _ _ _).trans (congrArg₂ HMul.hMul eL eR))).trans (map_mul _ _ _).symm
  have hres_P₂ : residue W.toValuationSubring ⟨(αj - βj ^ ℓ) * (βN - αN ^ ℓ), hmem_P₂⟩
      = algebraMap (AlgebraicClosure ℚ) W.ResidueField
        (((aj : AlgebraicClosure ℚ) - (bj : AlgebraicClosure ℚ) ^ ℓ)
          * ((bN : AlgebraicClosure ℚ) - (aN : AlgebraicClosure ℚ) ^ ℓ)) := by
    have hsp : (⟨(αj - βj ^ ℓ) * (βN - αN ^ ℓ), hmem_P₂⟩ : W.toValuationSubring)
        = (⟨αj, hmem_αj⟩ - ⟨βj, hmem_βj⟩ ^ ℓ) * (⟨βN, hmem_βN⟩ - ⟨αN, hmem_αN⟩ ^ ℓ) := rfl
    have eL : residue W.toValuationSubring (⟨αj, hmem_αj⟩ - ⟨βj, hmem_βj⟩ ^ ℓ)
        = algebraMap (AlgebraicClosure ℚ) W.ResidueField
          ((aj : AlgebraicClosure ℚ) - (bj : AlgebraicClosure ℚ) ^ ℓ) :=
      ((map_sub _ _ _).trans (congrArg₂ HSub.hSub hres_αj
          ((map_pow _ _ _).trans (congrArg (· ^ ℓ) hres_βj)))).trans
        ((congrArg₂ HSub.hSub rfl (map_pow _ _ _).symm).trans (map_sub _ _ _).symm)
    have eR : residue W.toValuationSubring (⟨βN, hmem_βN⟩ - ⟨αN, hmem_αN⟩ ^ ℓ)
        = algebraMap (AlgebraicClosure ℚ) W.ResidueField
          ((bN : AlgebraicClosure ℚ) - (aN : AlgebraicClosure ℚ) ^ ℓ) :=
      ((map_sub _ _ _).trans (congrArg₂ HSub.hSub hres_βN
          ((map_pow _ _ _).trans (congrArg (· ^ ℓ) hres_αN)))).trans
        ((congrArg₂ HSub.hSub rfl (map_pow _ _ _).symm).trans (map_sub _ _ _).symm)
    exact ((congrArg (residue W.toValuationSubring) hsp).trans
      ((map_mul _ _ _).trans (congrArg₂ HMul.hMul eL eR))).trans (map_mul _ _ _).symm
  have hres_P₁' : residue W.toValuationSubring ⟨(βj - αj ^ ℓ) * (αN - βN ^ ℓ), hmem_P₁⟩
      = algebraMap (AlgebraicClosure ℚ) W.ResidueField
        (((ℓ : ℕ) : AlgebraicClosure ℚ) * (r₁ : AlgebraicClosure ℚ)) := by
    have hsp : (⟨(βj - αj ^ ℓ) * (αN - βN ^ ℓ), hmem_P₁⟩ : W.toValuationSubring)
        = ((ℓ : ℕ) : W.toValuationSubring) * ⟨M₁, hM₁mem⟩ := by
      apply Subtype.ext
      push_cast
      exact hP₁
    exact ((congrArg (residue W.toValuationSubring) hsp).trans
      ((map_mul _ _ _).trans (congrArg₂ HMul.hMul (map_natCast _ ℓ) hr₁))).trans
      ((congrArg₂ HMul.hMul (map_natCast (algebraMap (AlgebraicClosure ℚ)
        W.ResidueField) ℓ).symm rfl).trans (map_mul _ _ _).symm)
  have hres_P₂' : residue W.toValuationSubring ⟨(αj - βj ^ ℓ) * (βN - αN ^ ℓ), hmem_P₂⟩
      = algebraMap (AlgebraicClosure ℚ) W.ResidueField
        (((ℓ : ℕ) : AlgebraicClosure ℚ) * (r₂ : AlgebraicClosure ℚ)) := by
    have hsp : (⟨(αj - βj ^ ℓ) * (βN - αN ^ ℓ), hmem_P₂⟩ : W.toValuationSubring)
        = ((ℓ : ℕ) : W.toValuationSubring) * ⟨M₂, hM₂mem⟩ := by
      apply Subtype.ext
      push_cast
      exact hP₂
    exact ((congrArg (residue W.toValuationSubring) hsp).trans
      ((map_mul _ _ _).trans (congrArg₂ HMul.hMul (map_natCast _ ℓ) hr₂))).trans
      ((congrArg₂ HMul.hMul (map_natCast (algebraMap (AlgebraicClosure ℚ)
        W.ResidueField) ℓ).symm rfl).trans (map_mul _ _ _).symm)
  have hQ₁ : ((bj : AlgebraicClosure ℚ) - (aj : AlgebraicClosure ℚ) ^ ℓ)
      * ((aN : AlgebraicClosure ℚ) - (bN : AlgebraicClosure ℚ) ^ ℓ)
      = ((ℓ : ℕ) : AlgebraicClosure ℚ) * (r₁ : AlgebraicClosure ℚ) :=
    (algebraMap (AlgebraicClosure ℚ) W.ResidueField).injective
      (hres_P₁.symm.trans hres_P₁')
  have hQ₂ : ((aj : AlgebraicClosure ℚ) - (bj : AlgebraicClosure ℚ) ^ ℓ)
      * ((bN : AlgebraicClosure ℚ) - (aN : AlgebraicClosure ℚ) ^ ℓ)
      = ((ℓ : ℕ) : AlgebraicClosure ℚ) * (r₂ : AlgebraicClosure ℚ) :=
    (algebraMap (AlgebraicClosure ℚ) W.ResidueField).injective
      (hres_P₂.symm.trans hres_P₂')
  have hA₁ : (bj - aj ^ ℓ) * (aN - bN ^ ℓ) = ((ℓ : ℕ) : A) * r₁ := by
    apply Subtype.val_injective
    push_cast
    exact hQ₁
  have hA₂ : (aj - bj ^ ℓ) * (bN - aN ^ ℓ) = ((ℓ : ℕ) : A) * r₂ := by
    apply Subtype.val_injective
    push_cast
    exact hQ₂
  have hR₁ : (red bj - red aj ^ ℓ) * (red aN - red bN ^ ℓ) = 0 := by
    have h := congrArg red hA₁
    rw [map_mul, map_mul, map_sub, map_sub, map_pow, map_pow, map_natCast] at h
    rw [h, CharP.cast_eq_zero k ℓ, zero_mul]
  have hR₂ : (red aj - red bj ^ ℓ) * (red bN - red aN ^ ℓ) = 0 := by
    have h := congrArg red hA₂
    rw [map_mul, map_mul, map_sub, map_sub, map_pow, map_pow, map_natCast] at h
    rw [h, CharP.cast_eq_zero k ℓ, zero_mul]
  exact coupled_of_dichotomies_of_mixed_products hdj hdN hR₁ hR₂

end Assembly

end ModularCurve

end S_ModularCurve_kroneckerCentreDichotomy
end P2MW
export P2MW.S_ModularCurve_kroneckerCentreDichotomy (solution)
