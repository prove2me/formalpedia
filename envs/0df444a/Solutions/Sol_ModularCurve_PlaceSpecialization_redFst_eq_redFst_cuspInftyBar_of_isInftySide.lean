-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.redFst_eq_redFst_cuspInftyBar_of_isInftySide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a13e4043-ad75-5228-8b61-e00834ed77cc

import Mathlib
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_ModularCurve_isInftySide_cuspInftyBar
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace Ws23
namespace NodePlaceAPI

open AlgebraicCurve IsLocalRing Polynomial

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_of_ord_sub_pos {v : Place K F} {g : F} {c : K}
    (h : 0 < v.ord (g - algebraMap K F c)) : v.HasValue g c := by
  have hne : g - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt hne h.le
  have hnu : ¬ IsUnit (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    have h0' : v.ord (g - algebraMap K F c) = 0 := h0
    rw [h0'] at h
    exact lt_irrefl _ h
  have hmax : (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hres0 : residue v.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = algebraMap K v.ResidueField 0 := by
    rw [map_zero]
    exact (residue_eq_zero_iff _).mpr hmax
  have hd := hasValue_add (⟨hmem, hres0⟩ : v.HasValue (g - algebraMap K F c) 0) (v.hasValue_algebraMap c)
  rwa [sub_add_cancel, zero_add] at hd

theorem hasValue_congrRingEquiv {F' : Type*} [Field F'] [Algebra K F'] (e : F ≃+* F')
    (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a) (v : Place K F) {g : F} {c : K}
    (h : v.HasValue g c) : (Place.congrRingEquiv e he v).HasValue (e g) c := by
  obtain ⟨hg, hr⟩ := h
  let φ := Place.comapSymmRingEquiv e v.toValuationSubring
  have hg' : e g ∈ (Place.congrRingEquiv e he v).toValuationSubring := (φ ⟨g, hg⟩).2
  refine ⟨hg', ?_⟩
  have h1 : (⟨e g, hg'⟩ : (Place.congrRingEquiv e he v).toValuationSubring) = φ ⟨g, hg⟩ := rfl
  have h3 : φ (algebraMap K v.toValuationSubring c)
      = algebraMap K (Place.congrRingEquiv e he v).toValuationSubring c := by
    ext
    rw [Place.coe_comapSymmRingEquiv_apply, Place.coe_algebraMap, Place.coe_algebraMap]
    exact he c
  rw [h1, ← Place.residue_algebraMap, ← h3]
  have key : ∀ z : v.toValuationSubring,
      residue _ (φ z) = IsLocalRing.ResidueField.mapEquiv φ (residue _ z) := fun z => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  show residue _ (φ ⟨g, hg⟩) = residue _ (φ (algebraMap K v.toValuationSubring c))
  rw [key, key, hr, Place.residue_algebraMap]

theorem hasValue_placeOfPoint (a : K) (p : K[X]) :
    (RationalFunctionField.placeOfPoint K a).HasValue (algebraMap K[X] (RatFunc K) p) (p.eval a) := by
  let w := RationalFunctionField.heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)
  have hmem : algebraMap K[X] (RatFunc K) p ∈ (RationalFunctionField.placeOfPoint K a).toValuationSubring :=
    RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w p
  refine ⟨hmem, ?_⟩
  have hker : p - C (p.eval a) ∈ RingHom.ker (RationalFunctionField.residueOfHeightOneSpectrum K w) := by
    rw [RationalFunctionField.ker_residueOfHeightOneSpectrum,
      RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, dvd_iff_isRoot]
    simp [IsRoot]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, RationalFunctionField.residueOfHeightOneSpectrum_apply,
    RationalFunctionField.residueOfHeightOneSpectrum_apply] at hker
  have hC : (⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :
        (RationalFunctionField.placeOfPoint K a).toValuationSubring)
      = algebraMap K (RationalFunctionField.placeOfPoint K a).toValuationSubring (p.eval a) := by
    ext
    rw [Place.coe_algebraMap, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  have hker' : residue (RationalFunctionField.placeOfPoint K a).toValuationSubring ⟨_, hmem⟩
      = residue (RationalFunctionField.placeOfPoint K a).toValuationSubring
          ⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :=
    hker
  rw [hker', hC, Place.residue_algebraMap]

end PlaceLemmas

end Ws23.NodePlaceAPI

namespace Ws23
namespace NodePlaceAPI

open AlgebraicCurve IsLocalRing Polynomial ModularCurve

section PlaceLemmas2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_eq_of_hasValue' {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem hasValue_pow {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

end PlaceLemmas2

section JLine

variable (K : Type*) [Field K]

noncomputable def jC1 : ↥(modularFunctionFieldC K 1) := ⟨jqModC K, jqModC_mem K 1⟩

@[scoped simp] theorem coe_jC1 : ((jC1 K : ↥(modularFunctionFieldC K 1)) : LaurentSeries K) = jqModC K := rfl

theorem ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC K (algebraMap K[X] (RatFunc K) X) = jC1 K := by
  apply Subtype.ext
  rw [RatFunc.algebraMap_X, ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (jqModC K) (transcendental_jqModC K)

theorem ratFuncEquivCharLOneC_polynomial (p : K[X]) :
    ratFuncEquivCharLOneC K (algebraMap K[X] (RatFunc K) p) = Polynomial.aeval (jC1 K) p := by
  have hfun : ((ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)).comp
      (IsScalarTower.toAlgHom K K[X] (RatFunc K))) = Polynomial.aeval (jC1 K) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
    exact ratFuncEquivCharLOneC_X K
  exact AlgHom.congr_fun hfun p

theorem hasValue_charLGeomPlaceOfPoint_aeval (a : K) (p : K[X]) :
    (charLGeomPlaceOfPoint K a).HasValue (Polynomial.aeval (jC1 K) p) (p.eval a) := by
  have h := hasValue_congrRingEquiv (K := K) (ratFuncEquivCharLOneC K).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC K).commutes c) (RationalFunctionField.placeOfPoint K a)
    (hasValue_placeOfPoint a p)
  rw [← ratFuncEquivCharLOneC_polynomial]
  exact h

theorem hasValue_charLGeomPlaceOfPoint_jC1 (a : K) :
    (charLGeomPlaceOfPoint K a).HasValue (jC1 K) a := by
  simpa using hasValue_charLGeomPlaceOfPoint_aeval K a X

end JLine

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23"

namespace Ws23
namespace NodePlaceAPI

open AlgebraicCurve AlgebraicCurve.RationalFunctionField IsLocalRing Polynomial ModularCurve

section Orders

variable {K : Type*} [Field K]

theorem ord_placeOfPoint_algebraMap_eq_mul (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (rootMultiplicity a q : ℤ)
          * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) := by
  obtain ⟨r, hr⟩ := pow_rootMultiplicity_dvd q a
  set m : ℕ := rootMultiplicity a q with hm
  have hXa : (X : K[X]) - C a ≠ 0 := X_sub_C_ne_zero a
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hq (by simpa using hr)
  have hndvd : ¬((X : K[X]) - C a) ∣ r := by
    intro ⟨s, hs⟩
    have : (X - C a) ^ (m + 1) ∣ q := ⟨s, by rw [hr, hs]; ring⟩
    have := (le_rootMultiplicity_iff hq).mpr this
    omega
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hr0' : algebraMap K[X] (RatFunc K) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr0
  have hpow' : algebraMap K[X] (RatFunc K) ((X - C a) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m hXa)
  have hordr : (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) = 0 := by
    by_contra hcon
    apply hndvd
    have hmem := (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
      (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) hr0).mp hcon
    rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton] at hmem
    exact hmem
  calc (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m)
          * algebraMap K[X] (RatFunc K) r) := by rw [← map_mul, ← hr]
    _ = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m))
          + (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) :=
        (placeOfPoint K a).ord_mul hpow' hr0'
    _ = (placeOfPoint K a).ord ((algebraMap K[X] (RatFunc K) (X - C a)) ^ (m : ℤ)) := by
        rw [hordr, add_zero, map_pow, ← zpow_natCast]
    _ = (m : ℤ) * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) :=
        (placeOfPoint K a).ord_zpow _ _

theorem ord_placeOfPoint_algebraMap (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = (rootMultiplicity a q : ℤ) := by
  rw [ord_placeOfPoint_algebraMap_eq_mul a hq, StandardAnnulus.ord_placeOfPoint_X_sub_C_self a, mul_one]

theorem ord_placeOfPoint_algebraMap' (a : K) (q : K[X]) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = (rootMultiplicity a q : ℤ) := by
  by_cases hq : q = 0
  · rw [hq, map_zero, Place.ord_zero, rootMultiplicity_zero, Nat.cast_zero]
  · exact ord_placeOfPoint_algebraMap a hq

variable (K)

theorem ord_charLGeomPlaceOfPoint_ratFuncEquiv (a : K) (f : RatFunc K) :
    (charLGeomPlaceOfPoint K a).ord (ratFuncEquivCharLOneC K f) = (placeOfPoint K a).ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC K).commutes c) (placeOfPoint K a) f

theorem ord_charLGeomPlaceOfPoint_aeval (a : K) (p : K[X]) :
    (charLGeomPlaceOfPoint K a).ord (Polynomial.aeval (jC1 K) p) = (rootMultiplicity a p : ℤ) := by
  rw [← ratFuncEquivCharLOneC_polynomial, ord_charLGeomPlaceOfPoint_ratFuncEquiv, ord_placeOfPoint_algebraMap']

end Orders
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"

namespace Ws23
namespace Dict

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ramificationIndexAlong_pos' {K E E' : Type*} [Field K] [Field E] [Field E'] [Algebra K E] [Algebra K E']
    (φ : E →ₐ[K] E') (hφ : φ.toRingHom.IsIntegral) (w : Place K E') : 0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.ramificationIndex_pos (F := E) (w := w)

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

theorem heckeAlphaBar_jOne :
    heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
      modularFunctionFieldBar 1) = (PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

theorem ord_jFun_sub_eq (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (a : A) :
    W.ord ((PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q)))
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))
      = (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) W : ℤ)
        * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα).ord
            ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
              modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ)) := by
  have e := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα W
    ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
      modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ))
  rw [map_sub, AlgHom.commutes, heckeAlphaBar_jOne] at e
  exact e

theorem redFst_eq_charLGeomPlaceOfPoint_of_ord_pos (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (a : A) (h : 0 < W.ord ((PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q)))
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))) :
    P.redFst W = charLGeomPlaceOfPoint k (red a) := by
  have hepos := ramificationIndexAlong_pos' (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα W
  rw [ord_jFun_sub_eq (hα := hα) W a] at h
  have hpos := pos_of_mul_pos_right h (by exact_mod_cast hepos.le)
  exact eq_charLGeomPlaceOfPoint_of_ord_pos (P.d0_j _ a hpos)

theorem not_isAffineGeomPlace_redFst_of_isCuspidal {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : P.IsCuspidal W) : ¬ IsAffineGeomPlace k 1 (P.redFst W) := by
  intro haff
  have hpole : (P.redFst W).ord (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) < 0 := by
    apply P.d0_j_pole (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα)
    intro a
    have h := hW a
    have hepos := ramificationIndexAlong_pos' (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα W
    by_contra hpos
    have hpos' : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα).ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
          modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ)) :=
      not_le.mp hpos
    have : 0 < W.ord ((PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q)))
        - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) := by
      rw [ord_jFun_sub_eq (hα := hα) W a]
      exact mul_pos (by exact_mod_cast hepos) hpos'
    exact absurd h (not_le.mpr this)
  have hmem : (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) ∈ (P.redFst W).toValuationSubring := haff.1

  have hX : (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
    intro h0
    apply transcendental_jqModC k
    have h0' : jqModC k = 0 := congrArg Subtype.val h0
    rw [h0']
    exact isAlgebraic_zero
  have hnn := GaussReduction.ord_nonneg_of_mem_gen (P.redFst W) hmem hX
  omega

end Ws23.Dict
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"

namespace Ws23
namespace Dict

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

theorem isAffineGeomPlace_charLGeomPlaceOfPoint (c : k) : IsAffineGeomPlace k 1 (charLGeomPlaceOfPoint k c) := by
  have h1 : 0 < (charLGeomPlaceOfPoint k c).ord (jGeomGen k 1 - algebraMap k _ c) := by
    have h := Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval k c (Polynomial.X - Polynomial.C c)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.rootMultiplicity_X_sub_C_self] at h
    have hj : (Ws23.NodePlaceAPI.jC1 k) = jGeomGen k 1 := rfl
    rw [hj] at h
    rw [h]
    exact Int.one_pos
  have h2 : 0 < (charLGeomPlaceOfPoint k c).ord (jNGeomGen k 1 - algebraMap k _ c) := by
    have hjN : jNGeomGen k 1 = jGeomGen k 1 := Subtype.ext (jqNModC_one k)
    rw [hjN]; exact h1
  exact IsCentreOf.isAffineGeomPlace (c := (c, c)) ⟨h1, h2⟩

theorem redFst_eq_charLGeomPlaceOfPoint_iff (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (c₀ : k) :
    P.redFst W = charLGeomPlaceOfPoint k c₀ ↔
      ∃ a : A, red a = c₀ ∧
        0 < W.ord ((PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q)))
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) := by
  constructor
  · intro h
    have hnc : ¬ P.IsCuspidal W := by
      intro hc
      exact not_isAffineGeomPlace_redFst_of_isCuspidal P hc (h ▸ isAffineGeomPlace_charLGeomPlaceOfPoint c₀)
    obtain ⟨a, ha⟩ := not_forall.mp hnc
    have hpos := not_le.mp ha
    refine ⟨a, ?_, hpos⟩
    have h' := redFst_eq_charLGeomPlaceOfPoint_of_ord_pos P W a hpos
    rw [h] at h'
    exact (charLGeomPlaceOfPoint_injective k h').symm
  · rintro ⟨a, rfl, hpos⟩
    exact redFst_eq_charLGeomPlaceOfPoint_of_ord_pos P W a hpos

end Ws23.Dict
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"

namespace Ws23
namespace Dict

open AlgebraicCurve AlgebraicCurve.RationalFunctionField IsLocalRing ModularCurve ModularCurve.PlaceSpecialization Polynomial

theorem exists_asIdeal_eq_span_X_sub_C (k : Type) [Field k] [IsAlgClosed k]
    (w : IsDedekindDomain.HeightOneSpectrum (Polynomial k)) :
    ∃ c : k, w.asIdeal = Ideal.span {X - C c} := by
  obtain ⟨p, hp⟩ := Submodule.IsPrincipal.principal w.asIdeal
  have hp' : w.asIdeal = Ideal.span {p} := hp
  have hp0 : p ≠ 0 := by
    intro h0
    apply w.ne_bot
    rw [hp', h0, Ideal.span_singleton_eq_bot]
  have hprime : Prime p := (Ideal.span_singleton_prime hp0).mp (hp' ▸ w.isPrime)
  have hirr : Irreducible p := hprime.irreducible
  have hdeg : p.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k hirr
  obtain ⟨c, hc⟩ := Polynomial.exists_root_of_degree_eq_one hdeg
  refine ⟨c, ?_⟩
  rw [hp']
  apply Ideal.span_singleton_eq_span_singleton.mpr
  exact ((irreducible_X_sub_C c).associated_of_dvd hirr (dvd_iff_isRoot.mpr hc)).symm

theorem eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (k : Type) [Field k] [IsAlgClosed k]
    [DecidableEq (RatFunc k)] (v : Place k ↥(modularFunctionFieldC k 1)) :
    (∃ c : k, v = charLGeomPlaceOfPoint k c) ∨ v = charLGeomPlaceEquiv k (placeInfty k) := by
  have hv : v = charLGeomPlaceEquiv k ((charLGeomPlaceEquiv k).symm v) := ((charLGeomPlaceEquiv k).apply_symm_apply v).symm
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty ((charLGeomPlaceEquiv k).symm v) with ⟨w, hw⟩ | hinf
  · left
    obtain ⟨c, hc⟩ := exists_asIdeal_eq_span_X_sub_C k w
    refine ⟨c, ?_⟩
    rw [hv, hw, charLGeomPlaceOfPoint, placeOfPoint_eq_ofHeightOneSpectrum]
    congr 2
    exact IsDedekindDomain.HeightOneSpectrum.ext (by rw [hc, heightOneSpectrumOfIrreducible_asIdeal])
  · right
    rw [hv, hinf]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

theorem eq_charLGeomPlaceEquiv_placeInfty_of_not_isAffineGeomPlace [DecidableEq (RatFunc k)]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hv : ¬ IsAffineGeomPlace k 1 v) :
    v = charLGeomPlaceEquiv k (placeInfty k) := by
  rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty k v with ⟨c, rfl⟩ | h
  · exact (hv (isAffineGeomPlace_charLGeomPlaceOfPoint c)).elim
  · exact h

theorem redFst_cuspInftyBar_eq [DecidableEq (RatFunc k)] :
    P.redFst (cuspInftyBar (1 * q)) = charLGeomPlaceEquiv k (placeInfty k) :=
  eq_charLGeomPlaceEquiv_placeInfty_of_not_isAffineGeomPlace
    (not_isAffineGeomPlace_redFst_of_isCuspidal P (isInftySide_cuspInftyBar P).1)

theorem redFst_eq_redFst_cuspInftyBar_of_isInftySide (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hW : P.IsInftySide W) : P.redFst W = P.redFst (cuspInftyBar (1 * q)) := by
  classical
  rw [redFst_cuspInftyBar_eq P]
  exact eq_charLGeomPlaceEquiv_placeInfty_of_not_isAffineGeomPlace (not_isAffineGeomPlace_redFst_of_isCuspidal P hW.1)

theorem frobOnPlacesGeomLevel_redFst_cuspInftyBar :
    frobOnPlacesGeomLevel k 1 data hKr (P.redFst (cuspInftyBar (1 * q))) = P.redFst (cuspInftyBar (1 * q)) := by
  classical
  rw [redFst_cuspInftyBar_eq P]
  exact frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty k data hKr

end Ws23.Dict
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide.Ws23.NodePlaceAPI"

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : P.IsInftySide W) :
    P.redFst W = P.redFst (cuspInftyBar (1 * q)) :=
  Ws23.Dict.redFst_eq_redFst_cuspInftyBar_of_isInftySide P W hW

end S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_redFst_cuspInftyBar_of_isInftySide (solution)
