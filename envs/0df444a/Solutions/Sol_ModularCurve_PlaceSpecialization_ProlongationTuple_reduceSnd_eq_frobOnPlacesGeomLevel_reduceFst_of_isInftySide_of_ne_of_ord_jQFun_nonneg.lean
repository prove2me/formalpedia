-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/09cc24fc-b4be-5e6d-b616-21dbcbdc3a6a

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_restrictAlong_heckeBetaBar_eq_of_hasValuation_jFun_pow
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeAlphaBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeBetaBar
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_ValuationSubring_valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_pow_of_isInftySide
import Theorems.Thm_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_place
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace SolutionAux

namespace Step
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple
open scoped Pointwise

private noncomputable def jN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

section ValueGroup

variable {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem one_lt_of_pow_eq {δ x : A.ValueGroup} (hx : x ^ q = δ) (hδ : 1 < δ) : 1 < x := by
  by_contra h
  rw [not_lt] at h
  have : x ^ q ≤ 1 := pow_le_one₀ zero_le' h
  rw [hx] at this
  exact absurd hδ (not_lt.mpr this)

private theorem valuation_natCast_lt_one {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    A.valuation (q : AlgebraicClosure ℚ) < 1 := by
  have hq : red (q : A) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero k q
  have hnu : ¬ IsUnit (q : A) := fun hu => (hu.map red).ne_zero hq
  have hlt : A.valuation ((q : A) : AlgebraicClosure ℚ) < 1 :=
    (A.valuation_lt_one_or_eq_one (q : A)).resolve_right fun h => hnu ((A.valuation_eq_one_iff _).mpr h)
  simpa using hlt

end ValueGroup

section Glue

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]

private theorem mem_nonunits_iff_mem_and' {L : Type*} [Field L] (B : ValuationSubring L) (x : L) :
    x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
  constructor
  · intro h
    refine ⟨B.nonunits_subset h, ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inl hx
    · right
      intro hinv
      rw [ValuationSubring.mem_nonunits_iff] at h
      have h1 : B.valuation x⁻¹ ≤ 1 := (B.valuation_le_one_iff _).mpr hinv
      have h2 : B.valuation (x * x⁻¹) < 1 := by
        rw [map_mul]
        calc B.valuation x * B.valuation x⁻¹ ≤ B.valuation x * 1 := by gcongr
          _ = B.valuation x := mul_one _
          _ < 1 := h
      rw [mul_inv_cancel₀ hx, map_one] at h2
      exact lt_irrefl _ h2
  · rintro ⟨hx, h⟩
    rcases h with h | h
    · subst h
      rw [ValuationSubring.mem_nonunits_iff, map_zero]
      exact zero_lt_one
    · rw [ValuationSubring.mem_nonunits_iff]
      rcases lt_or_ge (B.valuation x) 1 with hlt | hle
      · exact hlt
      · exfalso
        apply h
        rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
        exact inv_le_one_of_one_le₀ hle

private theorem mem_nonunits_iff_map_mem_nonunits' {L L' : Type*} [Field L] [Field L']
    (B : ValuationSubring L) (B' : ValuationSubring L') (φ : L →+* L')
    (hmem : ∀ y, y ∈ B ↔ φ y ∈ B') (x : L) :
    x ∈ B.nonunits ↔ φ x ∈ B'.nonunits := by
  rw [mem_nonunits_iff_mem_and', mem_nonunits_iff_mem_and', ← hmem,
    map_eq_zero_iff φ φ.injective, ← map_inv₀, ← hmem]

private theorem hasValue_iff_sub_mem_nonunits' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (g : F) (a : K) :
    v.HasValue g a ↔ g - algebraMap K F a ∈ v.toValuationSubring.nonunits := by
  constructor
  · rintro ⟨hg, hga⟩
    have hmem : g - algebraMap K F a ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' a)
    have hrepr : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - algebraMap K v.toValuationSubring a := rfl
    have key : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
      rw [hrepr, ← residue_eq_zero_iff, map_sub, hga, Place.residue_algebraMap, sub_self]
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mpr key
  · intro h
    have hmem : g - algebraMap K F a ∈ v.toValuationSubring := v.toValuationSubring.nonunits_subset h
    have hg : g ∈ v.toValuationSubring := by
      have := add_mem hmem (v.algebraMap_mem' a)
      simpa using this
    refine ⟨hg, ?_⟩
    have h' : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mp h
    have hrepr : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - algebraMap K v.toValuationSubring a := rfl
    rw [hrepr, ← residue_eq_zero_iff, map_sub, sub_eq_zero, Place.residue_algebraMap] at h'
    exact h'

private theorem mem_restrictAlong_iff' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := by
  letI := algebraAlong φ
  exact Iff.rfl

private theorem hasValuation_restrictAlong_iff' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (A' : ValuationSubring K) (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (W : Place K F') (g : F)
    (γ : A'.ValueGroup) :
    (W.restrictAlong φ hφ).HasValuation A' g γ ↔ W.HasValuation A' (φ g) γ := by
  simp only [Place.hasValuation_iff]
  refine exists_congr fun a => and_congr_left fun _ => ?_
  rw [hasValue_iff_sub_mem_nonunits', hasValue_iff_sub_mem_nonunits',
    mem_nonunits_iff_map_mem_nonunits' _ W.toValuationSubring φ.toRingHom (mem_restrictAlong_iff' φ hφ W), map_sub]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

private theorem heckeAlphaBar_jN : heckeAlphaBar (AlgebraicClosure ℚ) N q (jN N) = jFun N q :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

private theorem heckeBetaBar_jN : heckeBetaBar (AlgebraicClosure ℚ) N q (jN N) = jQFun N q :=
  Subtype.ext (by
    rw [coe_heckeBetaBar]
    show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    exact (coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm)

private theorem hasValuation_restrictAlong_alpha_iff (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (γ : A.ValueGroup) :
    (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).HasValuation A (jN N) γ ↔
      W.HasValuation A (jFun N q) γ := by
  rw [hasValuation_restrictAlong_iff', heckeAlphaBar_jN]

private theorem hasValuation_restrictAlong_beta_iff (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (γ : A.ValueGroup) :
    (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).HasValuation A (jN N) γ ↔
      W.HasValuation A (jQFun N q) γ := by
  rw [hasValuation_restrictAlong_iff', heckeBetaBar_jN]

private theorem evalModularPair_jQFun_jFun_eq_zero (data : ModularPolynomialData q) :
    evalModularPair (jQFun N q) (jFun N q) data.Φ = 0 := by
  have hsym : evalModularPair (jqN q) jq data.Φ = 0 := by
    have key : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN q)
        = (Polynomial.aeval (R := ℤ) (jqN q)).toRingHom :=
      Polynomial.ringHom_ext' (Subsingleton.elim _ _) (by simp)
    have hsymm : EvalSymm data.Φ := ModularPolynomialData.evalSymm_of_prime q data
    unfold evalModularPair
    rw [key, hsymm (jqN q) jq]
    exact data.eval_eq_zero
  apply Subtype.ext
  have hnat := map_evalModularPair (modularFunctionFieldBar (N * q)).val.toRingHom (jQFun N q) (jFun N q) data.Φ
  have hcoe : ((evalModularPair (jQFun N q) (jFun N q) data.Φ : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) = (modularFunctionFieldBar (N * q)).val.toRingHom (evalModularPair (jQFun N q) (jFun N q) data.Φ) := rfl
  have hj : (modularFunctionFieldBar (N * q)).val.toRingHom (jFun N q) = coeffEmb (AlgebraicClosure ℚ) jq := rfl
  have hjq : (modularFunctionFieldBar (N * q)).val.toRingHom (jQFun N q) = coeffEmb (AlgebraicClosure ℚ) (jqN q) := rfl
  rw [hcoe, hnat, hj, hjq, ← map_evalModularPair, hsym, map_zero]
  all_goals simp

private theorem jFun_mem_of_jQFun_mem (data : ModularPolynomialData q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hjq : jQFun N q ∈ W.toValuationSubring) :
    jFun N q ∈ W.toValuationSubring := by
  set O := W.toValuationSubring
  have hjq' : jQFun N q ∈ O.valuation.integer := by
    rw [Valuation.mem_integer_iff, O.valuation_le_one_iff]; exact hjq
  have hint : IsIntegral O.valuation.integer (jFun N q) := by
    refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom O.valuation.integer) ⟨jQFun N q, hjq'⟩),
      data.monic.map _, ?_⟩
    have h0 := evalModularPair_jQFun_jFun_eq_zero (N := N) data
    unfold evalModularPair at h0
    rw [Polynomial.eval₂_map]
    convert h0 using 2 <;> try rfl
    refine Polynomial.ringHom_ext' ?_ ?_
    · exact Subsingleton.elim _ _
    all_goals (try simp)
    all_goals rfl
  have hmem := (Valuation.integer.integers O.valuation).mem_of_integral hint
  rw [Valuation.mem_integer_iff, O.valuation_le_one_iff] at hmem
  exact hmem

private theorem exists_hasValue_of_mem (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {g : modularFunctionFieldBar (N * q)} (hg : g ∈ W.toValuationSubring) : ∃ a : AlgebraicClosure ℚ, W.HasValue g a := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (N * q)
  haveI : Module.Finite (AlgebraicClosure ℚ) W.ResidueField := IsCurveOver.finiteResidue W
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) W.ResidueField := Algebra.IsIntegral.of_finite _ _
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := W.ResidueField)).2
  obtain ⟨a, ha, -⟩ := W.exists_hasValue_of_surjective hsurj hg
  exact ⟨a, ha⟩

private theorem exists_hasValuation_jFun (data : ModularPolynomialData q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) {γ : A.ValueGroup}
    (hW : W.HasValuation A (jQFun N q) γ) : ∃ δ : A.ValueGroup, W.HasValuation A (jFun N q) δ := by
  obtain ⟨b, hb, -⟩ := (Place.hasValuation_iff _ _ _ _).mp hW
  have hjq : jQFun N q ∈ W.toValuationSubring := hb.1
  obtain ⟨a, ha⟩ := exists_hasValue_of_mem W (jFun_mem_of_jQFun_mem data W hjq)
  exact ⟨A.valuation a, (Place.hasValuation_iff _ _ _ _).mpr ⟨a, ha, rfl⟩⟩

private theorem mem_smul_iff' {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F) (v : Place K F)
    (x : F) : x ∈ (g • v).toValuationSubring ↔ g⁻¹ • x ∈ v.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

private theorem semilinear_smul_restrictAlong' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (s : SemilinearAut K F') (t : SemilinearAut K F) (h : ∀ x, α (t • x) = s • β x) (W : Place K F') :
    (s • W).restrictAlong α hα = t • W.restrictAlong β hβ := by
  ext x
  rw [mem_restrictAlong_iff', mem_smul_iff', mem_smul_iff', mem_restrictAlong_iff']
  have hx : s⁻¹ • α x = β (t⁻¹ • x) := by
    rw [inv_smul_eq_iff, ← h, smul_inv_smul]
  rw [hx]

private theorem arithmeticGalois_smul_restrictAlong (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
        = arithmeticGalois (modularFunctionFieldFull N) σ • W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ∧
      (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
        = arithmeticGalois (modularFunctionFieldFull N) σ • W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ :=
  ⟨semilinear_smul_restrictAlong' _ _ hα hα _ _ (fun x => (arithmeticGalois_smul_heckeAlphaBar N q σ x).symm) W,
    semilinear_smul_restrictAlong' _ _ hβ hβ _ _ (fun x => (arithmeticGalois_smul_heckeBetaBar N q σ x).symm) W⟩

private theorem exists_swap_places (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) (hqN : ¬ q ∣ N) :
    ∃ τ : modularFunctionFieldBar (N * q) ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar (N * q),
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (τ • W).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
            = W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ ∧
        (τ • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
            = W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN
  obtain ⟨τ, hτα, hτβ⟩ := exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar (AlgebraicClosure ℚ) N q σ hσ
  refine ⟨τ, fun W => ⟨?_, ?_⟩⟩
  · have h := Place.smul_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) (heckeBetaBar (AlgebraicClosure ℚ) N q)
      hα hβ τ (AlgEquiv.refl) (fun x => by simpa using (AlgHom.congr_fun hτβ x).symm) W
    rwa [show (AlgEquiv.refl : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N) = 1 from rfl,
      one_smul] at h
  · have h := Place.smul_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      hβ hα τ (AlgEquiv.refl) (fun x => by simpa using (AlgHom.congr_fun hτα x).symm) W
    rwa [show (AlgEquiv.refl : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N) = 1 from rfl,
      one_smul] at h

private theorem ord_pos_of_mem_nonunits' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) (h : f ∈ v.toValuationSubring.nonunits) : 0 < v.ord f := by
  have hmem : f ∈ v.toValuationSubring := v.toValuationSubring.nonunits_subset h
  have h' : ((⟨f, hmem⟩ : v.toValuationSubring) : F) ∈ v.toValuationSubring.nonunits := h
  rw [ValuationSubring.coe_mem_nonunits_iff] at h'
  exact (v.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'

private theorem jQFun_ne_zero' : jQFun N q ≠ 0 := by
  intro h
  have h' : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = 0 := congrArg Subtype.val h
  rw [map_eq_zero_iff _ (coeffEmb (AlgebraicClosure ℚ)).injective, map_eq_zero_iff _ (qExpand ℚ q).injective] at h'
  exact jq_ne_zero h'

private theorem jFun_ne_algebraMap (a : AlgebraicClosure ℚ) :
    jFun N q ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a := by
  intro h
  have h' : coeffEmb (AlgebraicClosure ℚ) jq = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a :=
    congrArg Subtype.val h
  have hc := congrArg (fun x : LaurentSeries (AlgebraicClosure ℚ) => x.coeff (-1 : ℤ)) h'

  have hconst : (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a).coeff (-1 : ℤ) = 0 := by
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
    exact HahnSeries.coeff_single_of_ne (by decide)
  simp only [coeffEmb_coeff, coeff_jq_neg_one, map_one] at hc
  rw [hconst] at hc
  exact one_ne_zero hc

end Glue

section BaseDepth

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
  [CharP k q] {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem exists_one_lt_hasValuation_jFun (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : IsInftySide P c)
    (hord : 0 ≤ c.ord (jQFun N q)) : ∃ γ : A.ValueGroup, 1 < γ ∧ c.HasValuation A (jFun N q) γ := by
  have hjq : jQFun N q ∈ c.toValuationSubring := c.mem_of_ord_nonneg jQFun_ne_zero' hord
  obtain ⟨J, hJ⟩ := exists_hasValue_of_mem c (jFun_mem_of_jQFun_mem data c hjq)
  refine ⟨A.valuation J, ?_, (Place.hasValuation_iff _ _ _ _).mpr ⟨J, hJ, rfl⟩⟩
  by_contra hle
  rw [not_lt] at hle
  have hJA : J ∈ A := (A.valuation_le_one_iff J).mp hle
  have hcusp := hc.1 ⟨J, hJA⟩
  have hpos : 0 < c.ord (jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) J) :=
    ord_pos_of_mem_nonunits' c (sub_ne_zero.mpr (jFun_ne_algebraMap J)) ((hasValue_iff_sub_mem_nonunits' c _ _).mp hJ)
  exact absurd (lt_of_lt_of_le hpos hcusp) (lt_irrefl _)

end BaseDepth

section Chain

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private structure ChainState (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) where
  vPrev : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
  vCur : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
  W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
  δPrev : A.ValueGroup
  δCur : A.ValueGroup
  hδPrev : 1 < δPrev
  hδCur : 1 < δCur
  hpow : δCur ^ q = δPrev
  hvPrev : vPrev.HasValuation A (jN N) δPrev
  hvCur : vCur.HasValuation A (jN N) δCur
  hWβ : W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = vPrev
  hWα : W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = vCur
  hWφ : P.sp vCur = frobOnPlacesGeomLevel k N data hKr (P.sp vPrev)
  hmovedPrev : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp vPrev)) ≠ P.sp vPrev
  hmovedCur : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp vCur)) ≠ P.sp vCur
  hinert : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
    arithmeticGalois (modularFunctionFieldFull N) σ • v₀ = v₀ →
    arithmeticGalois (modularFunctionFieldFull N) σ • vCur = vCur

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} {hqN : ¬ q ∣ N}
  {v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}

private noncomputable def ChainState.step (s : ChainState P hqN v₀) :
    { t : ChainState P hqN v₀ // t.vPrev = s.vCur ∧ t.δPrev = s.δCur } := by
  classical

  have hd2 := P.d2 s.vCur s.hmovedCur
  let W' := hd2.choose
  obtain ⟨hW'β, hW'sp, -, hW'uniq⟩ := hd2.choose_spec

  have hW'jq : W'.HasValuation A (jQFun N q) s.δCur :=
    (hasValuation_restrictAlong_beta_iff hβ W' s.δCur).mp (hW'β ▸ s.hvCur)

  have hex := exists_hasValuation_jFun data W' hW'jq
  let δ' := hex.choose
  have hW'j : W'.HasValuation A (jFun N q) δ' := hex.choose_spec

  have hqA : A.valuation (q : AlgebraicClosure ℚ) < 1 := valuation_natCast_lt_one red
  have hdich := hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence A hqA hKr W' s.hδCur hW'j hW'jq

  have hshallow : s.δCur = δ' ^ q := by
    rcases hdich with h | h
    · exact h
    · exfalso
      obtain ⟨τ, hτ⟩ := exists_swap_places hα hβ hqN
      obtain ⟨hτα, hτβ⟩ := hτ s.W
      have hWW' : (τ • s.W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
          = W'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ := by
        rw [hτβ, s.hWα, hW'β]
      have hW : (τ • s.W).HasValuation A (jQFun N q) s.δCur :=
        (hasValuation_restrictAlong_beta_iff hβ _ _).mp (by rw [hτβ, s.hWα]; exact s.hvCur)
      have hdeep : (τ • s.W).HasValuation A (jFun N q) (s.δCur ^ q) :=
        (hasValuation_restrictAlong_alpha_iff hα _ _).mp (by rw [hτα, s.hWβ, s.hpow]; exact s.hvPrev)
      have hdeep' : W'.HasValuation A (jFun N q) (s.δCur ^ q) := h ▸ hW'j
      have heq : τ • s.W = W' :=
        eq_of_restrictAlong_heckeBetaBar_eq_of_hasValuation_jFun_pow A hqA hKr hβ hqN hWW' s.hδCur hW hdeep hdeep'

      have hα' : W'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = s.vPrev := by
        rw [← heq, hτα, s.hWβ]
      apply s.hmovedPrev
      rw [← s.hWφ]
      rw [hα'] at hW'sp
      exact hW'sp.symm

  have hδ' : 1 < δ' := one_lt_of_pow_eq hshallow.symm s.hδCur
  refine ⟨{ vPrev := s.vCur
            vCur := W'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
            W := W'
            δPrev := s.δCur
            δCur := δ'
            hδPrev := s.hδCur
            hδCur := hδ'
            hpow := hshallow.symm
            hvPrev := s.hvCur
            hvCur := (hasValuation_restrictAlong_alpha_iff hα W' δ').mpr hW'j
            hWβ := hW'β
            hWα := rfl
            hWφ := hW'sp
            hmovedPrev := s.hmovedCur
            hmovedCur := ?_
            hinert := ?_ }, rfl, rfl⟩
  ·
    intro hfix
    apply s.hmovedCur
    apply frobOnPlacesGeomLevel_injective k N data hKr
    rw [hW'sp] at hfix
    exact hfix
  ·
    intro σ hσ hσv₀
    have hσcur : arithmeticGalois (modularFunctionFieldFull N) σ • s.vCur = s.vCur := s.hinert σ hσ hσv₀
    obtain ⟨hcα, hcβ⟩ := arithmeticGalois_smul_restrictAlong hα hβ σ W'
    have hfixW' : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W' = W' := by
      apply hW'uniq
      · rw [hcβ, hW'β, hσcur]
      · rw [hcα, P.d6_inertia σ hσ, hW'sp]
    rw [← hcα, hfixW']

private theorem ChainState.step_vPrev (s : ChainState P hqN v₀) : (s.step.1).vPrev = s.vCur := s.step.2.1

private theorem ChainState.step_δPrev (s : ChainState P hqN v₀) : (s.step.1).δPrev = s.δCur := s.step.2.2

end Chain
end Step

namespace InertiaValues

private noncomputable def inertiaIndex (A : ValuationSubring (AlgebraicClosure ℚ))
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) : ℕ :=
  (L₀.fixingSubgroup.subgroupOf (A.inertiaSubgroupIn ℚ)).index

private theorem inertiaIndex_ne_zero (A : ValuationSubring (AlgebraicClosure ℚ))
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀] :
    inertiaIndex A L₀ ≠ 0 := by
  haveI : L₀.fixingSubgroup.FiniteIndex := by
    refine ⟨?_⟩
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  exact Subgroup.FiniteIndex.index_ne_zero

private theorem valuation_apply_eq_of_mem_inertiaSubgroupIn (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (z : AlgebraicClosure ℚ) : A.valuation (σ z) = A.valuation z := by
  unfold ValuationSubring.inertiaSubgroupIn at hσ
  obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hσ
  exact ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A t.2 z

private theorem core (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L₀] {y : AlgebraicClosure ℚ} (hy0 : y ≠ 0) (hy1 : A.valuation y ≤ 1)
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (∀ z ∈ L₀, σ z = z) → σ y = y) :
    ∃ r : ℚ, r ≠ 0 ∧ A.valuation y ^ inertiaIndex A L₀ = A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) r) := by
  classical
  set I := A.inertiaSubgroupIn ℚ with hI

  have hle : L₀.fixingSubgroup.subgroupOf I ≤ MulAction.stabilizer I y := by
    intro σ hσ
    rw [Subgroup.mem_subgroupOf] at hσ
    rw [MulAction.mem_stabilizer_iff]
    exact hfix σ σ.2 ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ)
  have hdvd : (MulAction.stabilizer I y).index ∣ inertiaIndex A L₀ := Subgroup.index_dvd_of_le hle
  have hstab_ne : (MulAction.stabilizer I y).index ≠ 0 := fun h => inertiaIndex_ne_zero A L₀ (by
    rcases hdvd with ⟨k, hk⟩
    rw [hk, h, zero_mul])
  haveI : (MulAction.stabilizer I y).FiniteIndex := ⟨hstab_ne⟩
  haveI : Finite (MulAction.orbit I y) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer I y).symm
  have horb : (MulAction.orbit I y).Finite := Set.toFinite _
  set S : Finset (AlgebraicClosure ℚ) := horb.toFinset with hS
  have hmemS : ∀ z, z ∈ S ↔ z ∈ MulAction.orbit I y := fun z => by simp [hS]
  set c : AlgebraicClosure ℚ := ∏ z ∈ S, z with hc

  have hval : ∀ z ∈ S, A.valuation z = A.valuation y := by
    intro z hz
    obtain ⟨τ, rfl⟩ := (hmemS z).1 hz
    exact valuation_apply_eq_of_mem_inertiaSubgroupIn A τ.2 y
  have hne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz
    obtain ⟨τ, rfl⟩ := (hmemS z).1 hz
    exact (map_ne_zero_iff (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).injective).2 hy0

  have hcard : S.card = (MulAction.stabilizer I y).index := by
    rw [MulAction.index_stabilizer, Set.ncard_eq_toFinset_card _ horb]
  have hvc : A.valuation c = A.valuation y ^ (MulAction.stabilizer I y).index := by
    rw [hc, map_prod, Finset.prod_congr rfl hval, Finset.prod_const, hcard]
  have hcA : c ∈ A := by
    rw [← A.valuation_le_one_iff, hvc]
    exact pow_le_one₀ zero_le' hy1
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 hne

  have hcfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ I → σ c = c := by
    intro σ hσ
    rw [hc, map_prod]
    refine Finset.prod_nbij (fun z => σ z) ?_ ?_ ?_ (fun z _ => rfl)
    · intro z hz
      obtain ⟨τ, rfl⟩ := (hmemS z).1 hz
      rw [hmemS]
      exact ⟨⟨σ, hσ⟩ * τ, mul_smul _ _ _⟩
    · exact fun z _ z' _ h => σ.injective h
    · intro z hz
      obtain ⟨τ, rfl⟩ := (hmemS z).1 hz
      refine ⟨(⟨σ, hσ⟩ : I)⁻¹ • (τ • y), ?_, ?_⟩
      · rw [Finset.mem_coe, hmemS]
        exact ⟨(⟨σ, hσ⟩ : I)⁻¹ * τ, mul_smul _ _ _⟩
      · show σ ((⟨σ, hσ⟩ : I)⁻¹ • (τ • y)) = τ • y
        exact smul_inv_smul (⟨σ, hσ⟩ : I) (τ • y)
  obtain ⟨s, u, huA, huiA, hcu⟩ :=
    ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn q A hA c hcA hc0 hcfix

  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hc0 (by simpa using hcu)
  have hvu : A.valuation u = 1 := by
    have h1 := (A.valuation_le_one_iff u).2 huA
    have h2 := (A.valuation_le_one_iff u⁻¹).2 huiA
    rw [map_inv₀] at h2
    have hv0 : A.valuation u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
    refine le_antisymm h1 ?_
    by_contra hlt
    rw [not_le] at hlt
    exact absurd h2 (not_le.2 ((one_lt_inv₀ (pos_iff_ne_zero.2 hv0)).2 hlt))
  have hmain : A.valuation y ^ (MulAction.stabilizer I y).index = A.valuation ((q : AlgebraicClosure ℚ)) ^ s := by
    rw [← hvc, hcu, map_mul, map_pow, hvu, mul_one]
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨(q : ℚ) ^ (s * k), pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero), ?_⟩
  have halg : algebraMap ℚ (AlgebraicClosure ℚ) ((q : ℚ) ^ (s * k)) = (q : AlgebraicClosure ℚ) ^ (s * k) := by
    rw [map_pow, map_natCast]
  rw [halg, map_pow, hk, pow_mul, hmain, ← pow_mul]

private theorem exists_valuation_pow_inertiaIndex_eq (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L₀] {y : AlgebraicClosure ℚ} (hy0 : y ≠ 0)
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (∀ z ∈ L₀, σ z = z) → σ y = y) :
    ∃ r : ℚ, r ≠ 0 ∧ A.valuation y ^ inertiaIndex A L₀ = A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) r) := by
  by_cases hy1 : A.valuation y ≤ 1
  · exact core q A hA L₀ hy0 hy1 hfix
  · have hy1' : A.valuation y⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hy1))
    have hfix' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (∀ z ∈ L₀, σ z = z) → σ y⁻¹ = y⁻¹ := fun σ hσ hL => by
      rw [map_inv₀, hfix σ hσ hL]
    obtain ⟨r, hr0, hr⟩ := core q A hA L₀ (inv_ne_zero hy0) hy1' hfix'
    refine ⟨r⁻¹, inv_ne_zero hr0, ?_⟩
    rw [map_inv₀, map_inv₀, ← hr, map_inv₀, inv_pow, inv_inv]

private theorem false_of_forall_pow_eq_of_one_lt (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L₀] (δ : ℕ → A.ValueGroup) (hstep : ∀ n, δ (n + 1) ^ q = δ n) (hδ0 : 1 < δ 0)
    (hy : ∀ n, ∃ y : AlgebraicClosure ℚ, y ≠ 0 ∧ A.valuation y = δ n ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (∀ z ∈ L₀, σ z = z) → σ y = y) :
    False := by
  have hm := inertiaIndex_ne_zero A L₀
  have hK : ∀ n, ∃ x ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), x ≠ 0 ∧
      A.valuation x = δ n ^ inertiaIndex A L₀ := by
    intro n
    obtain ⟨y, hy0, hyv, hyfix⟩ := hy n
    obtain ⟨r, hr0, hr⟩ := exists_valuation_pow_inertiaIndex_eq q A hA L₀ hy0 hyfix
    refine ⟨algebraMap ℚ (AlgebraicClosure ℚ) r, IntermediateField.algebraMap_mem _ r,
      (map_ne_zero _).2 hr0, ?_⟩
    rw [← hr, hyv]
  have hstep' : ∀ n, (δ (n + 1) ^ inertiaIndex A L₀) ^ q = δ n ^ inertiaIndex A L₀ := fun n => by
    rw [← pow_right_comm, hstep]
  have h1 := ValuationSubring.valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional A ⊥
    (Fact.out : q.Prime).one_lt (fun n => δ n ^ inertiaIndex A L₀) hK hstep'
  exact absurd h1 (one_lt_pow₀ hδ0 hm).ne'
end InertiaValues

namespace Main
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple
open Step InertiaValues
section Glue

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]

private theorem arithmeticGalois_smul_jN (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) σ • Step.jN N = Step.jN N :=
  Subtype.ext (coeffMap_coeffEmb σ jq)

private theorem apply_eq_of_smul_eq (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hσv : arithmeticGalois (modularFunctionFieldFull N) σ • v = v) {a : AlgebraicClosure ℚ}
    (ha : v.HasValue (Step.jN N) a) : σ a = a := by
  have h1 := ha.smul (arithmeticGalois (modularFunctionFieldFull N) σ)
  rw [hσv, arithmeticGalois_smul_jN, baseAut_arithmeticGalois] at h1
  exact (ha.unique h1).symm

end Glue

section NonUnit

private theorem natCast_mem_nonunits {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] (red : A →+* k) :
    ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hqA, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : red ⟨(q : ℕ), hqA⟩ = (q : k) := by
    rw [show (⟨((q : ℕ) : AlgebraicClosure ℚ), hqA⟩ : A) = ((q : ℕ) : A) from Subtype.ext (by simp)]
    exact map_natCast red q
  have h0 : (q : k) = 0 := CharP.cast_eq_zero k q
  exact (hu.map red).ne_zero (h1.trans h0)

end NonUnit

section Assembly

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem reduceSnd_eq_of_isInftySide (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∀ c, IsInftySide P c →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c)) ≠ P.reduceSnd c →
      0 ≤ c.ord (jQFun N q) →
      P.reduceSnd c = frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) := by
  intro c hIS hmoved hfin
  rcases P.d1 c with h₁ | h₂
  swap
  · exact h₂.symm
  exfalso

  obtain ⟨γ, hγ, hj⟩ := Step.exists_one_lt_hasValuation_jFun P c hIS hfin
  have hjq : c.HasValuation A (jQFun N q) (γ ^ q) := hasValuation_jQFun_pow_of_isInftySide P c hIS hj
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hγq : 1 < γ ^ q := one_lt_pow' hγ (NeZero.ne q)
  set v₀ := c.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ with hv₀
  have s₀ : Step.ChainState P hqN v₀ :=
    { vPrev := v₀
      vCur := c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
      W := c
      δPrev := γ ^ q
      δCur := γ
      hδPrev := hγq
      hδCur := hγ
      hpow := rfl
      hvPrev := (hasValuation_restrictAlong_beta_iff hβ c (γ ^ q)).mpr hjq
      hvCur := (hasValuation_restrictAlong_alpha_iff hα c γ).mpr hj
      hWβ := rfl
      hWα := rfl
      hWφ := h₁
      hmovedPrev := hmoved
      hmovedCur := by
        intro hfix
        apply hmoved
        apply frobOnPlacesGeomLevel_injective k N data hKr
        change frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
          (P.sp (c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα))) = _ at hfix
        rw [h₁] at hfix
        exact hfix
      hinert := by
        intro σ hσ hσv₀
        obtain ⟨W₀, -, -, -, huniq⟩ := P.d2 v₀ hmoved
        obtain ⟨hcα, hcβ⟩ := arithmeticGalois_smul_restrictAlong hα hβ σ c
        have hc0 : c = W₀ := huniq c rfl h₁
        have hσc : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • c = W₀ := by
          apply huniq
          · rw [hcβ, hσv₀]
          · rw [hcα, P.d6_inertia σ hσ, h₁]
        rw [← hcα, hσc, ← hc0] }

  let S : ℕ → Step.ChainState P hqN v₀ := fun n => Nat.rec s₀ (fun _ s => (s.step).1) n
  let δ : ℕ → A.ValueGroup := fun n => (S n).δCur
  have hstep : ∀ n, δ (n + 1) ^ q = δ n := by
    intro n
    change ((S n).step.1).δCur ^ q = (S n).δCur
    rw [((S n).step.1).hpow]
    exact Step.ChainState.step_δPrev (S n)
  have hδ0 : 1 < δ 0 := s₀.hδCur

  obtain ⟨L₀, hfd, hL₀⟩ := MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_place N v₀
  haveI := hfd

  refine InertiaValues.false_of_forall_pow_eq_of_one_lt q A (natCast_mem_nonunits red) L₀ δ hstep hδ0 ?_
  intro n
  obtain ⟨a, ha, hav⟩ := (S n).hvCur
  refine ⟨a, ?_, hav, ?_⟩
  · intro h0
    have h1 := (S n).hδCur
    rw [← hav, h0, map_zero] at h1
    exact (not_lt.mpr zero_le') h1
  · intro σ hσ hσL₀
    have hσv₀ := hL₀ σ ((IntermediateField.mem_fixingSubgroup_iff L₀ σ).mpr hσL₀)
    exact apply_eq_of_smul_eq σ (S n).vCur ((S n).hinert σ hσ hσv₀) ha

end Assembly
end Main

end SolutionAux

open ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∀ c, IsInftySide P c →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c)) ≠ P.reduceSnd c →
      0 ≤ c.ord (jQFun N q) →
      P.reduceSnd c = frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) :=
  SolutionAux.Main.reduceSnd_eq_of_isInftySide P hqN

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg (solution)
