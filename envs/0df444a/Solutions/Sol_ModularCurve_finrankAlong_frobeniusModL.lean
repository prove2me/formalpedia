-- Prove2me | solution 1 for ModularCurve.finrankAlong_frobeniusModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d24ae35f-e1e7-511a-ac1f-869ea9678532

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_frobeniusModL
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace W6FK1

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem finrankAlong_eq_relfinrank (φ : F →ₐ[K] F') :
    AlgebraicCurve.finrankAlong K φ =
      IntermediateField.relfinrank ((⊤ : IntermediateField K F).map φ) ⊤ := by
  rw [IntermediateField.relfinrank_top_right]
  letI : Algebra F F' := AlgebraicCurve.algebraAlong φ
  change Module.finrank F F' = Module.finrank ((⊤ : IntermediateField K F).map φ) F'
  refine Algebra.finrank_eq_of_equiv_equiv
    ((IntermediateField.topEquiv (F := K) (E := F)).symm.trans
      (IntermediateField.equivMap (⊤ : IntermediateField K F) φ)).toRingEquiv
    (RingEquiv.refl F') ?_
  ext a
  rfl

theorem relfinrank_adjoin_simple (E : IntermediateField K F) {a : F} (ha : IsIntegral E a) :
    IntermediateField.relfinrank E (restrictScalars K E⟮a⟯) = (minpoly E a).natDegree := by
  have hle : E ≤ restrictScalars K E⟮a⟯ := fun u hu => (algebraMap E E⟮a⟯ ⟨u, hu⟩).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  have hext : extendScalars hle = E⟮a⟯ :=
    IntermediateField.restrictScalars_injective K (extendScalars_restrictScalars hle)
  rw [hext, IntermediateField.adjoin.finrank ha]

theorem not_mem_adjoin_pow {x : F} (hx : Transcendental K x) {p : ℕ} (hp : 2 ≤ p) :
    x ∉ K⟮x ^ p⟯ := by
  intro hmem
  rw [mem_adjoin_simple_iff] at hmem
  obtain ⟨r, s, hrs⟩ := hmem
  by_cases hs : aeval (x ^ p) s = 0
  · rw [hs, div_zero] at hrs
    exact hx (hrs ▸ isAlgebraic_zero)
  · have h1 : x * aeval (x ^ p) s = aeval (x ^ p) r := by
      rw [← div_mul_cancel₀ (aeval (x ^ p) r) hs, ← hrs]
    have h2 : aeval x (X * expand K p s) = aeval x (expand K p r) := by
      rw [map_mul, aeval_X, expand_aeval, expand_aeval, h1]
    have h3 : X * expand K p s = expand K p r := (transcendental_iff_injective.mp hx) h2
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hs (by simp)
    have hp0 : 0 < p := by omega
    have hes : expand K p s ≠ 0 := by rwa [Ne, expand_eq_zero hp0]
    have h4 := congrArg natDegree h3
    rw [natDegree_X_mul hes, natDegree_expand, natDegree_expand] at h4
    have h5 : p ∣ s.natDegree * p + 1 := h4 ▸ dvd_mul_left p r.natDegree
    have h6 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p _)).mp h5
    have : p ≤ 1 := Nat.le_of_dvd one_pos h6
    omega

theorem relfinrank_map_top_eq {p : ℕ} [hp : Fact p.Prime] [CharP F p] (φ : F →ₐ[K] F) {x : F}
    (hx : Transcendental K x) (hφx : φ x = x ^ p) [FiniteDimensional K⟮x⟯ F] :
    IntermediateField.relfinrank ((⊤ : IntermediateField K F).map φ) ⊤ = p := by
  have hp' : p.Prime := hp.out
  set L : IntermediateField K F := K⟮x⟯ with hL
  set L' : IntermediateField K F := K⟮x ^ p⟯ with hL'

  have hmapL : L.map φ = L' := by
    rw [hL, adjoin_map, Set.image_singleton, hφx]
  have hL'L : L' ≤ L := adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self K x) p)
  have hL'E : L' ≤ (⊤ : IntermediateField K F).map φ := hmapL ▸ map_mono φ le_top

  have hnpos : 0 < Module.finrank L F := Module.finrank_pos
  have hn : IntermediateField.relfinrank L ⊤ = Module.finrank L F := relfinrank_top_right L

  have h1 : IntermediateField.relfinrank L' ((⊤ : IntermediateField K F).map φ) = Module.finrank L F := by
    rw [← hmapL, relfinrank_map_map, relfinrank_top_right]

  have hxint : IsIntegral L' x :=
    ⟨X ^ p - C (AdjoinSimple.gen K (x ^ p)), monic_X_pow_sub_C _ hp'.ne_zero, by simp⟩
  have hLeq : restrictScalars K L'⟮x⟯ = L := by
    rw [hL', hL, adjoin_simple_adjoin_simple]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro u (rfl | rfl)
      · exact pow_mem (mem_adjoin_simple_self K x) p
      · exact mem_adjoin_simple_self K u
    · exact adjoin.mono K _ _ (Set.subset_insert _ _)
  have hminpoly : minpoly L' x = X ^ p - C (AdjoinSimple.gen K (x ^ p)) := by
    refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ (monic_X_pow_sub_C _ hp'.ne_zero)).symm
    · refine X_pow_sub_C_irreducible_of_prime hp' fun b hb => ?_
      have hb' : ((b : F)) ^ p = x ^ p := by
        have := congrArg (algebraMap L' F) hb
        simpa using this
      have hbx : (b : F) = x := frobenius_inj F p (by rw [frobenius_def, frobenius_def, hb'])
      have hmem : x ∈ L' := hbx ▸ b.2
      exact not_mem_adjoin_pow hx hp'.two_le hmem
    · simp
  have h2 : IntermediateField.relfinrank L' L = p := by
    rw [← hLeq, relfinrank_adjoin_simple L' hxint, hminpoly, natDegree_X_pow_sub_C]

  have h3 := relfinrank_mul_relfinrank hL'L (le_top : L ≤ ⊤)
  have h4 := relfinrank_mul_relfinrank hL'E (le_top : (⊤ : IntermediateField K F).map φ ≤ ⊤)
  rw [h2, hn] at h3
  rw [h1] at h4
  have h5 : Module.finrank L F *
      IntermediateField.relfinrank ((⊤ : IntermediateField K F).map φ) ⊤ = Module.finrank L F * p := by
    rw [h4, ← h3, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hnpos h5

end Generic

end W6FK1

end

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "Polynomial IntermediateField HahnSeries ModularCurve~coeffMap_injective"

namespace W6FK1

section JBar

variable (K : Type*) [Field K]

theorem eq_zero_of_aeval_jqModC_eq_zero {p : K[X]} (hp : aeval (jqModC K) p = 0) : p = 0 := by
  by_contra hp0
  set n := p.natDegree with hn
  have hcoeff : (aeval (jqModC K) p).coeff (-(n : ℤ)) = p.coeff n := by
    rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single n]
    · rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_self, mul_one]
    · intro i hi hin
      have hilt : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_of_lt K (by omega), mul_zero]
    · intro hn'
      exact absurd (Finset.self_mem_range_succ n) hn'
  rw [hp, HahnSeries.coeff_zero] at hcoeff
  exact hp0 (leadingCoeff_eq_zero.mp hcoeff.symm)

theorem transcendental_jqModC : Transcendental K (jqModC K) :=
  transcendental_iff.mpr fun _ hp => eq_zero_of_aeval_jqModC_eq_zero K hp

end JBar

section ModularPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

variable (R) in

def evalAtJC : ℤ[X] →+* LaurentSeries R := eval₂RingHom (Int.castRingHom _) (jqModC R)

@[scoped simp]
theorem evalAtJC_X : evalAtJC R X = jqModC R := by simp [evalAtJC]

theorem coeffMap_comp_evalAtJC (f : R →+* S) : (coeffMap f).comp (evalAtJC R) = evalAtJC S :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [coeffMap_jqModC])

theorem coeffMap_eval₂_evalAtJC (f : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (N : ℕ) [NeZero N] :
    coeffMap f (Φ.eval₂ (evalAtJC R) (jqNModC R N)) = Φ.eval₂ (evalAtJC S) (jqNModC S N) := by
  rw [hom_eval₂, coeffMap_comp_evalAtJC, coeffMap_jqNModC]

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem evalAtJ_eq : evalAtJ = evalAtJC ℚ := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [evalAtJ_X, evalAtJC_X, jqModC_rat]

theorem modularPolynomial_eval₂_eq_zero {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (R : Type*) [CommRing R] : data.Φ.eval₂ (evalAtJC R) (jqNModC R N) = 0 := by
  have hQ : data.Φ.eval₂ (evalAtJC ℚ) (jqNModC ℚ N) = 0 := by
    rw [← evalAtJ_eq, jqNModC_rat]; exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (evalAtJC ℤ) (jqNModC ℤ N) = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [coeffMap_eval₂_evalAtJC, hQ, map_zero]
  rw [← coeffMap_eval₂_evalAtJC (Int.castRingHom R), hZ, map_zero]

end ModularPolynomial

section FunctionField

variable (K : Type*) [Field K] (N : ℕ)

def jGen : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jGen : (jGen K N : LaurentSeries K) = jqModC K := rfl

def jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) : modularFunctionFieldFullC K N :=
  ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩

@[scoped simp] theorem coe_jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (jGenD K N d hd : LaurentSeries K) = qExpand K d (jqModC K) := rfl

theorem transcendental_jGen : Transcendental K (jGen K N) := by
  rw [← transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (modularFunctionFieldFullC K N) (LaurentSeries K))]
  exact transcendental_jqModC K

def gensC : Set (modularFunctionFieldFullC K N) := Subtype.val ⁻¹' divisorExpansionsC K N

theorem image_gensC : Subtype.val '' gensC K N = divisorExpansionsC K N := by
  rw [gensC, Set.image_preimage_eq_iff]
  rintro x ⟨d, hne, hd, rfl⟩
  exact ⟨⟨_, @jqModCd_mem_full K _ N d hne hd⟩, rfl⟩

theorem gensC_finite [NeZero N] : (gensC K N).Finite := by
  classical
  let g : N.divisors → modularFunctionFieldFullC K N := fun d =>
    haveI : NeZero (d : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors d.2)⟩
    ⟨qExpand K d (jqModC K), jqModCd_mem_full K N (Nat.dvd_of_mem_divisors d.2)⟩
  refine (Set.finite_range g).subset ?_
  rintro ⟨x, hx⟩ ⟨d, hne, hd, rfl⟩
  refine ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, NeZero.ne N⟩⟩, Subtype.ext ?_⟩
  exact qExpand_congr rfl _

theorem adjoin_gensC_eq_top : adjoin K (gensC K N) = ⊤ := by
  apply lift_injective
  have h1 := IntermediateField.lift_adjoin K (modularFunctionFieldFullC K N) (gensC K N)
  have h2 := IntermediateField.lift_top K (modularFunctionFieldFullC K N)
  rw [image_gensC] at h1
  exact h1.trans h2.symm

theorem adjoin_adjoin_gensC_eq_top : adjoin K⟮jGen K N⟯ (gensC K N) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [restrictScalars_adjoin, restrictScalars_top]
  refine le_antisymm le_top ?_
  rw [← adjoin_gensC_eq_top]
  exact adjoin.mono K _ _ Set.subset_union_right

theorem isIntegral_jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) : IsIntegral K⟮jGen K N⟯ (jGenD K N d hd) := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData d
  let e : ℤ[X] →+* K⟮jGen K N⟯ := eval₂RingHom (Int.castRingHom _) (AdjoinSimple.gen K (jGen K N))
  refine ⟨data.Φ.map e, data.monic.map e, ?_⟩
  rw [eval₂_map]
  apply FaithfulSMul.algebraMap_injective (modularFunctionFieldFullC K N) (LaurentSeries K)
  rw [map_zero, hom_eval₂]
  have hcomp : ((algebraMap (modularFunctionFieldFullC K N) (LaurentSeries K)).comp
      ((algebraMap K⟮jGen K N⟯ (modularFunctionFieldFullC K N)).comp e)) = evalAtJC K := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [e, evalAtJC]
  rw [hcomp]
  exact modularPolynomial_eval₂_eq_zero data K

theorem isIntegral_of_mem_gensC {y : modularFunctionFieldFullC K N} (hy : y ∈ gensC K N) :
    IsIntegral K⟮jGen K N⟯ y := by
  obtain ⟨d, hne, hd, hyd⟩ := hy
  have : y = jGenD K N d hd := Subtype.ext hyd
  rw [this]
  exact isIntegral_jGenD K N d hd

theorem finiteDimensional_adjoin_jGen [NeZero N] :
    FiniteDimensional K⟮jGen K N⟯ (modularFunctionFieldFullC K N) := by
  haveI : Finite (gensC K N) := (gensC_finite K N).to_subtype
  haveI : FiniteDimensional K⟮jGen K N⟯ (adjoin K⟮jGen K N⟯ (gensC K N)) :=
    finiteDimensional_adjoin fun y hy => isIntegral_of_mem_gensC K N hy
  rw [adjoin_adjoin_gensC_eq_top] at this
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := K⟮jGen K N⟯) (E := modularFunctionFieldFullC K N)).toLinearEquiv

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

omit [Fact ℓ.Prime] in
theorem charP_full : CharP (modularFunctionFieldFullC K N) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldFullC K N)).injective ℓ

theorem frobeniusModL_jGen [NeZero N] : frobeniusModL K N ℓ (jGen K N) = jGen K N ^ ℓ := by
  apply Subtype.ext
  rw [coe_frobeniusModL, coe_jGen, qExpand_jqModC_eq_pow_unconditional K]
  rfl

end FunctionField

end W6FK1
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_frobeniusModL.W6FK1"

end
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_frobeniusModL.W6FK1"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N] :
    AlgebraicCurve.finrankAlong K (ModularCurve.frobeniusModL K N ℓ) = ℓ := by
  rw [W6FK1.finrankAlong_eq_relfinrank]
  haveI := W6FK1.charP_full K N (ℓ := ℓ)
  haveI := W6FK1.finiteDimensional_adjoin_jGen K N
  exact W6FK1.relfinrank_map_top_eq (ModularCurve.frobeniusModL K N ℓ)
    (W6FK1.transcendental_jGen K N) (W6FK1.frobeniusModL_jGen K N)

end S_ModularCurve_finrankAlong_frobeniusModL
end P2MW
export P2MW.S_ModularCurve_finrankAlong_frobeniusModL (solution)
