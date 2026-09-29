-- Prove2me | solution 1 for ModularCurve.essFiniteType_modularFunctionFieldFullC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5963adf6-919e-58a9-9375-09793721f6a5

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_essFiniteType_modularFunctionFieldFullC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace S20FullC

section Criterion

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p]

theorem frobenius_image_range_algebraMap :
    (frobenius L p) '' Set.range (algebraMap K L) = Set.range (algebraMap K L) := by
  ext u
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a ^ p, by rw [map_pow, frobenius_def]⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := surjective_frobenius K p a
    exact ⟨algebraMap K L b, ⟨b, rfl⟩, by rw [frobenius_def, frobenius_def, map_pow]⟩

theorem map_frobenius_adjoin_toSubfield (S : Set L) :
    (adjoin K S).toSubfield.map (frobenius L p) = (adjoin K ((frobenius L p) '' S)).toSubfield := by
  rw [adjoin_toSubfield, adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    frobenius_image_range_algebraMap]

omit [CharP K p] [PerfectRing K p] in

theorem map_frobenius_adjoin_toSubfield_le (S : Set L) :
    (adjoin K S).toSubfield.map (frobenius L p) ≤ (adjoin K ((frobenius L p) '' S)).toSubfield := by
  rw [adjoin_toSubfield, RingHom.map_field_closure, Subfield.closure_le, Set.image_union]
  rintro u (⟨_, ⟨a, rfl⟩, rfl⟩ | hu)
  · exact pow_mem ((adjoin K _).algebraMap_mem a) p
  · exact IntermediateField.subset_adjoin K _ hu

omit [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p] in

theorem relfinrank_adjoin_simple (F : IntermediateField K L) {a : L} (ha : IsIntegral F a) :
    IntermediateField.relfinrank F (restrictScalars K F⟮a⟯) = (minpoly F a).natDegree := by
  have hle : F ≤ restrictScalars K F⟮a⟯ := fun u hu => (algebraMap F F⟮a⟯ ⟨u, hu⟩).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  have hext : extendScalars hle = F⟮a⟯ :=
    IntermediateField.restrictScalars_injective K (extendScalars_restrictScalars hle)
  rw [hext, IntermediateField.adjoin.finrank ha]

omit [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p] in
theorem le_restrictScalars_adjoin (F : IntermediateField K L) (S : Set L) :
    F ≤ restrictScalars K (adjoin F S) := fun u hu => (algebraMap F (adjoin F S) ⟨u, hu⟩).2

include p in

theorem isSeparable_of_forall_pow_ne {x : L} (hx : ∀ u : L, u ^ p ≠ x)
    {y : L} (hy : IsIntegral K⟮x⟯ y) : IsSeparable K⟮x⟯ y := by
  classical
  by_contra hsep
  set E : IntermediateField K L := K⟮x⟯ with hE
  have hp : p.Prime := Fact.out

  have hirr : Irreducible (minpoly E y) := minpoly.irreducible hy
  obtain hs | ⟨-, g, hg, hgm⟩ := Polynomial.separable_or p hirr
  · exact hsep hs
  set z : L := y ^ p with hz
  have hgz : aeval z g = 0 := by
    rw [hz, ← expand_aeval p g y, hgm, minpoly.aeval]
  have hgmonic : g.Monic := by
    have h := minpoly.monic hy
    rw [← hgm] at h
    exact (monic_expand_iff hp.pos).mp h
  have hgmin : g = minpoly E z := minpoly.eq_of_irreducible_of_monic hg hgz hgmonic
  have hzint : IsIntegral E z := hy.pow p
  set r : ℕ := g.natDegree with hr
  have hrpos : 0 < r := by rw [hr, hgmin]; exact minpoly.natDegree_pos hzint
  have hdegm : (minpoly E y).natDegree = r * p := by rw [← hgm, natDegree_expand]

  let φ : L →+* L := frobenius L p
  set SE : Subfield L := E.toSubfield with hSE
  set SM : Subfield L := (restrictScalars K E⟮y⟯).toSubfield with hSM
  set SM₁ : Subfield L := (restrictScalars K E⟮z⟯).toSubfield with hSM₁
  set SE' : Subfield L := SE.map φ with hSE'
  set SM' : Subfield L := SM.map φ with hSM'

  have h1 : SE.relfinrank SM = r * p := by
    change IntermediateField.relfinrank E (restrictScalars K E⟮y⟯) = r * p
    rw [relfinrank_adjoin_simple E hy, hdegm]

  have h2 : SE.relfinrank SM₁ = r := by
    change IntermediateField.relfinrank E (restrictScalars K E⟮z⟯) = r
    rw [relfinrank_adjoin_simple E hzint, ← hgmin]

  have h3 : SE'.relfinrank SM' = r * p := by
    rw [hSE', hSM', Subfield.relfinrank_map_map, h1]

  have hE' : SE' = (K⟮x ^ p⟯).toSubfield := by
    rw [hSE', hSE, hE, map_frobenius_adjoin_toSubfield p, Set.image_singleton, frobenius_def]
  have hxpE : IsIntegral K⟮x ^ p⟯ x := by
    refine ⟨X ^ p - C (AdjoinSimple.gen K (x ^ p)), monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
    simp
  have hEeq : restrictScalars K (K⟮x ^ p⟯)⟮x⟯ = E := by
    rw [adjoin_simple_adjoin_simple, hE]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro u (rfl | rfl)
      · exact pow_mem (mem_adjoin_simple_self K x) p
      · exact mem_adjoin_simple_self K u
    · exact adjoin.mono K _ _ (Set.subset_insert _ _)
  have h4 : SE'.relfinrank SE ≤ p := by
    rw [hE', hSE, ← hEeq]
    change IntermediateField.relfinrank K⟮x ^ p⟯ (restrictScalars K (K⟮x ^ p⟯)⟮x⟯) ≤ p
    rw [relfinrank_adjoin_simple _ hxpE]
    have hdvd : minpoly K⟮x ^ p⟯ x ∣ X ^ p - C (AdjoinSimple.gen K (x ^ p)) :=
      minpoly.dvd _ _ (by simp)
    calc (minpoly K⟮x ^ p⟯ x).natDegree
        ≤ (X ^ p - C (AdjoinSimple.gen K (x ^ p))).natDegree :=
          natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero hp.pos _)
      _ = p := natDegree_X_pow_sub_C
  have h4' : 0 < SE'.relfinrank SE := by
    rw [hE', hSE, ← hEeq]
    change 0 < IntermediateField.relfinrank K⟮x ^ p⟯ (restrictScalars K (K⟮x ^ p⟯)⟮x⟯)
    rw [relfinrank_adjoin_simple _ hxpE]
    exact minpoly.natDegree_pos hxpE

  have hE'E : SE' ≤ SE := by
    rw [hSE']
    rintro _ ⟨u, hu, rfl⟩
    exact pow_mem hu p
  have hEM₁ : SE ≤ SM₁ := le_restrictScalars_adjoin E {z}
  have hEM : SE ≤ SM := le_restrictScalars_adjoin E {y}
  have hM'M₁ : SM' ≤ SM₁ := by
    rw [hSM', hSM]
    have hM : restrictScalars K E⟮y⟯ = adjoin K {x, y} := by
      rw [hE, adjoin_simple_adjoin_simple]
    rw [hM]
    refine (map_frobenius_adjoin_toSubfield_le p _).trans ?_
    change adjoin K (frobenius L p '' {x, y}) ≤ restrictScalars K E⟮z⟯
    rw [adjoin_le_iff]
    rintro u ⟨v, hv, rfl⟩
    rcases hv with rfl | rfl
    · exact pow_mem (le_restrictScalars_adjoin E {z} (mem_adjoin_simple_self K v)) p
    · change frobenius L p _ ∈ E⟮z⟯
      rw [frobenius_def, ← hz]
      exact mem_adjoin_simple_self E z
  have hE'M' : SE' ≤ SM' := by
    rw [hSE', hSM']
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hEM hu, rfl⟩

  have h5 : SE'.relfinrank SM₁ = SE'.relfinrank SE * r := by
    rw [← Subfield.relfinrank_mul_relfinrank hE'E hEM₁, h2]
  have h6 : SE'.relfinrank SM₁ = r * p * SM'.relfinrank SM₁ := by
    rw [← Subfield.relfinrank_mul_relfinrank hE'M' hM'M₁, h3]
  have hne : SE'.relfinrank SM₁ ≠ 0 := by
    rw [h5]; exact Nat.mul_ne_zero h4'.ne' hrpos.ne'
  have hone : SM'.relfinrank SM₁ = 1 := by
    have hle : SE'.relfinrank SE * r ≤ p * r := Nat.mul_le_mul_right r h4
    rw [← h5, h6] at hle
    have hk : SM'.relfinrank SM₁ ≠ 0 := fun h => hne (by rw [h6, h]; ring)
    have hk1 : SM'.relfinrank SM₁ ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have : r * p * 2 ≤ r * p * SM'.relfinrank SM₁ := Nat.mul_le_mul_left _ hcon
      have hrp : 0 < r * p := Nat.mul_pos hrpos hp.pos
      nlinarith
    omega

  have hxM' : x ∈ SM' := by
    have hM₁M' : SM₁ ≤ SM' := Subfield.relfinrank_eq_one_iff.mp hone
    exact hM₁M' (le_restrictScalars_adjoin E {z} (mem_adjoin_simple_self K x))
  rw [hSM'] at hxM'
  obtain ⟨u, -, hu⟩ := hxM'
  exact hx u hu

end Criterion

end S20FullC

end

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "Polynomial IntermediateField HahnSeries ModularCurve~coeffMap_injective"

namespace S20FullC

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

theorem pow_ne_jqModC (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (u : LaurentSeries K) : u ^ ℓ ≠ jqModC K := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  simp only [coeff_jqModC_neg_one] at h1
  rw [pow_char_eq_coeffMap_frobenius_qExpand ℓ u, coeffMap_coeff,
    qExpand_coeff_of_not_dvd ℓ u ?_, map_zero] at h1
  · exact zero_ne_one h1
  · intro hdvd
    have h2 : (ℓ : ℤ) ∣ 1 := (Int.dvd_neg).mp hdvd
    have h3 : ℓ = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h2
    exact (Fact.out : ℓ.Prime).one_lt.ne' h3

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

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

omit [PerfectRing K ℓ] in

theorem pow_ne_jGen (u : modularFunctionFieldFullC K N) : u ^ ℓ ≠ jGen K N := fun h =>
  pow_ne_jqModC K ℓ (u : LaurentSeries K) (by rw [← coe_jGen K N, ← h]; rfl)

omit [PerfectRing K ℓ] [Fact ℓ.Prime] in
theorem charP_full : CharP (modularFunctionFieldFullC K N) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldFullC K N)).injective ℓ

include ℓ in

theorem isSeparable_adjoin_jGen :
    Algebra.IsSeparable K⟮jGen K N⟯ (modularFunctionFieldFullC K N) := by
  haveI := charP_full K N (ℓ := ℓ)
  haveI : Algebra.IsSeparable K⟮jGen K N⟯ (adjoin K⟮jGen K N⟯ (gensC K N)) := by
    rw [isSeparable_adjoin_iff_isSeparable]
    intro y hy
    exact isSeparable_of_forall_pow_ne ℓ (pow_ne_jGen K N) (isIntegral_of_mem_gensC K N hy)
  rw [adjoin_adjoin_gensC_eq_top] at this
  exact Algebra.IsSeparable.of_algHom _ _
    (IntermediateField.topEquiv (F := K⟮jGen K N⟯) (E := modularFunctionFieldFullC K N)).symm.toAlgHom

end FunctionField

end S20FullC
p2m_reactivate "P2MW.S_ModularCurve_essFiniteType_modularFunctionFieldFullC.S20FullC"

end
p2m_reactivate "P2MW.S_ModularCurve_essFiniteType_modularFunctionFieldFullC.S20FullC"

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Algebra.EssFiniteType K ↥(ModularCurve.modularFunctionFieldFullC K N) :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional
    (S20FullC.transcendental_jGen K N) (S20FullC.finiteDimensional_adjoin_jGen K N)

end S_ModularCurve_essFiniteType_modularFunctionFieldFullC
end P2MW
export P2MW.S_ModularCurve_essFiniteType_modularFunctionFieldFullC (solution)
