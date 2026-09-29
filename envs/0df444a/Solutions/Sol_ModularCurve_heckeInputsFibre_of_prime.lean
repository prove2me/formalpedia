-- Prove2me | solution 1 for ModularCurve.heckeInputsFibre_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1530f775-ab07-5801-b391-f8b4f6bb45af

import Theorems.Thm_ModularCurve_heckeDivFibreDescends_of_separable_phi_map
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_modularPolynomialData
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeInputsFibre_of_prime
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeDivFibreDescends_of_separable_phi_map charLDegeneracyRoof heckeAlphaC heckeBetaC HeckeAlphaCIntegral HeckeBetaCIntegral heckeDivFibre HeckeDivFibreDescends HeckeInputsFibre heckePic0Fibre heckeInputsFibre_intro heckePic0Fibre_eq qExpandAlgC qExpandAlgC_apply jqModC jqNModC qExpand_qExpand ModularPolynomialData finiteAlong_heckeAlphaC finiteAlong_heckeBetaC ModularPolynomialData.separable_map_ratFunc_of_prime exists_modularPolynomialData_evalSymm transcendental_jqModC isIntegral_jqNModC_all isSeparable_jqNModC_of_modularPolynomialData"
p2m_open "ModularCurve"

open AlgebraicCurve

section Closed

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]

private theorem toRingHom_isIntegral_of_finiteAlong {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hfin : FiniteAlong k φ) : φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := hfin
  exact fun x => IsIntegral.of_finite F x

private theorem heckeAlphaCIntegral_of_finite : HeckeAlphaCIntegral k N q :=
  toRingHom_isIntegral_of_finiteAlong k (heckeAlphaC k N q) (finiteAlong_heckeAlphaC k N q)

private theorem heckeBetaCIntegral_of_finite [Fact q.Prime] : HeckeBetaCIntegral k N q :=
  toRingHom_isIntegral_of_finiteAlong k (heckeBetaC k N q) (finiteAlong_heckeBetaC k N q)

private theorem heckeDivFibreDescends_of_natCast_ne_zero [Fact q.Prime] (hqk : (q : k) ≠ 0) :
    HeckeDivFibreDescends k N q := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm q
  exact heckeDivFibreDescends_of_separable_phi_map k N q data hsymm hqk
    (ModularPolynomialData.separable_map_ratFunc_of_prime k q data hqk)

private theorem heckeInputsFibre_of_natCast_ne_zero [HasPrincipalDivisors k (charLDegeneracyRoof k N q)] [Fact q.Prime]
    (hqk : (q : k) ≠ 0) : HeckeInputsFibre k N q :=
  heckeInputsFibre_intro k N q (heckeBetaCIntegral_of_finite k N q) (heckeAlphaCIntegral_of_finite k N q)
    (heckeDivFibreDescends_of_natCast_ne_zero k N q hqk ‹_› _ _)

private theorem heckePic0Fibre_eq_of_natCast_ne_zero [HasPrincipalDivisors k (charLDegeneracyRoof k N q)] [Fact q.Prime]
    (hqk : (q : k) ≠ 0) :
    heckePic0Fibre k N q
      = (AlgebraicCurve.Divisor.toPic0End
          (heckeDivFibre k N q (heckeBetaCIntegral_of_finite k N q) (heckeAlphaCIntegral_of_finite k N q))).toIntLinearMap :=
  heckePic0Fibre_eq k N q _ _ (heckeDivFibreDescends_of_natCast_ne_zero k N q hqk ‹_› _ _)

end Closed

section Generic

variable {k L L' : Type*} [Field k] [Field L] [Field L'] [Algebra k L] [Algebra k L']

private theorem algebraMap_comp_inclusion_of_le {F E : IntermediateField k L} (h : F ≤ E) :
    (algebraMap E L).comp (IntermediateField.inclusion h).toRingHom = algebraMap F L :=
  RingHom.ext fun _ => rfl

private theorem isIntegral_of_intermediateField_le {F E : IntermediateField k L} (h : F ≤ E) {x : L} (hx : IsIntegral F x) :
    IsIntegral E x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (IntermediateField.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, algebraMap_comp_inclusion_of_le h]
  exact hpx

private theorem isSeparable_of_intermediateField_le {F E : IntermediateField k L} (h : F ≤ E) {x : L} (hx : IsSeparable F x) :
    IsSeparable E x := by
  have h0 : Polynomial.aeval x ((minpoly F x).map (IntermediateField.inclusion h).toRingHom) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_inclusion_of_le h]
    exact minpoly.aeval F x
  exact Polynomial.Separable.of_dvd (Polynomial.Separable.map hx) (minpoly.dvd E x h0)

private theorem isSeparable_map_algHom (σ : L →ₐ[k] L') (F : IntermediateField k L) {x : L}
    (hx : IsSeparable F x) : IsSeparable (F.map σ) (σ x) := by
  have hc : (algebraMap (F.map σ) L').comp (F.equivMap σ).toAlgHom.toRingHom
      = σ.toRingHom.comp (algebraMap F L) :=
    RingHom.ext fun _ => rfl
  have h0 := Polynomial.map_aeval_eq_aeval_map hc (minpoly F x) x
  rw [minpoly.aeval, map_zero] at h0
  exact Polynomial.Separable.of_dvd (Polynomial.Separable.map hx) (minpoly.dvd _ _ h0.symm)

end Generic

section RoofHPD

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]

private theorem jqModC_mem_charLDegeneracyRoof : jqModC k ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

private theorem jqNModC_mem_charLDegeneracyRoof_left : jqNModC k N ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

private theorem jqNModC_mem_charLDegeneracyRoof_right : jqNModC k q ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

private theorem jqNModC_mem_charLDegeneracyRoof_mul : jqNModC k (N * q) ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

private theorem adjoin_jqModC_le_charLDegeneracyRoof :
    IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) ≤ charLDegeneracyRoof k N q :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_charLDegeneracyRoof k N q))

private abbrev jRoof : charLDegeneracyRoof k N q := ⟨jqModC k, jqModC_mem_charLDegeneracyRoof k N q⟩

local notation "KJ" => IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))
local notation "ROOF" => charLDegeneracyRoof k N q
local notation "KX" => IntermediateField.adjoin k ({jRoof k N q} : Set (charLDegeneracyRoof k N q))

private theorem transcendental_jRoof : Transcendental k (jRoof k N q) :=
  fun h => transcendental_jqModC k (h.algHom (charLDegeneracyRoof k N q).val)

private theorem map_adjoin_jRoof : IntermediateField.map (charLDegeneracyRoof k N q).val KX = KJ := by
  have h := IntermediateField.adjoin_map k ({jRoof k N q} : Set (charLDegeneracyRoof k N q)) (charLDegeneracyRoof k N q).val
  rw [Set.image_singleton] at h
  exact h

private theorem mem_adjoin_jRoof_of_mem {z : LaurentSeries k} (hz : z ∈ KJ) :
    (⟨z, adjoin_jqModC_le_charLDegeneracyRoof k N q hz⟩ : charLDegeneracyRoof k N q) ∈ KX := by
  have hz' : z ∈ (IntermediateField.map (charLDegeneracyRoof k N q).val KX : Set (LaurentSeries k)) := by
    rw [map_adjoin_jRoof]
    exact hz
  rw [IntermediateField.coe_map] at hz'
  obtain ⟨w, hw, hwz⟩ := hz'
  have : w = ⟨z, adjoin_jqModC_le_charLDegeneracyRoof k N q hz⟩ := Subtype.ext hwz
  exact this ▸ hw

private def adjoinJCToRoof : KJ →+* KX where
  toFun z := ⟨⟨z, adjoin_jqModC_le_charLDegeneracyRoof k N q z.2⟩, mem_adjoin_jRoof_of_mem k N q z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem algebraMap_comp_adjoinJCToRoof :
    ((algebraMap ROOF (LaurentSeries k)).comp (algebraMap KX ROOF)).comp (adjoinJCToRoof k N q)
      = algebraMap KJ (LaurentSeries k) :=
  RingHom.ext fun _ => rfl

private theorem eval₂_map_adjoinJCToRoof_eq_zero {y : ROOF} {P : Polynomial KJ}
    (h : Polynomial.eval₂ (algebraMap KJ (LaurentSeries k)) (y : LaurentSeries k) P = 0) :
    Polynomial.eval₂ (algebraMap KX ROOF) y (P.map (adjoinJCToRoof k N q)) = 0 := by
  have h1 : algebraMap ROOF (LaurentSeries k)
      (Polynomial.eval₂ (algebraMap KX ROOF) y (P.map (adjoinJCToRoof k N q))) = 0 := by
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, algebraMap_comp_adjoinJCToRoof]
    exact h
  exact (map_eq_zero_iff _ (algebraMap ROOF (LaurentSeries k)).injective).mp h1

private theorem isIntegral_adjoin_jRoof_of {y : ROOF} (hy : IsIntegral KJ (y : LaurentSeries k)) : IsIntegral KX y := by
  obtain ⟨P, hPm, hP0⟩ := hy
  exact ⟨P.map (adjoinJCToRoof k N q), hPm.map _, eval₂_map_adjoinJCToRoof_eq_zero k N q hP0⟩

private theorem isSeparable_adjoin_jRoof_of {y : ROOF} (hy : IsSeparable KJ (y : LaurentSeries k)) : IsSeparable KX y := by
  have h0 : Polynomial.aeval y ((minpoly KJ (y : LaurentSeries k)).map (adjoinJCToRoof k N q)) = 0 := by
    rw [Polynomial.aeval_def]
    refine eval₂_map_adjoinJCToRoof_eq_zero k N q ?_
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval KJ (y : LaurentSeries k)
  exact Polynomial.Separable.of_dvd (Polynomial.Separable.map hy) (minpoly.dvd _ y h0)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem finiteDimensional_adjoin_jRoof : FiniteDimensional KX ROOF := by
  set S : Set ROOF :=
    {⟨jqNModC k N, jqNModC_mem_charLDegeneracyRoof_left k N q⟩, ⟨jqNModC k q, jqNModC_mem_charLDegeneracyRoof_right k N q⟩,
      ⟨jqNModC k (N * q), jqNModC_mem_charLDegeneracyRoof_mul k N q⟩} with hS
  haveI : FiniteDimensional KX (IntermediateField.adjoin KX S) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      rcases hy with rfl | rfl | hy
      · exact isIntegral_adjoin_jRoof_of k N q (isIntegral_jqNModC_all k N)
      · exact isIntegral_adjoin_jRoof_of k N q (isIntegral_jqNModC_all k q)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact isIntegral_adjoin_jRoof_of k N q (isIntegral_jqNModC_all k (N * q))

  have hS_le : IntermediateField.adjoin k (insert (jRoof k N q) S) ≤ (IntermediateField.adjoin KX S).restrictScalars k := by
    refine IntermediateField.adjoin_le_iff.mpr (Set.insert_subset_iff.mpr ⟨?_, ?_⟩)
    · exact (IntermediateField.adjoin KX S).algebraMap_mem
        (⟨jRoof k N q, IntermediateField.mem_adjoin_simple_self k (jRoof k N q)⟩ : KX)
    · exact IntermediateField.subset_adjoin _ _

  have hall : ∀ y : ROOF, y ∈ IntermediateField.adjoin k (insert (jRoof k N q) S) := fun y => by
    have hmap := IntermediateField.adjoin_map k (insert (jRoof k N q) S) (charLDegeneracyRoof k N q).val
    have himg : (charLDegeneracyRoof k N q).val '' insert (jRoof k N q) S
        = {jqModC k, jqNModC k N, jqNModC k q, jqNModC k (N * q)} := by
      simp only [hS, Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [himg] at hmap
    have hy : (y : LaurentSeries k)
        ∈ (IntermediateField.map (charLDegeneracyRoof k N q).val (IntermediateField.adjoin k (insert (jRoof k N q) S))
            : Set (LaurentSeries k)) := by
      rw [hmap]
      exact y.2
    rw [IntermediateField.coe_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    exact this ▸ hz
  exact Module.Finite.of_surjective (IntermediateField.adjoin KX S).val.toLinearMap
    fun y => ⟨⟨y, hS_le (hall y)⟩, rfl⟩

variable [Fact N.Prime] [Fact q.Prime]

private theorem isSeparable_adjoin_jqModC_jqNModC_mul (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    IsSeparable KJ (jqNModC k (N * q)) := by
  obtain ⟨dN, hsN⟩ := exists_modularPolynomialData_evalSymm N
  obtain ⟨dq, hsq⟩ := exists_modularPolynomialData_evalSymm q
  have hAN : IsSeparable KJ (jqNModC k N) := isSeparable_jqNModC_of_modularPolynomialData k dN hsN hN
  have hAq : IsSeparable KJ (jqNModC k q) := isSeparable_jqNModC_of_modularPolynomialData k dq hsq hq

  have hmapN : IntermediateField.map (qExpandAlgC k N) KJ
      = IntermediateField.adjoin k ({jqNModC k N} : Set (LaurentSeries k)) := by
    have h := IntermediateField.adjoin_map k ({jqModC k} : Set (LaurentSeries k)) (qExpandAlgC k N)
    rw [Set.image_singleton, qExpandAlgC_apply] at h
    exact h
  have e : qExpandAlgC k N (jqNModC k q) = jqNModC k (N * q) := by
    rw [qExpandAlgC_apply, jqNModC, jqNModC, qExpand_qExpand]
  have hNq : IsSeparable (IntermediateField.adjoin k ({jqNModC k N} : Set (LaurentSeries k))) (jqNModC k (N * q)) := by
    have h := isSeparable_of_intermediateField_le (le_of_eq hmapN) (isSeparable_map_algHom (qExpandAlgC k N) KJ hAq)
    rwa [e] at h

  haveI : Algebra.IsSeparable KJ (IntermediateField.adjoin KJ ({jqNModC k N} : Set (LaurentSeries k))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (F := KJ) (E := LaurentSeries k) (x := jqNModC k N)).mpr hAN
  have hle : IntermediateField.adjoin k ({jqNModC k N} : Set (LaurentSeries k))
      ≤ (IntermediateField.adjoin KJ ({jqNModC k N} : Set (LaurentSeries k))).restrictScalars k :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.mem_adjoin_simple_self KJ (jqNModC k N)))
  have hE : IsSeparable (IntermediateField.adjoin KJ ({jqNModC k N} : Set (LaurentSeries k))) (jqNModC k (N * q)) :=
    isSeparable_of_intermediateField_le hle hNq
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable (F := KJ)
    (E := IntermediateField.adjoin KJ ({jqNModC k N} : Set (LaurentSeries k))) (K := LaurentSeries k) hE

private theorem isSeparable_adjoin_jqModC_of_mem_charLDegeneracyRoof (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0)
    {y : LaurentSeries k} (hy : y ∈ charLDegeneracyRoof k N q) : IsSeparable KJ y := by
  obtain ⟨dN, hsN⟩ := exists_modularPolynomialData_evalSymm N
  obtain ⟨dq, hsq⟩ := exists_modularPolynomialData_evalSymm q
  have hle : charLDegeneracyRoof k N q ≤ (separableClosure KJ (LaurentSeries k)).restrictScalars k := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro z (rfl | rfl | rfl | hz)
    · exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_algebraMap (⟨jqModC k, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ : KJ)))
    · exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_jqNModC_of_modularPolynomialData k dN hsN hN))
    · exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_jqNModC_of_modularPolynomialData k dq hsq hq))
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_adjoin_jqModC_jqNModC_mul k N q hN hq))
  exact mem_separableClosure_iff.mp ((IntermediateField.mem_restrictScalars k).mp (hle hy))

private theorem hasPrincipalDivisors_charLDegeneracyRoof_of_prime (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    HasPrincipalDivisors k (charLDegeneracyRoof k N q) :=
  haveI : Algebra.IsSeparable KX ROOF :=
    ⟨fun y => isSeparable_adjoin_jRoof_of k N q (isSeparable_adjoin_jqModC_of_mem_charLDegeneracyRoof k N q hN hq y.2)⟩
  hasPrincipalDivisors_of_transcendental_of_isSeparable (transcendental_jRoof k N q) (finiteDimensional_adjoin_jRoof k N q)
    inferInstance

private theorem heckeInputsFibre_of_prime (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) : HeckeInputsFibre k N q :=
  haveI := hasPrincipalDivisors_charLDegeneracyRoof_of_prime k N q hN hq
  heckeInputsFibre_of_natCast_ne_zero k N q hq

private theorem heckePic0Fibre_eq_of_prime (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    heckePic0Fibre k N q
      = (letI := hasPrincipalDivisors_charLDegeneracyRoof_of_prime k N q hN hq
         (AlgebraicCurve.Divisor.toPic0End
          (heckeDivFibre k N q (heckeBetaCIntegral_of_finite k N q) (heckeAlphaCIntegral_of_finite k N q))).toIntLinearMap) :=
  letI := hasPrincipalDivisors_charLDegeneracyRoof_of_prime k N q hN hq
  heckePic0Fibre_eq_of_natCast_ne_zero k N q hq

end RoofHPD

end ModularCurve

end

#check @ModularCurve.hasPrincipalDivisors_charLDegeneracyRoof_of_prime
#print axioms ModularCurve.hasPrincipalDivisors_charLDegeneracyRoof_of_prime
#check @ModularCurve.heckeInputsFibre_of_prime
#print axioms ModularCurve.heckeInputsFibre_of_prime
#check @ModularCurve.heckeDivFibreDescends_of_natCast_ne_zero
#print axioms ModularCurve.heckeDivFibreDescends_of_natCast_ne_zero
#check @ModularCurve.heckeInputsFibre_of_natCast_ne_zero
#print axioms ModularCurve.heckeInputsFibre_of_natCast_ne_zero
#check @ModularCurve.heckePic0Fibre_eq_of_natCast_ne_zero

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_heckeInputsFibre_of_prime.ModularCurve AlgebraicCurve in
theorem solution (k : Type*)
    [Field k] (N q : ℕ) [NeZero N] [NeZero q] [Fact N.Prime] [Fact q.Prime]
    (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    HeckeInputsFibre k N q :=
  ModularCurve.heckeInputsFibre_of_prime k N q hN hq

end S_ModularCurve_heckeInputsFibre_of_prime
end P2MW
export P2MW.S_ModularCurve_heckeInputsFibre_of_prime (solution)
