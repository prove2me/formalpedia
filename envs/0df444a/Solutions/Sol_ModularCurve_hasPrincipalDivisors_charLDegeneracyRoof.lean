-- Prove2me | solution 1 for ModularCurve.hasPrincipalDivisors_charLDegeneracyRoof
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/16355d9a-2fcb-5936-af7b-af67cbf74af3

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "ModularCurve P2MW.S_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof.ModularCurve AlgebraicCurve IntermediateField"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof jqModC jqNModC isSeparable_jqNModC_of_natCast_ne_zero transcendental_jqModC isIntegral_jqNModC_all"
p2m_open "ModularCurve"

namespace GeneralRoof

open AlgebraicCurve

section Generic

variable {k L L' : Type*} [Field k] [Field L] [Field L'] [Algebra k L] [Algebra k L']

theorem algebraMap_comp_inclusion_of_le {F E : IntermediateField k L} (h : F ≤ E) :
    (algebraMap E L).comp (IntermediateField.inclusion h).toRingHom = algebraMap F L :=
  RingHom.ext fun _ => rfl

theorem isIntegral_of_intermediateField_le {F E : IntermediateField k L} (h : F ≤ E) {x : L} (hx : IsIntegral F x) :
    IsIntegral E x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (IntermediateField.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, algebraMap_comp_inclusion_of_le h]
  exact hpx

theorem isSeparable_of_intermediateField_le {F E : IntermediateField k L} (h : F ≤ E) {x : L} (hx : IsSeparable F x) :
    IsSeparable E x := by
  have h0 : Polynomial.aeval x ((minpoly F x).map (IntermediateField.inclusion h).toRingHom) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_inclusion_of_le h]
    exact minpoly.aeval F x
  exact Polynomial.Separable.of_dvd (Polynomial.Separable.map hx) (minpoly.dvd E x h0)

theorem isSeparable_map_algHom (σ : L →ₐ[k] L') (F : IntermediateField k L) {x : L}
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

theorem jqModC_mem_charLDegeneracyRoof : jqModC k ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem jqNModC_mem_charLDegeneracyRoof_left : jqNModC k N ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem jqNModC_mem_charLDegeneracyRoof_right : jqNModC k q ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem jqNModC_mem_charLDegeneracyRoof_mul : jqNModC k (N * q) ∈ charLDegeneracyRoof k N q :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem adjoin_jqModC_le_charLDegeneracyRoof :
    IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) ≤ charLDegeneracyRoof k N q :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_charLDegeneracyRoof k N q))

abbrev jRoof : charLDegeneracyRoof k N q := ⟨jqModC k, jqModC_mem_charLDegeneracyRoof k N q⟩

local notation "KJ" => IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))
local notation "ROOF" => charLDegeneracyRoof k N q
local notation "KX" => IntermediateField.adjoin k ({jRoof k N q} : Set (charLDegeneracyRoof k N q))

theorem transcendental_jRoof : Transcendental k (jRoof k N q) :=
  fun h => transcendental_jqModC k (h.algHom (charLDegeneracyRoof k N q).val)

theorem map_adjoin_jRoof : IntermediateField.map (charLDegeneracyRoof k N q).val KX = KJ := by
  have h := IntermediateField.adjoin_map k ({jRoof k N q} : Set (charLDegeneracyRoof k N q)) (charLDegeneracyRoof k N q).val
  rw [Set.image_singleton] at h
  exact h

theorem mem_adjoin_jRoof_of_mem {z : LaurentSeries k} (hz : z ∈ KJ) :
    (⟨z, adjoin_jqModC_le_charLDegeneracyRoof k N q hz⟩ : charLDegeneracyRoof k N q) ∈ KX := by
  have hz' : z ∈ (IntermediateField.map (charLDegeneracyRoof k N q).val KX : Set (LaurentSeries k)) := by
    rw [map_adjoin_jRoof]
    exact hz
  rw [IntermediateField.coe_map] at hz'
  obtain ⟨w, hw, hwz⟩ := hz'
  have : w = ⟨z, adjoin_jqModC_le_charLDegeneracyRoof k N q hz⟩ := Subtype.ext hwz
  exact this ▸ hw

def adjoinJCToRoof : KJ →+* KX where
  toFun z := ⟨⟨z, adjoin_jqModC_le_charLDegeneracyRoof k N q z.2⟩, mem_adjoin_jRoof_of_mem k N q z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem algebraMap_comp_adjoinJCToRoof :
    ((algebraMap ROOF (LaurentSeries k)).comp (algebraMap KX ROOF)).comp (adjoinJCToRoof k N q)
      = algebraMap KJ (LaurentSeries k) :=
  RingHom.ext fun _ => rfl

theorem eval₂_map_adjoinJCToRoof_eq_zero {y : ROOF} {P : Polynomial KJ}
    (h : Polynomial.eval₂ (algebraMap KJ (LaurentSeries k)) (y : LaurentSeries k) P = 0) :
    Polynomial.eval₂ (algebraMap KX ROOF) y (P.map (adjoinJCToRoof k N q)) = 0 := by
  have h1 : algebraMap ROOF (LaurentSeries k)
      (Polynomial.eval₂ (algebraMap KX ROOF) y (P.map (adjoinJCToRoof k N q))) = 0 := by
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, algebraMap_comp_adjoinJCToRoof]
    exact h
  exact (map_eq_zero_iff _ (algebraMap ROOF (LaurentSeries k)).injective).mp h1

theorem isIntegral_adjoin_jRoof_of {y : ROOF} (hy : IsIntegral KJ (y : LaurentSeries k)) : IsIntegral KX y := by
  obtain ⟨P, hPm, hP0⟩ := hy
  exact ⟨P.map (adjoinJCToRoof k N q), hPm.map _, eval₂_map_adjoinJCToRoof_eq_zero k N q hP0⟩

theorem isSeparable_adjoin_jRoof_of {y : ROOF} (hy : IsSeparable KJ (y : LaurentSeries k)) : IsSeparable KX y := by
  have h0 : Polynomial.aeval y ((minpoly KJ (y : LaurentSeries k)).map (adjoinJCToRoof k N q)) = 0 := by
    rw [Polynomial.aeval_def]
    refine eval₂_map_adjoinJCToRoof_eq_zero k N q ?_
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval KJ (y : LaurentSeries k)
  exact Polynomial.Separable.of_dvd (Polynomial.Separable.map hy) (minpoly.dvd _ y h0)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem finiteDimensional_adjoin_jRoof : FiniteDimensional KX ROOF := by
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

theorem isSeparable_adjoin_jqModC_of_mem_charLDegeneracyRoof (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0)
    {y : LaurentSeries k} (hy : y ∈ charLDegeneracyRoof k N q) : IsSeparable KJ y := by
  have hNq : ((N * q : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_mul]; exact mul_ne_zero hN hq
  have hle : charLDegeneracyRoof k N q ≤ (separableClosure KJ (LaurentSeries k)).restrictScalars k := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro z (rfl | rfl | rfl | hz)
    · exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_algebraMap (⟨jqModC k, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ : KJ)))
    · exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_jqNModC_of_natCast_ne_zero k N hN))
    · exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_jqNModC_of_natCast_ne_zero k q hq))
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (IntermediateField.mem_restrictScalars k).mpr (mem_separableClosure_iff.mpr
        (isSeparable_jqNModC_of_natCast_ne_zero k (N * q) hNq))
  exact mem_separableClosure_iff.mp ((IntermediateField.mem_restrictScalars k).mp (hle hy))

theorem hasPrincipalDivisors_charLDegeneracyRoof' (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    HasPrincipalDivisors k (charLDegeneracyRoof k N q) :=
  haveI : Algebra.IsSeparable KX ROOF :=
    ⟨fun y => isSeparable_adjoin_jRoof_of k N q (isSeparable_adjoin_jqModC_of_mem_charLDegeneracyRoof k N q hN hq y.2)⟩
  hasPrincipalDivisors_of_transcendental_of_isSeparable (transcendental_jRoof k N q)
    (finiteDimensional_adjoin_jRoof k N q) inferInstance

end RoofHPD

end GeneralRoof

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof.ModularCurve AlgebraicCurve in
theorem solution (k : Type*)
    [Field k] (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime]
    (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    HasPrincipalDivisors k (charLDegeneracyRoof k N q) :=
  ModularCurve.GeneralRoof.hasPrincipalDivisors_charLDegeneracyRoof' k N q hN hq

end S_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
end P2MW
export P2MW.S_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof (solution)
