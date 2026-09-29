-- Prove2me | solution 1 for HorizontalPadicL.unitNormRelationThetaSystem_to_normalizedMeasure_inverseSeed_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:55:18.694984+00:00
-- url     : https://prove2.me/submissions/3615cb0e-ead6-4eb4-80fa-c43c07289fbb

import Definitions.Def_KN_InverseSeedConventionV2
import Definitions.Def_KN_SeededFiniteThetaCriticalZeroSetV2

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

private def extendHorizontalCoordinates {p : ℕ} {m : ℕ → ℕ}
    {A B : Finset ℕ} (hAB : A ⊆ B) :
    HorizontalFiniteGroup p m A →* HorizontalFiniteGroup p m B where
  toFun x i := if hi : i.1 ∈ A then x ⟨i.1, hi⟩ else 1
  map_one' := by ext i; split <;> rfl
  map_mul' x y := by
    ext i
    split <;> simp_all

private theorem restrict_extend {p : ℕ} {m : ℕ → ℕ}
    {A B : Finset ℕ} (hAB : A ⊆ B) (x : HorizontalFiniteGroup p m A) :
    restrictHorizontalCoordinates hAB (extendHorizontalCoordinates hAB x) = x := by
  ext i
  change (if hi : i.1 ∈ A then x ⟨i.1, hi⟩ else 1) = x i
  simp

private def horizontalInflation (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) :
    HorizontalGroupAlgebra R p m A →+* HorizontalGroupAlgebra R p m B :=
  MonoidAlgebra.mapDomainRingHom R (extendHorizontalCoordinates hAB)

private theorem projection_inflation (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A B : Finset ℕ} (hAB : A ⊆ B)
    (x : HorizontalGroupAlgebra R p m A) :
    horizontalGroupAlgebraProjection R hAB (horizontalInflation R hAB x) = x := by
  change MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hAB)
      (MonoidAlgebra.mapDomainRingHom R (extendHorizontalCoordinates hAB) x) = x
  rw [← RingHom.comp_apply, ← MonoidAlgebra.mapDomainRingHom_comp]
  have hh : (horizontalRestrictionHom hAB).comp (extendHorizontalCoordinates hAB) =
      MonoidHom.id (HorizontalFiniteGroup p m A) := by
    apply MonoidHom.ext
    intro x
    exact restrict_extend hAB x
  rw [hh, MonoidAlgebra.mapDomainRingHom_id]
  rfl

private noncomputable def thetaEdgeUnit
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hunit : Θ.HasUnitEulerFactors) (r : ℕ) :
    (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent (Finset.range r))ˣ :=
  (hunit (Finset.range r) r).unit

private noncomputable def thetaEdgeInverse
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hunit : Θ.HasUnitEulerFactors) (r : ℕ) :
    HorizontalGroupAlgebra Θ.coefficientRing p L.exponent (Finset.range r) :=
  ↑((thetaEdgeUnit Θ hunit r)⁻¹)

private noncomputable def thetaMultiplier
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hunit : Θ.HasUnitEulerFactors) :
    ∀ r : ℕ, HorizontalGroupAlgebra Θ.coefficientRing p L.exponent (Finset.range r) :=
  fun r => Nat.rec (motive := fun s =>
      HorizontalGroupAlgebra Θ.coefficientRing p L.exponent (Finset.range s))
    1 (fun s v => horizontalInflation Θ.coefficientRing
      (Finset.range_mono (Nat.le_succ s))
      (v * thetaEdgeInverse Θ hunit s)) r

private theorem thetaMultiplier_succ
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hunit : Θ.HasUnitEulerFactors) (r : ℕ) :
    thetaMultiplier Θ hunit (Nat.succ r) =
      horizontalInflation Θ.coefficientRing
        (Finset.range_mono (Nat.le_succ r))
        (thetaMultiplier Θ hunit r * thetaEdgeInverse Θ hunit r) := by
  simp only [thetaMultiplier]

private theorem thetaMultiplier_isUnit
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hunit : Θ.HasUnitEulerFactors) :
    ∀ r, IsUnit (thetaMultiplier Θ hunit r) := by
  intro r
  induction r with
  | zero => exact isUnit_one
  | succ r ihr =>
      simp only [thetaMultiplier, Nat.rec]
      exact (ihr.mul (show IsUnit (thetaEdgeInverse Θ hunit r) from
        ((thetaEdgeUnit Θ hunit r)⁻¹).isUnit)).map _

private noncomputable def normalizedThetaChain
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hunit : Θ.HasUnitEulerFactors) (r : ℕ) :=
  thetaMultiplier Θ hunit r * Θ.theta (Finset.range r)

private theorem normalizedThetaChain_compatible
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors) (r : ℕ) :
    horizontalGroupAlgebraProjection Θ.coefficientRing
      (Finset.range_mono (Nat.le_succ r))
      (normalizedThetaChain Θ hunit (Nat.succ r)) =
      normalizedThetaChain Θ hunit r := by
  unfold normalizedThetaChain
  rw [thetaMultiplier_succ]
  rw [map_mul, projection_inflation]
  have hrange : insert r (Finset.range r) = Finset.range (r + 1) := by
    ext x
    simp [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, or_comm]
  have hrel := hnorm (Finset.range r) r (by simp)
  have hrel' : horizontalGroupAlgebraProjection Θ.coefficientRing
      (Finset.range_mono (Nat.le_succ r)) (Θ.theta (Finset.range (Nat.succ r))) =
      Θ.eulerFactor (Finset.range r) r * Θ.theta (Finset.range r) := by
    convert hrel using 1
    let q : {B : Finset ℕ // Finset.range r ⊆ B} →
        HorizontalGroupAlgebra Θ.coefficientRing p L.exponent (Finset.range r) :=
      fun B => horizontalGroupAlgebraProjection Θ.coefficientRing B.2 (Θ.theta B.1)
    have hz : (⟨Finset.range (Nat.succ r),
        Finset.range_mono (Nat.le_succ r)⟩ : {B : Finset ℕ // Finset.range r ⊆ B}) =
        ⟨insert r (Finset.range r), Finset.subset_insert r (Finset.range r)⟩ := by
      apply Subtype.ext
      exact hrange.symm
    exact congrArg q hz
  rw [hrel']
  change (thetaMultiplier Θ hunit r * thetaEdgeInverse Θ hunit r) *
      (↑(thetaEdgeUnit Θ hunit r) * Θ.theta (Finset.range r)) = _
  unfold thetaEdgeInverse
  rw [mul_assoc, ← mul_assoc (↑((thetaEdgeUnit Θ hunit r)⁻¹))
    (↑(thetaEdgeUnit Θ hunit r)) (Θ.theta (Finset.range r)),
    Units.inv_mul, one_mul]

private theorem horizontalGroupAlgebraProjection_comp (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A B C : Finset ℕ}
    (hAB : A ⊆ B) (hBC : B ⊆ C)
    (x : HorizontalGroupAlgebra R p m C) :
    horizontalGroupAlgebraProjection R hAB
        (horizontalGroupAlgebraProjection R hBC x) =
      horizontalGroupAlgebraProjection R (hAB.trans hBC) x := by
  change MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hAB)
      (MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hBC) x) = _
  rw [← RingHom.comp_apply, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 2

private theorem horizontalGroupAlgebraProjection_refl (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A : Finset ℕ} (hAA : A ⊆ A)
    (x : HorizontalGroupAlgebra R p m A) :
    horizontalGroupAlgebraProjection R hAA x = x := by
  change MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hAA) x = x
  have hh : horizontalRestrictionHom hAA = MonoidHom.id (HorizontalFiniteGroup p m A) := by
    apply MonoidHom.ext
    intro g
    rfl
  rw [hh, MonoidAlgebra.mapDomainRingHom_id]
  rfl

private theorem normalizedThetaChain_compatible_of_le
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors) {r s : ℕ} (hrs : r ≤ s) :
    horizontalGroupAlgebraProjection Θ.coefficientRing (Finset.range_mono hrs)
        (normalizedThetaChain Θ hunit s) =
      normalizedThetaChain Θ hunit r := by
  induction s, hrs using Nat.le_induction with
  | base =>
      exact horizontalGroupAlgebraProjection_refl _ _ _
  | succ s hrs ih =>
      calc
        horizontalGroupAlgebraProjection Θ.coefficientRing
            (Finset.range_mono (Nat.le_trans hrs (Nat.le_succ s)))
            (normalizedThetaChain Θ hunit (s + 1)) =
          horizontalGroupAlgebraProjection Θ.coefficientRing (Finset.range_mono hrs)
            (horizontalGroupAlgebraProjection Θ.coefficientRing
              (Finset.range_mono (Nat.le_succ s))
              (normalizedThetaChain Θ hunit (s + 1))) := by
                rw [horizontalGroupAlgebraProjection_comp]
        _ = horizontalGroupAlgebraProjection Θ.coefficientRing (Finset.range_mono hrs)
            (normalizedThetaChain Θ hunit s) := by
                rw [normalizedThetaChain_compatible Θ hnorm hunit s]
        _ = normalizedThetaChain Θ hunit r := ih

private def horizontalLevelBound (A : Finset ℕ) : ℕ := A.sup id + 1

private theorem subset_range_horizontalLevelBound (A : Finset ℕ) :
    A ⊆ Finset.range (horizontalLevelBound A) := by
  intro n hn
  simp only [Finset.mem_range, horizontalLevelBound]
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)

private theorem horizontalLevelBound_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    horizontalLevelBound A ≤ horizontalLevelBound B := by
  apply Nat.succ_le_succ
  apply Finset.sup_le
  intro n hn
  exact Finset.le_sup (f := id) (hAB hn)

private noncomputable def normalizedFiniteLevel
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hunit : Θ.HasUnitEulerFactors)
    (A : Finset ℕ) : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A :=
  horizontalGroupAlgebraProjection Θ.coefficientRing
    (subset_range_horizontalLevelBound A)
    (normalizedThetaChain Θ hunit (horizontalLevelBound A))

private theorem normalizedFiniteLevel_eq_projection
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors) (A : Finset ℕ) {s : ℕ}
    (hs : horizontalLevelBound A ≤ s) :
    horizontalGroupAlgebraProjection Θ.coefficientRing
        ((subset_range_horizontalLevelBound A).trans (Finset.range_mono hs))
        (normalizedThetaChain Θ hunit s) =
      normalizedFiniteLevel Θ hunit A := by
  unfold normalizedFiniteLevel
  calc
    horizontalGroupAlgebraProjection Θ.coefficientRing
        ((subset_range_horizontalLevelBound A).trans (Finset.range_mono hs))
        (normalizedThetaChain Θ hunit s) =
      horizontalGroupAlgebraProjection Θ.coefficientRing
        (subset_range_horizontalLevelBound A)
        (horizontalGroupAlgebraProjection Θ.coefficientRing (Finset.range_mono hs)
          (normalizedThetaChain Θ hunit s)) := by
            rw [horizontalGroupAlgebraProjection_comp]
    _ = horizontalGroupAlgebraProjection Θ.coefficientRing
        (subset_range_horizontalLevelBound A)
        (normalizedThetaChain Θ hunit (horizontalLevelBound A)) := by
          rw [normalizedThetaChain_compatible_of_le Θ hnorm hunit hs]

private theorem normalizedFiniteLevel_compatible
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors) (A B : Finset ℕ) (hAB : A ⊆ B) :
    horizontalGroupAlgebraProjection Θ.coefficientRing hAB
        (normalizedFiniteLevel Θ hunit B) =
      normalizedFiniteLevel Θ hunit A := by
  unfold normalizedFiniteLevel
  rw [horizontalGroupAlgebraProjection_comp]
  have hbound := horizontalLevelBound_mono hAB
  rw [← normalizedThetaChain_compatible_of_le Θ hnorm hunit hbound]
  rw [horizontalGroupAlgebraProjection_comp]

private theorem theta_projection_unit_multiple
    {N k p B₀ : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B₀}
    (Θ : SeededFiniteThetaDataV3 L) (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors) (A B : Finset ℕ) (hAB : A ⊆ B) :
    ∃ u : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ,
      horizontalGroupAlgebraProjection Θ.coefficientRing hAB (Θ.theta B) =
        (u : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A := by
  classical
  by_cases hEq : A = B
  · subst B
    refine ⟨1, ?_⟩
    rw [horizontalGroupAlgebraProjection_refl, Units.val_one, one_mul]
  · have hss : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hAB, hEq⟩
    obtain ⟨n, hnB, hnA⟩ := Finset.exists_of_ssubset hss
    let C := B.erase n
    have hAC : A ⊆ C := by
      intro a ha
      simp only [C, Finset.mem_erase]
      exact ⟨fun han => hnA (han ▸ ha), hAB ha⟩
    have hCB : C ⊆ B := Finset.erase_subset n B
    obtain ⟨u, hu⟩ := theta_projection_unit_multiple Θ hnorm hunit A C hAC
    let q : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent C →+*
        HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A :=
      horizontalGroupAlgebraProjection Θ.coefficientRing hAC
    let v : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ :=
      Units.map q.toMonoidHom ((hunit C n).unit)
    refine ⟨v * u, ?_⟩
    calc
      horizontalGroupAlgebraProjection Θ.coefficientRing hAB (Θ.theta B) =
          horizontalGroupAlgebraProjection Θ.coefficientRing hAC
            (horizontalGroupAlgebraProjection Θ.coefficientRing hCB (Θ.theta B)) := by
              rw [horizontalGroupAlgebraProjection_comp]
      _ = horizontalGroupAlgebraProjection Θ.coefficientRing hAC
            (Θ.eulerFactor C n * Θ.theta C) := by
              congr 1
              have hrel := hnorm C n (by simp [C])
              have hins : insert n C = B := by simp [C, hnB]
              let q' : {D : Finset ℕ // C ⊆ D} →
                  HorizontalGroupAlgebra Θ.coefficientRing p L.exponent C :=
                fun D => horizontalGroupAlgebraProjection Θ.coefficientRing D.2 (Θ.theta D.1)
              have hz : (⟨B, hCB⟩ : {D : Finset ℕ // C ⊆ D}) =
                  ⟨insert n C, Finset.subset_insert n C⟩ := by
                apply Subtype.ext
                exact hins.symm
              exact (congrArg q' hz).trans hrel
      _ = q (Θ.eulerFactor C n) * q (Θ.theta C) := map_mul q _ _
      _ = (v : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) *
            ((u : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A) := by
              rw [hu]
              rfl
      _ = ((v * u : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ) :
            HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A := by
              simp only [Units.val_mul]
              rw [mul_assoc]
termination_by (B \ A).card
decreasing_by
  have heq : B.erase n \ A = (B \ A).erase n := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    aesop
  rw [heq]
  exact Finset.card_erase_lt_of_mem (by simp [hnB, hnA])

private theorem normalizedFiniteLevel_unit_multiple
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors) (A : Finset ℕ) :
    ∃ u : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ,
      normalizedFiniteLevel Θ hunit A =
        (u : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A := by
  let hA := subset_range_horizontalLevelBound A
  obtain ⟨v, hv⟩ := theta_projection_unit_multiple Θ hnorm hunit A
    (Finset.range (horizontalLevelBound A)) hA
  let q : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent
        (Finset.range (horizontalLevelBound A)) →+*
      HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A :=
    horizontalGroupAlgebraProjection Θ.coefficientRing hA
  let w : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ :=
    Units.map q.toMonoidHom ((thetaMultiplier_isUnit Θ hunit
      (horizontalLevelBound A)).unit)
  refine ⟨w * v, ?_⟩
  unfold normalizedFiniteLevel normalizedThetaChain
  change q (thetaMultiplier Θ hunit (horizontalLevelBound A) *
      Θ.theta (Finset.range (horizontalLevelBound A))) = _
  rw [map_mul q, hv]
  change (w : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) *
      ((v : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A) = _
  simp only [Units.val_mul]
  rw [mul_assoc]

private def horizontalCharacterEvalRingHom
    {p : ℕ} [Fact p.Prime] {m : ℕ → ℕ} (R : Subring ℂ_[p])
    (χ : HorizontalCharacter p m) :
    HorizontalGroupAlgebra R p m χ.support →+* ℂ_[p] :=
  ((MonoidAlgebra.lift R ℂ_[p] (HorizontalFiniteGroup p m χ.support)) χ.toMonoidHom).toRingHom

private theorem horizontalCharacterEvalRingHom_apply
    {p : ℕ} [Fact p.Prime] {m : ℕ → ℕ} (R : Subring ℂ_[p])
    (χ : HorizontalCharacter p m) (x : HorizontalGroupAlgebra R p m χ.support) :
    horizontalCharacterEvalRingHom R χ x =
      x.coeff.sum fun g a => (a : ℂ_[p]) * χ.toMonoidHom g := by
  unfold horizontalCharacterEvalRingHom
  change ((MonoidAlgebra.lift R ℂ_[p] (HorizontalFiniteGroup p m χ.support))
    χ.toMonoidHom) x = _
  rw [MonoidAlgebra.lift_apply]
  apply Finsupp.sum_congr
  intro g hg
  change (x.coeff g : ℂ_[p]) * χ.toMonoidHom g =
    (x.coeff g : ℂ_[p]) * χ.toMonoidHom g
  rfl

theorem _root_.solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L)
    (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors)
    (hzero : Θ.HasSeededCriticalZeroSet) :
    ∃ μ : SeededNormalizedThetaMeasureV3 L,
      μ.characters = Θ.characters ∧
      μ.InterpolatesSeededCriticalValues := by
  let ν : HorizontalMeasure Θ.coefficientRing p L.exponent :=
    { finiteLevel := fun A => (normalizedFiniteLevel Θ hunit A).coeff
      compatible := by
        intro A B hAB
        have h := normalizedFiniteLevel_compatible Θ hnorm hunit A B hAB
        exact congrArg MonoidAlgebra.coeff h }
  let μ : SeededNormalizedThetaMeasureV3 L :=
    { coefficientRing := Θ.coefficientRing
      coefficientRing_eq := Θ.coefficientRing_eq
      coefficient_integral := Θ.coefficient_integral
      characters := Θ.characters
      measure := ν }
  refine ⟨μ, rfl, ?_⟩
  intro χ
  have heval : ν.eval χ ≠ 0 ↔ Θ.eval χ ≠ 0 := by
    obtain ⟨u, hu⟩ := normalizedFiniteLevel_unit_multiple Θ hnorm hunit χ.support
    let ev := horizontalCharacterEvalRingHom Θ.coefficientRing χ
    have hν : ν.eval χ = ev (normalizedFiniteLevel Θ hunit χ.support) := by
      rw [HorizontalMeasure.eval, horizontalCharacterEvalRingHom_apply]
    have hΘ : Θ.eval χ = ev (Θ.theta χ.support) := by
      rw [SeededFiniteThetaDataV3.eval, horizontalCharacterEvalRingHom_apply]
    rw [hν, hΘ, hu, map_mul]
    exact mul_ne_zero_iff_left ((u.isUnit.map ev).ne_zero)
  change ν.eval χ ≠ 0 ↔ _
  rw [heval]
  exact hzero χ

end HorizontalPadicL
