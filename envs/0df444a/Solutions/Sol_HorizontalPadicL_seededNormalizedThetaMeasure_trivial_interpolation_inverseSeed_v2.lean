-- Prove2me | solution 1 for HorizontalPadicL.seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:55:17.763567+00:00
-- url     : https://prove2.me/submissions/46bb78a2-a638-480e-a066-88f692325916

import Definitions.Def_KN_InverseSeedConventionV2
import Definitions.Def_KN_SeededFiniteThetaCriticalZeroSetV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

private theorem changeLevel_heq_self_of_eq {n m : ℕ}
    (h : n ∣ m) (e : m = n) (χ : DirichletCharacter MTT.Qbar n) :
    HEq (DirichletCharacter.changeLevel h χ) χ := by
  subst m
  have hh : h = dvd_refl n := Subsingleton.elim _ _
  subst h
  exact heq_of_eq (DirichletCharacter.changeLevel_self χ)

private theorem primitiveCharacter_heq_self_of_isPrimitive
    {n : ℕ} [NeZero n] (χ : DirichletCharacter MTT.Qbar n)
    (hχ : χ.IsPrimitive) : HEq χ.primitiveCharacter χ := by
  have h := changeLevel_heq_self_of_eq χ.conductor_dvd_level
    hχ.symm χ.primitiveCharacter
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  exact h.symm

private theorem primitiveProductV2_trivial_right
    (η : DirichletCharacterWithLevel) (hη : η.2.IsPrimitive) :
    primitiveProductV2 η trivialCharacterWithLevelV2 = η := by
  rcases η with ⟨⟨n, hn⟩, χ⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (Nat.lcm n 1) :=
    ⟨Nat.lcm_ne_zero (Nat.ne_of_gt hn) Nat.one_ne_zero⟩
  change χ.conductor = n at hη
  unfold primitiveProductV2 trivialCharacterWithLevelV2
  dsimp only
  have hc : (χ.mul (1 : DirichletCharacter MTT.Qbar 1)).conductor = n := by
    simp only [DirichletCharacter.mul, map_one, mul_one]
    rw [DirichletCharacter.conductor_changeLevel]
    exact hη
  apply Sigma.ext (Subtype.ext hc)
  have hφprim : (χ.mul (1 : DirichletCharacter MTT.Qbar 1)).IsPrimitive :=
    hc.trans (Nat.lcm_one_right n).symm
  have hprim := primitiveCharacter_heq_self_of_isPrimitive
    (χ.mul (1 : DirichletCharacter MTT.Qbar 1)) hφprim
  have hmul : HEq (χ.mul (1 : DirichletCharacter MTT.Qbar 1)) χ := by
    simp only [DirichletCharacter.mul, map_one, mul_one]
    exact changeLevel_heq_self_of_eq _ (Nat.lcm_one_right n) χ
  exact hprim.trans hmul

theorem _root_.solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (hηprim : η.2.IsPrimitive)
    (characters : SeededHorizontalCharacterRealizationV3 L)
    (hcharacters : characters.HasExpectedProperties)
    (μ : SeededNormalizedThetaMeasureV3 L)
    (hμcharacters : μ.characters = characters)
    (hinterp : μ.InterpolatesSeededCriticalValues) :
    μ.measure.eval (trivialHorizontalCharacterV2 p L.exponent) ≠ 0 ↔
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by
  have h := hinterp (trivialHorizontalCharacterV2 p L.exponent)
  have hrealized : μ.characters.realized
      (trivialHorizontalCharacterV2 p L.exponent) =
      trivialCharacterWithLevelV2 :=
    (congrArg (fun R : SeededHorizontalCharacterRealizationV3 L =>
      R.realized (trivialHorizontalCharacterV2 p L.exponent))
      hμcharacters).trans hcharacters.2.1
  have htheta : primitiveProductV2 η (μ.characters.realized
      (trivialHorizontalCharacterV2 p L.exponent)) = η :=
    (congrArg (primitiveProductV2 η) hrealized).trans
      (primitiveProductV2_trivial_right η hηprim)
  have hcritical := congrArg (fun θ : DirichletCharacterWithLevel =>
    @MTT.criticalLValue ι f.form θ.1.1
      ⟨Nat.ne_of_gt θ.1.2⟩ θ.2 (k / 2 - 1)) htheta
  dsimp only at h
  rw [hcritical] at h
  exact h

end HorizontalPadicL
