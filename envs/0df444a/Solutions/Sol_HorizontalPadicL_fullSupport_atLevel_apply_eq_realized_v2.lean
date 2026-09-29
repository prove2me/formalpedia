-- Prove2me | solution 1 for HorizontalPadicL.fullSupport_atLevel_apply_eq_realized_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:30:04.029072+00:00
-- url     : https://prove2.me/submissions/0d7af5e1-470b-4abd-a105-2c728e0dca8f

import Definitions.Def_KN_SeededInverseThetaSystemV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- If a horizontal character uses its full conductor, then the full-level
character used in the quotient construction agrees, on units, with its
primitive realization.  The formulation on integer representatives avoids
dependent transports between equal `ZMod` levels. -/
theorem fullSupport_atLevel_apply_eq_realized
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ : HorizontalCharacter p L.exponent)
    (hfull : (R.realized χ).2.conductor = L.supportModulus χ.support)
    (u : (ZMod (L.supportModulus χ.support))ˣ) :
    R.atLevel χ u.val.val = (R.realized χ).2 u.val.val := by
  haveI : NeZero (L.supportModulus χ.support) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
  have hcop : IsCoprime ((u.val.val : ℕ) : ℤ) ((L.supportModulus χ.support : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
  have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime (R.atLevel χ) hcop
  simp only [Int.cast_natCast] at h
  exact h.symm

end HorizontalPadicL


-- Platform entry point: restates the target verbatim.
namespace HorizontalPadicL

/-- If a horizontal character uses its full conductor, then the full-level
character used in the quotient construction agrees, on units, with its
primitive realization.  The formulation on integer representatives avoids
dependent transports between equal `ZMod` levels. -/
theorem _root_.solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ : HorizontalCharacter p L.exponent)
    (hfull : (R.realized χ).2.conductor = L.supportModulus χ.support)
    (u : (ZMod (L.supportModulus χ.support))ˣ) :
    R.atLevel χ u.val.val = (R.realized χ).2 u.val.val := by
  apply @HorizontalPadicL.fullSupport_atLevel_apply_eq_realized <;> assumption

end HorizontalPadicL
