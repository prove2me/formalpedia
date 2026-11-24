-- Prove2me | solution 1 for GlobalTheory.StabFlat.flat_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:13.84518+00:00
-- url     : https://prove2.me/submissions/03629a40-2710-4930-ad98-d2596739278b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat
namespace GlobalTheory.StabFlat
theorem _root_.solution {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] {ϖ : V}
    (hϖ : Irreducible ϖ) (σ : V →+* C) (h : IsSMulRegular C (σ ϖ)) : σ.Flat := by
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, mul_assoc, map_pow] at h1
  exact (h.pow n).right_eq_zero_of_smul (((u.isUnit.map σ).mul_right_eq_zero).1 h1)
end GlobalTheory.StabFlat
