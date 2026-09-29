-- Prove2me | solution 1 for ModularCurve.sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ab71bdb8-ef8b-55be-82f0-c22a955c7a38

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Theorems.Thm_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve KaehlerDifferential

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    [HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)] [HasCanonicalLocalResidueKStar K ↥(charLDegeneracyRoof K N ℓ)] [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    [∀ v : Place K ↥(modularFunctionFieldC K N), v.DCoordGenerates] [∀ w : Place K ↥(charLDegeneracyRoof K N ℓ), w.DCoordGenerates]
    [Nontrivial Ω[↥(modularFunctionFieldC K N)⁄K]] [Nontrivial Ω[↥(charLDegeneracyRoof K N ℓ)⁄K]]
    (hαI : HeckeAlphaCIntegral K N ℓ) (hβI : HeckeBetaCIntegral K N ℓ)
    (hFα : FibreResidueIdentityAlong (heckeAlphaC K N ℓ) hαI) (hFβ : FibreResidueIdentityAlong (heckeBetaC K N ℓ) hβI)
    (hsep : SeparableAlong K (heckeBetaC K N ℓ))
    (hΩ : ∀ η : Ω[↥(charLDegeneracyRoof K N ℓ)⁄K], ∃ (ω₁ : Ω[↥(modularFunctionFieldC K N)⁄K]) (c : ↥(charLDegeneracyRoof K N ℓ)), η = c • Differential.pullbackAlong (heckeBetaC K N ℓ) ω₁)
    (SS : Finset (Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (hstab : ∀ w : Place K ↥(charLDegeneracyRoof K N ℓ),
      Place.restrictAlong (heckeAlphaC K N ℓ) hαI w ∈ SS ↔ Place.restrictAlong (heckeBetaC K N ℓ) hβI w ∈ SS)
    (m : ℕ) (hm : 1 ≤ m) (u : ↥(charLDegeneracyRoof K N ℓ)) (gv f₁ : ↥(modularFunctionFieldC K N)) (ω : Ω[↥(modularFunctionFieldC K N)⁄K])
    (hSP : ∀ x : SSIndex p N K hp5 (2 * (m : ℤ)),
      f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u) = 0 ∨
        -(ModularCurve.weightDivisor K N m x.1) + 1 ≤ x.1.ord (f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u)))
    (hLT : ∀ x ∈ SS, ¬ ((placeWidth N x : ℤ) ∣ (m : ℤ)) →
      f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u) = 0 ∨
        -(ModularCurve.weightDivisor K N m x) ≤ x.ord (f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u)))
    (hωi : ∀ x : SSIndex p N K hp5 (2 * (m : ℤ)), ModularCurve.weightDivisor K N m x.1 - 1 ≤ x.1.ordDifferential ω)
    (hωn : ∀ x ∈ SS, ¬ ((placeWidth N x : ℤ) ∣ (m : ℤ)) → ModularCurve.weightDivisor K N m x ≤ x.ordDifferential ω) :
    ∑ x ∈ SS, kaehlerResidueTerm ω (diagonalHom K ↥(modularFunctionFieldC K N) f₁) x
      = ∑ z ∈ SS, kaehlerResidueTerm
          (Differential.traceAlong (heckeBetaC K N ℓ) (u • Differential.pullbackAlong (heckeAlphaC K N ℓ) ω))
          (diagonalHom K ↥(modularFunctionFieldC K N) gv) z := by
  classical
  set g : ↥(modularFunctionFieldC K N) := traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u) with hg

  have step1 : ∀ x ∈ SS, kaehlerResidueTerm ω (diagonalHom K _ f₁) x = kaehlerResidueTerm ω (diagonalHom K _ g) x := by
    intro x hx
    have hsplit : f₁ = (f₁ - g) + g := by abel
    rw [hsplit, map_add, kaehlerResidueTerm_add_right]
    suffices h0 : kaehlerResidueTerm ω (diagonalHom K _ (f₁ - g)) x = 0 by rw [h0, zero_add]
    apply kaehlerResidueTerm_eq_zero_of_ord_nonneg
    rw [diagonalHom_apply]
    by_cases hd : f₁ - g = 0
    · exact Or.inl (by rw [hd, zero_mul])
    by_cases hω0 : x.differentialCoeff ω = 0
    · exact Or.inl (by rw [hω0, mul_zero])
    refine Or.inr ?_
    rw [x.ord_mul hd hω0]
    by_cases hidx : (placeWidth N x : ℤ) ∣ (m : ℤ)
    · have hxI : x ∈ ssPlaces p N K ∧ 2 ≤ 2 * (m : ℤ) ∧ 2 ∣ 2 * (m : ℤ) ∧ ((placeWidth N x : ℤ) ∣ 2 * (m : ℤ) / 2) ∧ 5 ≤ p := by
        refine ⟨(hSS x).mp hx, ?_, dvd_mul_right 2 _, ?_, hp5⟩
        · omega
        · rwa [Int.mul_ediv_cancel_left _ two_ne_zero]
      rcases hSP ⟨x, hxI⟩ with hsp | hsp
      · exact absurd hsp hd
      · have hω' := hωi ⟨x, hxI⟩
        change ModularCurve.weightDivisor K N m x - 1 ≤ x.ord (x.differentialCoeff ω) at hω'
        change -(ModularCurve.weightDivisor K N m x) + 1 ≤ x.ord (f₁ - g) at hsp
        omega
    · rcases hLT x hx hidx with hlt | hlt
      · exact absurd hlt hd
      · have hω' := hωn x hx hidx
        change ModularCurve.weightDivisor K N m x ≤ x.ord (x.differentialCoeff ω) at hω'
        omega
  rw [Finset.sum_congr rfl step1, hg]
  exact AlgebraicCurve.sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
    (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ) hαI hβI hFα hFβ hsep hΩ SS hstab gv u ω

end S_ModularCurve_sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong
end P2MW
export P2MW.S_ModularCurve_sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong (solution)
