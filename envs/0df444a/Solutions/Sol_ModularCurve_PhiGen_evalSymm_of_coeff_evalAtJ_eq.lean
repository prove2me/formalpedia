-- Prove2me | solution 1 for ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a592ac79-051d-5abe-9c4d-f0214d50b34f

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_poleOrderLE
import Theorems.Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead
import Theorems.Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le
import Theorems.Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq
import Theorems.Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion
import Theorems.Thm_ModularCurve_PhiGen_evalSymm_of_splits
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul dedekindPsi evalAtJ ModularPolynomialData EvalSymm coeffEmb coeffEmb_coeff dedekindPsi_prime"
p2m_open "ModularCurve"
namespace PhiGen
p2m_export "ModularCurve.PhiGen" "conj phiProd PhiGenDescends phiProd_conj_coeff_zero_lead phiProd_conj_coeff_eq_zero_of_le splits_of_coeff_evalAtJ_eq evalSymm_of_splits"
p2m_open "ModularCurve.PhiGen"

section Seam

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

namespace PhiGenDescends p2m_export "ModularCurve.PhiGen.PhiGenDescends" "poleOrderLE" end PhiGenDescends
namespace PhiGenDescends
p2m_open_scoped "ModularCurve.PhiGen.PhiGenDescends" in

private theorem _root_.ModularCurve.PhiGen.PhiGenDescends.coeff_phiProd_coeff (hc : PhiGenDescends ℓ ζ c) (k : ℕ) (m : ℤ) :
    ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) = algebraMap ℚ K ((c k).coeff m) := by
  rw [hc k, coeffEmb_coeff, qExpand_coeff_mul]

end PhiGenDescends
p2m_export "ModularCurve.PhiGen" "PhiGenDescends.coeff_phiProd_coeff"
namespace PhiGenDescends
p2m_open_scoped "ModularCurve.PhiGen.PhiGenDescends" in

private theorem _root_.ModularCurve.PhiGen.PhiGenDescends.c_zero_coeff_lead (hc : PhiGenDescends ℓ ζ c)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (c 0).coeff (-((ℓ + 1 : ℕ) : ℤ)) = 1 := by
  refine (algebraMap ℚ K).injective ?_
  rw [← hc.coeff_phiProd_coeff 0 (-((ℓ + 1 : ℕ) : ℤ)), map_one]
  have hidx : (ℓ : ℤ) * (-((ℓ + 1 : ℕ) : ℤ)) = -((ℓ * ℓ + ℓ : ℕ) : ℤ) := by push_cast; ring
  rw [hidx]
  exact phiProd_conj_coeff_zero_lead ℓ ζ hζ

end PhiGenDescends
p2m_export "ModularCurve.PhiGen" "PhiGenDescends.c_zero_coeff_lead"
namespace PhiGenDescends
p2m_open_scoped "ModularCurve.PhiGen.PhiGenDescends" in

private theorem _root_.ModularCurve.PhiGen.PhiGenDescends.c_coeff_eq_zero_of_ne_zero (hc : PhiGenDescends ℓ ζ c)
    (k : ℕ) (hk : k ≠ 0) (m : ℕ) (hm : ℓ + 1 ≤ m) :
    (c k).coeff (-(m : ℤ)) = 0 := by
  refine (algebraMap ℚ K).injective ?_
  rw [← hc.coeff_phiProd_coeff k (-(m : ℤ)), map_zero]
  have hidx : (ℓ : ℤ) * (-(m : ℤ)) = -((ℓ * m : ℕ) : ℤ) := by push_cast; ring
  rw [hidx]
  exact phiProd_conj_coeff_eq_zero_of_le ℓ ζ k hk (ℓ * m) (by nlinarith [hℓ.out.two_le])

end PhiGenDescends
p2m_export "ModularCurve.PhiGen" "PhiGenDescends.c_coeff_eq_zero_of_ne_zero"
namespace PhiGenDescends
p2m_open_scoped "ModularCurve.PhiGen.PhiGenDescends" in

private theorem _root_.ModularCurve.PhiGen.PhiGenDescends.c_zero_coeff_eq_zero_of_lt (hc : PhiGenDescends ℓ ζ c)
    (m : ℕ) (hm : ℓ + 1 < m) :
    (c 0).coeff (-(m : ℤ)) = 0 :=
  hc.poleOrderLE 0 (-(m : ℤ)) (by push_cast; omega)

end PhiGenDescends
p2m_export "ModularCurve.PhiGen" "PhiGenDescends.c_zero_coeff_eq_zero_of_lt"
end Seam

section Symmetry

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

private theorem evalSymm_of_coeff_evalAtJ_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    EvalSymm data.Φ := by

  have hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) :=
    splits_of_coeff_evalAtJ_eq ζ hc data hcoeff

  have h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-((dedekindPsi ℓ : ℕ) : ℤ)) = 1 := by
    rw [hcoeff 0, dedekindPsi_prime hℓ.out]
    exact hc.c_zero_coeff_lead hζ
  have h0le : ∀ m : ℕ, dedekindPsi ℓ < m →
      (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0 := by
    intro m hm
    rw [hcoeff 0]
    exact hc.c_zero_coeff_eq_zero_of_lt m (by rwa [dedekindPsi_prime hℓ.out] at hm)
  have hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi ℓ ≤ m →
      (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0 := by
    intro k hk0 m hm
    rw [hcoeff k]
    exact hc.c_coeff_eq_zero_of_ne_zero k hk0 m (by rwa [dedekindPsi_prime hℓ.out] at hm)

  obtain ⟨hTmonic, hTdeg⟩ := data.transposeToAdjoin_monic_of_qExpansion h0top h0le hk

  exact evalSymm_of_splits ℓ ζ hζ data hsplit hTmonic hTdeg.le

end Symmetry

end PhiGen
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.ModularCurve.PhiGen in

theorem solution {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) : EvalSymm data.Φ :=
  ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq hζ hc data hcoeff

#print axioms solution

end S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq
end P2MW
export P2MW.S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq (solution)
