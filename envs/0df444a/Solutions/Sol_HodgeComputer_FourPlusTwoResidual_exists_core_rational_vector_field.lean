-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_core_rational_vector_field
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T14:17:07.031969+00:00
-- url     : https://prove2.me/submissions/319c904e-6d43-4771-892c-058abe20fb9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_ratio_coordinates
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_chart_t4_current_for_core_ratio_P
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_core_rational_equation_of_ratio_chart_transport
import Definitions.Def_HodgeComputerFourPlusTwoWormholeBridge
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial

/-!
WORMHOLE sketch of `exists_core_rational_vector_field`:
1. produce standard core ratio coordinates `(a,s,t,P)` in the given fraction field;
2. produce a δ-frame-compatible ratio-chart `t⁴` current for that `P`;
3. assemble `v` via ratio-chart transport into `CoreRationalEquation`.
-/

theorem solution
    {K : Type} [Field K] [CharZero K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    [IsFractionRing (MvPolynomial (Fin 4) ℂ) K]
    (δ : Fin 4 → Derivation ℤ K K)
    (hδ : ∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
      δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
        algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) :
    ∃ v : Fin 4 → K, HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v := by
  obtain ⟨a, s, t, P, ha, ht, _, _, _, hP, hSrc⟩ :=
    exists_core_ratio_coordinates (K := K)
  obtain ⟨Dr, Ds, Dt, qr, qs, qt, hW, hFrame1, hFrame2, hFrame3⟩ :=
    exists_chart_t4_current_for_core_ratio_P (K := K) δ hδ a s t P ha ht hP hSrc
  exact core_rational_equation_of_ratio_chart_transport (K := K) δ hδ
    Dr Ds Dt a s t P qr qs qt hW hP hSrc hFrame1 hFrame2 hFrame3
