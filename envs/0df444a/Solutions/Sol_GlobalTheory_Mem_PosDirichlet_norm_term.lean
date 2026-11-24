-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.norm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:16.464301+00:00
-- url     : https://prove2.me/submissions/34820b16-db78-42fd-ad2d-0eec2d091dee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {w : ℝ} (hw : 0 ≤ w) {N : ℕ} (hN : N ≠ 0) (s : ℂ) :
    ‖(w : ℂ) * (N : ℂ) ^ (-s)‖ = ((w : ℂ) * (N : ℂ) ^ (-(s.re : ℂ))).re := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN), Complex.norm_real,
    Real.norm_of_nonneg hw, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg N), ← Complex.ofReal_mul, Complex.ofReal_re, neg_re]
end GlobalTheory.Mem.PosDirichlet
