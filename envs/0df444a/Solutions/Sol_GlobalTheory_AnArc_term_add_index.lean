-- Prove2me | solution 1 for GlobalTheory.AnArc.term_add_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:01.490852+00:00
-- url     : https://prove2.me/submissions/cfd46a54-4d62-4356-bb29-a71c4bd4aa04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_e_nat_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ y : A.X) (v : A.V) :
    A.term j α th (μ + y) v =
      (A.psi y : ℂ) ^ j * eTwoPi (A.T y α) * A.term j (α + j • y) (fun z => th (z + A.ct y)) μ v := by
  have h1 : α + j • (μ + y) = α + j • y + j • μ := by rw [smul_add]; abel
  rw [term, term, h1, psi_add, map_add A.ct, add_assoc v.2, map_add A.T, AddMonoidHom.add_apply,
    map_add (A.T μ), map_nsmul (A.T μ), nsmul_eq_mul]
  simp only [e_add, e_nat_mul, mul_pow]
  ring
end GlobalTheory.AnArc
