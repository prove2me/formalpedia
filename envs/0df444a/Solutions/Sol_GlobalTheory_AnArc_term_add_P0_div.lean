-- Prove2me | solution 1 for GlobalTheory.AnArc.term_add_P0_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:03.966422+00:00
-- url     : https://prove2.me/submissions/c6de7813-4d74-44c7-9b6b-754751c769dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_exp_lin
import Theorems.Thm_P2M_GlobalTheory_AnArc_shift_apply__29043617d48c
import Theorems.Thm_GlobalTheory_AnArc_e_neg_div


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
variable (k : ℕ) [NeZero k]
namespace GlobalTheory.AnArc
theorem _root_.solution (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) :
    A.term k α th μ (v + (k : ℂ)⁻¹ • A.P0 la) =
      Complex.exp (A.lin la v) * A.term k (α + la.y) (A.shift k la α th) μ v := by
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  have h1 : (v + (k : ℂ)⁻¹ • A.P0 la).1 (α + k • μ) = v.1 (α + k • μ) + (A.P0 la).1 α / k + A.T μ la.y +
      la.n μ + -(A.H (A.ct μ) la.l / (2 * Complex.I)) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, Prod.smul_fst, AddMonoidHom.smul_apply, map_add (A.P0 la).1,
      map_nsmul, degeneratingTori_basePeriodMap_fst_apply A la μ, A.T_symm μ, smul_eq_mul, nsmul_eq_mul, mul_add, inv_mul_cancel_left₀ hk]
    ring
  have h2 : (v + (k : ℂ)⁻¹ • A.P0 la).2 + A.ct μ = v.2 + A.ct μ + (k : ℂ)⁻¹ • (A.P0 la).2 := by
    rw [Prod.snd_add, Prod.smul_snd]; abel
  have h3 : v.1 (α + la.y + k • μ) = v.1 (α + k • μ) + v.1 la.y := by
    rw [add_right_comm, map_add]
  rw [term, term, h1, h2, h3, shift_apply', exp_lin, map_add (A.T μ), H_add_left]
  simp only [e_add, e_intCast, e_neg_div, mul_add, neg_add, Complex.exp_add, Complex.exp_neg]
  have := e_ne_zero (v.1 la.y)
  have := Complex.exp_ne_zero (Real.pi * A.H v.2 la.l)
  field_simp
end GlobalTheory.AnArc
