-- Prove2me | solution 1 for GlobalTheory.AnArc.term_add_Pw_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:27:42.242042+00:00
-- url     : https://prove2.me/submissions/544e2705-0675-4002-b521-24ad4a2cf47f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_add_P0_div
import Theorems.Thm_GlobalTheory_AnArc_exponent_add_weight

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
theorem _root_.solution (w : ℂ) (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) :
    A.term k α th μ (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (w * A.exponent k α μ) =
      Complex.exp (A.lin la v) * eTwoPi (w * A.be la.y α / k) *
        (A.term k (α + la.y) (A.shift k la α th) μ v * eTwoPi (w * A.exponent k (α + la.y) μ)) := by
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  have h1 : (v + (k : ℂ)⁻¹ • A.Pw w la).1 (α + k • μ) =
      (v + (k : ℂ)⁻¹ • A.P0 la).1 (α + k • μ) + w * A.be la.y α / k + w * A.be la.y μ := by
    simp only [Prod.fst_add, AddMonoidHom.add_apply, Prod.smul_fst, AddMonoidHom.smul_apply, Pw_fst_apply,
      degeneratingTori_basePeriodMap_fst_apply, smul_eq_mul, map_add (A.be la.y), map_nsmul (A.be la.y), nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have h2 : A.term k α th μ (v + (k : ℂ)⁻¹ • A.Pw w la) = A.term k α th μ (v + (k : ℂ)⁻¹ • A.P0 la) *
      eTwoPi (w * A.be la.y α / k) * eTwoPi (w * A.be la.y μ) := by
    rw [term, term, h1, e_add, e_add]
    simp only [Prod.snd_add, Prod.smul_snd, Pw_snd, degeneratingTori_basePeriodMap_snd]
    ring
  rw [h2, term_add_P0_div, exponent_add_weight]
  push_cast
  rw [mul_add w, e_add]
  ring
end GlobalTheory.AnArc
