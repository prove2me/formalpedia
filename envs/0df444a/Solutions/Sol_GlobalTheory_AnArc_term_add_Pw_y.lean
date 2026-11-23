-- Prove2me | solution 1 for GlobalTheory.AnArc.term_add_Pw_y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:55.85583+00:00
-- url     : https://prove2.me/submissions/cb269de6-495d-4d4c-956b-f6b2060cf486

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_e_nat_mul
import Theorems.Thm_GlobalTheory_AnArc_q_add

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
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (μ y : A.X) (v : A.V) :
    (A.psi y * eTwoPi (v.1 y) * eTwoPi (w * A.q y)) ^ j *
        (A.term j α th μ (v + A.Pw w (La.mk y 0 0)) * eTwoPi (w * A.exponent j α μ)) =
      A.term j α th (μ + y) v * eTwoPi (w * A.exponent j α (μ + y)) := by
  have h1 : (v + A.Pw w (La.mk y 0 0)).1 (α + j • μ) =
      v.1 (α + j • μ) + A.T y α + j * A.T μ y + w * A.be y α + j * (w * A.be μ y) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, Pw_fst_apply, A.T_symm μ y, A.be_symm μ y]
    simp; ring
  have h2 : (v + A.Pw w (La.mk y 0 0)).2 + A.ct μ = v.2 + A.ct (μ + y) := by
    simp; abel
  have h3 : v.1 (α + j • (μ + y)) = v.1 (α + j • μ) + j * v.1 y := by
    simp; ring
  have h4 : w * A.exponent j α (μ + y) =
      w * A.exponent j α μ + j * (w * A.q y) + j * (w * A.be μ y) + w * A.be y α := by
    simp [exponent, q_add]; ring
  rw [term, term, h1, h2, h3, h4, psi_add, map_add A.T, AddMonoidHom.add_apply]
  simp only [e_add, e_nat_mul, mul_pow]
  ring
end GlobalTheory.AnArc
