-- Prove2me | solution 1 for GlobalTheory.AnArc.translate_mem_Theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:56.608272+00:00
-- url     : https://prove2.me/submissions/2bafd007-5026-4714-8b38-cd2821f76fa4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_H_smul_left
import Theorems.Thm_GlobalTheory_AnArc_ah_add

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
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (μ : A.X) :
    (fun z => th (z + A.ct μ)) ∈ A.Theta j (α + j • μ) :=
  ⟨h.1.comp (differentiable_id.add_const _), fun l z => by
    have h1 : A.H (A.ct (α + j • μ)) l = A.H (A.ct α) l + j * A.H (A.ct μ) l := by
      rw [map_add, map_nsmul, H_add_left, ← Nat.cast_smul_eq_nsmul ℂ, H_smul_left]
    show th (z + l + A.ct μ) = _ * _ * th (z + A.ct μ)
    rw [add_right_comm, h.2, ah_add, h1, mul_pow, ← Complex.exp_nat_mul, mul_add, Complex.exp_add,
      mul_left_comm (Real.pi : ℂ) (j : ℂ)]
    ring⟩
end GlobalTheory.AnArc
