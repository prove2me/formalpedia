-- Prove2me | solution 1 for GlobalTheory.AnArc.term_add_P0_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:58.560457+00:00
-- url     : https://prove2.me/submissions/8bd0ccc0-d685-447a-bb8c-8a0cc24945de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_e_neg_div
import Theorems.Thm_GlobalTheory_AnArc_translate_mem_Theta

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
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (μ : A.X) (l : A.abelian₂)
    (v : A.V) : A.term j α th μ (v + A.P0 (La.mk 0 0 l)) =
      (A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l)) ^ j * A.term j α th μ v := by
  have h1 : (v + A.P0 (La.mk 0 0 l)).1 (α + j • μ) =
      v.1 (α + j • μ) + -(A.H (A.ct (α + j • μ)) l / (2 * Complex.I)) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, degeneratingTori_basePeriodMap_fst_apply]; simp
  have h2 : (v + A.P0 (La.mk 0 0 l)).2 + A.ct μ = v.2 + l + A.ct μ := by simp
  have h3 := (A.translate_mem_Theta h μ).2 l v.2
  beta_reduce at h3
  have h4 : Complex.exp (-(Real.pi * A.H (A.ct (α + j • μ)) l)) *
      Complex.exp (Real.pi * A.H (A.ct (α + j • μ)) l) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [term, term, h1, h2, h3, e_add, e_neg_div]
  change _ = A.ah l v.2 ^ j * _
  linear_combination ((A.psi μ : ℂ) ^ j * eTwoPi (A.T μ α) * eTwoPi (v.1 (α + j • μ)) * A.ah l v.2 ^ j *
    th (v.2 + A.ct μ)) * h4
end GlobalTheory.AnArc
