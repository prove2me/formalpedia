-- Prove2me | solution 1 for GlobalTheory.FlagMahler.Kset_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:46.890868+00:00
-- url     : https://prove2.me/submissions/752050ae-dd9e-4467-959a-ac597af57fa6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open GlobalTheory GlobalTheory.FlagMahler
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open Complex
open NumberField Module
open Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
namespace GlobalTheory.FlagMahler
namespace _root_.GlobalTheory.FlagMahler
theorem _root_.solution (R : ℝ) :
    IsCompact (_root_.GlobalTheory.FlagMahler.Kset X R) := by
  change IsCompact (_root_.GlobalTheory.FlagMahler.Kset X R : Set (X.Ψ → Fin r → Fin r → ℂ))
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : (_root_.GlobalTheory.FlagMahler.Kset X R : Set (X.Ψ → Fin r → Fin r → ℂ)) = ⋂ τ : X.Ψ,
        ({w : X.Ψ → Fin r → Fin r → ℂ | _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (Matrix.of (w τ)) =
          diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ))} ∩
          ⋂ a : Fin r, ⋂ c : Fin r, {w | ‖w τ a c‖ ≤ R}) := by
      ext w
      simp only [_root_.GlobalTheory.FlagMahler.Kset, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Set.mem_setOf_eq, Set.mem_iInter,
        Set.mem_inter_iff]
    rw [this]
    refine isClosed_iInter fun τ => IsClosed.inter ?_ ?_
    · refine isClosed_eq ?_ continuous_const
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply]
      fun_prop
    · exact isClosed_iInter fun a => isClosed_iInter fun c =>
        isClosed_le (by fun_prop) continuous_const
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨|R|, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun c => ?_
    exact ((hw τ).2 a c).trans (le_abs_self R)
end _root_.GlobalTheory.FlagMahler
end GlobalTheory.FlagMahler
