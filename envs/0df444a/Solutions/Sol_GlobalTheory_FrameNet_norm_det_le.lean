-- Prove2me | solution 1 for GlobalTheory.FrameNet.norm_det_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:51.500081+00:00
-- url     : https://prove2.me/submissions/8704eb63-549a-4ecc-8933-57a5b61bf7d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
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
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
namespace GlobalTheory.FrameNet
theorem _root_.solution {r : ℕ} {m : Matrix (Fin r) (Fin r) ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hm : ∀ i k, ‖m i k‖ ≤ s) : ‖m.det‖ ≤ (r : ℝ) ^ r * s ^ r := by
  have hσ : ∀ σ : Equiv.Perm (Fin r), ‖Equiv.Perm.sign σ • ∏ i, m (σ i) i‖ ≤ s ^ r := by
    intro σ
    have hp : ‖∏ i, m (σ i) i‖ ≤ s ^ r := by
      rw [norm_prod]
      calc ∏ i, ‖m (σ i) i‖ ≤ ∏ _i : Fin r, s :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hm _ _)
        _ = s ^ r := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using hp
  have hfac : ((Nat.factorial r : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ • ∏ i, m (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin r), ‖Equiv.Perm.sign σ • ∏ i, m (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), s ^ r := Finset.sum_le_sum fun σ _ => hσ σ
    _ = (Nat.factorial r : ℝ) * s ^ r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (r : ℝ) ^ r * s ^ r := mul_le_mul_of_nonneg_right hfac (pow_nonneg hs _)
end GlobalTheory.FrameNet
