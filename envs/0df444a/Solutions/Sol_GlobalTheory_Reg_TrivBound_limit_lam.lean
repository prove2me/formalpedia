-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.limit_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:06.611119+00:00
-- url     : https://prove2.me/submissions/d80a132b-e706-4eeb-abc1-aa6ba3fb244f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]
namespace GlobalTheory.Reg.TrivBound
theorem _root_.solution (w t nu c' : ℝ) (eO : ℕ) (heO : 0 < eO) (ht : 0 ≤ t) (hc' : 0 ≤ c')
    (h : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) + (⌈(N : ℝ) * c'⌉₊ : ℝ) * t) :
    w ≤ nu + c' * t := by
  by_contra hlt
  push Not at hlt
  have hδ0 : 0 < w - nu - c' * t := by linarith
  have heOr : (0 : ℝ) < eO := by exact_mod_cast heO
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / eO + t) / (w - nu - c' * t))
  have hNr : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by positivity) hδ0.le) hN
  have hN0 : 0 < N := by exact_mod_cast hNr
  have h1 := h N hN0
  have hc1 : (⌈(eO : ℝ) * N * nu⌉ : ℝ) ≤ eO * N * nu + 1 := (Int.ceil_lt_add_one _).le
  have hc2 : (⌈(N : ℝ) * c'⌉₊ : ℝ) ≤ N * c' + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) ≤ N * nu + 1 / eO := by
    calc (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) ≤ (eO * N * nu + 1) * (1 / eO) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ = N * nu + 1 / eO := by field_simp
  have h3 : (⌈(N : ℝ) * c'⌉₊ : ℝ) * t ≤ (N * c' + 1) * t := mul_le_mul_of_nonneg_right hc2 ht
  have key : (N : ℝ) * (w - nu - c' * t) ≤ 1 / eO + t := by nlinarith
  have := (div_lt_iff₀ hδ0).1 hN
  linarith
end GlobalTheory.Reg.TrivBound
