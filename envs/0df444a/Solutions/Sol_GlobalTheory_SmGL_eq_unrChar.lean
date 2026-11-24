-- Prove2me | solution 1 for GlobalTheory.SmGL.eq_unrChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:36.4844+00:00
-- url     : https://prove2.me/submissions/54e7bfcc-22c2-4abb-87b0-1e2976e20633

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.SmGL
theorem _root_.solution {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) : χ = unrChar k (χ ϖ) := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  refine MonoidHom.ext fun x => ?_
  have h1 : o (x / ϖ ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  have h2 := h _ (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  rw [map_div, map_zpow, div_eq_one] at h2
  exact h2
end GlobalTheory.SmGL
