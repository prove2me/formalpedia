-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.quad_affine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:15.198638+00:00
-- url     : https://prove2.me/submissions/9582c9c6-9340-48ef-8bf3-c1963f2bf889

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution {S : AddSubgroup M} {h : M → ℂ} (h1 : ∀ x ∈ S, IsMu (h x))
    (h2 : ∀ x ∈ S, ∀ y ∈ S, h (x + y) * h 0 = h x * h y) : Quad S h := by
  refine ⟨h1, fun x hx y hy z hz => ?_⟩
  have h0 : h 0 ≠ 0 := mu_ne (h1 0 S.zero_mem)
  have e1 : h (x + y) = h x * h y / h 0 := by rw [eq_div_iff h0]; exact h2 x hx y hy
  have e2 : h (y + z) = h y * h z / h 0 := by rw [eq_div_iff h0]; exact h2 y hy z hz
  have e3 : h (x + z) = h x * h z / h 0 := by rw [eq_div_iff h0]; exact h2 x hx z hz
  have e4 : h (x + y + z) = h (x + y) * h z / h 0 := by
    rw [eq_div_iff h0]; exact h2 _ (S.add_mem hx hy) z hz
  rw [e4, e1, e2, e3]
  field_simp
end GlobalTheory.Phase.ShapeOps
