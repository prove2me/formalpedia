-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:03.58981+00:00
-- url     : https://prove2.me/submissions/5e7c5dbc-64d9-4d48-a49c-1c18263423bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_hasRationalTorsion_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K]
variable {W : WeierstrassCurve K} {L : Type*} [Field L] [Algebra K L] {m n : ℕ}
namespace GlobalTheory
namespace HasRationalTorsion
theorem _root_.solution (h : HasRationalTorsion W L n) (C : VariableChange K) :
    HasRationalTorsion (C • W) L n := by
  classical
  rw [hasRationalTorsion_iff] at h ⊢
  intro x y hP h0
  have e : (C.map (algebraMap K L)) • (W.baseChange L) = (C • W).baseChange L := map_variableChange ..
  have h1 := congrArg (variableChangePoint _ e) h0
  rw [map_nsmul, map_zero, variableChangePoint_some] at h1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h _ _ _ h1
  have hu : algebraMap K L C.u ≠ 0 := by simp
  simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_coe] at ha hb
  have hx : algebraMap K L ((a - C.r) / C.u ^ 2) = x := by
    simp only [map_div₀, map_sub, map_pow, ha]
    field_simp
    ring
  refine ⟨⟨_, hx⟩, ⟨(b - C.s * (a - C.r) - C.t) / C.u ^ 3, ?_⟩⟩
  simp only [map_div₀, map_sub, map_mul, map_pow, ha, hb]
  field_simp
  ring
end HasRationalTorsion
end GlobalTheory
