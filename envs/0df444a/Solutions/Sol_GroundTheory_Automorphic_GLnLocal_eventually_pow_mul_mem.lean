-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.eventually_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:33.402656+00:00
-- url     : https://prove2.me/submissions/a45674ec-701c-4a67-bc5b-9ab7e7b3e907

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (x : F) :
    ∀ᶠ m in atTop, (uniformizer F : F) ^ m * x ∈ 𝒪[F] := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hx')⁻¹
  have hm' : valuation F (uniformizer F : F) ^ m ≤ (valuation F x)⁻¹ := by simpa using hm.le
  refine eventually_atTop.mpr ⟨m, fun m' hmm' => ?_⟩
  rw [Valuation.mem_integer_iff, map_mul, map_pow]
  calc valuation F (uniformizer F : F) ^ m' * valuation F x
      ≤ (valuation F x)⁻¹ * valuation F x :=
        mul_le_mul' ((pow_le_pow_right_of_le_one' (valuation_uniformizer_lt_one F).le hmm').trans
          hm') le_rfl
    _ = 1 := inv_mul_cancel₀ hx'
end GroundTheory.Automorphic.GLnLocal
