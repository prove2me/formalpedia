-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_permGL_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:29.363855+00:00
-- url     : https://prove2.me/submissions/f1852709-b3ad-4198-912c-e615a1bb3e3f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_permGL_mem_blockUpper_iff
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL
import Theorems.Thm_GroundTheory_Automorphic_mem_borel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable {β γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (g : GL (Fin n) F) :
    ∃ w : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ) := by
  set s := Tuple.sort β
  set t := Tuple.sort γ
  have hB : ∀ {δ : Fin n → ℕ} {u : Equiv.Perm (Fin n)}, Monotone (δ ∘ u) →
      ∀ b ∈ GroundTheory.Automorphic.borel n F, b ∈ blockUpper F n (δ ∘ u) := by
    intro δ u hm b hb i j hij
    apply (mem_borel_iff b).1 hb
    by_contra hle
    exact absurd (hm (not_lt.1 hle)) (not_le.2 hij)
  obtain ⟨w, hw⟩ := exists_mem_doubleCoset_permGL (k := F) ((permGL F s)⁻¹ * g * permGL F t)
  obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := mem_doubleCoset.1 hw
  refine ⟨s * w * t⁻¹, mem_doubleCoset.2 ⟨permGL F s * b₁ * (permGL F s)⁻¹,
    (conj_permGL_mem_blockUpper_iff s).2 (hB (Tuple.monotone_sort β) b₁ hb₁),
    permGL F t * b₂ * (permGL F t)⁻¹,
    (conj_permGL_mem_blockUpper_iff t).2 (hB (Tuple.monotone_sort γ) b₂ hb₂), ?_⟩⟩
  have hg : g = permGL F s * ((permGL F s)⁻¹ * g * permGL F t) * (permGL F t)⁻¹ := by group
  rw [hg, heq, map_mul, map_mul, map_inv]
  group
end GroundTheory.Automorphic.Parabolic
