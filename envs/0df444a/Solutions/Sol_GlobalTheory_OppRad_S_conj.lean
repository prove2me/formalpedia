-- Prove2me | solution 1 for GlobalTheory.OppRad.S_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:28.388915+00:00
-- url     : https://prove2.me/submissions/050b2268-909d-4954-a9a4-a18e52c9d4ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_un_val
import Theorems.Thm_GlobalTheory_OppRad_S_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.OppRad.un_val

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
variable {π}
namespace GlobalTheory.OppRad
theorem _root_.solution {H K : Subgroup G} {w : G} (h1 : ∀ u ∈ H, w * u * w⁻¹ ∈ K) (h2 : ∀ u ∈ K, w⁻¹ * u * w⁻¹⁻¹ ∈ H)
    (v : V) : π w (S π H v) = S π K (π w v) := by
  haveI := Fintype.ofFinite H
  haveI := Fintype.ofFinite K
  rw [S_apply, S_apply, map_sum]
  refine Fintype.sum_equiv ⟨fun u => ⟨_, h1 u u.2⟩, fun u => ⟨_, h2 u u.2⟩, fun u => Subtype.ext (by simp [mul_assoc]),
    fun u => Subtype.ext (by simp [mul_assoc])⟩ _ _ fun u => ?_
  simp [← Module.End.mul_apply, ← map_mul]
end GlobalTheory.OppRad
