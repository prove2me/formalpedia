-- Prove2me | solution 1 for GlobalTheory.SignedLengthTower.relLength_span_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:14:21.264743+00:00
-- url     : https://prove2.me/submissions/9333748b-0704-4a65-8a0c-6412758ce428

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanMatrix
import Theorems.Thm_GlobalTheory_SignedLengthTower_length_coker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthTower
namespace GlobalTheory.SignedLengthTower
theorem _root_.solution {R V ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι] {a c : ι → V}
    (ha : LinearIndependent R a) (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, M i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range c)) =
      Ring.ord R M.det := by
  let φ := Fintype.linearCombination R a
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by simpa [φ, Fintype.linearCombination_apply] using hx) i
  have hf : Function.Injective (Matrix.toLin' M) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using hx)
  have hA : Submodule.span R (Set.range a) = Submodule.map φ ⊤ := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hC : Submodule.span R (Set.range c) =
      Submodule.map φ (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [φ, Fintype.linearCombination_apply, hc]
  rw [hA, hC, relLength_map_of_injective φ hφ, relLength_top_left, length_coker _ hf,
    LinearMap.det_toLin']
end GlobalTheory.SignedLengthTower
