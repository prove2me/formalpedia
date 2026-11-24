-- Prove2me | solution 1 for GlobalTheory.sec_eq_zero_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:46.914788+00:00
-- url     : https://prove2.me/submissions/6aa2cf3e-dd21-45fe-b1bc-cdd8fbc81f58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroOfDvdPowUniformiser

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} [IsIntegral X] (N : LB X) (s : LB.Sec N)
    (j : N.ι) (x : X) (hx : x ∈ N.U j) (hj : s.f j = 0) (i : N.ι) : s.f i = 0 := by
  by_cases hi : (N.U i : Set X).Nonempty
  · have hij : ((N.U i ⊓ N.U j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen hi ⟨x, hx⟩
    have : Nonempty (N.U i ⊓ N.U j : X.Opens) := hij.to_subtype
    have h := s.compat i j
    rw [hj, map_zero, mul_zero] at h
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : N.U i ⊓ N.U j ≤ N.U i))
    rw [map_zero]
    exact h
  · have : N.U i = ⊥ := by
      ext1
      simpa using Set.not_nonempty_iff_eq_empty.1 hi
    have : Subsingleton Γ(X, N.U i) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
end GlobalTheory
