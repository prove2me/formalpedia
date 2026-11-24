-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.sec_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:08:09.207042+00:00
-- url     : https://prove2.me/submissions/47d88d50-ac82-40d0-a151-cd7a30232ed3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow

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
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution {X : Scheme.{0}} [IsIntegral X] {M : LB X} (s : LB.Sec M) {i₀ : M.ι}
    (h₀ : s.f i₀ ≠ 0) (i : M.ι) [hi : Nonempty (M.U i)] : s.f i ≠ 0 := by
  intro hz
  have hi₀ : Nonempty (M.U i₀) := by
    by_contra hn
    have e : M.U i₀ = ⊥ := by
      ext x
      exact ⟨fun hx => (hn ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    haveI : Subsingleton Γ(X, M.U i₀) := by rw [e]; infer_instance
    exact h₀ (Subsingleton.elim _ _)
  haveI : Nonempty (M.U i₀ ⊓ M.U i : X.Opens) := by
    obtain ⟨a⟩ := hi₀
    obtain ⟨b⟩ := hi
    obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (M.U i₀).isOpen (M.U i).isOpen ⟨a.1, a.2⟩ ⟨b.1, b.2⟩
    exact ⟨⟨x, hx⟩⟩
  have hc := s.compat i₀ i
  rw [hz, map_zero, mul_zero] at hc
  apply h₀
  apply map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U i₀ ⊓ M.U i ≤ M.U i₀))
  simpa using hc
end GlobalTheory.FinrankGrowthBounds
