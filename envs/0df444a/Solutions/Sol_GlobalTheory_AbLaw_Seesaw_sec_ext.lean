-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.sec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:59.818372+00:00
-- url     : https://prove2.me/submissions/14348520-2492-4899-8848-86fe941f491a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector

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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution {N : LB Y} (s s' : LB.Sec N) {I : Type} (V : I → Y.Opens) (c : I → N.ι)
    (le : ∀ i, V i ≤ N.U (c i)) (hV : ∀ y, ∃ i, y ∈ V i)
    (h : ∀ i, rs Y (le i) (s.f (c i)) = rs Y (le i) (s'.f (c i))) : s = s' := by
  have : s.f = s'.f := funext fun j => by
    refine Y.sheaf.eq_of_locally_eq' (fun i => N.U j ⊓ V i) (N.U j) (fun i => homOfLE inf_le_left)
      (fun y hy => ?_) _ _ fun i => ?_
    · obtain ⟨i, hi⟩ := hV y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩
    · have l : N.U j ⊓ V i ≤ N.U j ⊓ N.U (c i) := inf_le_inf_left _ (le i)
      have e₁ := congrArg (rs Y l) (s.compat j (c i))
      have e₂ := congrArg (rs Y l) (s'.compat j (c i))
      have e₃ := congrArg (rs Y (inf_le_right : N.U j ⊓ V i ≤ V i)) (h i)
      simp only [map_mul, rs_rs] at e₁ e₂ e₃
      change rs Y _ (s.f j) = rs Y _ (s'.f j)
      rw [e₁, e₂, e₃]
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := s'
  obtain rfl : f = f' := this
  rfl
end GlobalTheory.AbLaw.Seesaw
