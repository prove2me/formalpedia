-- Prove2me | solution 1 for GlobalTheory.ThetaGen.mem_of_homog_mem_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:09.83598+00:00
-- url     : https://prove2.me/submissions/24232dce-3bd4-4068-b100-983ba9dc4e17

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {X : Type}
namespace GlobalTheory.ThetaGen
theorem _root_.solution (T : ℕ → Submodule ℂ (X → ℂ)) (d : ℕ) (f : X → ℂ)
    (h : homog d f ∈ ⨆ k, (T k).map (homogL k)) : f ∈ T d := by
  have key : ∀ F ∈ ⨆ k, (T k).map (homogL (X := X) k),
      ∃ u : Polynomial (X → ℂ), (∀ k, u.coeff k ∈ T k) ∧
        ∀ t x, F (t, x) = (u.map (Pi.evalRingHom (fun _ : X => ℂ) x)).eval t := by
    intro F hF
    induction hF using Submodule.iSup_induction' with
    | mem k F hF =>
      obtain ⟨v, hv, rfl⟩ := hF
      refine ⟨Polynomial.monomial k v, fun j => ?_, fun t x => ?_⟩
      · rw [Polynomial.coeff_monomial]
        split_ifs with hj
        · exact hj ▸ hv
        · exact zero_mem _
      · simp [homogL, homog, mul_comm]
    | zero => exact ⟨0, fun k => by simp, fun t x => by simp⟩
    | add F G _ _ hF hG =>
      obtain ⟨u, hu, hu'⟩ := hF
      obtain ⟨v, hv, hv'⟩ := hG
      exact ⟨u + v, fun k => by rw [Polynomial.coeff_add]; exact add_mem (hu k) (hv k),
        fun t x => by simp [hu', hv']⟩
  obtain ⟨u, hu, hu'⟩ := key _ h
  have : f = u.coeff d := by
    funext x
    have h1 : u.map (Pi.evalRingHom (fun _ : X => ℂ) x) = Polynomial.monomial d (f x) := by
      apply Polynomial.funext
      intro t
      rw [← hu']
      simp [homog, mul_comm]
    have h2 := congrArg (fun q => Polynomial.coeff q d) h1
    simpa using h2.symm
  exact this ▸ hu d
end GlobalTheory.ThetaGen
