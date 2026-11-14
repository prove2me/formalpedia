-- Prove2me | solution 1 for OAI.KadisonKastler.relative_ambient_scalar_of_common_equivs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:53:19.985211+00:00
-- url     : https://prove2.me/submissions/dbd7d73a-a196-4c4e-8276-9496698d5b47

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Definitions.Def_Q260K002

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeIrreducibilityTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting a scalar relative commutant through common representations -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M R : VonNeumannAlgebra H} {P S : VonNeumannAlgebra K}

theorem relative_scalar_of_common_equivs (hRM : R ≤ M) (hSP : S ≤ P)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra R ≃⋆ₐ[ℂ] Algebra S)
    (hcompat : ∀ r, e (coordinateInclusion hRM r) = coordinateInclusion hSP (f r))
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (x : Algebra P)
    (hx : ∀ s : Algebra S, coordinateInclusion hSP s * x = x * coordinateInclusion hSP s) :
    ∃ c : ℂ, x = c • (1 : Algebra P) := by
  have hc (r : Algebra R) : coordinateInclusion hRM r * e.symm x =
      e.symm x * coordinateInclusion hRM r := by
    apply e.injective
    rw [map_mul, map_mul]
    change e (coordinateInclusion hRM r) * e (e.symm x) =
      e (e.symm x) * e (coordinateInclusion hRM r)
    rw [hcompat, e.apply_symm_apply]
    exact hx (f r)
  obtain ⟨c, hc⟩ := hirr (e.symm x) hc
  refine ⟨c, ?_⟩
  calc
    x = e (e.symm x) := (e.apply_symm_apply x).symm
    _ = e (c • (1 : Algebra M)) := congrArg e hc
    _ = c • (1 : Algebra P) := by
      change e.toAlgEquiv.toLinearMap (c • 1) = _
      rw [e.toAlgEquiv.toLinearMap.map_smul]
      congr 1
      exact e.map_one

theorem relative_ambient_scalar_of_common_equivs_oai (hRM : R ≤ M) (hSP : S ≤ P)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra R ≃⋆ₐ[ℂ] Algebra S)
    (hcompat : ∀ r, e (coordinateInclusion hRM r) = coordinateInclusion hSP (f r))
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (T : K →L[ℂ] K) (hT : T ∈ P) (hc : ∀ s ∈ S, s * T = T * s) :
    ∃ c : ℂ, T = c • (1 : K →L[ℂ] K) := by
  obtain ⟨c, he⟩ := relative_scalar_of_common_equivs hRM hSP e f hcompat hirr
    ⟨T, hT⟩ (fun s => Subtype.ext (hc s.val s.property))
  exact ⟨c, congrArg (fun a : Algebra P => a.val) he⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.relative_ambient_scalar_of_common_equivs_oai.{u_1, u_2} := @OAI.KadisonKastler.relative_ambient_scalar_of_common_equivs_oai.{u_1, u_2}
