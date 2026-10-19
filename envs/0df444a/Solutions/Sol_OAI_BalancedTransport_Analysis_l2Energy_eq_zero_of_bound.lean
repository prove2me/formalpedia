-- Prove2me | solution 1 for OAI.BalancedTransport.Analysis.l2Energy_eq_zero_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:22:45.284982+00:00
-- url     : https://prove2.me/submissions/331a8e6d-f3d9-4c54-b8a5-200dd5855f51

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve

open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal


theorem solution
    {V W : ℝ → Lp Space 2 (volume : Measure Space)}
    (hV : ContinuousOn V (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt V (W t) (Ici 0) t)
    (hzero : V 0 = 0) {T K : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Ico (0 : ℝ) T, l2EnergyRate (V t) (W t) ≤ K * l2Energy (V t)) :
    l2Energy (V T) = 0 := by
  have hE : ∀ t, 0 ≤ t → HasDerivWithinAt (fun s => l2Energy (V s))
      (l2EnergyRate (V t) (W t)) (Ici 0) t := by
    intro t ht
    have hc : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        HasDerivWithinAt (fun s => ‖coordinateL2 i (V s)‖ ^ 2)
          (2 * inner ℝ (coordinateL2 i (V t)) (coordinateL2 i (W t))) (Ici 0) t := by
      intro i _
      exact ((coordinateL2 i).hasFDerivAt.comp_hasDerivWithinAt t (hderiv t ht)).norm_sq
    have := HasDerivWithinAt.fun_sum hc
    unfold l2Energy l2EnergyRate
    rw [Finset.mul_sum]
    exact this
  have hEnn : ∀ t, 0 ≤ l2Energy (V t) := fun t => Finset.sum_nonneg (fun i _ => by positivity)
  have hexp : ∀ t : ℝ, HasDerivAt (fun x => Real.exp (-K * x)) (Real.exp (-K * t) * (-K * 1)) t :=
    fun t => ((hasDerivAt_id' t).const_mul (-K)).exp
  have hg : ∀ t, 0 ≤ t → HasDerivWithinAt (fun x => Real.exp (-K * x) * l2Energy (V x))
      (Real.exp (-K * t) * (-K * 1) * l2Energy (V t) + Real.exp (-K * t) * l2EnergyRate (V t) (W t))
      (Ici 0) t := fun t ht => (hexp t).hasDerivWithinAt.mul (hE t ht)
  have hcont : ContinuousOn (fun x => Real.exp (-K * x) * l2Energy (V x)) (Icc 0 T) := by
    intro t ht
    exact ((hg t ht.1).continuousWithinAt).mono Icc_subset_Ici_self
  have hdiff : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt (fun x => Real.exp (-K * x) * l2Energy (V x))
      (Real.exp (-K * t) * (-K * 1) * l2Energy (V t) + Real.exp (-K * t) * l2EnergyRate (V t) (W t)) t :=
    fun t ht => (hg t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  have hanti : AntitoneOn (fun x => Real.exp (-K * x) * l2Energy (V x)) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont
    · rw [interior_Icc]
      intro t ht
      exact (hdiff t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hdiff t ht).deriv]
      have hb := hbound t ⟨ht.1.le, ht.2⟩
      have he := Real.exp_pos (-K * t)
      nlinarith
  have h0 : l2Energy (V 0) = 0 := by
    rw [hzero]; simp [l2Energy]
  have hle := hanti ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  simp only [mul_zero, Real.exp_zero, one_mul, h0] at hle
  have he := Real.exp_pos (-K * T)
  have hnn := hEnn T
  have : l2Energy (V T) ≤ 0 := by
    by_contra hc
    push_neg at hc
    have := mul_pos he hc
    linarith
  linarith

