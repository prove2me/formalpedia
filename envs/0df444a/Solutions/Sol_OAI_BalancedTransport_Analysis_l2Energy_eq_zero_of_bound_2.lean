-- Prove2me | solution 2 for OAI.BalancedTransport.Analysis.l2Energy_eq_zero_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:48:48.903981+00:00
-- url     : https://prove2.me/submissions/c5074129-50fa-4180-958a-ad76cbcbd76c

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EnergyCurve.lean:L64-L84
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Analysis.l2Energy_eq_zero_of_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EnergyCurve ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal

lemma coordinateL2_hasDerivWithinAt
    {V W : ℝ → Lp Space 2 (volume : Measure Space)} {t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt V (W t) s t) (i : Fin 3) :
    HasDerivWithinAt (fun t => coordinateL2 i (V t)) (coordinateL2 i (W t)) s t :=
  (coordinateL2 i).hasFDerivAt.comp_hasDerivWithinAt t h

lemma l2Energy_nonneg (V : Lp Space 2 (volume : Measure Space)) : 0 ≤ l2Energy V :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma l2Energy_continuous : Continuous l2Energy := by
  unfold l2Energy
  fun_prop

lemma l2Energy_hasDerivWithinAt
    {V W : ℝ → Lp Space 2 (volume : Measure Space)} {t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt V (W t) s t) :
    HasDerivWithinAt (fun t => l2Energy (V t)) (l2EnergyRate (V t) (W t)) s t := by
  simpa only [l2Energy, l2EnergyRate, Finset.mul_sum] using
    HasDerivWithinAt.fun_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) =>
      (coordinateL2_hasDerivWithinAt h i).norm_sq)

lemma l2Energy_eq_zero_of_bound
    {V W : ℝ → Lp Space 2 (volume : Measure Space)}
    (hV : ContinuousOn V (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt V (W t) (Ici 0) t)
    (hzero : V 0 = 0) {T K : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Ico (0 : ℝ) T, l2EnergyRate (V t) (W t) ≤ K * l2Energy (V t)) :
    l2Energy (V T) = 0 := by
  have hec : ContinuousOn (fun t => l2Energy (V t)) (Icc 0 T) :=
    l2Energy_continuous.comp_continuousOn (hV.mono (fun _ ht => ht.1))
  have he0 : l2Energy (V 0) ≤ 0 := by simp [hzero, l2Energy]
  have he' : ∀ x ∈ Ico (0 : ℝ) T, ∀ r : ℝ, l2EnergyRate (V x) (W x) < r →
      ∃ᶠ z in 𝓝[>] x, (z-x)⁻¹ * (l2Energy (V z) - l2Energy (V x)) < r := by
    intro x hx r hr
    have hh : HasDerivWithinAt (fun t => l2Energy (V t))
        (l2EnergyRate (V x) (W x)) (Ici x) x :=
      (l2Energy_hasDerivWithinAt (hderiv x hx.1)).mono (Ici_subset_Ici.mpr hx.1)
    simpa only [slope_def_field, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh.liminf_right_slope_le hr
  have H := le_gronwallBound_of_liminf_deriv_right_le (K := K) (ε := 0) hec he' he0
    (fun t ht => by simpa only [add_zero] using hbound t ht) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at H
  exact le_antisymm H (l2Energy_nonneg _)

end BalancedTransport.Analysis
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.BalancedTransport.Analysis.l2Energy_eq_zero_of_bound := @_root_.OAI.BalancedTransport.Analysis.l2Energy_eq_zero_of_bound
