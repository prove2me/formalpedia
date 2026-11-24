-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.ballLat_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:12.322785+00:00
-- url     : https://prove2.me/submissions/d1057777-9d90-42d4-a8b2-e8a5e2b0ed91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {m : Type} [Fintype m]
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution (s : kˣ) : (ballLat m s).IsLattice k := by
  classical
  have hs : ∀ i : m, (Pi.single i (s : k) : m → k) ∈ ballLat m s := fun i j => by
    rw [Pi.single_apply]; split_ifs <;> simp [cball]
  constructor
  · refine ⟨Finset.univ.image fun i : m => (Pi.single i (s : k) : m → k), le_antisymm ?_ fun x hx => ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hs i
    · rw [← Finset.univ_sum_single x]
      refine sum_mem fun i _ => ?_
      have h1 : x i * (s : k)⁻¹ ∈ 𝒪[k] := by
        rw [Valuation.mem_integer_iff, map_mul, map_inv₀, mul_inv_le_iff₀ (by simp [zero_lt_iff]), one_mul]
        exact hx i
      have e : (Pi.single i (x i) : m → k) = (⟨_, h1⟩ : 𝒪[k]) • (Pi.single i (s : k) : m → k) := by
        funext j
        show _ = x i * (s : k)⁻¹ * (Pi.single i (s : k) : m → k) j
        simp only [Pi.single_apply]; split_ifs <;> simp
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ => ?_
    have e : (Pi.single i (x i) : m → k) = (x i * (s : k)⁻¹) • (Pi.single i (s : k) : m → k) := by
      funext j
      simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
end GlobalTheory.RootEx.UniformLattices
