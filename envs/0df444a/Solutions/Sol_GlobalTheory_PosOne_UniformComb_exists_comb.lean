-- Prove2me | solution 1 for GlobalTheory.PosOne.UniformComb.exists_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:14.14925+00:00
-- url     : https://prove2.me/submissions/465701ad-be27-474b-9e1e-748841521049

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevel
import Theorems.Thm_GlobalTheory_PosOne_UniformComb_comb_sum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LatPair_isClopen_lattice
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_ballLat_isLattice
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_exists_ballLat_subset
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_exists_isReps
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_integral_eq_sum_reps
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_isCompact_lattice
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_isCompact_perp
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_perp_mem_nhds
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.PosOne GlobalTheory.PosOne.UniformComb
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.PosOne.UniformComb
theorem _root_.solution {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    (g : (n → k) → GL (n ⊕ Fin c) k) (hg : Continuous g) (hg1 : g 0 = 1)
    (hadd : ∀ a b, g (a + b) = g a * g b) (U : Subgroup (GL (n ⊕ Fin c) k)) (hU : IsOpen (U : Set (GL (n ⊕ Fin c) k)))
    (W : Submodule 𝒪[k] (n → k)) (hW : W.IsLattice k) :
    ∃ e : GL (n ⊕ Fin c) k →₀ ℂ, ∀ f : GL (n ⊕ Fin c) k → ℂ,
      (∀ x b, g b ∈ U → f (g x * g b) = f (g x)) → (∀ x, x ∉ perp ψ W → f (g x) = 0) →
      ∫ x, f (g x) ∂(Measure.pi fun _ => ν) = comb e f := by
  have := secondCountable k
  have := t2Space k
  have hV : {b : n → k | g b ∈ U} ∈ 𝓝 (0 : n → k) :=
    hg.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [hg1, U.one_mem]))
  obtain ⟨t, ht⟩ := exists_ballLat_subset (inter_mem hV (perp_mem_nhds hψ W hW))
  have hBl := ballLat_isLattice (m := n) t
  obtain ⟨T, hT⟩ := exists_isReps (perp ψ W) (ballLat n t).toAddSubgroup (isCompact_perp hψ hψ1 W hW)
    (LatPair.isClopen_lattice (ballLat n t)).2
  refine ⟨∑ x ∈ T, Finsupp.single (g x)
    ((((Measure.pi fun _ : n => ν).real ((ballLat n t).toAddSubgroup : Set (n → k)) : ℝ) : ℂ)), fun f h1 h0 => ?_⟩
  rw [comb_sum]
  refine integral_eq_sum_reps (Measure.pi fun _ : n => ν) (fun x hx => (ht hx).2)
    (LatPair.isClopen_lattice (ballLat n t)).2 (isCompact_lattice _ hBl) hT (fun x => f (g x)) h0
    fun x b hb => ?_
  simp only [hadd]
  exact h1 x b (ht hb).1
end GlobalTheory.PosOne.UniformComb
