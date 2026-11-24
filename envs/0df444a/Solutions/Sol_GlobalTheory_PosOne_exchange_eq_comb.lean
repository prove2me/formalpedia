-- Prove2me | solution 1 for GlobalTheory.PosOne.exchange_eq_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:50.643255+00:00
-- url     : https://prove2.me/submissions/a891fcff-04f0-4a36-b42b-d293d1d836b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevel
import Theorems.Thm_GlobalTheory_PosOne_UniformComb_exists_comb
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_add
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_zero
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_colE
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_rowE
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_exchange_support
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_add
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_zero
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_colE
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_ballLat_isLattice
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_exists_ballLat_subset
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
open GlobalTheory GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage GlobalTheory.RootEx.UniformLattices GlobalTheory.PosOne.UniformComb
namespace GlobalTheory.PosOne
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (∀ u ∈ U, σ u v = v) → (IsNEquiv ψ (p + 1) σ l → exDown ν p σ l v = comb e fun g => l (σ g v)) ∧ (IsNEquiv ψ p σ l → exUp ν p σ l v = comb e' fun g => l (σ g v)) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hc ψ hψ hψ1 ν _ U hU
  have hrowN : {u : n → k | rowE c p u ∈ U} ∈ 𝓝 (0 : n → k) :=
    ExchangeSupport.continuous_rowE.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simp [ExchangeSupport.rowE_zero, U.one_mem]))
  have hcolN : {β : n → k | colE c (p + 1) β ∈ U} ∈ 𝓝 (0 : n → k) :=
    ExchangeSupport.continuous_colE.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simp [ExchangeSupport.colE_zero, U.one_mem]))
  obtain ⟨s, hs⟩ := exists_ballLat_subset hrowN
  obtain ⟨s', hs'⟩ := exists_ballLat_subset hcolN
  obtain ⟨e, he⟩ := exists_comb hψ hψ1 ν (colE c (p + 1)) ExchangeSupport.continuous_colE
    ExchangeSupport.colE_zero ExchangeSupport.colE_add U hU (ballLat n s) (ballLat_isLattice s)
  obtain ⟨e', he'⟩ := exists_comb hψ hψ1 ν (rowE c p) ExchangeSupport.continuous_rowE
    ExchangeSupport.rowE_zero ExchangeSupport.rowE_add U hU (ballLat n s') (ballLat_isLattice s')
  refine ⟨e, e', fun A _ _ σ hσ l v hv => ⟨fun hl => ?_, fun hl => ?_⟩⟩
  · refine he (fun g => l (σ g v)) (fun x b hb => ?_) (fun x hx => ?_)
    · simp only [map_mul, Module.End.mul_apply, hv _ hb]
    · by_contra hne
      refine hx fun u hu => ?_
      have := ((ExchangeSupport.exchange_support k n c p hp hc ψ hψ hψ1 ν A σ hσ l v).2 hl).2 u x
      rw [hv _ (hs hu)] at this
      have h4 : (ψ (-(u ⬝ᵥ x)) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact this.symm)
      rw [← inv_eq_one, ← AddChar.map_neg_eq_inv]
      exact Circle.ext (by simpa only [Circle.coe_one] using h4)
  · refine he' (fun g => l (σ g v)) (fun x b hb => ?_) (fun x hx => ?_)
    · simp only [map_mul, Module.End.mul_apply, hv _ hb]
    · by_contra hne
      refine hx fun β hβ => ?_
      have := ((ExchangeSupport.exchange_support k n c p hp hc ψ hψ hψ1 ν A σ hσ l v).1 hl).2.1 x β
      rw [hv _ (hs' hβ)] at this
      have h4 : (ψ (x ⬝ᵥ β) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact this.symm)
      rw [dotProduct_comm]
      exact Circle.ext (by simpa only [Circle.coe_one] using h4)
end GlobalTheory.PosOne
