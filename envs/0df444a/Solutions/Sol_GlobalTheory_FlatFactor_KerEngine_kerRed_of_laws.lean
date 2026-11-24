-- Prove2me | solution 1 for GlobalTheory.FlatFactor.KerEngine.kerRed_of_laws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:24:59.648965+00:00
-- url     : https://prove2.me/submissions/8a394494-84f0-4b70-877e-1b630c1054f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillsPartialEvalIntegralKernelOfLaws
import Theorems.Thm_GlobalTheory_FlatFactor_KerEngine_pullSB_apply
import Theorems.Thm_GlobalTheory_FlatFactor_KerEngine_trip_apply
import Theorems.Thm_GlobalTheory_FlatFactor_KerEngine_toTrip_add
import Theorems.Thm_GlobalTheory_FlatFactor_KerEngine_ofTrip_zero
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CoinvSB_kernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor
namespace GlobalTheory.FlatFactor.KerEngine
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → (∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ ev, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ it, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev it β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it hd h1 h2 Θ hΘ
  let e := trip (k := k) ev it hd β
  let l' := l ∘ₗ pullSB e
  have hback : pullSB e (pullSB e.symm Θ) = Θ := by
    ext t
    simp [pullSB_apply]
  have key := GlobalTheory.CoinvSB.kernel k ψ ν hψc hψ1 hν (Rest ev it) {x // x ∈ ev} {x // x ∈ it} M l' ?_ ?_
    (pullSB e.symm Θ) ?_
  · simpa [l', hback] using key
  · intro b Φ Φ' hΦ
    refine h1 (fun e => if h : e ∈ ev then b ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    congr 3
    simp only [e, trip_apply, toTrip, dotProduct]
    rw [← Finset.sum_coe_sort ev]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  · intro a Φ Φ' hΦ
    refine h2 (fun e => if h : e ∈ it then a ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    simp only [e, trip_apply]
    rw [toTrip_add ev it hd β t a]
  · intro x₀
    have hr := hΘ (ofTrip ev it β (x₀, 0, 0))
    simp only [red] at hr
    rw [← hr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [pullSB_apply]
    rw [← ofTrip_zero]
    rfl
end GlobalTheory.FlatFactor.KerEngine
