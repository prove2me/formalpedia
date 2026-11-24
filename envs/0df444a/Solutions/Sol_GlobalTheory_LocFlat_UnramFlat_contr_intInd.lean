-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.contr_intInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:50:08.060926+00:00
-- url     : https://prove2.me/submissions/1fdb8873-ddc2-460c-bb3f-badb0197627f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_integral_psi_box
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_ind_eq_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {n' n'' : Type} [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
namespace GlobalTheory.LocFlat.UnramFlat
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν)
    (q : Matrix n n' k × Matrix n'' n k) :
    contr ψ ν (Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1)
      (Set.indicator {x : Matrix (n'' ⊕ Unit) n k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) q =
    Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.1 *
      Set.indicator {x : Matrix n'' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.2 := by
  classical
  have h1 : ∀ y : n → k, IntM (fromCols q.1 (Matrix.of fun r (_ : Unit) => y r)) ↔ IntM q.1 ∧ ∀ r, y r ∈ 𝒪[k] := by
    intro y
    constructor
    · intro h
      exact ⟨fun r s => by simpa using h r (Sum.inl s), fun r => by simpa using h r (Sum.inr ())⟩
    · rintro ⟨h, h'⟩ r (s | ⟨⟩)
      · simpa using h r s
      · simpa using h' r
  have h2 : ∀ u : n → k, IntM (fromRows q.2 (Matrix.of fun (_ : Unit) => u)) ↔ IntM q.2 ∧ ∀ r, u r ∈ 𝒪[k] := by
    intro u
    constructor
    · intro h
      exact ⟨fun r s => by simpa using h (Sum.inl r) s, fun r => by simpa using h (Sum.inr ()) r⟩
    · rintro ⟨h, h'⟩ (r | ⟨⟩) s
      · simpa using h r s
      · simpa using h' s
  have hhat : ∀ u, hat ψ ν (-1) (fun y => Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ))
      (fromCols q.1 (Matrix.of fun r _ => y r))) u =
      (if IntM q.1 then 1 else 0) * (if ∀ r, u r ∈ 𝒪[k] then 1 else 0) := by
    intro u
    rw [← integral_psi_box hψ hν u, ← integral_const_mul]
    unfold hat
    congr 1
    funext y
    beta_reduce
    rw [ind_eq_ite, if_congr (h1 y) rfl rfl]
    by_cases a : IntM q.1 <;> by_cases b : ∀ r, y r ∈ 𝒪[k] <;> simp [a, b]
  unfold contr
  refine (integral_congr_ae (μ := Measure.pi fun _ : n => ν)
    (g := fun u => ((if IntM q.1 then (1 : ℂ) else 0) * (if IntM q.2 then 1 else 0)) *
      ((if ∀ r, u r ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * ((0 : n → k) ⬝ᵥ u)) : ℂ)))
    (Filter.Eventually.of_forall fun u => ?_)).trans ?_
  · dsimp only
    rw [hhat, ind_eq_ite, if_congr (h2 u) rfl rfl]
    simp only [zero_dotProduct, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
    by_cases a : IntM q.1 <;> by_cases b : IntM q.2 <;> by_cases c : ∀ r, u r ∈ 𝒪[k] <;> simp [a, b, c]
  · rw [integral_const_mul, integral_psi_box hψ hν 0, ind_eq_ite, ind_eq_ite]
    simp
end GlobalTheory.LocFlat.UnramFlat
