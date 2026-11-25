-- Prove2me | solution 1 for GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:49.095416+00:00
-- url     : https://prove2.me/submissions/1402e095-3a38-4795-a0f4-3bc1ccdae327

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiFactorsLocalFlat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiFactorsLocalFlatStatement
import Theorems.Thm_GlobalTheory_FlatFactor_flCol_factor
import Theorems.Thm_GlobalTheory_LocFlat_flCol_factor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.FlatFactor.flCol_factor | exact GlobalTheory.FlatFactor.flCol_factor | (intros; apply GlobalTheory.FlatFactor.flCol_factor <;> assumption)
end _root_.GlobalTheory.T
