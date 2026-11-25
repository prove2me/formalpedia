-- Prove2me | solution 1 for GlobalTheory.LatClass.first_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:44.965666+00:00
-- url     : https://prove2.me/submissions/0fd88ee0-3c6b-4242-a07a-01c96d893157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
import Theorems.Thm_GlobalTheory_LatClass_aff_low
import Theorems.Thm_GlobalTheory_LatClass_exists_supp
import Theorems.Thm_GlobalTheory_LatClass_col_mem_nf
import Theorems.Thm_GlobalTheory_LatClass_mem_nf
import Theorems.Thm_GlobalTheory_LatClass_zero_mem_pow
import Theorems.Thm_GlobalTheory_LatClass_zpow_mem_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k}
omit [BorelSpace k]
namespace GlobalTheory.LatClass
theorem _root_.solution (hϖ : valuation k (ϖ : k) = uniformizer k)
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ((ϖ ^ e' 0 : kˣ) : k) • (Sum.elim (x₀ *ᵥ z') (Pi.single 0 1) : n ⊕ Fin (c + 1) → k) ∈ latOf h ∧
      ∀ w ∈ latOf g', (Sum.elim (x₀ *ᵥ w) 0 : n ⊕ Fin (c + 1) → k) ∈ latOf h := by
  obtain ⟨y, hy⟩ := exists_supp h0
  constructor
  · have := hs _ hy _ (col_mem_nf 0 ((zpow_mem_pow hϖ).2 le_rfl))
    rw [aff_low] at this
    convert this using 1
    ext (r | l)
    · simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    · simp [Pi.single_apply]
  · intro w hw
    have := hs _ hy (Sum.elim w (Pi.single 0 0)) (mem_nf.2 ⟨by simpa using hw, fun i => by simpa using zero_mem_pow⟩)
    rw [aff_low] at this
    simpa using this
end GlobalTheory.LatClass
