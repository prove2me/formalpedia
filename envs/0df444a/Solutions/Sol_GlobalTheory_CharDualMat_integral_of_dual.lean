-- Prove2me | solution 1 for GlobalTheory.CharDualMat.integral_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:46.995344+00:00
-- url     : https://prove2.me/submissions/d149050e-870e-4281-ba5a-af04b6615111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Theorems.Thm_GlobalTheory_CharDualMat_mem_integer_of_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.CharDualMat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CharDualMat
namespace _root_.GlobalTheory.CharDualMat
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle)
    (hψ : Continuous ψk) (hne : ψk ≠ 1) (x : Matrix Y Y' k)
    (hx : ∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) →
      ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1)
    (r₀ : Y) (q₀ : Y') : x r₀ q₀ ∈ 𝒪[k] := by
  classical
  refine _root_.GlobalTheory.CharDualMat.mem_integer_of_dual ψk hψ hne (x r₀ q₀) (fun s hs => ?_)
  let b : Matrix Y Y' k := fun r q => if r = r₀ ∧ q = q₀ then s else 0
  have key : ∀ y : Matrix Y Y' k, ∑ r, ∑ q, b r q * y r q = s * y r₀ q₀ := by
    intro y
    rw [Finset.sum_eq_single r₀ (fun r _ hr => Finset.sum_eq_zero fun q _ => by simp [b, hr])
      (by simp), Finset.sum_eq_single q₀ (fun q _ hq => by simp [b, hq]) (by simp)]
    simp [b]
  have := hx b (fun u hu => by rw [key]; exact hs _ (hu r₀ q₀))
  rwa [key] at this
end _root_.GlobalTheory.CharDualMat
end GlobalTheory.CharDualMat
