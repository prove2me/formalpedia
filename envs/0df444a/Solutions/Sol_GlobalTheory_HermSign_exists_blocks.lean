-- Prove2me | solution 1 for GlobalTheory.HermSign.exists_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:20.745051+00:00
-- url     : https://prove2.me/submissions/1b3956eb-ebfc-450e-a8dc-543e601eeabe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution {ι : Type} [Fintype ι] {r : ℕ}
    (f : (ι → Fin r → ℂ) →ₗ[ℝ] (ι → Fin r → ℂ)) (hf : ∀ (c : ι → ℂ) u, f (c • u) = c • f u) :
    ∃ N : ι → Matrix (Fin r) (Fin r) ℂ, ∀ u τ, f u τ = N τ *ᵥ u τ := by
  classical
  let g : (ι → Fin r → ℂ) →ₗ[ℂ] (ι → Fin r → ℂ) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c u => hf (fun _ => c) u }
  refine ⟨fun τ => LinearMap.toMatrix' (LinearMap.proj τ ∘ₗ g ∘ₗ
    LinearMap.single ℂ (fun _ : ι => Fin r → ℂ) τ), fun u τ => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have h1 : (Pi.single τ 1 : ι → ℂ) • u = Pi.single τ (u τ) := by
    funext σ
    by_cases h : σ = τ
    · subst h; simp
    · simp [h]
  have h2 := congrFun (hf (Pi.single τ 1) u) τ
  rw [h1] at h2
  simpa [g] using h2.symm
end GlobalTheory.HermSign
