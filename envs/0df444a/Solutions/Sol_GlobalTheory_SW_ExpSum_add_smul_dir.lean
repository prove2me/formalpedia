-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.add_smul_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:25:30.154124+00:00
-- url     : https://prove2.me/submissions/4d49963a-e7ef-4cf3-8999-e66281d459a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open Classical
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution {m : ℕ} (x : CM Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ) :
    (fun σ => x σ + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) =
      (HAdd.hAdd (α := CF Ψ m N) (β := CF Ψ m N) x (s • dir Ψ τ k a) : CF Ψ m N) := by
  funext σ i j
  change x σ i j + (if σ = τ then Matrix.single k a s else 0 : Matrix (Fin m) (Fin N) ℂ) i j =
    x σ i j + s * dir Ψ τ k a σ i j
  by_cases h : σ = τ <;> by_cases h1 : i = k <;> by_cases h2 : j = a <;>
    simp [dir, h, h1, h2, Matrix.single] <;> tauto
end GlobalTheory.SW.ExpSum
