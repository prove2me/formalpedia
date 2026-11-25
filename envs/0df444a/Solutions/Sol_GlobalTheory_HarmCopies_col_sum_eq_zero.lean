-- Prove2me | solution 1 for GlobalTheory.HarmCopies.col_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:49.901873+00:00
-- url     : https://prove2.me/submissions/bd1e7a8e-fc97-4465-9842-f70be1a0528a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.HarmCopies
open GlobalTheory.PowGerm
namespace GlobalTheory.HarmCopies
theorem _root_.solution {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : MvPolynomial.rename (letterEquiv T r n) Q ∈ harmK r n k cc isX (fun _ => 1))
    (τ : T) (hτ : isX τ) (i : Fin (r τ)) (i' : Fin (r (cc τ))) :
    ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
      (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0 := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hQ
  have h := hQ τ hτ i i'
  apply MvPolynomial.rename_injective _ (letterEquiv T r n).injective
  rw [map_zero, ← h, map_sum, lap, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single b]
  · rw [Matrix.one_apply_eq, one_smul, ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective,
      ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective]
    rfl
  · intro b' _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul, LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_univ _) h
end GlobalTheory.HarmCopies
