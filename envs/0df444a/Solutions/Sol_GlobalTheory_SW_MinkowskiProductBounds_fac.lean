-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:29.555694+00:00
-- url     : https://prove2.me/submissions/5dff8566-b7cd-4afd-b878-e72e48e385b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) :
    ∃ B : Matrix (Fin m) (Fin m) ℂ, H = B * Bᴴ ∧ (∀ x y : Fin m → ℂ, x ⬝ᵥ H *ᵥ star y =
      inner ℂ (WithLp.toLp 2 (y ᵥ* B)) (WithLp.toLp 2 (x ᵥ* B))) ∧
      ∀ x : Fin m → ℂ, (x ⬝ᵥ H *ᵥ star x).re = ‖WithLp.toLp 2 (x ᵥ* B)‖ ^ 2 := by
  open MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hH.posSemidef.nonneg
  have h1 : H = Bᴴ * Bᴴᴴ := by simpa [star_eq_conjTranspose] using hB
  have h2 : ∀ x y : Fin m → ℂ, x ⬝ᵥ H *ᵥ star y =
      inner ℂ (WithLp.toLp 2 (y ᵥ* Bᴴ)) (WithLp.toLp 2 (x ᵥ* Bᴴ)) := by
    intro x y
    rw [EuclideanSpace.inner_toLp_toLp, h1, ← mulVec_mulVec, dotProduct_mulVec, star_vecMul]
  refine ⟨Bᴴ, h1, h2, fun x => ?_⟩
  rw [h2, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl
end GlobalTheory.SW.MinkowskiProductBounds
