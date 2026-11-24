-- Prove2me | solution 1 for GlobalTheory.LatFin.finite_automorphisms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:41.674512+00:00
-- url     : https://prove2.me/submissions/f11871cc-281c-4dad-8edb-69566adcfbdd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Theorems.Thm_GlobalTheory_LatFin_finite_bounded
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den
import Theorems.Thm_GlobalTheory_LatFin_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LatFin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LatFin
theorem _root_.solution (r : ℕ) (X : Data E r) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded X.Ψ X.cmType (k * l b) (mul_ne_zero hk (hl b)) R
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
  refine ⟨?_, fun τ => hb τ a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this
end GlobalTheory.LatFin
