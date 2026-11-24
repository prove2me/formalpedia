-- Prove2me | solution 1 for GlobalTheory.SW.NearPrim.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:51.010833+00:00
-- url     : https://prove2.me/submissions/249208ff-9d99-4cc9-b702-3160c70f013c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim
namespace GlobalTheory.SW.NearPrim
theorem _root_.solution {E : Type} [Field E] [NumberField E] {k : ℕ} {m : Type} [Fintype m]
    (W : Matrix (Fin k) m E) (hW : LinearIndependent E (fun i => W i)) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ s : Fin k → E, (∀ j, IsIntegral ℤ ((s ᵥ* W) j)) →
      ∀ i, IsIntegral ℤ ((d : E) * s i) := by
  classical
  have hinj : LinearMap.ker (W.vecMulLinear) = ⊥ :=
    LinearMap.ker_eq_bot.2 (Matrix.vecMul_injective_iff.2 hW)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image fun p : m × Fin k => g (Pi.single p.1 1) p.2)
  refine ⟨d, hd, fun s hs i => ?_⟩
  have h1 : g (s ᵥ* W) = s := by simpa using LinearMap.congr_fun hg s
  have h2 : s ᵥ* W = ∑ j, (s ᵥ* W) j • (Pi.single j 1 : m → E) := pi_eq_sum_univ' _
  rw [← h1, h2, map_sum, Finset.sum_apply, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  refine (hs j).mul ?_
  have := hint _ (Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩)
  simpa [zsmul_eq_mul] using this
end GlobalTheory.SW.NearPrim
