-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.half_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:42:45.076293+00:00
-- url     : https://prove2.me/submissions/e31b71c2-a3cd-4ede-aead-2db3d4fa54ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
import Theorems.Thm_GlobalTheory_SW_HermLat_sum_univ
import Theorems.Thm_GlobalTheory_SW_Base_map_cc


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HermLat
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {x : E} (hx : cc x = x) :
    (((1 / 2 : ℚ) * Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : Ψ, τ.1 x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ x = ∑ σ : E →+* ℂ, σ x :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun _ => rfl)).symm
  rw [h2, sum_univ hΨ] at h
  have h3 : ∀ τ : Ψ, ComplexEmbedding.conjugate τ.1 x = τ.1 x := fun τ => by
    rw [ComplexEmbedding.conjugate_coe_eq, ← Base.map_cc, hx]
  simp only [h3, ← two_mul, ← Finset.mul_sum] at h
  have h4 : algebraMap ℚ ℂ (Algebra.trace ℚ E x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := rfl
  rw [h4] at h
  push_cast
  rw [h]; ring
end GlobalTheory.SW.HermLat
