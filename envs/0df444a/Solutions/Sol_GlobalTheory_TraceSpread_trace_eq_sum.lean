-- Prove2me | solution 1 for GlobalTheory.TraceSpread.trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:10.827282+00:00
-- url     : https://prove2.me/submissions/83fc9292-d99b-4a35-a5e1-bd6ac6812639

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Theorems.Thm_GlobalTheory_TraceSpread_isSplitting_embeddings
import Theorems.Thm_GlobalTheory_EigenSplit_apply_mem_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_isInternal_eigenSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TraceSpread
variable {E : Type} [Field E] [NumberField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TraceSpread
namespace _root_.GlobalTheory.TraceSpread
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {V : Type} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (ρ : 𝓞 E →+* Module.End K V) (a : 𝓞 E) :
    LinearMap.trace K V (ρ a) = ∑ φ : E →+* K,
      (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : K) *
        φ a := by
  classical
  have hsplit := _root_.GlobalTheory.TraceSpread.isSplitting_embeddings (E := E) K
  have hint := _root_.GlobalTheory.EigenSplit.isInternal_eigenSub hsplit ρ
  have hmaps : ∀ φ : E →+* K, Set.MapsTo (ρ a)
      (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
      (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) :=
    fun φ x hx => _root_.GlobalTheory.EigenSplit.apply_mem_eigenSub hx a
  rw [LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  refine Finset.sum_congr rfl fun φ _ => ?_
  have hres : (ρ a).restrict (hmaps φ) = (φ a) • LinearMap.id := by
    ext x
    show ρ a (x : V) = φ (a : E) • (x : V)
    exact (_root_.GlobalTheory.EigenSplit.mem_eigenSub.mp x.2) a
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
end _root_.GlobalTheory.TraceSpread
end GlobalTheory.TraceSpread
