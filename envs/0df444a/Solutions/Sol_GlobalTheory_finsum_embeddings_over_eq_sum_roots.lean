-- Prove2me | solution 1 for GlobalTheory.finsum_embeddings_over_eq_sum_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:10.840912+00:00
-- url     : https://prove2.me/submissions/a098da3c-c4c9-4fba-b017-0f0e93f5eac9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MeasurableSumEmbeddingsOverGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution {F L : Type} [Field F] [Field L] [Algebra F L]
    [Algebra.IsSeparable F L] (pb : PowerBasis F L) (τ : F →+* ℂ) {δ : ℕ} (r : Fin δ → ℂ)
    (hr : ∏ i, (X - C (r i)) = (minpoly F pb.gen).map τ) (g : (L →+* ℂ) → ℝ) (g' : ℂ → ℝ)
    (hg : ∀ P : L →+* ℂ, P.comp (algebraMap F L) = τ → g P = g' (P pb.gen)) :
    ∑ᶠ P ∈ {P : L →+* ℂ | P.comp (algebraMap F L) = τ}, g P = ∑ k, g' (r k) := by
  classical
  letI : Algebra F ℂ := τ.toAlgebra
  have hτ : algebraMap F ℂ = τ := rfl
  have hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0 := by
    intro k
    rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hsep : (∏ i, (X - C (r i))).Separable := by
    rw [hr]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen)
  have hinj : Function.Injective r := separable_prod_X_sub_C_iff.mp hsep
  let P : Fin δ → (L →+* ℂ) := fun k => (pb.lift (r k) (hroot k)).toRingHom
  have hPgen : ∀ k, P k pb.gen = r k := fun k => pb.lift_gen (r k) (hroot k)
  have hPinj : Function.Injective P := by
    intro k l h
    apply hinj
    rw [← hPgen, ← hPgen, h]
  have hPτ : ∀ k, (P k).comp (algebraMap F L) = τ := by
    intro k
    ext x
    exact (pb.lift (r k) (hroot k)).commutes x
  have hset : {P : L →+* ℂ | P.comp (algebraMap F L) = τ} = Set.range P := by
    ext Q
    constructor
    · intro hQ
      have hQ' : Q.comp (algebraMap F L) = τ := hQ
      let Q' : L →ₐ[F] ℂ := { Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }
      have h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0 := by
        rw [aeval_algHom_apply, minpoly.aeval, map_zero]
      rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod, Finset.prod_eq_zero_iff] at h0
      obtain ⟨k, -, hk⟩ := h0
      refine ⟨k, ?_⟩
      have hk' : Q' pb.gen = r k := by simpa [sub_eq_zero] using hk
      have : pb.lift (r k) (hroot k) = Q' := by
        apply pb.algHom_ext
        rw [pb.lift_gen, hk']
      show (pb.lift (r k) (hroot k)).toRingHom = Q
      rw [this]
    · rintro ⟨k, rfl⟩
      exact hPτ k
  rw [hset, finsum_mem_range hPinj, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hg _ (hPτ k), hPgen]
end GlobalTheory
