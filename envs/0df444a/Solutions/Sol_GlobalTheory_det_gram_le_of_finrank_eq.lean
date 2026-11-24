-- Prove2me | solution 1 for GlobalTheory.det_gram_le_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:49.162679+00:00
-- url     : https://prove2.me/submissions/f452005d-7787-4171-ba9e-1a738b663c0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Theorems.Thm_GlobalTheory_det_gram_eq_normSq_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] (h : finrank 𝕜 V = Fintype.card ι) (v : ι → V) :
    (gram 𝕜 v).det ≤ ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  let e := (Fintype.equivFin ι).symm
  have h' : finrank 𝕜 V = Fintype.card (Fin (Fintype.card ι)) := by simpa using h
  have h1 : (gram 𝕜 v).det = (gram 𝕜 (v ∘ e)).det := by
    rw [← det_submatrix_equiv_self e]; rfl
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h' (v ∘ e)
  have hb : b.toBasis.det (v ∘ e) = ∏ i, ⟪b i, (v ∘ e) i⟫_𝕜 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det h' _
  rw [h1, det_gram_eq_normSq_det b, hb, RCLike.ofReal_le_ofReal, norm_prod, ← Finset.prod_pow,
    ← e.prod_comp (fun i ↦ ‖v i‖ ^ 2)]
  refine Finset.prod_le_prod (fun i _ ↦ by positivity) fun i _ ↦ ?_
  gcongr
  simpa using norm_inner_le_norm (𝕜 := 𝕜) (b i) (v (e i))
end GlobalTheory
