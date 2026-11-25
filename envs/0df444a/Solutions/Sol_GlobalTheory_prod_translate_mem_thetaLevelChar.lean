-- Prove2me | solution 1 for GlobalTheory.prod_translate_mem_thetaLevelChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:43:09.497985+00:00
-- url     : https://prove2.me/submissions/6e6cd1a2-2fc9-4f90-ac27-074fa46b4e83

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution {κ : Type*} (s : Finset κ) {d : κ → ℕ}
    {F : κ → (ι → ℂ) → ℂ} (hF : ∀ i ∈ s, F i ∈ thetaLevelChar a b (d i) τ) (u : κ → ι → ℂ)
    (hu : ∑ i ∈ s, (d i : ℂ) • u i = 0) :
    (fun z => ∏ i ∈ s, F i (z + u i)) ∈ thetaLevelChar a b (∑ i ∈ s, d i) τ := by
  classical
  refine ⟨fun z => (HasFDerivAt.finsetProd (g := fun i z => F i (z + u i)) fun i hi =>
    (((hF i hi).1.comp (differentiable_id.add_const (u i))) z).hasFDerivAt).differentiableAt,
    fun n n' z => ?_⟩
  have h1 : ∀ i ∈ s, F i (z + τ *ᵥ ofIntVec n + ofIntVec n' + u i) =
      eC ((d i : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n) +
        -(d i : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z) -
        ofIntVec n ⬝ᵥ ((d i : ℂ) • u i)) * F i (z + u i) := by
    intro i hi
    rw [show z + τ *ᵥ ofIntVec n + ofIntVec n' + u i = z + u i + τ *ᵥ ofIntVec n + ofIntVec n' by abel,
      (hF i hi).2, ← eC_add, dotProduct_add, dotProduct_smul, smul_eq_mul]
    congr 2; ring
  have h2 : ∀ x : κ → ℂ, ∏ i ∈ s, eC (x i) = eC (∑ i ∈ s, x i) := fun x => by
    simp only [eC, Finset.mul_sum, Complex.exp_sum]
  simp only
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, h2, ← eC_add, Finset.sum_sub_distrib,
    ← dotProduct_sum, hu, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  simp
end GlobalTheory
