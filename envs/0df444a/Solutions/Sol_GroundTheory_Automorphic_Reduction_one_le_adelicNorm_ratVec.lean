-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:49:02.00981+00:00
-- url     : https://prove2.me/submissions/442684ab-4ad9-4a8c-96e8-d33af3601974

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_euclidNorm
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_finite_mulSupport
import Theorems.Thm_GroundTheory_Automorphic_Reduction_eventually_norm_eq_one
import Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_ratVec
import Theorems.Thm_GroundTheory_Automorphic_Reduction_prod_norm_mul_finprod_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {x : Fin n → K} (hx : x ≠ 0) : 1 ≤ adelicNorm (ratVec x) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  rw [← prod_norm_mul_finprod_norm hi₀, adelicNorm]
  have hfin := (hasFiniteContent_ratVec hx).finite_mulSupport
  have hfin' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      ‖(x i₀ : v.adicCompletion K)‖).Finite :=
    Filter.eventually_cofinite.1 (eventually_norm_eq_one hi₀)
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _)
  · exact Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_euclidNorm (infComp w (ratVec x)) i₀) _
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin'.toFinset ∪ hfin.toFinset)
      (fun v hv => Finset.mem_coe.2 (Finset.mem_union_left _ (hfin'.mem_toFinset.2 hv))),
      finprod_eq_prod_of_mulSupport_subset _ (s := hfin'.toFinset ∪ hfin.toFinset)
      (fun v hv => Finset.mem_coe.2 (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ =>
      norm_le_pi_norm (finComp v (ratVec x)) i₀
end GroundTheory.Automorphic.Reduction
