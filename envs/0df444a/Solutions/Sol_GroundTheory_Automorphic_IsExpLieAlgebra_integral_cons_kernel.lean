-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.integral_cons_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:16.730897+00:00
-- url     : https://prove2.me/submissions/747dd4e5-7cdb-48e5-8adc-ceba08f8f5d5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
import Theorems.Thm_GroundTheory_Automorphic_integral_fin_succ_cons
import Theorems.Thm_GroundTheory_Automorphic_tsupport_cons_kernel
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_revProdExp_succ
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_revProdExp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x) =
      ∫ s, ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x))) := by
  have hint : Integrable
      (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ha.comp (continuous_apply 0)).mul
        (hK.comp (continuous_pi fun j => continuous_apply j.succ))).mul
        (hF.comp ((h.continuous_revProdExp X).mul continuous_const))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε has hKs))
  rw [integral_fin_succ_cons hint]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, h.revProdExp_succ, mul_assoc]
end GroundTheory.Automorphic.IsExpLieAlgebra
