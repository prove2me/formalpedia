-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.integrable_integral_cons_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:13.900407+00:00
-- url     : https://prove2.me/submissions/df1d1c28-f7e0-4fea-ac5b-69efcba5f2df

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_revProdExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x)))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      (((h.continuous_revProdExp (Fin.tail X)).comp continuous_snd).mul
        ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_const))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left
end GroundTheory.Automorphic.IsExpLieAlgebra
