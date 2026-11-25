-- Prove2me | solution 1 for GlobalTheory.SobolevRep.integrable_integral_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:38.429816+00:00
-- url     : https://prove2.me/submissions/fc965af6-7ef9-4d52-820e-93f392ba6cc6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
import Theorems.Thm_P2M_GlobalTheory_SobolevRep_continuous_prodExp__16071771a47c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory
open GlobalTheory.SobolevRep
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
namespace GlobalTheory.SobolevRep
theorem _root_.solution {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t'))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      ((continuous_const.mul (h.continuous_expG.comp (continuous_fst.smul continuous_const))).mul
        ((continuous_prodExp' h (Fin.tail X)).comp continuous_snd))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left
end GlobalTheory.SobolevRep
