-- Prove2me | solution 1 for GlobalTheory.SobolevRep.sum_integral_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:15.913065+00:00
-- url     : https://prove2.me/submissions/a947645a-14cc-4df2-9648-d2b0777d0c9c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
import Theorems.Thm_GlobalTheory_SobolevRep_integral_cons
import Theorems.Thm_GlobalTheory_SobolevRep_integrable_integral_cons

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
theorem _root_.solution {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (y * h.prodExp (Fin.tail X) t')) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (x * h.prodExp X t) =
      ∫ s, a s * f₁ (x * h.expG (s • X 0)) := by
  rw [Finset.sum_congr rfl fun i _ => integral_cons h X hε ha has (hK i) (hKs i) (hF i) x,
    ← integral_finsetSum _ fun i _ =>
      integrable_integral_cons h X ha has (hK i) (hKs i) (hF i) x]
  congr 1; funext s
  rw [hd, Finset.mul_sum]
  congr 1; funext i
  rw [← integral_const_mul]
end GlobalTheory.SobolevRep
