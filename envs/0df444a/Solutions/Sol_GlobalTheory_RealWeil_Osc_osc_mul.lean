-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.osc_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:46.806419+00:00
-- url     : https://prove2.me/submissions/be219dd8-794a-49af-ab97-a54f5a19862f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_heis
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_comp
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_ext
import Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_smul
import Theorems.Thm_GlobalTheory_RealWeil_Osc_k_mul
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_osc
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_heis
import Theorems.Thm_GlobalTheory_RealWeil_Osc_pr_osc
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_pr
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_scalar_mul
import Theorems.Thm_GlobalTheory_RealWeil_Good_sm
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}
variable {G : Type} [Group G] {k : G →* (V →L[ℝ] V)} {c : G → ℂ}
variable (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y)
include hJ
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hl : ∀ g, star (c g) * c g * lam (k g) = 1)
    (hm : ∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) (g g' : G) {f : B}
    (hf : Sm ρ f) : osc h hk c (g * g') f = osc h hk c g (osc h hk c g' f) := by
  have s1 := sm_osc (c := c) hJ h hk g' hf
  refine good_ext hJ (h := h.twist (k (g * g')) (hk _))
    (good_of_sm hJ _ (sm_comp _ (sm_osc hJ h hk _ hf))) (good_of_sm hJ _ (sm_comp _ (sm_osc hJ h hk _ s1))) fun v => ?_
  have s2 := sm_heis h v hf
  have s3 : Sm ρ (proj h (ρ v f)) := (good_proj hJ h _).sm hJ
  show pr h hk (g * g') _ = pr h hk (g * g') _
  rw [← osc_heis hJ h hk _ v hf, pr_osc hJ h hk _ s2, k_mul, ← osc_heis hJ h hk _ _ s1, ← osc_heis hJ h hk _ v hf,
    ← osc_pr hJ h hk _ _ (sm_osc hJ h hk _ s2), pr_osc hJ h hk _ s2, osc, intw_smul, ← osc,
    osc_pr hJ h hk _ _ s3, osc_proj hJ h hk _ s2, map_smul, smul_smul, mul_comm (c g'), scalar_mul hJ h hk hl hm]
end GlobalTheory.RealWeil.Osc
