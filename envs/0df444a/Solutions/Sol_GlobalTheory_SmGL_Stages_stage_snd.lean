-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.stage_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:30:00.649282+00:00
-- url     : https://prove2.me/submissions/f0deec6c-cfff-4388-a53b-93396c9a5818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_stage
import Theorems.Thm_GlobalTheory_SmGL_Stages_pr_sec
import Theorems.Thm_GlobalTheory_SmGL_Stages_continuous_sec
import Theorems.Thm_GlobalTheory_SmGL_Stages_dl_sec
import Theorems.Thm_GlobalTheory_SmGL_Stages_iwasawa_two
import Theorems.Thm_GlobalTheory_SmGL_Stages_tauFst_apply
import Theorems.Thm_GlobalTheory_SmGL_Stages_dat_fst
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution (e : a ⊕ bc ≃ n) (f : b ⊕ c ≃ bc) {R : Subgroup (GL n k)} (hRQ : R ≤ parab k (two e))
    (hR : ∀ q : parab k (two e), (q : GL n k) ∈ R ↔ (pr e q).2 ∈ parab k (two f))
    (σ : Representation ℂ (parab k (two f)) V₁) (π : Representation ℂ (GL a k) V₂)
    (ρ : Representation ℂ R W) (i : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W)
    (hi : ∀ (q : parab k (two e)) (h : (q : GL n k) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨(pr e q).2, (hR q).1 h⟩) (tauFst e π q) z)) :
    Nonempty ((smInd _ (dat e (extTensor π (smInd _ σ)))).Equiv (smInd R ρ)) :=
  stage hRQ ((MonoidHom.snd _ _).comp (pr e)) ((sec e).comp (MonoidHom.inr _ _))
    ((continuous_sec e).comp (Continuous.prodMk_right 1))
    (fun m => congrArg Prod.snd (pr_sec e (1, m))) hR SplitFlip.isCompact_KO (iwasawa_two f) σ (tauFst e π)
    ((((Continuous.prodMk_right 1).tendsto 1).eventually (dl_sec e)).mono fun u hu => by
      ext v
      show tauFst e π (sec e (1, u)) v = v
      rw [tauFst_apply, hu, pr_sec]; simp)
    _ (TensorProduct.comm _ _ _) (fun q y => dat_fst e π _ q y) ρ i hi
end GlobalTheory.SmGL.Stages
