-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.stage_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:29:59.604232+00:00
-- url     : https://prove2.me/submissions/326450ea-73d9-4b72-bac7-6e8969488ac5

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
import Theorems.Thm_GlobalTheory_SmGL_Stages_tauSnd_apply
import Theorems.Thm_GlobalTheory_SmGL_Stages_dat_snd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl


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
theorem _root_.solution (e : ab ⊕ c ≃ n) (f : a ⊕ b ≃ ab) {R : Subgroup (GL n k)} (hRQ : R ≤ parab k (two e))
    (hR : ∀ q : parab k (two e), (q : GL n k) ∈ R ↔ (pr e q).1 ∈ parab k (two f))
    (σ : Representation ℂ (parab k (two f)) V₁) (π : Representation ℂ (GL c k) V₂)
    (ρ : Representation ℂ R W) (i : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W)
    (hi : ∀ (q : parab k (two e)) (h : (q : GL n k) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨(pr e q).1, (hR q).1 h⟩) (tauSnd e π q) z)) :
    Nonempty ((smInd _ (dat e (extTensor (smInd _ σ) π))).Equiv (smInd R ρ)) :=
  stage hRQ ((MonoidHom.fst _ _).comp (pr e)) ((sec e).comp (MonoidHom.inl _ _))
    ((continuous_sec e).comp (Continuous.prodMk_left 1))
    (fun m => congrArg Prod.fst (pr_sec e (m, 1))) hR SplitFlip.isCompact_KO (iwasawa_two f) σ (tauSnd e π)
    ((((Continuous.prodMk_left 1).tendsto 1).eventually (dl_sec e)).mono fun u hu => by
      ext v
      show tauSnd e π (sec e (u, 1)) v = v
      rw [tauSnd_apply, hu, pr_sec]; simp)
    _ (.refl _ _) (fun q y => dat_snd e _ π q y) ρ i hi
end GlobalTheory.SmGL.Stages
