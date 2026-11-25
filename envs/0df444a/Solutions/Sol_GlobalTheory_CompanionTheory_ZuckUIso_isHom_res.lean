-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckUIso.isHom_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:19:29.857956+00:00
-- url     : https://prove2.me/submissions/cbd82b85-25e4-4ab9-a3b5-2001c06dd0c0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_dsW_map
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_res_coe
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie
import Theorems.Thm_CompanionTheory_Zuck_URep_sig_coe
import Theorems.Thm_P2M_CompanionTheory_D_Upq_Sm_dsigW_eq__320e841fce93


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckUIso
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckUIso
theorem _root_.solution (F : FRep k r) (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (hn : ∀ x, ‖e x‖ = ‖x‖) :
    IsHom (F, U) (F, U') (dOp F.ι (res U U' e he)) where
  cont W hW := by
    refine ⟨1, [W], by simpa using hW, fun x => le_of_eq ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, sn]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dsigW_eq', dsigW_eq']
    change ‖dsW U'.R.σ W (e (x c : U.R.H))‖ = _
    rw [dsW_map U.repOn e he (v := (x c : U.R.H)) (x c).2 (fun X hX t => ex_mem_of_lie (hW X hX) t), hn]
  equiv g hg := by
    have h1 : res U U' e he ∘ₗ U.sig g = U'.sig g ∘ₗ res U U' e he := by
      ext v
      simp only [LinearMap.comp_apply, res_coe, URep.sig_coe _ hg, he g hg]
    refine LinearMap.ext fun x => funext fun c => ?_
    have h2 : ∀ d, res U U' e he (U.sig g (x d)) = U'.sig g (res U U' e he (x d)) :=
      fun d => LinearMap.congr_fun h1 (x d)
    simp [CompanionTheory.Zuck.act, mAct, dOp, h2]
end GlobalTheory.CompanionTheory.ZuckUIso
