-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckDecTens.dec1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:09:51.639567+00:00
-- url     : https://prove2.me/submissions/dcdc6bcd-89b6-40b4-b348-88702bf94898

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTensorFromHomLaws
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckDecTens_hom_reindex

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckDecTens
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckDecTens
theorem _root_.solution (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F, U)} {pr : ∀ a, M (F, U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F', T a))
      (fun a => on1 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.snd : Unit × F'.ι → F'.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F'.ι => ((), c)) ∘ₗ on1 (pr a)) where
  io_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
    (hom_reindex hM F' ((triv k r).tens F') (T a) (Equiv.punitProd _) (fun g => by
      ext c d; simp))
    (hT k r _ _ F' _ _ _ (h.io_hom a)).1
  pr_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
    (hT k r _ _ F' _ _ _ (h.pr_hom a)).1
    (hom_reindex hM ((triv k r).tens F') F' (T a) (Equiv.punitProd _).symm (fun g => by
      ext c d; simp))
  sum := by
    refine LinearMap.ext fun x => funext fun p => ?_
    have := congrFun (LinearMap.congr_fun h.sum (fun c => x (c, p.2))) p.1
    rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
    exact this
  pr_io a := by
    refine LinearMap.ext fun x => funext fun c => ?_
    exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
  pr_io_ne a a' hne := by
    refine LinearMap.ext fun x => funext fun c => ?_
    exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()
end GlobalTheory.CompanionTheory.ZuckDecTens
