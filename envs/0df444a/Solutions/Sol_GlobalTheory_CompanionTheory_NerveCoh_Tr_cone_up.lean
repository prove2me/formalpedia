-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.Tr.cone_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:10.488961+00:00
-- url     : https://prove2.me/submissions/855857ad-c81b-40cb-8d44-e392823efbf4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_succ_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_of_acyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_zero_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_uniq
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_zero_ex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
variable {C D : Type} [Category.{0} C] [Category.{0} D]
open GlobalTheory.CompanionTheory.NerveCoh.Tr
variable (τ : Tr R C D)
namespace GlobalTheory.CompanionTheory.NerveCoh.Tr
theorem _root_.solution [Quiver.IsThin C] [Quiver.IsThin D] (k : ℕ) : (cone τ.up.pull).Ex k := by
  have hA : ∀ k, (cn τ.J).Ex (k + 1) := fun k ↦ Cx.ex_succ_iff.2 fun a ha ↦
    (coindD fun T ↦ ModuleCat.of R (∀ U : D, τ.G.obj (T, U))).exact k a ha
  have hB : ∀ k, (cn τ.I).Ex (k + 1) := fun k ↦ Cx.ex_succ_iff.2 fun a ha ↦ (coindD τ.G.obj).exact k a ha
  refine cone_ex_of_acyclic (A := cn τ.J) (B := cn τ.I) τ.up.pull hA hB ?_ ?_ k
  · intro a ha h
    refine (coindD fun T ↦ ModuleCat.of R (∀ U : D, τ.G.obj (T, U))).zero_ext a ha fun T' ↦ funext fun U ↦ ?_
    exact congrFun (congrFun h (pt (T', U))) ⟨(T', U), 𝟙 _⟩
  · intro b hb
    obtain ⟨a, ha, hab⟩ := (coindD (fun T ↦ ModuleCat.of R (∀ U : D, τ.G.obj (T, U)))).zero_ex
      (fun T' U ↦ (coindD τ.G.obj).ev (𝟙 _) ((b : MCn τ.I 0) (pt (T', U))))
    refine ⟨a, ha, ?_⟩
    have h1 : τ.up.pull.f 1 ((cn τ.J).d 0 a) = (cn τ.I).d 0 (τ.up.pull.f 0 a) := τ.up.pull.f_d 0 a
    have h2 : (cn τ.J).d 0 a = 0 := ha
    rw [h2, map_zero] at h1
    exact (coindD τ.G.obj).uniq _ _ h1.symm hb fun y ↦ congrFun (hab y.1) y.2
end GlobalTheory.CompanionTheory.NerveCoh.Tr
