-- Prove2me | solution 1 for GroundTheory.Arith.Etale.isBaseChangeSection_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:37.194637+00:00
-- url     : https://prove2.me/submissions/c4cd2d6a-9f9b-4c0a-add9-1a13afd381a3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Theorems.Thm_GroundTheory_Arith_Etale_bijective_pullbackSection_of_isIso
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackSection_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace GroundTheory.Arith.Etale
theorem _root_.solution {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules) :
    IsBaseChangeSection g N := by
  intro Q _ _ ψ hψ
  have hb := bijective_pullbackSection_of_isIso g N
  have : IsIso g.appTop := inferInstanceAs (IsIso (g.app ⊤))
  let e := AddEquiv.ofBijective (pullbackSection g N) hb
  have he : ∀ n, e.symm (pullbackSection g N n) = n := fun n => e.symm_apply_apply n
  have hs : ∀ x, pullbackSection g N (e.symm x) = x := fun x => e.apply_symm_apply x
  refine ⟨{ toFun := fun x => ψ (e.symm x)
            map_add' := fun x y => by simp
            map_smul' := fun t x => ?_ }, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Γ(U, ⊤), g.appTop a = t :=
      ⟨(asIso g.appTop).inv t, by simp⟩
    simp only [RingHom.id_apply]
    rw [← hψ, ← hs x, he, ← pullbackSection_smul, he]
  · simp [he]
  · ext x
    obtain ⟨n, rfl⟩ := hb.2 x
    simp [he, hψ'']
end GroundTheory.Arith.Etale
