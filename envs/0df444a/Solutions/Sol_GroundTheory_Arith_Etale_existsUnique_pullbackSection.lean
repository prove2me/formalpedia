-- Prove2me | solution 1 for GroundTheory.Arith.Etale.existsUnique_pullbackSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:21.81907+00:00
-- url     : https://prove2.me/submissions/6ecd0ce9-09f7-4c6f-acb3-1ffb629ad004

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Theorems.Thm_GroundTheory_Arith_Etale_isBaseChangeSection_specMap
import Theorems.Thm_GroundTheory_Arith_Etale_isBaseChangeSection_of_isIso
import Theorems.Thm_GroundTheory_Arith_Etale_isQuasicoherent_pullback_of_isIso

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
theorem _root_.solution {T U : Scheme.{u}} (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] (Q : Type u) [AddCommGroup Q] [Module Γ(T, ⊤) Q]
    (ψ : Γ(N, ⊤) →+ Q) (hψ : ∀ (a : Γ(U, ⊤)) (n : Γ(N, ⊤)), ψ (a • n) = g.appTop a • ψ n) :
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q,
      ∀ n, ψ' (pullbackSection g N n) = ψ n := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = T.isoSpec.inv ≫ g ≫ U.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hg : g = T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv := by simp [hφ]
  have key : IsBaseChangeSection g N := by
    rw [hg]
    have := isQuasicoherent_pullback_of_isIso U.isoSpec.inv N
    have := (isQuasicoherent_iff_isIso_fromTildeΓ
      ((Scheme.Modules.pullback U.isoSpec.inv).obj N)).mp inferInstance
    exact IsBaseChangeSection.comp (IsBaseChangeSection.comp (isBaseChangeSection_of_isIso _ N)
      (isBaseChangeSection_specMap φ _)) (isBaseChangeSection_of_isIso _ _)
  exact key Q ψ hψ
end GroundTheory.Arith.Etale
