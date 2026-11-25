-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBaseChangeAt_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:51.1844+00:00
-- url     : https://prove2.me/submissions/85d7cccf-f6de-4e0f-9a6d-fa41a93d2e18

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_smul_at
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sectionLinearAt_apply
import Theorems.Thm_GroundTheory_Arith_Etale_openInclLE_left
import Theorems.Thm_GroundTheory_Arith_Etale_openIncl_left
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Etale.openInclLE_left
attribute [local simp] GroundTheory.Arith.Etale.openIncl_left


attribute [local simp] GroundTheory.Arith.SchemeCoh.sectionLinearAt_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {W T U : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (j : T ⟶ U) [IsOpenImmersion j] (N : U.Modules)
    {O : U.Opens} (hO : O ≤ j.opensRange) : IsBaseChangeAt j N O := by
  intro Q _ _ ψ hψ
  have hb := Etale.pullbackUnitApp_bijective j N hO
  have : IsIso (j.app O) := Scheme.Hom.isIso_app j O hO
  let e := AddEquiv.ofBijective (Etale.pullbackUnitApp j N O) hb
  have he : ∀ n, e.symm (Etale.pullbackUnitApp j N O n) = n := fun n => e.symm_apply_apply n
  have hs : ∀ x, Etale.pullbackUnitApp j N O (e.symm x) = x := fun x => e.apply_symm_apply x
  refine ⟨{ toFun := fun x => ψ (e.symm x)
            map_add' := fun x y => by simp
            map_smul' := fun t x => ?_ }, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Γ(U, O), j.app O a = t :=
      ⟨(asIso (j.app O)).inv t, by simp⟩
    simp only [RingHom.id_apply]
    rw [← hψ, ← hs x, he, ← pullbackUnitApp_smul_at, he]
  · simp [he]
  · ext x
    obtain ⟨n, rfl⟩ := hb.2 x
    simp [he, hψ'']
end GroundTheory.Arith.SchemeCoh
