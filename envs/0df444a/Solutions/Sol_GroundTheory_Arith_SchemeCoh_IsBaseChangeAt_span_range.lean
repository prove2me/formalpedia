-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.span_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:42.941096+00:00
-- url     : https://prove2.me/submissions/a033df52-463c-4539-b51c-aeef3b7380fa

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sectionLinearAt_apply
import Theorems.Thm_GroundTheory_Arith_Etale_openInclLE_left
import Theorems.Thm_GroundTheory_Arith_Etale_openIncl_left
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
namespace IsBaseChangeAt
theorem _root_.solution {g : T ⟶ U} {N : U.Modules} {O : U.Opens}
    (h : IsBaseChangeAt g N O) :
    Submodule.span Γ(T, g ⁻¹ᵁ O) (Set.range (Etale.pullbackUnitApp g N O)) = ⊤ := by
  set L := Submodule.span Γ(T, g ⁻¹ᵁ O) (Set.range (Etale.pullbackUnitApp g N O))
  obtain ⟨ψ', -, huniq⟩ := h (Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) ⧸ L) 0
    (fun a n => by simp)
  have h0 : (0 : _ →ₗ[Γ(T, g ⁻¹ᵁ O)] (_ ⧸ L)) = ψ' := huniq 0 (fun n => by simp)
  have h1 : L.mkQ = ψ' := huniq L.mkQ (fun n => by
    simpa using (Submodule.Quotient.mk_eq_zero L).2 (Submodule.subset_span ⟨n, rfl⟩))
  rw [eq_top_iff]
  intro q _
  have := LinearMap.congr_fun (h1.trans h0.symm) q
  exact (Submodule.Quotient.mk_eq_zero L).1 this
end IsBaseChangeAt
end GroundTheory.Arith.SchemeCoh
