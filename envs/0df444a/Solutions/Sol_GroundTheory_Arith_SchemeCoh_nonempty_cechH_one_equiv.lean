-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.nonempty_cechH_one_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:34.590291+00:00
-- url     : https://prove2.me/submissions/f7d4f83e-0d62-4d0a-a18b-80326a64313a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_globalCocycle
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H___map_g_ddac18c3408a
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H_exact__02328f27094f
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H_exact__598dfd24061d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
noncomputable section
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w w' u
variable {X : TopCat.{u}}
variable {ι : Type w}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) [Injective S.X₂]
include hS
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (U : ι → Opens X) (hU : iSup U = ⊤)
    (hC : IsCechShortExact U S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj U) :
    Nonempty (cechH S.X₁.obj U 1 ≃+ Sheaf.H.{w'} S.X₁ 1) := by
  let pC : S.X₃.obj.obj (op ⊤) →+ cechH S.X₁.obj U 1 :=
    (hC.delta 0).comp (globalCocycle S.X₃.obj U)
  let pH : S.X₃.obj.obj (op ⊤) →+ Sheaf.H.{w'} S.X₁ 1 :=
    (H.δ hS 0 1 rfl).comp (Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm.toAddMonoidHom
  have hpC : Function.Surjective pC :=
    (hC.delta_surjective hI 0).comp (globalCocycle_surjective _ U S.X₃.property hU)
  have hpH : Function.Surjective pH := by
    intro x
    obtain ⟨y, hy⟩ := H.exact₁ hS rfl x (H.eq_zero_of_injective S.X₂ _)
    exact ⟨Sheaf.H.equiv₀ S.X₃ isTerminalTop y, by simp [pH, hy]⟩
  have hker : pC.ker = pH.ker := by
    ext s
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    have e1 : pC s = 0 ↔ ∃ t, S.g.hom.app (op ⊤) t = s := by
      change hC.delta 0 (globalCocycle S.X₃.obj U s) = 0 ↔ _
      rw [hC.delta_eq_zero_iff]
      constructor
      · rintro ⟨κ, hκ, hgκ⟩
        obtain ⟨t, ht⟩ := globalCocycle_surjective _ U S.X₂.property hU
          ⟨κ, (mem_cocycles κ).2 hκ⟩
        refine ⟨t, globalCocycle_injective _ U S.X₃.property hU (Subtype.ext ?_)⟩
        rw [← push_globalCocycle, ht]
        exact hgκ
      · rintro ⟨t, rfl⟩
        exact ⟨(globalCocycle S.X₂.obj U t).1, (mem_cocycles _).1 (globalCocycle _ U t).2,
          push_globalCocycle U _ t⟩
    have e2 : pH s = 0 ↔ ∃ t, S.g.hom.app (op ⊤) t = s := by
      change H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s) = 0 ↔ _
      constructor
      · intro h
        obtain ⟨x, hx⟩ := H.exact₃ hS rfl _ h
        refine ⟨Sheaf.H.equiv₀ S.X₂ isTerminalTop x, ?_⟩
        apply (Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm.injective
        rw [← Sheaf.H.equiv₀_symm_naturality, AddEquiv.symm_apply_apply, hx]
      · rintro ⟨t, rfl⟩
        rw [← Sheaf.H.equiv₀_symm_naturality]
        exact H.δ_map_g hS rfl _
    rw [e1, e2]
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective pC hpC).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective pH hpH))⟩
end GroundTheory.Arith.SchemeCoh
