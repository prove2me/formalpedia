-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.of_comp_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:49.785085+00:00
-- url     : https://prove2.me/submissions/4058afc7-4ad6-4e43-a9e8-e84c8f8dcbb1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_smul_at
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sectionLinearAt_apply
import Theorems.Thm_GroundTheory_Arith_Etale_openInclLE_left
import Theorems.Thm_GroundTheory_Arith_Etale_openIncl_left
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
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
theorem _root_.solution {f : W ⟶ T} [IsOpenImmersion f] {g : T ⟶ U}
    {N : U.Modules} {O : U.Opens} (hO : g ⁻¹ᵁ O ≤ f.opensRange)
    (h : IsBaseChangeAt (f ≫ g) N O) : IsBaseChangeAt g N O := by
  intro Q _ _ ψ hψ
  have : IsIso (f.app (g ⁻¹ᵁ O)) := Scheme.Hom.isIso_app f _ hO
  let ρ := asIso (f.app (g ⁻¹ᵁ O))
  let O' := (f ≫ g) ⁻¹ᵁ O
  letI instW : Module Γ(W, O') Q := Module.compHom Q ρ.inv.hom
  have hsm : ∀ (w : Γ(W, O')) (q : Q), w • q = ρ.inv w • q := fun _ _ => rfl
  have hρ : ∀ t : Γ(T, g ⁻¹ᵁ O), ρ.inv (f.app (g ⁻¹ᵁ O) t) = t := fun t => by
    rw [← ConcreteCategory.comp_apply]
    change (ρ.hom ≫ ρ.inv) t = t
    rw [ρ.hom_inv_id]
    rfl
  have hρ' : ∀ w : Γ(W, O'), f.app (g ⁻¹ᵁ O) (ρ.inv w) = w := fun w => by
    change (ρ.inv ≫ ρ.hom) w = w
    rw [ρ.inv_hom_id]
    rfl
  obtain ⟨Ψ, hΨ, uΨ⟩ := h Q ψ (fun a n => by
    rw [hψ, hsm]
    change _ = ρ.inv ((f.app (g ⁻¹ᵁ O)) ((g.app O) a)) • ψ n
    rw [hρ])
  have hb := Etale.pullbackUnitApp_bijective f ((Scheme.Modules.pullback g).obj N) hO
  let e := AddEquiv.ofBijective (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O)) hb
  let c := (Scheme.Modules.pullbackComp f g).app N
  have hchi : ∀ x, c.inv.app O' (c.hom.app O' x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.hom_inv_id]; rfl
  have hchi' : ∀ x, c.hom.app O' (c.inv.app O' x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]; rfl
  let ψ' : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) →ₗ[Γ(T, g ⁻¹ᵁ O)] Q :=
    { toFun := fun x => Ψ (c.hom.app O' (e x))
      map_add' := fun x y => by
        change Ψ (c.hom.app O' (e (x + y))) = Ψ (c.hom.app O' (e x)) + Ψ (c.hom.app O' (e y))
        erw [map_add, map_add, map_add]
      map_smul' := fun t x => by
        change Ψ (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (t • x))) =
          t • Ψ (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x))
        rw [pullbackUnitApp_smul_at]
        have h1 := Scheme.Modules.Hom.app_smul c.hom (U := O') (f.app (g ⁻¹ᵁ O) t)
          (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x)
        erw [h1, map_smul, hsm, hρ] }
  refine ⟨ψ', fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · change Ψ (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n))) =
      ψ n
    have hcomp := Etale.pullbackUnitApp_comp f g N O n
    have h2 : c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n)) =
        Etale.pullbackUnitApp (f ≫ g) N O n :=
      (congrArg (fun z => c.hom.app O' z) hcomp).symm.trans (hchi' _)
    exact (congrArg Ψ h2).trans (hΨ n)
  · let χ : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, O') →ₗ[Γ(W, O')] Q :=
      { toFun := fun x => ψ'' (e.symm (c.inv.app O' x))
        map_add' := fun x y => by
          change ψ'' (e.symm (c.inv.app O' (x + y))) =
            ψ'' (e.symm (c.inv.app O' x)) + ψ'' (e.symm (c.inv.app O' y))
          erw [map_add, map_add, map_add]
        map_smul' := fun w x => by
          change ψ'' (e.symm (c.inv.app O' (w • x))) = ρ.inv w • ψ'' (e.symm (c.inv.app O' x))
          have hs1 : c.inv.app O' (w • x) = w • c.inv.app O' x :=
            Scheme.Modules.Hom.app_smul c.inv w x
          set y : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N),
            f ⁻¹ᵁ (g ⁻¹ᵁ O)) := c.inv.app O' x
          have hs2 : e.symm (c.inv.app O' (w • x)) = ρ.inv w • e.symm y := by
            apply e.injective
            refine (e.apply_symm_apply _).trans ?_
            change c.inv.app O' (w • x) =
              Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (ρ.inv w • e.symm y)
            rw [pullbackUnitApp_smul_at, hρ', hs1]
            exact congrArg (fun z => w • z) (e.apply_symm_apply y).symm
          rw [hs2, map_smul] }
    have hχ : χ = Ψ := uΨ χ (fun n => by
      change ψ'' (e.symm (c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n))) = ψ n
      have hcomp := Etale.pullbackUnitApp_comp f g N O n
      have h3 : e.symm (c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n)) =
          Etale.pullbackUnitApp g N O n :=
        (congrArg (fun z => e.symm z) hcomp).trans (e.symm_apply_apply _)
      exact (congrArg ψ'' h3).trans (hψ'' n))
    ext x
    change ψ'' x = Ψ (c.hom.app O' (e x))
    rw [← hχ]
    change ψ'' x = ψ'' (e.symm (c.inv.app O' (c.hom.app O' (e x))))
    have h4 : e.symm (c.inv.app O' (c.hom.app O' (e x))) = x :=
      (congrArg (fun z => e.symm z) (hchi (e x))).trans (e.symm_apply_apply x)
    exact (congrArg ψ'' h4).symm
end IsBaseChangeAt
end GroundTheory.Arith.SchemeCoh
