-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:48.356805+00:00
-- url     : https://prove2.me/submissions/4e229688-2811-4b7b-8d7c-c92d97713855

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_smul_at
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sectionLinearAt_apply
import Theorems.Thm_GroundTheory_Arith_Etale_openInclLE_left
import Theorems.Thm_GroundTheory_Arith_Etale_openIncl_left
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
theorem _root_.solution {f : W ⟶ T} {g : T ⟶ U} {N : U.Modules} {O : U.Opens}
    (hg : IsBaseChangeAt g N O)
    (hf : IsBaseChangeAt f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ O)) :
    IsBaseChangeAt (f ≫ g) N O := by
  intro Q _ instQ ψ hψ
  letI instW : Module Γ(W, f ⁻¹ᵁ (g ⁻¹ᵁ O)) Q := instQ
  letI : Module Γ(T, g ⁻¹ᵁ O) Q := Module.compHom Q (f.app (g ⁻¹ᵁ O)).hom
  have hsm : ∀ (t : Γ(T, g ⁻¹ᵁ O)) (q : Q), t • q = f.app (g ⁻¹ᵁ O) t • q := fun _ _ => rfl
  obtain ⟨ψ₁, hψ₁, u₁⟩ := hg Q ψ (fun a n => by
    rw [hψ, hsm]
    change (f ≫ g).app O a • ψ n = (f.app (g ⁻¹ᵁ O)) ((g.app O) a) • ψ n
    rw [Scheme.Hom.comp_app]
    rfl)
  obtain ⟨ψ₂, hψ₂, u₂⟩ := hf Q ψ₁.toAddMonoidHom (fun t x => ψ₁.map_smul t x)
  let c := (Scheme.Modules.pullbackComp f g).app N
  let O' := (f ≫ g) ⁻¹ᵁ O
  have hc : ∀ n, c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n) =
      Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n) :=
    Etale.pullbackUnitApp_comp f g N O
  have hchi : ∀ x, c.hom.app O' (c.inv.app O' x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]; rfl
  let Φ : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, O') →ₗ[Γ(W, O')] Q :=
    { toFun := fun x => ψ₂ (c.inv.app O' x)
      map_add' := fun x y => by
        change ψ₂ (c.inv.app O' (x + y)) = ψ₂ (c.inv.app O' x) + ψ₂ (c.inv.app O' y)
        erw [map_add, map_add]
      map_smul' := fun w x => by
        change ψ₂ (c.inv.app O' (w • x)) = w • ψ₂ (c.inv.app O' x)
        erw [Scheme.Modules.Hom.app_smul]
        exact ψ₂.map_smul w _ }
  refine ⟨Φ, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · change ψ₂ (c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n)) = ψ n
    rw [hc, hψ₂]
    exact hψ₁ n
  · let χ : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N),
        f ⁻¹ᵁ (g ⁻¹ᵁ O)) →ₗ[Γ(W, f ⁻¹ᵁ (g ⁻¹ᵁ O))] Q :=
      { toFun := fun y => ψ'' (c.hom.app O' y)
        map_add' := fun x y => by
          change ψ'' (c.hom.app O' (x + y)) = ψ'' (c.hom.app O' x) + ψ'' (c.hom.app O' y)
          erw [map_add, map_add]
        map_smul' := fun w y => by
          change ψ'' (c.hom.app O' (w • y)) = w • ψ'' (c.hom.app O' y)
          erw [Scheme.Modules.Hom.app_smul]
          exact ψ''.map_smul w _ }
    have hχ : ∀ n, χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n)) =
        ψ n := fun n => by
      change ψ'' (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O)
        (Etale.pullbackUnitApp g N O n))) = ψ n
      rw [← hc, hchi]
      exact hψ'' n
    let χ₁ : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) →ₗ[Γ(T, g ⁻¹ᵁ O)] Q :=
      { toFun := fun x => χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x)
        map_add' := fun x y => by
          change χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (x + y)) = _
          erw [map_add, map_add]
        map_smul' := fun t x => by
          change χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (t • x)) =
            t • χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x)
          rw [pullbackUnitApp_smul_at, map_smul, hsm] }
    have h₁ : χ₁ = ψ₁ := u₁ χ₁ hχ
    have h₂ : χ = ψ₂ := u₂ χ (fun x => congrArg (fun l => l x) h₁)
    ext x
    change ψ'' x = ψ₂ (c.inv.app O' x)
    rw [← h₂]
    change ψ'' x = ψ'' (c.hom.app O' (c.inv.app O' x))
    rw [hchi]
end IsBaseChangeAt
end GroundTheory.Arith.SchemeCoh
