-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommSplit.finrank_adjoin_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:34.818806+00:00
-- url     : https://prove2.me/submissions/225cea85-7e2d-4395-b881-8c4228a36631

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_of_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_adjoin_compr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommSplit
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommSplit
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
      (a : Fin l → Module.End ℂ V) (W W' : Submodule ℂ V), IsCompl W W' →
      ∀ (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (h' : ∀ i, ∀ w ∈ W', a i w ∈ W'),
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h i) : Module.End ℂ W))) +
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h' i) : Module.End ℂ W'))) := by
  intro V _ _ _ l a W W' hc h h'
  let AW := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : Module.End ℂ W))
  let AW' := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h' i) : Module.End ℂ W'))
  let Φ : Algebra.adjoin ℂ (Set.range a) →ₗ[ℂ] AW × AW' :=
    { toFun := fun b => (⟨compr W W' hc b, (adjoin_compr a W W' hc h b b.2).2⟩,
        ⟨compr W' W hc.symm b, (adjoin_compr a W' W hc.symm h' b b.2).2⟩)
      map_add' := fun b c => by
        ext <;> simp [map_add]
      map_smul' := fun t b => by
        ext <;> simp [map_smul] }
  have hinj : Function.Injective Φ := by
    intro b c hbc
    have h1 := congrArg (fun p => (p.1 : Module.End ℂ W)) hbc
    have h2 := congrArg (fun p => (p.2 : Module.End ℂ W')) hbc
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have e1 : (b : Module.End ℂ V) w = (c : Module.End ℂ V) w := by
      have e := LinearMap.congr_fun h1 ⟨w, hw⟩
      rw [compr_of_inv W W' hc _ (adjoin_compr a W W' hc h b b.2).1,
        compr_of_inv W W' hc _ (adjoin_compr a W W' hc h c c.2).1] at e
      exact congrArg Subtype.val e
    have e2 : (b : Module.End ℂ V) w' = (c : Module.End ℂ V) w' := by
      have e := LinearMap.congr_fun h2 ⟨w', hw'⟩
      rw [compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' b b.2).1,
        compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' c c.2).1] at e
      exact congrArg Subtype.val e
    rw [map_add, map_add, e1, e2]
  calc Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ (AW × AW') :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℂ AW + Module.finrank ℂ AW' := Module.finrank_prod
end GlobalTheory.CompanionTheory.CommSplit
