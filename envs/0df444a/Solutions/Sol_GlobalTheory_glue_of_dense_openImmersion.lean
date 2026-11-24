-- Prove2me | solution 1 for GlobalTheory.glue_of_dense_openImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:57.846797+00:00
-- url     : https://prove2.me/submissions/87e228e5-5ac0-45bd-8bde-878b1c938b09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueOfDenseOpenImmersion
import Theorems.Thm_GlobalTheory_app_injective_of_dense_range
import Theorems.Thm_GlobalTheory_app_res_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  intro T Z _ j _ hj U s hloc
  choose W hWU hmem h hh using hloc
  let Wf : U → Z.Opens := fun u => W u.1 u.2
  have hcover : U ≤ iSup Wf := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' Wf U (fun u => homOfLE (hWU u.1 u.2)) hcover
    (fun u => h u.1 u.2) (by
      intro u v
      apply app_injective_of_dense_range j hj
      change j.app _ (Z.presheaf.map _ (h u.1 u.2)) = j.app _ (Z.presheaf.map _ (h v.1 v.2))
      rw [app_res_eq j _ (homOfLE (j.preimage_mono inf_le_left)),
        app_res_eq j _ (homOfLE (j.preimage_mono inf_le_right)), hh, hh]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  let g' : Γ(Z, U) := g
  have hg' : ∀ u : U, Z.presheaf.map (homOfLE (hWU u.1 u.2)).op g' = h u.1 u.2 := hg
  refine ⟨g', ?_⟩
  refine T.sheaf.eq_of_locally_eq' (fun u : U => j ⁻¹ᵁ Wf u) (j ⁻¹ᵁ U)
    (fun u => homOfLE (j.preimage_mono (hWU u.1 u.2))) ?_ _ _ ?_
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨j x, hx⟩, hmem _ hx⟩
  · intro u
    have key : T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op (j.app U g') =
        T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op s := by
      rw [← app_res_eq j (homOfLE (hWU u.1 u.2)), hg' u, hh]
    exact key
end GlobalTheory
