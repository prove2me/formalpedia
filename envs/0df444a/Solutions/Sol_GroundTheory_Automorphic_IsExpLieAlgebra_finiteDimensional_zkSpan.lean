-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.finiteDimensional_zkSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:25.203621+00:00
-- url     : https://prove2.me/submissions/055dcc4c-e5f3-41ef-9040-6e4ed467ca59

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_zSpan_rightTranslate_le
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable (K : Subgroup G)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (f : h.smoothFuns (F := F))
    (hK : IsRightKFinite K (f : G → F)) (hZ : h.IsZFinite f) :
    FiniteDimensional ℂ (h.zkSpan K f) := by
  set W : Submodule ℂ (h.smoothFuns (F := F)) := Submodule.span ℂ (range fun k : K => h.rightTranslateEnd (k : G) f)
  haveI : FiniteDimensional ℂ W := by
    have hW : W.map (h.smoothFuns (F := F)).subtype = Submodule.span ℂ (range fun k : K => rightTranslate (k : G) (f : G → F)) := by
      rw [Submodule.map_span, ← range_comp]; rfl
    haveI : FiniteDimensional ℂ (W.map (h.smoothFuns (F := F)).subtype) := by rw [hW]; exact hK
    exact (Submodule.equivMapOfInjective _ (h.smoothFuns (F := F)).injective_subtype W).symm.finiteDimensional
  haveI : FiniteDimensional ℂ (h.zSpan f) := hZ

  have hfin : ∀ w ∈ W, FiniteDimensional ℂ (h.zSpan w) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.finiteDimensional_of_le (h.zSpan_rightTranslate_le f k)
    | zero =>
      refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
      rw [zSpan, Submodule.span_le]
      rintro _ ⟨z, -, rfl⟩
      simp
    | add x y _ _ hx hy =>
      refine Submodule.finiteDimensional_of_le (S₂ := h.zSpan x ⊔ h.zSpan y) ?_
      rw [zSpan, Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      dsimp only
      rw [SetLike.mem_coe, map_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
        (Submodule.subset_span ⟨z, hz, rfl⟩)
    | smul c x _ hx =>
      refine Submodule.finiteDimensional_of_le (S₂ := h.zSpan x) ?_
      rw [zSpan, Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      dsimp only
      rw [SetLike.mem_coe, map_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨z, hz, rfl⟩)
  haveI : Module.Free ℂ W := Module.Free.of_divisionRing ℂ W
  let b := Module.finBasis ℂ W
  haveI : ∀ i, FiniteDimensional ℂ (h.zSpan (b i : h.smoothFuns (F := F))) := fun i => hfin _ (b i).2
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, h.zSpan (b i : h.smoothFuns (F := F))) ?_
  rw [zkSpan, Submodule.span_le]
  rintro _ ⟨⟨z, k⟩, rfl⟩
  have hk : h.rightTranslateEnd (k : G) f ∈ W := Submodule.subset_span ⟨k, rfl⟩
  have e : h.rightTranslateEnd (k : G) f = ∑ i, b.repr ⟨_, hk⟩ i • (b i : h.smoothFuns (F := F)) := by
    conv_lhs => rw [show h.rightTranslateEnd (k : G) f = ((⟨_, hk⟩ : W) : h.smoothFuns (F := F)) from rfl,
      ← b.sum_repr ⟨_, hk⟩]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  simp only [SetLike.mem_coe]
  rw [e, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _
    ((le_iSup (fun i => h.zSpan (b i : h.smoothFuns (F := F))) i) (Submodule.subset_span ⟨z, z.2, rfl⟩))
end GroundTheory.Automorphic.IsExpLieAlgebra
