-- Prove2me | solution 1 for OAI.Release075.FreeChain.cyclic_chain_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:56:51.695771+00:00
-- url     : https://prove2.me/submissions/b6d36a56-af9f-4131-851b-8654c1205b71

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/CyclicAction.lean:L192-L223
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FreeChain.cyclic_chain_obstruction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction

-- ---- from OAI.GroupTheory.Hyperbolic.CyclicAction ----
namespace OAI

namespace Release075
namespace FreeChain
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A G : Type} [Group G]

end FreeChain
end Release075

namespace Release075
open CategoryTheory
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem finsupp_preimages {J M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →ₗ[ℤ] N) (c : J →₀ N)
    (h : ∀ i, ∃ b, f b = c i) : ∃ b : J →₀ M, ∀ i, f (b i) = c i := by
  choose b hb using h
  let w : J →₀ M := Finsupp.onFinset c.support
    (fun i => if i ∈ c.support then b i else 0)
    (by intro i; split_ifs <;> simp_all)
  refine ⟨w,fun i => ?_⟩
  change f (if i ∈ c.support then b i else 0) = c i
  split_ifs with hi
  · exact hb i
  · simpa only [map_zero] using (Finsupp.notMem_support_iff.mp hi).symm

private theorem regular_invariant_norm {H : Type} [CommGroup H] [Fintype H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g) (c : MonoidAlgebra ℤ H)
    (hc : Representation.leftRegular ℤ H g c = c) :
    ∃ b, (Representation.leftRegular ℤ H).norm b = c := by
  have hm : c ∈ LinearMap.ker
      (Rep.applyAsHom (Rep.leftRegular ℤ H) g - 𝟙 _).hom.toLinearMap := by
    simpa [Rep.sub_hom,Rep.applyAsHom,sub_eq_zero] using hc
  rw [← Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub ℤ g hg] at hm
  exact hm

private theorem regular_norm_zero {H : Type} [CommGroup H] [Fintype H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g) (c : MonoidAlgebra ℤ H)
    (hc : (Representation.leftRegular ℤ H).norm c = 0) :
    ∃ b, Representation.leftRegular ℤ H g b - b = c := by
  have hm : c ∈ LinearMap.ker (Rep.leftRegular ℤ H).norm.hom.toLinearMap := hc
  rw [← Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_norm ℤ g hg] at hm
  obtain ⟨b,hb⟩ := hm
  exact ⟨b, by simpa [Rep.sub_hom,Rep.applyAsHom] using hb⟩

namespace FreeChain
variable {A G : Type} [Group G] (H : Subgroup G) [Fintype H] [IsCyclic H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include hg in
theorem invariant_is_norm (c : FreeChain A G) (hc : chainShift (g:G) c = c) :
    ∃ b, subgroupNorm H b = c := by
  let : CommGroup H := IsCyclic.commGroup
  have hi (i : A × RightCosets H) : Representation.leftRegular ℤ H g
      (chainCosetEquiv H c i) = chainCosetEquiv H c i := by
    rw [← chainCosetEquiv_shift,hc]
  obtain ⟨b,hb⟩ := finsupp_preimages (Representation.leftRegular ℤ H).norm
    (chainCosetEquiv H c) (fun i => regular_invariant_norm g hg _ (hi i))
  refine ⟨(chainCosetEquiv H).symm b,?_⟩
  apply (chainCosetEquiv H).injective
  apply Finsupp.ext
  intro i
  rw [chainCosetEquiv_norm,LinearEquiv.apply_symm_apply,hb]

include hg in
theorem norm_zero_is_difference (c : FreeChain A G) (hc : subgroupNorm H c = 0) :
    ∃ b, chainShift (g:G) b - b = c := by
  let : CommGroup H := IsCyclic.commGroup
  have hi (i : A × RightCosets H) : (Representation.leftRegular ℤ H).norm
      (chainCosetEquiv H c i) = 0 := by
    rw [← chainCosetEquiv_norm,hc,map_zero,Finsupp.zero_apply]
  obtain ⟨b,hb⟩ := finsupp_preimages (Representation.leftRegular ℤ H g - LinearMap.id)
    (chainCosetEquiv H c) (fun i => regular_norm_zero g hg _ (hi i))
  refine ⟨(chainCosetEquiv H).symm b,?_⟩
  apply (chainCosetEquiv H).injective
  apply Finsupp.ext
  intro i
  rw [map_sub,Finsupp.sub_apply,chainCosetEquiv_shift,LinearEquiv.apply_symm_apply]
  exact hb i

end FreeChain
end Release075

namespace Release075.FreeChain
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B G : Type} [Group G]

theorem norm_map (H : Subgroup G) [Fintype H]
    (f : FreeChain A G →ₗ[ℤ] FreeChain B G)
    (hf : ∀ (h : H) c, f (chainShift (h:G) c) = chainShift (h:G) (f c))
    (c : FreeChain A G) : subgroupNorm H (f c) = f (subgroupNorm H c) := by
  simp only [subgroupNorm,LinearMap.sum_apply,map_sum,LinearEquiv.coe_coe]
  simp only [hf]

theorem cyclic_chain_obstruction {A₀ A₁ A₂ : Type} (H : Subgroup G)
    [Fintype H] [IsCyclic H] (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (b₁ : FreeChain A₁ G →ₗ[ℤ] FreeChain A₀ G)
    (b₂ : FreeChain A₂ G →ₗ[ℤ] FreeChain A₁ G)
    (h₁ : ∀ (h : H) c, b₁ (chainShift (h:G) c) = chainShift (h:G) (b₁ c))
    (h₂ : ∀ (h : H) c, b₂ (chainShift (h:G) c) = chainShift (h:G) (b₂ c))
    (hbb : ∀ c, b₁ (b₂ c) = 0)
    (haug : ∀ c, augmentation (b₁ c) = 0)
    (v : FreeChain A₀ G) (hv : augmentation v = 1)
    (c : FreeChain A₁ G) (hc : b₁ c = chainShift (g:G) v - v)
    (D : FreeChain A₂ G) (hD : b₂ D = subgroupNorm H c)
    (hDi : chainShift (g:G) D = D) : (g:G) = 1 := by
  obtain ⟨B,hB⟩ := invariant_is_norm H g hg D hDi
  have hz : subgroupNorm H (c - b₂ B) = 0 := by
    rw [map_sub,norm_map H b₂ h₂,hB,← hD,sub_self]
  obtain ⟨E,hE⟩ := norm_zero_is_difference H g hg (c-b₂ B) hz
  have hi : chainShift (g:G) (v - b₁ E) = v - b₁ E := by
    have he := congrArg b₁ hE
    rw [map_sub,h₁,map_sub,hbb,sub_zero,hc] at he
    rw [map_sub]
    rw [sub_eq_iff_eq_add.mp he]
    abel
  obtain ⟨w,hw⟩ := invariant_is_norm H g hg (v-b₁ E) hi
  have ha : (Fintype.card H : ℤ) * augmentation w = 1 := by
    rw [← augmentation_norm,hw,map_sub,hv,haug,sub_zero]
  have hcard : Fintype.card H = 1 := by
    have hd : (Fintype.card H : ℤ) ∣ 1 := ⟨augmentation w,ha.symm⟩
    have := Int.natCast_nonneg (Fintype.card H)
    have hpm := Int.eq_one_or_neg_one_of_mul_eq_one ha
    omega
  have : Subsingleton H := Fintype.card_le_one_iff_subsingleton.mp (hcard.le)
  exact congrArg (fun h : H => (h:G)) (Subsingleton.elim g 1)

end Release075.FreeChain

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.FreeChain
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.FreeChain.cyclic_chain_obstruction := @_root_.OAI.Release075.FreeChain.cyclic_chain_obstruction
