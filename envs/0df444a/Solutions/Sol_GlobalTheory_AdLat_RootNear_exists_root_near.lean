-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.exists_root_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:41:29.20263+00:00
-- url     : https://prove2.me/submissions/4e318949-fb58-404d-b7a5-e1e0934be593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear
import Theorems.Thm_GlobalTheory_AdLat_RootNear_finite_near
import Theorems.Thm_GlobalTheory_AdLat_RootNear_infinite_near
import Theorems.Thm_GlobalTheory_AdLat_RootNear_units_nhds
import Theorems.Thm_GlobalTheory_AdLat_RootNear_map_sg
import Theorems.Thm_GlobalTheory_T_exists_adeleRing_tensor_equiv_infinite_prod_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∀ W ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∃ N ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∀ u ∈ N, (u : AdeleRing (𝓞 F) F ⊗[F] E) * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ W, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c x := by
  intro F E _ _ _ _ _ c h2 hc hP
  letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  intro W hW
  obtain ⟨V, hV, hVW⟩ := units_nhds W hW
  obtain ⟨e, he, hec, hes⟩ := GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite F E
  have hs1 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).1 = sg _ c (e z).1 := fun z => by
    rw [(he _).1, (he _).1]
    exact map_sg F E c _ z
  have hs2 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).2 = sg _ c (e z).2 := fun z => by
    rw [(he _).2, (he _).2]
    exact map_sg F E c _ z
  have hV' : e.symm ⁻¹' V ∈ 𝓝 (1 : (InfiniteAdeleRing F ⊗[F] E) × RA F E) :=
    hes.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hV'
  have ht : Filter.Tendsto (fun u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ => e u) (𝓝 1) (𝓝 1) := by
    have := (hec.comp Units.continuous_val).tendsto 1
    simpa [Function.comp_def] using this
  have ht1 := (continuous_fst.tendsto _).comp ht
  have ht2 := (continuous_snd.tendsto _).comp ht
  refine ⟨_, Filter.inter_mem (ht1 (infinite_near F E c V₁ h₁)) (ht2 (finite_near F E c h2 hc hP V₂ h₂)), ?_⟩
  rintro u ⟨hu1, hu2⟩ hu
  have heu := congrArg e hu
  rw [map_mul, map_one] at heu
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hr₁⟩ := hu1 (by
    have := congrArg Prod.fst heu
    rw [Prod.fst_mul, hs1] at this
    exact this)
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂, hr₂⟩ := hu2 (by
    have := congrArg Prod.snd heu
    rw [Prod.snd_mul, hs2] at this
    exact this)
  have hxy : e.symm (x₁, x₂) * e.symm (y₁, y₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hxy₁, hxy₂]
    exact map_one _
  refine ⟨⟨e.symm (x₁, x₂), e.symm (y₁, y₂), hxy, by rw [mul_comm]; exact hxy⟩,
    hVW _ (hsub (⟨hx₁, hx₂⟩ : (x₁, x₂) ∈ V₁ ×ˢ V₂)) (hsub (⟨hy₁, hy₂⟩ : (y₁, y₂) ∈ V₁ ×ˢ V₂)), ?_⟩
  apply e.injective
  change e (e.symm (x₁, x₂)) = e (u * sg (AdeleRing (𝓞 F) F) c (e.symm (x₁, x₂)))
  rw [map_mul]
  apply Prod.ext
  · rw [Prod.fst_mul, hs1, e.apply_symm_apply]
    exact hr₁
  · rw [Prod.snd_mul, hs2, e.apply_symm_apply]
    exact hr₂
end GlobalTheory.AdLat.RootNear
