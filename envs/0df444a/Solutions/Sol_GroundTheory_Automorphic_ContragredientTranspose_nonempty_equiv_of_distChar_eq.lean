-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.nonempty_equiv_of_distChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:56:11.854427+00:00
-- url     : https://prove2.me/submissions/46b5f149-6cd9-4779-99a3-26998c47fb78

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_isSemisimpleModule_prod
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_levelLin_one
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_level
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isSimpleModule_fixedVectors
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_nonempty_equiv_of_fixedVectors_equiv
import Theorems.Thm_GroundTheory_Automorphic_exists_ne_zero_of_isIrreducible
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_forall_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
open HeckeAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : IsAdmissible ρ)
    (hσ : IsAdmissible σ) [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : distChar μ ρ hρ = distChar μ σ hσ) : Nonempty (ρ.Equiv σ) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 hρ.1 v
  have hVK : fixedVectors ρ K ≠ ⊥ := fun hb => hv (by
    have : v ∈ (⊥ : Submodule ℂ V) := hb ▸ hvK
    simpa using this)
  have := hρ.2 K hKc hKo
  have := hσ.2 K hKc hKo
  set H := HeckeAlgebraLevel μ K hKc hKo
  have htr : ∀ r : H, LinearMap.trace ℂ (fixedVectors ρ K) (levelLin hKc hKo ρ r) =
      LinearMap.trace ℂ (fixedVectors σ K) (levelLin hKc hKo σ r) := fun r => by
    rw [← distChar_level hKc hKo hρ r, ← distChar_level hKc hKo hσ r, h]
  have hdim : Module.finrank ℂ (fixedVectors ρ K) = Module.finrank ℂ (fixedVectors σ K) := by
    have := htr 1
    rw [levelLin_one, levelLin_one, LinearMap.trace_id, LinearMap.trace_id] at this
    exact_mod_cast this
  have hpos : 0 < Module.finrank ℂ (fixedVectors ρ K) :=
    Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hVK)
  have hWK : fixedVectors σ K ≠ ⊥ := by
    rw [← Submodule.nontrivial_iff_ne_bot, ← Module.finrank_pos_iff (R := ℂ), ← hdim]
    exact hpos
  have := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ.1 hVK
  have := isSimpleModule_fixedVectors (μ := μ) hKc hKo hσ.1 hWK
  by_contra hne
  have hiso : ¬ Nonempty (fixedVectors ρ K ≃ₗ[H] fixedVectors σ K) := fun ⟨e⟩ =>
    hne (nonempty_equiv_of_fixedVectors_equiv hKc hKo hρ.1 hσ.1 hVK e)
  have h12 : ∀ φ : fixedVectors ρ K →ₗ[H] fixedVectors σ K, φ = 0 := fun φ =>
    (LinearMap.bijective_or_eq_zero φ).resolve_left fun hb => hiso ⟨LinearEquiv.ofBijective φ hb⟩
  have h21 : ∀ φ : fixedVectors σ K →ₗ[H] fixedVectors ρ K, φ = 0 := fun φ =>
    (LinearMap.bijective_or_eq_zero φ).resolve_left fun hb =>
      hiso ⟨(LinearEquiv.ofBijective φ hb).symm⟩
  have : IsSemisimpleModule H (fixedVectors ρ K × fixedVectors σ K) := isSemisimpleModule_prod

  let fE : Module.End (Module.End H (fixedVectors ρ K × fixedVectors σ K))
      (fixedVectors ρ K × fixedVectors σ K) :=
    { toFun := fun m => (m.1, 0)
      map_add' := fun m m' => by simp
      map_smul' := fun φ m => by
        rw [Module.End.smul_def, RingHom.id_apply, Module.End.smul_def]
        have hC : (φ (m.1, 0)).2 = 0 := by
          have := h12 (LinearMap.snd H _ _ ∘ₗ φ ∘ₗ LinearMap.inl H _ _)
          exact LinearMap.congr_fun this m.1
        have hB : (φ (0, m.2)).1 = 0 := by
          have := h21 (LinearMap.fst H _ _ ∘ₗ φ ∘ₗ LinearMap.inr H _ _)
          exact LinearMap.congr_fun this m.2
        have hm : m = (m.1, 0) + (0, m.2) := by simp
        refine Prod.ext ?_ hC.symm
        conv_lhs => rw [hm]
        rw [map_add, Prod.fst_add, hB, add_zero] }
  let b := Module.finBasis ℂ (fixedVectors ρ K × fixedVectors σ K)
  obtain ⟨r, hr⟩ := jacobson_density fE (Finset.univ.image b)

  let Lr : (fixedVectors ρ K × fixedVectors σ K) →ₗ[ℂ] (fixedVectors ρ K × fixedVectors σ K) :=
    (levelLin hKc hKo ρ r).prodMap (levelLin hKc hKo σ r)
  have hL : Lr = (LinearMap.inl ℂ _ _) ∘ₗ (LinearMap.fst ℂ _ _) := by
    refine b.ext fun i => ?_
    have := hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact this.symm
  have h1 : levelLin hKc hKo ρ r = LinearMap.id := LinearMap.ext fun x => by
    have := LinearMap.congr_fun hL (x, 0)
    exact congrArg Prod.fst this
  have h2 : levelLin hKc hKo σ r = 0 := LinearMap.ext fun y => by
    have := LinearMap.congr_fun hL (0, y)
    exact congrArg Prod.snd this
  have := htr r
  rw [h1, h2, LinearMap.trace_id, map_zero, Nat.cast_eq_zero] at this
  omega
end GroundTheory.Automorphic.ContragredientTranspose
