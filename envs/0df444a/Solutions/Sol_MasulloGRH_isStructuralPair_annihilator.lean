-- Prove2me | solution 1 for MasulloGRH.isStructuralPair_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:32:13.688188+00:00
-- url     : https://prove2.me/submissions/b2f417ce-33f3-47f3-a9c8-6f48a2c7643b

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_LCAGroup_Annihilator
import Theorems.Thm_LCAGroup_pontryagin_duality

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_isStructuralPair_annihilator

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The annihilator of a subgroup is closed in the Pontryagin dual. -/
theorem isClosed_annihilator (H : Subgroup G) :
    IsClosed (LCAGroup.annihilator H : Set (PontryaginDual G)) := by
  have hset : (LCAGroup.annihilator H : Set (PontryaginDual G)) =
      ⋂ x ∈ H, {χ : PontryaginDual G | χ x = 1} := by
    ext χ
    simp only [SetLike.mem_coe, LCAGroup.mem_annihilator_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  refine isClosed_biInter fun x _ => ?_
  have hc : Continuous fun χ : PontryaginDual G => χ x := by
    have := (continuous_eval_const (F := C(G, Circle)) x).comp
      (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).continuous
    exact this
  exact isClosed_eq hc continuous_const

/-- Characters trivial on an open subgroup `H` separate the points outside `H`. -/
theorem exists_mem_annihilator_ne_one (H : Subgroup G) (hH : IsOpen (H : Set G))
    (x : G) (hx : x ∉ H) :
    ∃ χ ∈ LCAGroup.annihilator H, χ x ≠ 1 := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality (G ⧸ H)
  have hne : ((x : G ⧸ H)) ≠ 1 := by
    intro h1
    exact hx ((QuotientGroup.eq_one_iff x).mp h1)
  have hne' : e (x : G ⧸ H) ≠ 1 := by
    intro h1
    apply hne
    apply e.injective
    rw [h1, map_one]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : PontryaginDual (G ⧸ H), ψ (x : G ⧸ H) ≠ 1 := by
    by_contra hcon
    apply hne'
    refine PontryaginDual.ext fun ψ => ?_
    rw [he, PontryaginDual.one_apply]
    by_contra h2
    exact hcon ⟨ψ, h2⟩
  let mk : G →ₜ* G ⧸ H :=
    ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  refine ⟨ψ.comp mk, ?_, ?_⟩
  · intro y hy
    show ψ (y : G ⧸ H) = 1
    rw [(QuotientGroup.eq_one_iff y).mpr hy, map_one]
  · exact hψ

end Sol_MasulloGRH_isStructuralPair_annihilator

open MasulloGRH Sol_MasulloGRH_isStructuralPair_annihilator in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ k : Subgroup G) (h : IsStructuralPair Γ k) :
    IsStructuralPair (LCAGroup.annihilator k) (LCAGroup.annihilator Γ) := by
  obtain ⟨hΓo, ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hUcl⟩, ⟨_hkc, hko, ⟨A, hA, hAcg⟩⟩, hkΓ⟩ := h
  have hAeq : A = LCAGroup.annihilator k := SetLike.coe_injective hA
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
  -- the annihilator of `Γ^⊥` in the bidual is the image of `Γ`
  have hann : MasulloGRH.annihilator (LCAGroup.annihilator Γ) =
      ((Γ.map (e : G →* PontryaginDual (PontryaginDual G))) :
        Set (PontryaginDual (PontryaginDual G))) := by
    ext ξ
    constructor
    · intro hξ
      refine ⟨e.symm ξ, ?_, by simp⟩
      by_contra hx
      obtain ⟨χ, hχ, hχx⟩ := exists_mem_annihilator_ne_one Γ hΓo (e.symm ξ) hx
      apply hχx
      have h1 := hξ χ hχ
      rw [← he (e.symm ξ) χ, ContinuousMulEquiv.apply_symm_apply]
      exact h1
    · rintro ⟨x, hx, rfl⟩ χ hχ
      show e x χ = 1
      rw [he]
      exact hχ x hx
  have himg : ((Γ.map (e : G →* PontryaginDual (PontryaginDual G))) :
      Set (PontryaginDual (PontryaginDual G))) = e '' (Γ : Set G) := by
    rw [Subgroup.coe_map]
    rfl
  refine ⟨?_, ?_, ⟨isClosed_annihilator Γ, ?_, ?_⟩, ?_⟩
  · exact hko
  · rw [← hAeq]
    exact hAcg
  · rw [hann, himg]
    exact e.toHomeomorph.isOpenMap _ hΓo
  · refine ⟨Γ.map (e : G →* PontryaginDual (PontryaginDual G)), hann.symm, ?_⟩
    refine ⟨e '' U, hUc.image e.continuous, ?_, ⟨e '' V, ?_, ?_⟩, ?_⟩
    · rw [himg]
      exact Set.image_mono hUΓ
    · have : e '' V ∈ 𝓝 (e 1) := e.toHomeomorph.isOpenMap.image_mem_nhds hV
      rwa [map_one] at this
    · rw [himg, ← Set.image_inter e.injective]
      exact Set.image_mono hVU
    · have : ((e : G →* PontryaginDual (PontryaginDual G)) : G → _) '' U = e '' U := rfl
      rw [← this, ← MonoidHom.map_closure, hUcl]
  · intro χ hχ x hx
    exact hχ x (hkΓ hx)
