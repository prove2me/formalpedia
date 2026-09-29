-- Prove2me | solution 1 for HeckeCohomology.exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/df7b04a5-91ef-5c23-8271-60e755f8175e

import Mathlib
import Definitions.Def_GroupCohomology_TransferHecke
import Theorems.Thm_HeckeCohomology_heckeH1_natural
import Theorems.Thm_HeckeCohomology_heckeH1_delta0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact

set_option autoImplicit false

open groupCohomology CategoryTheory in

theorem solution
    {κ Γ : Type} [Field κ] [Group Γ]
    {X : CategoryTheory.ShortComplex (Rep κ Γ)} (hX : X.ShortExact)
    {ι : Type} (S₁ S₂ : ι → Subgroup Γ) (c : ∀ i, ↥(S₂ i) →* ↥(S₁ i)) [∀ i, (S₂ i).FiniteIndex]
    (φ₁ : ∀ i, X.X₁ →ₗ[κ] X.X₁) (hφ₁ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₁ (φ₁ i))
    (φ₂ : ∀ i, X.X₂ →ₗ[κ] X.X₂) (hφ₂ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i))
    (φ₃ : ∀ i, X.X₃ →ₗ[κ] X.X₃) (hφ₃ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i))
    (hf : ∀ (i : ι) (a : X.X₁), X.f.hom (φ₁ i a) = φ₂ i (X.f.hom a))
    (hg : ∀ (i : ι) (b : X.X₂), X.g.hom (φ₂ i b) = φ₃ i (X.g.hom b))
    (cc : ι → κ)
    (hinv : ∀ (i : ι) (z : X.X₃.ρ.invariants),
      HeckeCohomology.heckeInv (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i) (hφ₃ i) z = cc i • z)
    (lam : ι → κ)
    (hocc : ∃ x : groupCohomology.H1 X.X₁, x ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₁ (φ₁ i) (hφ₁ i) x = lam i • x) :
    (∃ y : groupCohomology.H1 X.X₂, y ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i) y = lam i • y) ∨
    ∀ i : ι, lam i = cc i := by
  classical
  obtain ⟨x, hx0, hx⟩ := hocc
  let f1 : H1 X.X₁ →ₗ[κ] H1 X.X₂ := (map (MonoidHom.id _) X.f 1).hom
  by_cases hy : f1 x = 0
  ·
    right
    have hex := (mapShortComplex₁_exact hX (rfl : 0 + 1 = 1)).moduleCat_range_eq_ker
    have hy' : (mapShortComplex₁ hX (rfl : 0 + 1 = 1)).g.hom x = 0 := hy
    have hxker := LinearMap.mem_ker.mpr hy'
    rw [← hex] at hxker
    obtain ⟨w, hw⟩ := hxker

    let z : X.X₃.ρ.invariants := (H0Iso X.X₃).hom w
    have hwz : (H0Iso X.X₃).inv z = w := by
      change ((H0Iso X.X₃).hom ≫ (H0Iso X.X₃).inv) w = w
      rw [Iso.hom_inv_id]; rfl
    have hxδ : x = (δ hX 0 1 rfl) ((H0Iso X.X₃).inv z) := by rw [hwz]; exact hw.symm
    intro i
    have h1 := HeckeCohomology.heckeH1_delta0 (S₁ i) (S₂ i) (c i) hX (φ₁ i) (hφ₁ i) (φ₂ i) (hφ₂ i) (φ₃ i) (hφ₃ i)
      (hf i) (hg i) z
    rw [hinv i z, map_smul, map_smul, ← hxδ, hx i] at h1

    by_contra hne
    apply hx0
    have h2 : (lam i - cc i) • x = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  · left
    refine ⟨f1 x, hy, fun i => ?_⟩
    have hn := HeckeCohomology.heckeH1_natural (S₁ i) (S₂ i) (c i) X.f (φ₁ i) (hφ₁ i) (φ₂ i) (hφ₂ i) (hf i) x
    rw [hx i, map_smul] at hn
    exact hn

end S_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact
end P2MW
export P2MW.S_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact (solution)
