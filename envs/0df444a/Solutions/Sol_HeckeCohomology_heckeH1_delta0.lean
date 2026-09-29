-- Prove2me | solution 1 for HeckeCohomology.heckeH1_delta0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8eca89c1-75b8-5245-86cb-2d0bdb99fb57

import Definitions.Def_GroupCohomology_TransferHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_heckeH1_delta0

set_option autoImplicit false

namespace TWDeltaAux

open CategoryTheory groupCohomology HeckeCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁)

theorem d₀₁_apply_apply' (A : Rep k Γ) (a : A) (g : Γ) :
    (d₀₁ A) a g = A.ρ g a - a := rfl

variable [S₂.FiniteIndex]
  {X : ShortComplex (Rep k Γ)} (hX : X.ShortExact)
  (φ₁ : X.X₁ →ₗ[k] X.X₁) (hφ₁ : IsTwist S₁ S₂ c X.X₁ φ₁)
  (φ₂ : X.X₂ →ₗ[k] X.X₂) (hφ₂ : IsTwist S₁ S₂ c X.X₂ φ₂)
  (φ₃ : X.X₃ →ₗ[k] X.X₃) (hφ₃ : IsTwist S₁ S₂ c X.X₃ φ₃)
  (hf : ∀ a : X.X₁, X.f.hom (φ₁ a) = φ₂ (X.f.hom a))
  (hg : ∀ b : X.X₂, X.g.hom (φ₂ b) = φ₃ (X.g.hom b))

include hφ₂ hf hg in

theorem heckeH1_δ₀_apply (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : Γ → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) :
    heckeH1 S₁ S₂ c X.X₁ φ₁ hφ₁ (δ hX 0 1 rfl ((H0Iso X.X₃).inv z)) =
      δ hX 0 1 rfl ((H0Iso X.X₃).inv (heckeInv S₁ S₂ c X.X₃ φ₃ hφ₃ z)) := by
  have hy' : X.g.hom (norm0 S₂ X.X₂ φ₂ y) = (heckeInv S₁ S₂ c X.X₃ φ₃ hφ₃ z : X.X₃) := by
    rw [coe_heckeInv, norm0_apply, norm0_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Rep.hom_comm_apply, hg, hy]
  have hxpt : ∀ g : Γ, X.f.hom (x g) = X.X₂.ρ g y - y := fun g => congrFun hx g
  have hx' : X.f.hom ∘ ⇑(heckeZ1 S₁ S₂ c X.X₁ φ₁ hφ₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩) =
      d₀₁ X.X₂ (norm0 S₂ X.X₂ φ₂ y) := by
    funext γ
    rw [Function.comp_apply, d₀₁_apply_apply', norm0_apply, heckeZ1_apply, map_sum,
      ← congrFun (corFun_coboundary S₂ X.X₂ (φ₂ y)) γ]
    simp only [corFun]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Rep.hom_comm_apply, hf, cocycles₁.coe_mk, hxpt, map_sub, hφ₂]
  rw [δ₀_apply hX z y hy x hx, heckeH1_H1π,
    δ₀_apply hX (heckeInv S₁ S₂ c X.X₃ φ₃ hφ₃ z) (norm0 S₂ X.X₂ φ₂ y) hy' _ hx']
  exact congrArg _ (cocycles₁_ext fun _ => rfl)

end TWDeltaAux

open CategoryTheory groupCohomology HeckeCohomology in
theorem solution {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) [S₂.FiniteIndex]
    {X : ShortComplex (Rep k Γ)} (hX : X.ShortExact)
    (φ₁ : X.X₁ →ₗ[k] X.X₁) (hφ₁ : IsTwist S₁ S₂ c X.X₁ φ₁)
    (φ₂ : X.X₂ →ₗ[k] X.X₂) (hφ₂ : IsTwist S₁ S₂ c X.X₂ φ₂)
    (φ₃ : X.X₃ →ₗ[k] X.X₃) (hφ₃ : IsTwist S₁ S₂ c X.X₃ φ₃)
    (hf : ∀ a : X.X₁, X.f.hom (φ₁ a) = φ₂ (X.f.hom a))
    (hg : ∀ b : X.X₂, X.g.hom (φ₂ b) = φ₃ (X.g.hom b))
    (z : X.X₃.ρ.invariants) :
    heckeH1 S₁ S₂ c X.X₁ φ₁ hφ₁ (δ hX 0 1 rfl ((H0Iso X.X₃).inv z)) =
      δ hX 0 1 rfl ((H0Iso X.X₃).inv (heckeInv S₁ S₂ c X.X₃ φ₃ hφ₃ z)) := by
  obtain ⟨y, hy⟩ := (Rep.epi_iff_surjective X.g).1 hX.epi_g (z : X.X₃)
  have hrange : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k Γ) (ModuleCat k))).moduleCat_range_eq_ker
  have hmem : ∀ g : Γ, ∃ u : X.X₁, X.f.hom u = X.X₂.ρ g y - y := fun g => by
    have hk : X.X₂.ρ g y - y ∈ LinearMap.range X.f.hom.toLinearMap := by
      rw [hrange, LinearMap.mem_ker]
      show X.g.hom (X.X₂.ρ g y - y) = 0
      rw [map_sub, Rep.hom_comm_apply, hy, (X.X₃.ρ.mem_invariants _).1 z.2 g, sub_self]
    exact LinearMap.mem_range.1 hk
  choose x hx using hmem
  exact TWDeltaAux.heckeH1_δ₀_apply S₁ S₂ c hX φ₁ hφ₁ φ₂ hφ₂ φ₃ hφ₃ hf hg z y hy x
    (funext fun g => hx g)

end S_HeckeCohomology_heckeH1_delta0
end P2MW
export P2MW.S_HeckeCohomology_heckeH1_delta0 (solution)
