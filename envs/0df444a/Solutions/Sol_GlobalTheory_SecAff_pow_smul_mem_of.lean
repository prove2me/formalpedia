-- Prove2me | solution 1 for GlobalTheory.SecAff.pow_smul_mem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:52.457091+00:00
-- url     : https://prove2.me/submissions/821c2ae8-a3f4-410b-9da4-0faddd4c93d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
namespace GlobalTheory.SecAff
theorem _root_.solution {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] {σ : R →+* R'} (F : M →ₛₗ[σ] M') (r : R)
    (h₁ : ∀ c : R', ∃ (n : ℕ) (d : R), σ d = σ r ^ n * c)
    (h₂ : ∀ s : M, F s = 0 → ∃ n : ℕ, r ^ n • s = 0) (W : Submodule R M) (s : M)
    (hs : F s ∈ Submodule.span R' (F '' W)) : ∃ N : ℕ, r ^ N • s ∈ W := by
  have key : ∀ t ∈ Submodule.span R' (F '' W), ∃ (N : ℕ), ∃ w ∈ W, F w = σ r ^ N • t := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx => obtain ⟨w, hw, rfl⟩ := hx; exact ⟨0, w, hw, by rw [pow_zero, _root_.one_smul]⟩
    | zero => exact ⟨0, 0, W.zero_mem, by rw [map_zero, smul_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, u, hu, eu⟩ := hx
      obtain ⟨n, v, hv, ev⟩ := hy
      refine ⟨m + n, r ^ n • u + r ^ m • v, W.add_mem (W.smul_mem _ hu) (W.smul_mem _ hv), ?_⟩
      rw [map_add, map_smulₛₗ, map_smulₛₗ, eu, ev, map_pow, map_pow, smul_smul, smul_smul,
        ← pow_add, ← pow_add, add_comm n m, smul_add]
    | smul c x _ hx =>
      obtain ⟨m, u, hu, eu⟩ := hx
      obtain ⟨n, d, hd⟩ := h₁ c
      refine ⟨m + n, d • u, W.smul_mem _ hu, ?_⟩
      rw [map_smulₛₗ, eu, hd, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨N, w, hw, e⟩ := key _ hs
  obtain ⟨K, hK⟩ := h₂ (r ^ N • s - w) (by rw [map_sub, map_smulₛₗ, map_pow, e, sub_self])
  refine ⟨K + N, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hK
  rw [hK]
  exact W.smul_mem _ hw
end GlobalTheory.SecAff
