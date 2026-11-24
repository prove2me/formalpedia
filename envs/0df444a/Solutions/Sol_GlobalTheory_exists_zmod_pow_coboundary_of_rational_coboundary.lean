-- Prove2me | solution 1 for GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:49:00.133797+00:00
-- url     : https://prove2.me/submissions/1236e97c-f4cf-4378-b80b-ea8609796eed

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsZmodPowCoboundaryOfRationalCoboundary
import Theorems.Thm_GlobalTheory_exists_addHom_zmod_pow_extend
import Theorems.Thm_GlobalTheory_addHom_zmod_pow_algebraMap_mul
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (ε : Γ → ℤ_[l]) (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L] [TopologicalSpace L] [IsTopologicalRing L] (ι : O →+* L), Function.Injective ι → IsOpen (Set.range ι) → (l : L) ≠ 0 → (∀ x : L, ∃ n : ℕ, (l : L) ^ n * x ∈ Set.range ι) → ∀ (β : O →+ ZMod (l ^ 1)) (z : Γ → Γ → O) (f : Γ → L), Continuous f → (∀ g h, ι (z g h) = ι (algebraMap ℤ_[l] O (ε g)) * f h - f (g * h) + f g) → ∃ (n : ℕ) (a : Γ → ZMod (l ^ (n + 1))), Continuous a ∧ ∀ g h, PadicInt.toZModPow (n + 1) (ε g) * a h - a (g * h) + a g = ((l ^ n * (β (z g h)).val : ℕ) : ZMod (l ^ (n + 1))) := by
  intro Γ _ _ _ l _ ε O L _ _ _ _ _ ι hι hopen hl hcov β z f hf hz

  have hstep : ∀ k x, (l : L) ^ k * x ∈ Set.range ι → (l : L) ^ (k + 1) * x ∈ Set.range ι := by
    rintro k x ⟨o, ho⟩
    exact ⟨(l : O) * o, by rw [map_mul, map_natCast, ho, pow_succ]; ring⟩
  have hmono : Monotone (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι}) :=
    monotone_nat_of_le_succ (fun k x hx => hstep k x hx)
  obtain ⟨N, hN⟩ := (isCompact_range hf).elim_directed_cover
    (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι})
    (fun k => hopen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono.directed_le
  have hN' : ∀ g, ∃ o : O, ι o = (l : L) ^ N * f g := fun g => hN ⟨g, rfl⟩
  choose F hF using hN'
  have hlN : ∀ k, (l : L) ^ k ≠ 0 := fun k => pow_ne_zero _ hl
  have hinjO : Function.Injective (fun o : O => (l : O) ^ N * o) := by
    intro a b hab
    apply hι
    have := congrArg ι hab
    simp only [map_mul, map_pow, map_natCast] at this
    exact mul_left_cancel₀ (hlN N) this
  obtain ⟨A, hA⟩ := exists_addHom_zmod_pow_extend O l N hinjO β

  have hrel : ∀ g h, (l : O) ^ N * z g h
      = algebraMap ℤ_[l] O (ε g) * F h - F (g * h) + F g := by
    intro g h
    apply hι
    rw [map_mul, map_pow, map_natCast, hz, map_add, map_sub, map_mul, hF, hF, hF]
    ring
  have hkill : ∀ x : O, A ((l : O) ^ (N + 1) * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨N, fun g => A (F g), ?_, ?_⟩
  ·
    refine ((IsLocallyConstant.iff_eventually_eq _).mpr fun g₁ => ?_).continuous
    have hPo : IsOpen {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} :=
      hopen.preimage (continuous_const.mul ((continuous_const.mul hf).sub continuous_const))
    have hmem : g₁ ∈ {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} := ⟨0, by simp⟩
    filter_upwards [hPo.mem_nhds hmem] with g hg
    obtain ⟨o, ho⟩ := hg
    have hFg : F g = F g₁ + (l : O) ^ (N + 1) * o := by
      apply hι
      rw [map_add, map_mul, map_pow, map_natCast, ho, mul_inv_cancel_left₀ (hlN _), hF, hF]
      ring
    show A (F g) = A (F g₁)
    rw [hFg, map_add, hkill, add_zero]
  · intro g h
    rw [← addHom_zmod_pow_algebraMap_mul O l (N + 1) A (ε g) (F h), ← map_sub, ← map_add,
      ← hrel, hA]
end GlobalTheory
