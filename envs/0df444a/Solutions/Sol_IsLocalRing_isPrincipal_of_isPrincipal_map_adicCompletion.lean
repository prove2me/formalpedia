-- Prove2me | solution 1 for IsLocalRing.isPrincipal_of_isPrincipal_map_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/10a86d9f-33f1-571b-890e-378e9f8f3161

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isPrincipal_of_isPrincipal_map_adicCompletion

set_option autoImplicit false

namespace C4sol
open IsLocalRing

theorem faithfullyFlat_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩

  have hm' : m = maximalIdeal R := (IsLocalRing.eq_maximalIdeal hm)
  subst hm'
  intro htop

  have hle : (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤
      LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := by
    have := AdicCompletion.pow_smul_top_le_ker_eval (I := maximalIdeal R) (M := R) 1
    simpa using this
  rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle

  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  rw [hle] at hsurj
  obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk 1)
  simp only [LinearMap.zero_apply] at hx
  have h1 : (1 : R) ∈ (maximalIdeal R) ^ 1 • (⊤ : Submodule R R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hx]
  rw [pow_one, Ideal.smul_eq_mul, Ideal.mul_top] at h1
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

theorem comap_map_adicCompletion_eq {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I := by
  haveI := faithfullyFlat_adicCompletion R
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

end C4sol

namespace C4a
open IsLocalRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

local notation "Rh" => AdicCompletion (maximalIdeal R) R
local notation "ι" => algebraMap R (AdicCompletion (maximalIdeal R) R)

theorem algebraMap_adicCompletion_injective : Function.Injective (ι) := by
  haveI : IsHausdorff (maximalIdeal R) R :=
    IsHausdorff.of_le_jacobson (maximalIdeal R) R (maximalIdeal_le_jacobson ⊥)
  intro a b h
  have := AdicCompletion.of_injective (maximalIdeal R) R
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at h
  exact this h

theorem isPrincipal_of_isPrincipal_map_adicCompletion' (I : Ideal R)
    (h : (I.map ι).IsPrincipal) : I.IsPrincipal := by
  classical
  obtain ⟨α, hα⟩ := h.principal
  change I.map ι = Ideal.span {α} at hα

  have hαmem : α ∈ Submodule.span (AdicCompletion (maximalIdeal R) R) ((ι) '' (I : Set R)) := by
    change α ∈ I.map ι
    rw [hα]; exact Ideal.mem_span_singleton_self α
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hαmem
  choose a ha using fun i => (g i).2

  have hmult : ∀ i, ∃ t : Rh, t * α = ι (a i) := fun i =>
    Ideal.mem_span_singleton'.mp (hα ▸ Ideal.mem_map_of_mem (ι) (ha i).1)
  choose t ht using hmult

  have happrox := fun i => AdicCompletion.exists_eq_algebraMap_add (maximalIdeal R)
    AdicCompletion.maximalIdeal_fg 1 (f i)
  choose c y hy hcy using happrox
  simp only [pow_one] at hy
  set z : Rh := ∑ i, f i * t i with hz
  have hzα : z * α = α := by
    rw [hz, Finset.sum_mul]
    conv_rhs => rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_assoc, ht i, (ha i).2]
  by_cases hzu : IsUnit z
  ·
    set a₀ : R := ∑ i, c i * a i with ha₀
    have ha₀I : a₀ ∈ I := I.sum_mem fun i _ => I.mul_mem_left _ (ha i).1
    set w : Rh := ∑ i, y i * t i with hw
    have hwmem : w ∈ (maximalIdeal R).map ι := Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hy i)
    have hιa₀ : ι a₀ = (z - w) * α := by
      rw [ha₀, map_sum, hz, hw, ← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← ht i, ← mul_assoc, ← sub_mul]
      congr 1
      rw [hcy i]; ring
    have hunit : IsUnit (z - w) := by
      rw [sub_eq_add_neg]
      exact AdicCompletion.isUnit_add_of_mem_map _ AdicCompletion.maximalIdeal_fg hzu (neg_mem hwmem)
    have hspan : (Ideal.span {a₀}).map ι = I.map ι := by
      rw [Ideal.map_span, Set.image_singleton, hα, hιa₀]
      exact Ideal.span_singleton_mul_left_unit hunit α
    refine ⟨⟨a₀, ?_⟩⟩
    change I = Ideal.span {a₀}
    rw [← C4sol.comap_map_adicCompletion_eq I, ← hspan, C4sol.comap_map_adicCompletion_eq]
  ·
    have h1z : IsUnit (1 - z) := isUnit_one_sub_self_of_mem_nonunits z hzu
    have hα0 : α = 0 := by
      have : (1 - z) * α = 0 := by rw [sub_mul, one_mul, hzα, sub_self]
      exact (h1z.mul_right_eq_zero).mp this
    refine ⟨⟨0, ?_⟩⟩
    change I = Ideal.span {(0 : R)}
    rw [Ideal.span_singleton_eq_bot.mpr rfl, ← C4sol.comap_map_adicCompletion_eq I, hα, hα0,
      Ideal.span_singleton_eq_bot.mpr rfl, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp algebraMap_adicCompletion_injective

end C4a

open IsLocalRing in
theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (h : (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).IsPrincipal) :
    I.IsPrincipal :=
  C4a.isPrincipal_of_isPrincipal_map_adicCompletion' I h

end S_IsLocalRing_isPrincipal_of_isPrincipal_map_adicCompletion
end P2MW
export P2MW.S_IsLocalRing_isPrincipal_of_isPrincipal_map_adicCompletion (solution)
