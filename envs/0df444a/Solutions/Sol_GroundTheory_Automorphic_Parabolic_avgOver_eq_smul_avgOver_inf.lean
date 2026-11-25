-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_eq_smul_avgOver_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:28.405514+00:00
-- url     : https://prove2.me/submissions/aa3bb62f-4432-4f4c-8185-54877571ca6a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_zero_of_forall
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_ne_zero_trans
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cosetIncl_injective
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_inf_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_avgOver
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_avgSub
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_le_rightStab_avgOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {A : Subgroup G}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {K K' : Subgroup G} {h : G → W} (hKK' : K ≤ K')
    (hf : AvgFinite K h) (hK : K.relIndex K' ≠ 0)
    (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k) :
    avgOver K' h 1 = (((K.relIndex K' : ℂ)⁻¹ * ((K ⊓ A).relIndex (K' ⊓ A) : ℂ))) •
      avgOver (K' ⊓ A) (avgOver K h) 1 := by
  classical
  set g := avgOver K h with hg
  have hgK : K ≤ rightStab g := le_rightStab_avgOver hf
  have hf' : AvgFinite K' h := relIndex_ne_zero_trans hKK' hf hK
  rw [← avgOver_avgOver hKK' hf']

  set S := K.subgroupOf K'
  set T := (K ⊓ A).subgroupOf (K' ⊓ A)
  have hT : T.index ≠ 0 := relIndex_inf_ne_zero hK
  have : S.FiniteIndex := ⟨hK⟩
  have : T.FiniteIndex := ⟨hT⟩
  let _ := Fintype.ofFinite (K' ⧸ S)
  let _ := Fintype.ofFinite ((K' ⊓ A : Subgroup G) ⧸ T)
  have hSle : S ≤ (rightStab g).subgroupOf K' := fun k hk => hgK hk
  have hTle : T ≤ (rightStab g).subgroupOf (K' ⊓ A) := fun k hk =>
    hgK (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
  rw [avgOver_eq_avgSub hSle hK, avgOver_eq_avgSub hTle hT, avgSub_eq_sum, avgSub_eq_sum,
    smul_smul]

  have hzero : ∀ q : K' ⧸ S, q ∉ Set.range (cosetIncl A (K := K) (K' := K')) →
      g (1 * ((Quotient.out q : K') : G)) = 0 := by
    intro q hq
    rw [one_mul]
    apply avgOver_eq_zero_of_forall
    intro k hk
    by_contra hne
    obtain ⟨a, ha, k₀, hk₀, hy⟩ := hsupp _ (K'.mul_mem (Quotient.out q).2 (hKK' hk)) hne
    apply hq
    have haK' : a ∈ K' := by
      have : a = (Quotient.out q : K') * k * k₀⁻¹ := by rw [hy]; group
      rw [this]
      exact K'.mul_mem (K'.mul_mem (Quotient.out q).2 (hKK' hk)) (K'.inv_mem (hKK' hk₀))
    refine ⟨QuotientGroup.mk ⟨a, Subgroup.mem_inf.2 ⟨haK', ha⟩⟩, ?_⟩
    unfold cosetIncl
    rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul T ⟨a, Subgroup.mem_inf.2 ⟨haK', ha⟩⟩
    have hsK : ((s : (K' ⊓ A : Subgroup G)) : G) ∈ K :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 s.2)).1
    rw [hs]
    show ((a * ((s : (K' ⊓ A : Subgroup G)) : G))⁻¹ * (Quotient.out q : K') : G) ∈ K
    have : ((a * ((s : (K' ⊓ A : Subgroup G)) : G))⁻¹ * (Quotient.out q : K') : G) =
        ((s : (K' ⊓ A : Subgroup G)) : G)⁻¹ * (k * k₀⁻¹)⁻¹ := by
      rw [show ((Quotient.out q : K') : G) = a * k₀ * k⁻¹ by rw [← hy]; group]
      group
    rw [this]
    exact K.mul_mem (K.inv_mem hsK) (K.inv_mem (K.mul_mem hk (K.inv_mem hk₀)))

  have hval : ∀ r : (K' ⊓ A : Subgroup G) ⧸ T,
      g (1 * ((Quotient.out (cosetIncl A (K := K) (K' := K') r) : K') : G)) =
        g (1 * ((Quotient.out r : (K' ⊓ A : Subgroup G)) : G)) := by
    intro r
    unfold cosetIncl
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S
      (Subgroup.inclusion (inf_le_left : K' ⊓ A ≤ K') (Quotient.out r))
    rw [hs]
    simp only [one_mul, Subgroup.coe_mul, Subgroup.coe_inclusion]
    exact hgK (Subgroup.mem_subgroupOf.1 s.2) _
  have hsum : ∑ q : K' ⧸ S, g (1 * ((Quotient.out q : K') : G)) =
      ∑ r : (K' ⊓ A : Subgroup G) ⧸ T, g (1 * ((Quotient.out r : (K' ⊓ A : Subgroup G)) : G)) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (cosetIncl A (K := K) (K' := K'))))
      (fun q _ hq => hzero q (by
        rintro ⟨r, rfl⟩
        exact hq (Finset.mem_image_of_mem _ (Finset.mem_univ r)))),
      Finset.sum_image (fun r _ r' _ h => cosetIncl_injective h)]
    exact Finset.sum_congr rfl fun r _ => hval r
  rw [hsum]
  congr 1
  show (S.index : ℂ)⁻¹ = ((K.relIndex K' : ℂ)⁻¹ * ((K ⊓ A).relIndex (K' ⊓ A) : ℂ)) * (T.index : ℂ)⁻¹
  have hT' : (T.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT
  rw [mul_assoc, show ((K ⊓ A).relIndex (K' ⊓ A) : ℂ) = T.index from rfl, mul_inv_cancel₀ hT',
    mul_one]
  rfl
end GroundTheory.Automorphic.Parabolic
