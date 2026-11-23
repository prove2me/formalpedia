-- Prove2me | solution 1 for GlobalTheory.PlaceModel.linearIndependent_wave
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:58.97928+00:00
-- url     : https://prove2.me/submissions/26c8e58e-3666-4499-927f-46fef5db0897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution (h : IsBichar χ) (hY : ∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → y ∈ L') :
    LinearIndependent ℂ fun i : (X ⧸ L.addSubgroupOf X) × (Y ⧸ L'.addSubgroupOf Y) =>
      wave χ L (i.1.out : X) (i.2.out : Y) := by
  classical

  let ψ : (Y ⧸ L'.addSubgroupOf Y) → (Multiplicative L →* ℂ) := fun d =>
    { toFun := fun u => χ ((Multiplicative.toAdd u : L) : G) ((d.out : Y) : G)
      map_one' := by simp [h.zero_left]
      map_mul' := fun u w => by simp [h.left] }
  have hψ : Function.Injective ψ := by
    intro d d' hdd
    have hval : ∀ u ∈ L, χ u ((d.out : Y) : G) = χ u ((d'.out : Y) : G) := fun u hu =>
      DFunLike.congr_fun hdd (Multiplicative.ofAdd (⟨u, hu⟩ : L))
    rw [← QuotientAddGroup.out_eq' d, ← QuotientAddGroup.out_eq' d', QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    refine hY _ (Y.add_mem (Y.neg_mem (d.out).2) (d'.out).2) fun u hu => ?_
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, h.right, ← hval u hu, ← h.right, neg_add_cancel,
      h.zero_right]
  have hind := (linearIndependent_monoidHom (Multiplicative L) ℂ).comp ψ hψ
  rw [linearIndependent_iff'] at hind ⊢
  intro s g hg i hi
  obtain ⟨a, c⟩ := i

  have hsupp : ∀ (b : X ⧸ L.addSubgroupOf X) (y u : G), u ∈ L →
      wave χ L ((b.out : X) : G) y (u - ((a.out : X) : G)) = if b = a then χ u y else 0 := by
    intro b y u hu
    simp only [wave]
    by_cases hb : b = a
    · subst hb
      simp [ind, hu]
    · rw [if_neg hb]
      have hn : u - ((a.out : X) : G) + ((b.out : X) : G) ∉ L := by
        intro hm
        apply hb
        rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
        have h2 := L.add_mem (L.neg_mem hm) hu
        convert h2 using 1
        abel
      simp [ind, hn]
  let T : Finset (Y ⧸ L'.addSubgroupOf Y) := (s.filter (fun i => i.1 = a)).image Prod.snd
  have hrel : ∑ d ∈ T, g (a, d) • ((fun f : Multiplicative L →* ℂ => (f : Multiplicative L → ℂ)) ∘ ψ) d
      = 0 := by
    funext u
    have e := congrFun hg (((Multiplicative.toAdd u : L) : G) - ((a.out : X) : G))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    rw [Finset.sum_image (fun i hi j hj hij => ?_)]
    · rw [Finset.sum_filter]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans e
      rw [hsupp i.1 _ _ (Multiplicative.toAdd u).2]
      by_cases h1 : i.1 = a
      · rw [if_pos h1, if_pos h1]
        obtain ⟨i1, i2⟩ := i
        simp only at h1
        subst h1
        rfl
      · rw [if_neg h1, if_neg h1, mul_zero]
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
      exact Prod.ext (hi.2.trans hj.2.symm) hij
  exact hind T (fun d => g (a, d)) hrel c
    (Finset.mem_image.mpr ⟨(a, c), Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩)
end GlobalTheory.PlaceModel
