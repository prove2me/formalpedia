-- Prove2me | solution 1 for LovaszSchrijver.OddHole.N_subset_H_add_G
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:25:07.968902+00:00
-- url     : https://prove2.me/submissions/cd3731fb-ea78-4ce5-ba57-f4b1037bf46e

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_FacetHyperplanes

open Pointwise

namespace LovaszSchrijver.OddHole

/-- Separation: a point outside a closed convex cone is separated by a dual vector. -/
theorem aux_nshg_sep {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (x : Option ι → ℝ) (hx : x ∉ K) :
    ∃ u ∈ dualCone K, dotProduct u x < 0 := by
  obtain ⟨hne, hadd, hsmul⟩ := hK
  have hconv : Convex ℝ K := by
    intro a ha b hb s t hs ht _
    exact hadd _ (hsmul s hs a ha) _ (hsmul t ht b hb)
  obtain ⟨f, u, hfx, hfK⟩ := geometric_hahn_banach_point_closed hconv hKc hx
  obtain ⟨k0, hk0⟩ := hne
  have h0 : (0 : Option ι → ℝ) ∈ K := by
    have := hsmul 0 le_rfl k0 hk0
    simpa using this
  have hu : u < 0 := by
    have := hfK 0 h0
    simpa using this
  have hfnn : ∀ b ∈ K, 0 ≤ f b := by
    intro b hb
    by_contra hneg
    push Not at hneg
    have hc : 0 ≤ u / f b := div_nonneg_of_nonpos hu.le hneg.le
    have := hfK _ (hsmul (u / f b) hc b hb)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  have hrep : ∀ y : Option ι → ℝ,
      dotProduct (fun j => f (Pi.single j 1)) y = f y := by
    intro y
    conv_rhs => rw [← Finset.univ_sum_single y]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : (Pi.single j (y j) : Option ι → ℝ) = y j • Pi.single j 1 := by
      ext k
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  refine ⟨fun j => f (Pi.single j 1), ?_, ?_⟩
  · intro b hb
    rw [hrep]
    exact hfnn b hb
  · rw [hrep]
    linarith

/-- Membership in the dual of `Q` for functionals nonnegative on the generators. -/
theorem aux_nshg_dualQ {ι : Type} [Fintype ι] (v : Option ι → ℝ)
    (hv : ∀ x : Option ι → ℝ, (x none = 1 ∧ ∀ i : ι, x (some i) = 0 ∨ x (some i) = 1) →
      0 ≤ dotProduct v x) :
    v ∈ dualCone (Q ι) := by
  intro x hx
  unfold Q at hx
  simp only [SetLike.mem_coe] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hv y hy
  | zero => simp
  | add y z _ _ hy hz => rw [dotProduct_add]; exact add_nonneg hy hz
  | smul a y _ hy =>
    show 0 ≤ v ⬝ᵥ ((a : ℝ) • y)
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_nonneg a.2 hy

theorem aux_nshg_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (Y : Matrix (Option ι) (Option ι) ℝ) (hY : Y ∈ M K (Q ι))
    (v : Option ι → ℝ) (hv : v ∈ dualCone (Q ι)) :
    Y.mulVec v ∈ K := by
  by_contra hno
  obtain ⟨u, hu, hlt⟩ := aux_nshg_sep K hK hKc _ hno
  have := hY.2.2 u hu v hv
  linarith

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole
open Pointwise

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKQ : K ⊆ Q ι)
    (i : ι) :
    N K ⊆ (K ∩ Hplane i) + (K ∩ Gplane i) := by
  intro x hx
  obtain ⟨Y, hY, rfl⟩ := hx
  set e0 : Option ι → ℝ := Pi.single none 1 with he0
  set ei : Option ι → ℝ := Pi.single (some i) 1 with hei
  have hd1 : e0 - ei ∈ dualCone (Q ι) := by
    apply aux_nshg_dualQ
    intro x ⟨hx0, hxi⟩
    rw [sub_dotProduct, he0, hei, single_dotProduct, single_dotProduct, hx0]
    rcases hxi i with h | h <;> rw [h] <;> norm_num
  have hd2 : ei ∈ dualCone (Q ι) := by
    apply aux_nshg_dualQ
    intro x ⟨_, hxi⟩
    rw [hei, single_dotProduct]
    rcases hxi i with h | h <;> rw [h] <;> norm_num
  have hsymm := hY.1
  have hdiag := hY.2.1 i
  refine Set.mem_add.mpr ⟨Y.mulVec (e0 - ei), ⟨aux_nshg_mem K hK hKc Y hY _ hd1, ?_⟩,
    Y.mulVec ei, ⟨aux_nshg_mem K hK hKc Y hY _ hd2, ?_⟩, ?_⟩
  · show (Y.mulVec (e0 - ei)) (some i) = 0
    rw [Matrix.mulVec_sub, Pi.sub_apply, he0, hei, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one]
    simp only [Matrix.col_apply]
    rw [hsymm.apply none (some i), hdiag]
    ring
  · show (Y.mulVec ei) (some i) = (Y.mulVec ei) none
    rw [hei, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply]
    exact hdiag
  · rw [← Matrix.mulVec_add, sub_add_cancel]
