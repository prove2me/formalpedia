-- Prove2me | solution 1 for LovaszSchrijver.OddHole.valid_N_of_deletion_contraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:13:46.335861+00:00
-- url     : https://prove2.me/submissions/8dad6cbc-3365-495c-9f0b-f7ddf7e3f5cf

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction



namespace LovaszSchrijver.OddHole

/-- Separation: a point outside a closed convex cone is separated by a dual vector. -/
theorem aux_vdc_sep {ι : Type} [Fintype ι] [DecidableEq ι]
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
theorem aux_vdc_dualQ {ι : Type} [Fintype ι] (v : Option ι → ℝ)
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

theorem aux_vdc_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (Y : Matrix (Option ι) (Option ι) ℝ) (hY : Y ∈ M K (Q ι))
    (v : Option ι → ℝ) (hv : v ∈ dualCone (Q ι)) :
    Y.mulVec v ∈ K := by
  by_contra hno
  obtain ⟨u, hu, hlt⟩ := aux_vdc_sep K hK hKc _ hno
  have := hY.2.2 u hu v hv
  linarith


theorem aux_vdc_homog {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (K : Set (Option V → ℝ)) (hK : IsConvexCone K) (hKFR : K ⊆ FR G)
    (c : V → ℝ) (d : ℝ) (hv : Valid {x | hom x ∈ K} c d)
    (k : Option V → ℝ) (hk : k ∈ K) (hnn : 0 ≤ k none) :
    ∑ i, c i * k (some i) ≤ d * k none := by
  have hFR := hKFR hk
  rcases hnn.lt_or_eq with hpos | hzero
  · have hmem : hom (fun i => k (some i) / k none) ∈ K := by
      have : hom (fun i => k (some i) / k none) = (1 / k none) • k := by
        funext o
        cases o with
        | none => simp [hom, hpos.ne']
        | some i => simp only [hom, Option.elim_some, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      exact hK.2.2 _ (by positivity) _ hk
    have := hv _ hmem
    have h2 : ∑ i, c i * (k (some i) / k none) = (∑ i, c i * k (some i)) / k none := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [h2, div_le_iff₀ hpos] at this
    linarith
  · have hz : ∀ i, k (some i) = 0 := by
      intro i
      obtain ⟨w, hw⟩ := hG i
      have := hFR.2 _ _ hw
      linarith [hFR.1 i, hFR.1 w]
    simp [hz, ← hzero]

theorem vdc_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (K : Set (Option V → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKFR : K ⊆ FR G)
    (a : V → ℝ) (b : ℝ) (v : V)
    (hdel : Valid {x | hom x ∈ K} (deletion a v) b)
    (hcon : Valid {x | hom x ∈ K} (contraction G a v) (b - a v)) :
    Valid {x | hom x ∈ N K} a b := by
  intro x hx
  obtain ⟨Y, hY, hYx⟩ := hx
  set e0 : Option V → ℝ := Pi.single none 1 with he0
  set ei : Option V → ℝ := Pi.single (some v) 1 with hei
  have hd1 : e0 - ei ∈ dualCone (Q V) := by
    apply aux_vdc_dualQ
    intro x ⟨hx0, hxi⟩
    rw [sub_dotProduct, he0, hei, single_dotProduct, single_dotProduct, hx0]
    rcases hxi v with h | h <;> rw [h] <;> norm_num
  have hd2 : ei ∈ dualCone (Q V) := by
    apply aux_vdc_dualQ
    intro x ⟨_, hxi⟩
    rw [hei, single_dotProduct]
    rcases hxi v with h | h <;> rw [h] <;> norm_num
  have hsymm := hY.1
  have hdiag := hY.2.1 v
  have hwK := aux_vdc_mem K hK hKc Y hY _ hd1
  have hzK := aux_vdc_mem K hK hKc Y hY _ hd2
  set w := Y.mulVec (e0 - ei) with hw
  set z := Y.mulVec ei with hz
  have hxw : ∀ o, hom x o = w o + z o := by
    intro o
    rw [← hYx, hw, hz, ← Pi.add_apply, ← Matrix.mulVec_add, sub_add_cancel]
  have hzv : z (some v) = z none := by
    rw [hz, hei, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply]
    exact hdiag
  have hwv : w (some v) = 0 := by
    rw [hw, Matrix.mulVec_sub, Pi.sub_apply, he0, hei, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one]
    simp only [Matrix.col_apply]
    rw [hsymm.apply none (some v), hdiag]
    ring
  have hx1 : w none + z none = 1 := by
    rw [← hxw]; rfl
  have hzFR := hKFR hzK
  have hzadj : ∀ u, G.Adj v u → z (some u) = 0 := by
    intro u hu
    have := hzFR.2 _ _ hu
    linarith [hzFR.1 u]
  have hwFR := hKFR hwK
  have hwnn : 0 ≤ w none := by
    obtain ⟨u, hu⟩ := hG v
    have := hwFR.2 _ _ hu
    linarith [hwFR.1 v, hwFR.1 u]
  have hznn : 0 ≤ z none := by rw [← hzv]; exact hzFR.1 v
  have h1 := aux_vdc_homog G hG K hK hKFR _ _ hdel w hwK hwnn
  have h2 := aux_vdc_homog G hG K hK hKFR _ _ hcon z hzK hznn
  have hA : ∑ i, a i * x i = ∑ i, deletion a v i * w (some i)
      + (a v * z none + ∑ i, contraction G a v i * z (some i)) := by
    have hdel' : ∑ i, a i * w (some i) = ∑ i, deletion a v i * w (some i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : i = v
      · subst h; simp [hwv]
      · simp [deletion, Function.update_of_ne h]
    have hcon' : ∑ i, a i * z (some i) =
        ∑ i, ((if v = i then a v * z none else 0) + contraction G a v i * z (some i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : i = v
      · subst h; simp [contraction, hzv]
      · have h' : v ≠ i := fun e => h e.symm
        by_cases ha : G.Adj v i
        · simp [contraction, hzadj i ha, h']
        · simp [contraction, h, ha, h']
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)] at hcon'
    rw [← hdel', ← hcon', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := hxw (some i)
    simp only [hom, Option.elim_some] at this
    rw [this]; ring
  rw [hA]
  linear_combination h1 + h2 + b * hx1

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (K : Set (Option V → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKFR : K ⊆ FR G)
    (a : V → ℝ) (b : ℝ) (v : V)
    (hdel : Valid {x | hom x ∈ K} (deletion a v) b)
    (hcon : Valid {x | hom x ∈ K} (contraction G a v) (b - a v)) :
    Valid {x | hom x ∈ N K} a b := by
  exact vdc_core G hG K hK hKc hKFR a b v hdel hcon
