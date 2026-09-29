-- Prove2me | solution 1 for NonmonotoneSubmod.SmoothLS.inter_lower_27ths
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:40:17.671593+00:00
-- url     : https://prove2.me/submissions/f7ff6817-6034-4ca5-8968-395b400b2614

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.Shared

section aux_i27_section

variable {X : Type} [Fintype X] [DecidableEq X]

theorem aux_i27_wsum (x : X → ℝ) :
    ∑ S : Finset X, ∏ i : X, (if i ∈ S then x i else 1 - x i) = 1 := by
  have h := Fintype.prod_add x (fun i => 1 - x i)
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun S _ => ?_
  have := Finset.prod_piecewise (Finset.univ : Finset X) S x (fun i => 1 - x i)
  simp only [Finset.univ_inter, ← Finset.compl_eq_univ_sdiff] at this
  rw [← this]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Finset.piecewise]

theorem aux_i27_wnn (x : X → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (S : Finset X) :
    0 ≤ ∏ i : X, (if i ∈ S then x i else 1 - x i) := by
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact h0 i
  · linarith [h1 i]

theorem aux_i27_mono (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (g h : Finset X → ℝ) (hgh : ∀ S, g S ≤ h S) : F g q ≤ F h q := by
  unfold F
  exact Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_right (hgh S) (aux_i27_wnn q h0 h1 S)

theorem aux_i27_ge (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (g : Finset X → ℝ) (v : ℝ) (hv : ∀ S, v ≤ g S) : v ≤ F g q := by
  have hc : F (fun _ => v) q = v := by
    unfold F
    rw [← Finset.mul_sum, aux_i27_wsum, mul_one]
  calc v = F (fun _ => v) q := hc.symm
    _ ≤ F g q := aux_i27_mono q h0 h1 _ _ hv

theorem aux_i27_add (g h : Finset X → ℝ) (q : X → ℝ) :
    F (fun S => g S + h S) q = F g q + F h q := by
  unfold F
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- Product of the factors off the coordinate `x`. -/
noncomputable def aux_i27_R (q : X → ℝ) (x : X) (T : Finset X) : ℝ :=
  ∏ i ∈ (Finset.univ.erase x), (if i ∈ T then q i else 1 - q i)

theorem aux_i27_decomp (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F g q =
      ∑ T ∈ (Finset.univ.erase x).powerset,
        ((1 - q x) * g T + q x * g (insert x T)) * aux_i27_R q x T := by
  unfold F
  have hU : (Finset.univ : Finset (Finset X)) = (insert x (Finset.univ.erase x)).powerset := by
    rw [Finset.insert_erase (Finset.mem_univ x), Finset.powerset_univ]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  rw [hU, Finset.sum_powerset_insert hxn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  have h1 : ∏ i : X, (if i ∈ T then q i else 1 - q i) = (1 - q x) * aux_i27_R q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp [hxT, aux_i27_R]
  have h2 : ∏ i : X, (if i ∈ insert x T then q i else 1 - q i) = q x * aux_i27_R q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp only [Finset.mem_insert, true_or, if_true, aux_i27_R]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hix : i ≠ x := Finset.ne_of_mem_erase hi
    simp [hix]
  rw [h1, h2]
  ring

theorem aux_i27_ins (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F (fun S => g (insert x S)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g (insert x T) * aux_i27_R q x T := by
  rw [aux_i27_decomp]
  refine Finset.sum_congr rfl ?_
  intro T _
  rw [Finset.insert_idem]
  ring

theorem aux_i27_erase (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F (fun S => g (S.erase x)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g T * aux_i27_R q x T := by
  rw [aux_i27_decomp]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  rw [Finset.erase_insert hxT, Finset.erase_eq_of_notMem hxT]
  ring

theorem aux_i27_split (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F g q = (1 - q x) * F (fun S => g (S.erase x)) q + q x * F (fun S => g (insert x S)) q := by
  rw [aux_i27_decomp g q x, aux_i27_ins g q x, aux_i27_erase g q x, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

theorem aux_i27_sub_erase (g : Finset X → ℝ) (hg : Submodular g) (a : X) :
    Submodular (fun S => g (S.erase a)) := by
  intro S T
  have h := hg (S.erase a) (T.erase a)
  have e1 : (S ∪ T).erase a = S.erase a ∪ T.erase a := by ext y; simp; tauto
  have e2 : (S ∩ T).erase a = S.erase a ∩ T.erase a := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

theorem aux_i27_sub_insert (g : Finset X → ℝ) (hg : Submodular g) (a : X) :
    Submodular (fun S => g (insert a S)) := by
  intro S T
  have h := hg (insert a S) (insert a T)
  have e1 : insert a (S ∪ T) = insert a S ∪ insert a T := by ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
  have e2 : insert a (S ∩ T) = insert a S ∩ insert a T := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

theorem aux_i27_sub_sdiff (g : Finset X → ℝ) (hg : Submodular g) (D : Finset X) :
    Submodular (fun S => g (S \ D)) := by
  intro S T
  have h := hg (S \ D) (T \ D)
  have e1 : (S ∪ T) \ D = S \ D ∪ T \ D := by ext y; simp; tauto
  have e2 : (S ∩ T) \ D = S \ D ∩ (T \ D) := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

theorem aux_i27_sub_union (g : Finset X → ℝ) (hg : Submodular g) (D : Finset X) :
    Submodular (fun S => g (S ∪ D)) := by
  intro S T
  have h := hg (S ∪ D) (T ∪ D)
  have e1 : S ∪ T ∪ D = (S ∪ D) ∪ (T ∪ D) := by ext y; simp; tauto
  have e2 : S ∩ T ∪ D = (S ∪ D) ∩ (T ∪ D) := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

/-- Block sampling lemma for the multilinear extension. -/
theorem aux_i27_blk (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1) (c : ℝ)
    (T : Finset X) :
    (∀ i ∈ T, q i = c) → ∀ g : Finset X → ℝ, Submodular g →
    (1 - c) * F (fun S => g (S \ T)) q + c * F (fun S => g (S ∪ T)) q ≤ F g q := by
  induction T using Finset.induction_on with
  | empty =>
    intro _ g _
    simp only [Finset.sdiff_empty, Finset.union_empty]
    have : (1 - c) * F g q + c * F g q = F g q := by ring
    linarith
  | @insert a T ha ih =>
    intro hT g hg
    have hqa : q a = c := hT a (Finset.mem_insert_self a T)
    have hT' : ∀ i ∈ T, q i = c := fun i hi => hT i (Finset.mem_insert_of_mem hi)
    have hc0 : 0 ≤ c := hqa ▸ h0 a
    have hc1 : c ≤ 1 := hqa ▸ h1 a
    have hs := aux_i27_split g q a
    rw [hqa] at hs
    have i1 : (1 - c) * F (fun S => g ((S \ T).erase a)) q
        + c * F (fun S => g ((S ∪ T).erase a)) q ≤ F (fun S => g (S.erase a)) q :=
      ih hT' (fun S => g (S.erase a)) (aux_i27_sub_erase g hg a)
    have i2 : (1 - c) * F (fun S => g (insert a (S \ T))) q
        + c * F (fun S => g (insert a (S ∪ T))) q ≤ F (fun S => g (insert a S)) q :=
      ih hT' (fun S => g (insert a S)) (aux_i27_sub_insert g hg a)
    have e1 : F (fun S => g ((S \ T).erase a)) q = F (fun S => g (S \ insert a T)) q := by
      congr 1; funext S; rw [Finset.sdiff_insert]
    have e2 : F (fun S => g (insert a (S ∪ T))) q = F (fun S => g (S ∪ insert a T)) q := by
      congr 1; funext S; rw [Finset.union_insert]
    rw [e1] at i1
    rw [e2] at i2
    have pw : F (fun S => g (S ∪ insert a T) + g (S \ insert a T)) q ≤
        F (fun S => g ((S ∪ T).erase a) + g (insert a (S \ T))) q := by
      apply aux_i27_mono q h0 h1
      intro S
      have h := hg ((S ∪ T).erase a) (insert a (S \ T))
      have u1 : (S ∪ T).erase a ∪ insert a (S \ T) = S ∪ insert a T := by
        ext y; simp; tauto
      have u2 : (S ∪ T).erase a ∩ insert a (S \ T) = S \ insert a T := by
        ext y; simp; tauto
      rw [u1, u2] at h
      linarith
    rw [aux_i27_add, aux_i27_add] at pw
    have hc' : (0 : ℝ) ≤ 1 - c := by linarith
    have m1 := mul_le_mul_of_nonneg_left i1 hc'
    have m2 := mul_le_mul_of_nonneg_left i2 hc0
    have m3 := mul_le_mul_of_nonneg_left pw (mul_nonneg hc0 hc')
    rw [hs]
    nlinarith [m1, m2, m3]

/-- Three-block version with lower bounds on the leaves. -/
theorem aux_i27_blk3 (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (g : Finset X → ℝ) (hg : Submodular g) (T1 T2 T3 : Finset X) (c1 c2 c3 : ℝ)
    (hT1 : ∀ i ∈ T1, q i = c1) (hT2 : ∀ i ∈ T2, q i = c2) (hT3 : ∀ i ∈ T3, q i = c3)
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1) (hc2 : 0 ≤ c2) (hc2' : c2 ≤ 1)
    (hc3 : 0 ≤ c3) (hc3' : c3 ≤ 1)
    (v000 v001 v010 v011 v100 v101 v110 v111 : ℝ)
    (k000 : ∀ S, v000 ≤ g (((S \ T3) \ T2) \ T1))
    (k001 : ∀ S, v001 ≤ g (((S ∪ T3) \ T2) \ T1))
    (k010 : ∀ S, v010 ≤ g (((S \ T3) ∪ T2) \ T1))
    (k011 : ∀ S, v011 ≤ g (((S ∪ T3) ∪ T2) \ T1))
    (k100 : ∀ S, v100 ≤ g (((S \ T3) \ T2) ∪ T1))
    (k101 : ∀ S, v101 ≤ g (((S ∪ T3) \ T2) ∪ T1))
    (k110 : ∀ S, v110 ≤ g (((S \ T3) ∪ T2) ∪ T1))
    (k111 : ∀ S, v111 ≤ g (((S ∪ T3) ∪ T2) ∪ T1)) :
    (1 - c1) * (1 - c2) * (1 - c3) * v000 + (1 - c1) * (1 - c2) * c3 * v001
      + (1 - c1) * c2 * (1 - c3) * v010 + (1 - c1) * c2 * c3 * v011
      + c1 * (1 - c2) * (1 - c3) * v100 + c1 * (1 - c2) * c3 * v101
      + c1 * c2 * (1 - c3) * v110 + c1 * c2 * c3 * v111 ≤ F g q := by
  have s1 : (1 - c1) * F (fun S => g (S \ T1)) q + c1 * F (fun S => g (S ∪ T1)) q ≤ F g q :=
    aux_i27_blk q h0 h1 c1 T1 hT1 g hg
  have s2 : (1 - c2) * F (fun S => g ((S \ T2) \ T1)) q
      + c2 * F (fun S => g ((S ∪ T2) \ T1)) q ≤ F (fun S => g (S \ T1)) q :=
    aux_i27_blk q h0 h1 c2 T2 hT2 (fun S => g (S \ T1)) (aux_i27_sub_sdiff g hg T1)
  have s3 : (1 - c2) * F (fun S => g ((S \ T2) ∪ T1)) q
      + c2 * F (fun S => g ((S ∪ T2) ∪ T1)) q ≤ F (fun S => g (S ∪ T1)) q :=
    aux_i27_blk q h0 h1 c2 T2 hT2 (fun S => g (S ∪ T1)) (aux_i27_sub_union g hg T1)
  have s4 : (1 - c3) * F (fun S => g (((S \ T3) \ T2) \ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) \ T2) \ T1)) q ≤ F (fun S => g ((S \ T2) \ T1)) q :=
    aux_i27_blk q h0 h1 c3 T3 hT3 (fun S => g ((S \ T2) \ T1))
      (aux_i27_sub_sdiff _ (aux_i27_sub_sdiff g hg T1) T2)
  have s5 : (1 - c3) * F (fun S => g (((S \ T3) ∪ T2) \ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) ∪ T2) \ T1)) q ≤ F (fun S => g ((S ∪ T2) \ T1)) q :=
    aux_i27_blk q h0 h1 c3 T3 hT3 (fun S => g ((S ∪ T2) \ T1))
      (aux_i27_sub_union _ (aux_i27_sub_sdiff g hg T1) T2)
  have s6 : (1 - c3) * F (fun S => g (((S \ T3) \ T2) ∪ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) \ T2) ∪ T1)) q ≤ F (fun S => g ((S \ T2) ∪ T1)) q :=
    aux_i27_blk q h0 h1 c3 T3 hT3 (fun S => g ((S \ T2) ∪ T1))
      (aux_i27_sub_sdiff _ (aux_i27_sub_union g hg T1) T2)
  have s7 : (1 - c3) * F (fun S => g (((S \ T3) ∪ T2) ∪ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) ∪ T2) ∪ T1)) q ≤ F (fun S => g ((S ∪ T2) ∪ T1)) q :=
    aux_i27_blk q h0 h1 c3 T3 hT3 (fun S => g ((S ∪ T2) ∪ T1))
      (aux_i27_sub_union _ (aux_i27_sub_union g hg T1) T2)
  have l000 := aux_i27_ge q h0 h1 (fun S => g (((S \ T3) \ T2) \ T1)) v000 k000
  have l001 := aux_i27_ge q h0 h1 (fun S => g (((S ∪ T3) \ T2) \ T1)) v001 k001
  have l010 := aux_i27_ge q h0 h1 (fun S => g (((S \ T3) ∪ T2) \ T1)) v010 k010
  have l011 := aux_i27_ge q h0 h1 (fun S => g (((S ∪ T3) ∪ T2) \ T1)) v011 k011
  have l100 := aux_i27_ge q h0 h1 (fun S => g (((S \ T3) \ T2) ∪ T1)) v100 k100
  have l101 := aux_i27_ge q h0 h1 (fun S => g (((S ∪ T3) \ T2) ∪ T1)) v101 k101
  have l110 := aux_i27_ge q h0 h1 (fun S => g (((S \ T3) ∪ T2) ∪ T1)) v110 k110
  have l111 := aux_i27_ge q h0 h1 (fun S => g (((S ∪ T3) ∪ T2) ∪ T1)) v111 k111
  have a1 : (0 : ℝ) ≤ 1 - c1 := by linarith
  have a2 : (0 : ℝ) ≤ 1 - c2 := by linarith
  have a3 : (0 : ℝ) ≤ 1 - c3 := by linarith
  have m2 := mul_le_mul_of_nonneg_left s2 a1
  have m3 := mul_le_mul_of_nonneg_left s3 hc1
  have m4 := mul_le_mul_of_nonneg_left s4 (mul_nonneg a1 a2)
  have m5 := mul_le_mul_of_nonneg_left s5 (mul_nonneg a1 hc2)
  have m6 := mul_le_mul_of_nonneg_left s6 (mul_nonneg hc1 a2)
  have m7 := mul_le_mul_of_nonneg_left s7 (mul_nonneg hc1 hc2)
  have n000 := mul_le_mul_of_nonneg_left l000 (mul_nonneg (mul_nonneg a1 a2) a3)
  have n001 := mul_le_mul_of_nonneg_left l001 (mul_nonneg (mul_nonneg a1 a2) hc3)
  have n010 := mul_le_mul_of_nonneg_left l010 (mul_nonneg (mul_nonneg a1 hc2) a3)
  have n011 := mul_le_mul_of_nonneg_left l011 (mul_nonneg (mul_nonneg a1 hc2) hc3)
  have n100 := mul_le_mul_of_nonneg_left l100 (mul_nonneg (mul_nonneg hc1 a2) a3)
  have n101 := mul_le_mul_of_nonneg_left l101 (mul_nonneg (mul_nonneg hc1 a2) hc3)
  have n110 := mul_le_mul_of_nonneg_left l110 (mul_nonneg (mul_nonneg hc1 hc2) a3)
  have n111 := mul_le_mul_of_nonneg_left l111 (mul_nonneg (mul_nonneg hc1 hc2) hc3)
  linarith

theorem aux_i27_sub_inter (g : Finset X → ℝ) (hg : Submodular g) (D : Finset X) :
    Submodular (fun S => g (S ∩ D)) := by
  intro S T
  have h := hg (S ∩ D) (T ∩ D)
  have e1 : (S ∪ T) ∩ D = S ∩ D ∪ T ∩ D := by ext y; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  have e2 : (S ∩ T) ∩ D = S ∩ D ∩ (T ∩ D) := by ext y; simp only [Finset.mem_inter]; tauto
  simp only
  rw [e1, e2]; exact h

end aux_i27_section

end NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.SmoothLS

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A C : Finset X) :
    8 / 27 * f (A ∩ C) + 2 / 27 * f (Aᶜ ∪ C) + 2 / 27 * f (Aᶜ ∩ C) + 4 / 27 * f C +
        4 / 27 * f ((A ∩ C) ∪ (Aᶜ \ C)) + 1 / 27 * f Aᶜ ≤
      NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (Aᶜ ∪ C))) (biasPt A (1 / 3)) := by
  set q := biasPt A (1 / 3 : ℝ) with hq
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i; simp only [hq, biasPt]; split_ifs <;> norm_num
  have hq1 : ∀ i, q i ≤ 1 := by
    intro i; simp only [hq, biasPt]; split_ifs <;> norm_num
  have hqA : ∀ i ∈ A, q i = 2 / 3 := by
    intro i hi; simp only [hq, biasPt, if_pos hi]; norm_num
  have hqB : ∀ i, i ∉ A → q i = 1 / 3 := by
    intro i hi; simp only [hq, biasPt, if_neg hi]; norm_num
  have L := aux_i27_blk3 q hq0 hq1 (fun S => f (S ∩ (Aᶜ ∪ C)))
    (aux_i27_sub_inter f hf (Aᶜ ∪ C)) (A ∩ C) (Aᶜ ∩ C) (Aᶜ \ C) (2 / 3) (1 / 3) (1 / 3)
    (fun i hi => hqA i (Finset.mem_inter.1 hi).1)
    (fun i hi => hqB i (Finset.mem_compl.1 (Finset.mem_inter.1 hi).1))
    (fun i hi => hqB i (Finset.mem_compl.1 (Finset.mem_sdiff.1 hi).1))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 0 (f (Aᶜ ∩ C)) (f Aᶜ) (f (A ∩ C)) (f ((A ∩ C) ∪ (Aᶜ \ C))) (f C) (f (Aᶜ ∪ C))
    (fun S => hf0 _) (fun S => hf0 _)
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
  linarith
