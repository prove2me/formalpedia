-- Prove2me | solution 1 for NonmonotoneSubmod.SmoothLS.terminal_four_ninths
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:32:47.640219+00:00
-- url     : https://prove2.me/submissions/301aa77e-43c6-4355-a0fb-a540185e3932

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.Shared

section aux_tfn_section

variable {X : Type} [Fintype X] [DecidableEq X]

theorem aux_tfn_wsum (x : X → ℝ) :
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

theorem aux_tfn_wnn (x : X → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (S : Finset X) :
    0 ≤ ∏ i : X, (if i ∈ S then x i else 1 - x i) := by
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact h0 i
  · linarith [h1 i]

theorem aux_tfn_mono (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (g h : Finset X → ℝ) (hgh : ∀ S, g S ≤ h S) : F g q ≤ F h q := by
  unfold F
  exact Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_right (hgh S) (aux_tfn_wnn q h0 h1 S)

theorem aux_tfn_ge (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (g : Finset X → ℝ) (v : ℝ) (hv : ∀ S, v ≤ g S) : v ≤ F g q := by
  have hc : F (fun _ => v) q = v := by
    unfold F
    rw [← Finset.mul_sum, aux_tfn_wsum, mul_one]
  calc v = F (fun _ => v) q := hc.symm
    _ ≤ F g q := aux_tfn_mono q h0 h1 _ _ hv

theorem aux_tfn_add (g h : Finset X → ℝ) (q : X → ℝ) :
    F (fun S => g S + h S) q = F g q + F h q := by
  unfold F
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- Product of the factors off the coordinate `x`. -/
noncomputable def aux_tfn_R (q : X → ℝ) (x : X) (T : Finset X) : ℝ :=
  ∏ i ∈ (Finset.univ.erase x), (if i ∈ T then q i else 1 - q i)

theorem aux_tfn_decomp (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F g q =
      ∑ T ∈ (Finset.univ.erase x).powerset,
        ((1 - q x) * g T + q x * g (insert x T)) * aux_tfn_R q x T := by
  unfold F
  have hU : (Finset.univ : Finset (Finset X)) = (insert x (Finset.univ.erase x)).powerset := by
    rw [Finset.insert_erase (Finset.mem_univ x), Finset.powerset_univ]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  rw [hU, Finset.sum_powerset_insert hxn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  have h1 : ∏ i : X, (if i ∈ T then q i else 1 - q i) = (1 - q x) * aux_tfn_R q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp [hxT, aux_tfn_R]
  have h2 : ∏ i : X, (if i ∈ insert x T then q i else 1 - q i) = q x * aux_tfn_R q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp only [Finset.mem_insert, true_or, if_true, aux_tfn_R]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hix : i ≠ x := Finset.ne_of_mem_erase hi
    simp [hix]
  rw [h1, h2]
  ring

theorem aux_tfn_ins (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F (fun S => g (insert x S)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g (insert x T) * aux_tfn_R q x T := by
  rw [aux_tfn_decomp]
  refine Finset.sum_congr rfl ?_
  intro T _
  rw [Finset.insert_idem]
  ring

theorem aux_tfn_erase (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F (fun S => g (S.erase x)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g T * aux_tfn_R q x T := by
  rw [aux_tfn_decomp]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  rw [Finset.erase_insert hxT, Finset.erase_eq_of_notMem hxT]
  ring

theorem aux_tfn_split (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F g q = (1 - q x) * F (fun S => g (S.erase x)) q + q x * F (fun S => g (insert x S)) q := by
  rw [aux_tfn_decomp g q x, aux_tfn_ins g q x, aux_tfn_erase g q x, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

theorem aux_tfn_sub_erase (g : Finset X → ℝ) (hg : Submodular g) (a : X) :
    Submodular (fun S => g (S.erase a)) := by
  intro S T
  have h := hg (S.erase a) (T.erase a)
  have e1 : (S ∪ T).erase a = S.erase a ∪ T.erase a := by ext y; simp; tauto
  have e2 : (S ∩ T).erase a = S.erase a ∩ T.erase a := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

theorem aux_tfn_sub_insert (g : Finset X → ℝ) (hg : Submodular g) (a : X) :
    Submodular (fun S => g (insert a S)) := by
  intro S T
  have h := hg (insert a S) (insert a T)
  have e1 : insert a (S ∪ T) = insert a S ∪ insert a T := by ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
  have e2 : insert a (S ∩ T) = insert a S ∩ insert a T := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

theorem aux_tfn_sub_sdiff (g : Finset X → ℝ) (hg : Submodular g) (D : Finset X) :
    Submodular (fun S => g (S \ D)) := by
  intro S T
  have h := hg (S \ D) (T \ D)
  have e1 : (S ∪ T) \ D = S \ D ∪ T \ D := by ext y; simp; tauto
  have e2 : (S ∩ T) \ D = S \ D ∩ (T \ D) := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

theorem aux_tfn_sub_union (g : Finset X → ℝ) (hg : Submodular g) (D : Finset X) :
    Submodular (fun S => g (S ∪ D)) := by
  intro S T
  have h := hg (S ∪ D) (T ∪ D)
  have e1 : S ∪ T ∪ D = (S ∪ D) ∪ (T ∪ D) := by ext y; simp; tauto
  have e2 : S ∩ T ∪ D = (S ∪ D) ∩ (T ∪ D) := by ext y; simp; tauto
  simp only
  rw [e1, e2]; exact h

/-- Block sampling lemma for the multilinear extension. -/
theorem aux_tfn_blk (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1) (c : ℝ)
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
    have hs := aux_tfn_split g q a
    rw [hqa] at hs
    have i1 : (1 - c) * F (fun S => g ((S \ T).erase a)) q
        + c * F (fun S => g ((S ∪ T).erase a)) q ≤ F (fun S => g (S.erase a)) q :=
      ih hT' (fun S => g (S.erase a)) (aux_tfn_sub_erase g hg a)
    have i2 : (1 - c) * F (fun S => g (insert a (S \ T))) q
        + c * F (fun S => g (insert a (S ∪ T))) q ≤ F (fun S => g (insert a S)) q :=
      ih hT' (fun S => g (insert a S)) (aux_tfn_sub_insert g hg a)
    have e1 : F (fun S => g ((S \ T).erase a)) q = F (fun S => g (S \ insert a T)) q := by
      congr 1; funext S; rw [Finset.sdiff_insert]
    have e2 : F (fun S => g (insert a (S ∪ T))) q = F (fun S => g (S ∪ insert a T)) q := by
      congr 1; funext S; rw [Finset.union_insert]
    rw [e1] at i1
    rw [e2] at i2
    have pw : F (fun S => g (S ∪ insert a T) + g (S \ insert a T)) q ≤
        F (fun S => g ((S ∪ T).erase a) + g (insert a (S \ T))) q := by
      apply aux_tfn_mono q h0 h1
      intro S
      have h := hg ((S ∪ T).erase a) (insert a (S \ T))
      have u1 : (S ∪ T).erase a ∪ insert a (S \ T) = S ∪ insert a T := by
        ext y; simp; tauto
      have u2 : (S ∪ T).erase a ∩ insert a (S \ T) = S \ insert a T := by
        ext y; simp; tauto
      rw [u1, u2] at h
      linarith
    rw [aux_tfn_add, aux_tfn_add] at pw
    have hc' : (0 : ℝ) ≤ 1 - c := by linarith
    have m1 := mul_le_mul_of_nonneg_left i1 hc'
    have m2 := mul_le_mul_of_nonneg_left i2 hc0
    have m3 := mul_le_mul_of_nonneg_left pw (mul_nonneg hc0 hc')
    rw [hs]
    nlinarith [m1, m2, m3]

/-- Three-block version with lower bounds on the leaves. -/
theorem aux_tfn_blk3 (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
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
    aux_tfn_blk q h0 h1 c1 T1 hT1 g hg
  have s2 : (1 - c2) * F (fun S => g ((S \ T2) \ T1)) q
      + c2 * F (fun S => g ((S ∪ T2) \ T1)) q ≤ F (fun S => g (S \ T1)) q :=
    aux_tfn_blk q h0 h1 c2 T2 hT2 (fun S => g (S \ T1)) (aux_tfn_sub_sdiff g hg T1)
  have s3 : (1 - c2) * F (fun S => g ((S \ T2) ∪ T1)) q
      + c2 * F (fun S => g ((S ∪ T2) ∪ T1)) q ≤ F (fun S => g (S ∪ T1)) q :=
    aux_tfn_blk q h0 h1 c2 T2 hT2 (fun S => g (S ∪ T1)) (aux_tfn_sub_union g hg T1)
  have s4 : (1 - c3) * F (fun S => g (((S \ T3) \ T2) \ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) \ T2) \ T1)) q ≤ F (fun S => g ((S \ T2) \ T1)) q :=
    aux_tfn_blk q h0 h1 c3 T3 hT3 (fun S => g ((S \ T2) \ T1))
      (aux_tfn_sub_sdiff _ (aux_tfn_sub_sdiff g hg T1) T2)
  have s5 : (1 - c3) * F (fun S => g (((S \ T3) ∪ T2) \ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) ∪ T2) \ T1)) q ≤ F (fun S => g ((S ∪ T2) \ T1)) q :=
    aux_tfn_blk q h0 h1 c3 T3 hT3 (fun S => g ((S ∪ T2) \ T1))
      (aux_tfn_sub_union _ (aux_tfn_sub_sdiff g hg T1) T2)
  have s6 : (1 - c3) * F (fun S => g (((S \ T3) \ T2) ∪ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) \ T2) ∪ T1)) q ≤ F (fun S => g ((S \ T2) ∪ T1)) q :=
    aux_tfn_blk q h0 h1 c3 T3 hT3 (fun S => g ((S \ T2) ∪ T1))
      (aux_tfn_sub_sdiff _ (aux_tfn_sub_union g hg T1) T2)
  have s7 : (1 - c3) * F (fun S => g (((S \ T3) ∪ T2) ∪ T1)) q
      + c3 * F (fun S => g (((S ∪ T3) ∪ T2) ∪ T1)) q ≤ F (fun S => g ((S ∪ T2) ∪ T1)) q :=
    aux_tfn_blk q h0 h1 c3 T3 hT3 (fun S => g ((S ∪ T2) ∪ T1))
      (aux_tfn_sub_union _ (aux_tfn_sub_union g hg T1) T2)
  have l000 := aux_tfn_ge q h0 h1 (fun S => g (((S \ T3) \ T2) \ T1)) v000 k000
  have l001 := aux_tfn_ge q h0 h1 (fun S => g (((S ∪ T3) \ T2) \ T1)) v001 k001
  have l010 := aux_tfn_ge q h0 h1 (fun S => g (((S \ T3) ∪ T2) \ T1)) v010 k010
  have l011 := aux_tfn_ge q h0 h1 (fun S => g (((S ∪ T3) ∪ T2) \ T1)) v011 k011
  have l100 := aux_tfn_ge q h0 h1 (fun S => g (((S \ T3) \ T2) ∪ T1)) v100 k100
  have l101 := aux_tfn_ge q h0 h1 (fun S => g (((S ∪ T3) \ T2) ∪ T1)) v101 k101
  have l110 := aux_tfn_ge q h0 h1 (fun S => g (((S \ T3) ∪ T2) ∪ T1)) v110 k110
  have l111 := aux_tfn_ge q h0 h1 (fun S => g (((S ∪ T3) ∪ T2) ∪ T1)) v111 k111
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

theorem aux_tfn_chain_up (f : Finset X → ℝ) (hf : Submodular f) (R D : Finset X) :
    f (R ∪ D) ≤ f R + ∑ x ∈ D, (f (insert x R) - f R) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert a D ha ih =>
    have h := hf (R ∪ D) (insert a R)
    have e1 : R ∪ D ∪ insert a R = R ∪ insert a D := by ext y; simp; tauto
    have e2 : (R ∪ D) ∩ insert a R = R := by
      ext y; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact h1
        · exact h1
        · exact absurd (h2 ▸ h1) ha
        · exact h2
      · intro h; exact ⟨Or.inl h, Or.inr h⟩
    rw [e1, e2] at h
    rw [Finset.sum_insert ha]
    linarith

theorem aux_tfn_chain_down (f : Finset X → ℝ) (hf : Submodular f) (R D : Finset X) :
    f (R \ D) + ∑ x ∈ D, (f R - f (R.erase x)) ≤ f R := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert a D ha ih =>
    have h := hf (R \ D) (R.erase a)
    have e1 : R \ D ∪ R.erase a = R := by
      ext y; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro (⟨h1, _⟩ | ⟨_, h1⟩) <;> exact h1
      · intro h; by_cases hy : y ∈ D
        · right; exact ⟨fun h' => ha (h' ▸ hy), h⟩
        · left; exact ⟨h, hy⟩
    have e2 : R \ D ∩ R.erase a = R \ insert a D := by ext y; simp; tauto
    rw [e1, e2] at h
    rw [Finset.sum_insert ha]
    linarith

theorem aux_tfn_up (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (f : Finset X → ℝ) (hf : Submodular f) (D : Finset X) :
    F (fun S => f (S ∪ D)) q ≤ F f q + ∑ x ∈ D, (F (fun S => f (insert x S)) q - F f q) := by
  have hle : F (fun S => f (S ∪ D)) q ≤
      F (fun S => f S + ∑ x ∈ D, (f (insert x S) - f S)) q :=
    aux_tfn_mono q h0 h1 _ _ (fun S => aux_tfn_chain_up f hf S D)
  have heq : F (fun S => f S + ∑ x ∈ D, (f (insert x S) - f S)) q =
      F f q + ∑ x ∈ D, (F (fun S => f (insert x S)) q - F f q) := by
    unfold F
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
    congr 1
    congr 1 <;> exact Finset.sum_comm
  linarith

theorem aux_tfn_down (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (f : Finset X → ℝ) (hf : Submodular f) (D : Finset X) :
    F (fun S => f (S \ D)) q + ∑ x ∈ D, (F f q - F (fun S => f (S.erase x)) q) ≤ F f q := by
  have hle : F (fun S => f (S \ D) + ∑ x ∈ D, (f S - f (S.erase x))) q ≤ F f q :=
    aux_tfn_mono q h0 h1 _ _ (fun S => aux_tfn_chain_down f hf S D)
  have heq : F (fun S => f (S \ D) + ∑ x ∈ D, (f S - f (S.erase x))) q =
      F (fun S => f (S \ D)) q + ∑ x ∈ D, (F f q - F (fun S => f (S.erase x)) q) := by
    unfold F
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
    congr 1
    congr 1 <;> exact Finset.sum_comm
  linarith

end aux_tfn_section

end NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.SmoothLS

theorem solution {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Finset X)
    (hA : ∀ x, x ∈ A → -(3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ≤ omegaB f A (1 / 3) x)
    (hB : ∀ x, x ∉ A → omegaB f A (1 / 3) x ≤ 3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) :
    4 / 9 * NonmonotoneSubmod.Shared.OPT f ≤ Phi f (1 / 3) A + 1 / 9 * f Aᶜ + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f := by
  set n : ℝ := (Fintype.card X : ℝ) with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  obtain ⟨C, -, hC⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  have hOPT : NonmonotoneSubmod.Shared.OPT f = f C := hC
  have hO0 : 0 ≤ NonmonotoneSubmod.Shared.OPT f := hOPT ▸ hf0 C
  set O := NonmonotoneSubmod.Shared.OPT f with hO
  set ε := 3 / n ^ 2 * O with hε
  have hε0 : 0 ≤ ε := by positivity
  have hnε : n * ε = 3 * (O / n) := by rw [hε]; field_simp
  set q := biasPt A (1 / 3 : ℝ) with hq
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i; simp only [hq, biasPt]; split_ifs <;> norm_num
  have hq1 : ∀ i, q i ≤ 1 := by
    intro i; simp only [hq, biasPt]; split_ifs <;> norm_num
  have hqA : ∀ i ∈ A, q i = 2 / 3 := by
    intro i hi; simp only [hq, biasPt, if_pos hi]; norm_num
  have hqB : ∀ i, i ∉ A → q i = 1 / 3 := by
    intro i hi; simp only [hq, biasPt, if_neg hi]; norm_num
  have hPhi : Phi f (1 / 3) A = NonmonotoneSubmod.Shared.F f q := rfl
  have hom : ∀ x, omegaB f A (1 / 3) x = NonmonotoneSubmod.Shared.F (fun S => f (insert x S)) q
      - NonmonotoneSubmod.Shared.F (fun S => f (S.erase x)) q := fun x => rfl
  -- upper estimate: adding `C \ A`
  have U1 : NonmonotoneSubmod.Shared.F (fun S => f (S ∪ (C \ A))) q ≤
      NonmonotoneSubmod.Shared.F f q + 2 / 3 * (n * ε) := by
    have h1 := aux_tfn_up q hq0 hq1 f hf (C \ A)
    have h2 : ∀ x ∈ C \ A, NonmonotoneSubmod.Shared.F (fun S => f (insert x S)) q
        - NonmonotoneSubmod.Shared.F f q ≤ 2 / 3 * ε := by
      intro x hx
      have hxA : x ∉ A := (Finset.mem_sdiff.1 hx).2
      have hs := aux_tfn_split f q x
      rw [hqB x hxA] at hs
      have := hB x hxA
      rw [hom x] at this
      linarith
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have hcard : ((C \ A).card : ℝ) ≤ n := by rw [hn]; exact_mod_cast Finset.card_le_univ _
    have h4 : ((C \ A).card : ℝ) * (2 / 3 * ε) ≤ n * (2 / 3 * ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have h5 : n * (2 / 3 * ε) = 2 / 3 * (n * ε) := by ring
    linarith
  -- upper estimate: removing `A \ C`
  have U2 : NonmonotoneSubmod.Shared.F (fun S => f (S \ (A \ C))) q ≤
      NonmonotoneSubmod.Shared.F f q + 2 / 3 * (n * ε) := by
    have h1 := aux_tfn_down q hq0 hq1 f hf (A \ C)
    have h2 : ∀ x ∈ A \ C, -(2 / 3 * ε) ≤ NonmonotoneSubmod.Shared.F f q
        - NonmonotoneSubmod.Shared.F (fun S => f (S.erase x)) q := by
      intro x hx
      have hxA : x ∈ A := (Finset.mem_sdiff.1 hx).1
      have hs := aux_tfn_split f q x
      rw [hqA x hxA] at hs
      have := hA x hxA
      rw [hom x] at this
      linarith
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have hcard : ((A \ C).card : ℝ) ≤ n := by rw [hn]; exact_mod_cast Finset.card_le_univ _
    have h4 : ((A \ C).card : ℝ) * (2 / 3 * ε) ≤ n * (2 / 3 * ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have h5 : n * (2 / 3 * ε) = 2 / 3 * (n * ε) := by ring
    have h6 : ((A \ C).card : ℝ) * -(2 / 3 * ε) = -(((A \ C).card : ℝ) * (2 / 3 * ε)) := by ring
    linarith
  -- lower bound for the removal set
  have La := aux_tfn_blk3 q hq0 hq1 (fun S => f (S \ (A \ C)))
    (aux_tfn_sub_sdiff f hf (A \ C)) (A ∩ C) (C \ A) (A ∪ C)ᶜ (2 / 3) (1 / 3) (1 / 3)
    (fun i hi => hqA i (Finset.mem_inter.1 hi).1)
    (fun i hi => hqB i (Finset.mem_sdiff.1 hi).2)
    (fun i hi => hqB i (fun h => (Finset.mem_compl.1 hi) (Finset.mem_union_left _ h)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 0 (f (C \ A)) (f Aᶜ) (f (A ∩ C)) (f ((A ∩ C) ∪ (A ∪ C)ᶜ)) (f C) (f (C ∪ Aᶜ))
    (fun S => hf0 _) (fun S => hf0 _)
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
  -- lower bound for the addition set
  have Lb := aux_tfn_blk3 q hq0 hq1 (fun S => f (S ∪ (C \ A)))
    (aux_tfn_sub_union f hf (C \ A)) (A ∩ C) (A \ C) (A ∪ C)ᶜ (2 / 3) (2 / 3) (1 / 3)
    (fun i hi => hqA i (Finset.mem_inter.1 hi).1)
    (fun i hi => hqA i (Finset.mem_sdiff.1 hi).1)
    (fun i hi => hqB i (fun h => (Finset.mem_compl.1 hi) (Finset.mem_union_left _ h)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (f (C \ A)) (f Aᶜ) (f ((A \ C) ∪ (C \ A))) 0 (f C) (f (C ∪ Aᶜ)) (f (C ∪ A)) 0
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => hf0 _)
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => le_of_eq (congrArg f (by ext y; simp; tauto)))
    (fun S => hf0 _)
  -- submodularity instances
  have i1 := hf (A ∩ C) (C \ A)
  have i1u : A ∩ C ∪ C \ A = C := by ext y; simp; tauto
  have i1i : A ∩ C ∩ (C \ A) = ∅ := by ext y; simp; tauto
  rw [i1u, i1i] at i1
  have i2 := hf ((A \ C) ∪ (C \ A)) Aᶜ
  have i2u : (A \ C) ∪ (C \ A) ∪ Aᶜ = (A ∩ C)ᶜ := by ext y; simp; tauto
  have i2i : ((A \ C) ∪ (C \ A)) ∩ Aᶜ = C \ A := by ext y; simp; tauto
  rw [i2u, i2i] at i2
  have i3 := hf (C ∪ A) (C ∪ Aᶜ)
  have i3u : C ∪ A ∪ (C ∪ Aᶜ) = Finset.univ := by ext y; simp; tauto
  have i3i : (C ∪ A) ∩ (C ∪ Aᶜ) = C := by ext y; simp; tauto
  rw [i3u, i3i] at i3
  have i4 := hf ((A ∩ C) ∪ (A ∪ C)ᶜ) Aᶜ
  have i4u : (A ∩ C) ∪ (A ∪ C)ᶜ ∪ Aᶜ = C ∪ Aᶜ := by ext y; simp; tauto
  have i4i : ((A ∩ C) ∪ (A ∪ C)ᶜ) ∩ Aᶜ = (A ∪ C)ᶜ := by ext y; simp; tauto
  rw [i4u, i4i] at i4
  have z1 := hf0 ∅
  have z2 := hf0 (A ∩ C)ᶜ
  have z3 := hf0 Finset.univ
  have z4 := hf0 (A ∪ C)ᶜ
  have e2n : 2 / n * O = 2 * (O / n) := by ring
  rw [hPhi, e2n]
  linarith
