-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.proposition_7_6_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:50:44.119614+00:00
-- url     : https://prove2.me/submissions/35ce6171-c456-4d2d-924a-5322c6b8c195

import Theorems.Thm_MDPFinance_InfiniteHorizonApplications_joint_index_action_dominates
import Theorems.Thm_MDPFinance_InfiniteHorizonApplications_corollary_7_6_8

set_option autoImplicit false
open MDPFinance.InfiniteHorizonApplications

namespace JointStructure

private lemma probability (mn : ℕ × ℕ) : 0 ≤ pMN mn ∧ pMN mn ≤ 1 := by
  unfold pMN
  have hm : (0 : ℝ) ≤ mn.1 := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ mn.2 := Nat.cast_nonneg _
  constructor
  · positivity
  · apply (div_le_one (by positivity)).2
    linarith

private lemma q_shift (a : Fin 2) (u v : BanditState2 → ℝ) (d : ℝ)
    (h : ∀ y, u y ≤ v y + d) (x : BanditState2) :
    QaBandit a u x ≤ QaBandit a v x + d := by
  unfold QaBandit Q1Bandit Q2Bandit
  split
  · have hp := probability x.1
    nlinarith [mul_le_mul_of_nonneg_left (h ((x.1.1+1,x.1.2),x.2)) hp.1,
      mul_le_mul_of_nonneg_left (h ((x.1.1,x.1.2+1),x.2)) (sub_nonneg.mpr hp.2)]
  · have hp := probability x.2
    nlinarith [mul_le_mul_of_nonneg_left (h (x.1,(x.2.1+1,x.2.2))) hp.1,
      mul_le_mul_of_nonneg_left (h (x.1,(x.2.1,x.2.2+1))) (sub_nonneg.mpr hp.2)]

private lemma q_affine (a : Fin 2) (u v : BanditState2 → ℝ) (s t d : ℝ)
    (x : BanditState2) :
    QaBandit a (fun y => s * u y + t * v y + d) x =
      s * QaBandit a u x + t * QaBandit a v x + d := by
  unfold QaBandit Q1Bandit Q2Bandit
  split <;> ring

private noncomputable def B (β K : ℝ) (v : BanditState2 → ℝ) (x : BanditState2) : ℝ :=
  max K (max (paBandit 0 x + β * QaBandit 0 v x)
    (paBandit 1 x + β * QaBandit 1 v x))

/-- Bounded subsolutions lie below supersolutions of the discounted stopped Bellman operator. -/
private lemma comparison {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (u v : BanditState2 → ℝ) (hb : ∃ C : ℝ, ∀ x, u x - v x ≤ C)
    (hu : ∀ x, u x ≤ B β K u x) (hv : ∀ x, B β K v x ≤ v x) :
    ∀ x, u x ≤ v x := by
  classical
  obtain ⟨C, hC⟩ := hb
  let S := sSup (Set.range (fun x => u x - v x))
  have hbounded : BddAbove (Set.range (fun x => u x - v x)) :=
    ⟨C, by rintro y ⟨x, rfl⟩; exact hC x⟩
  have hsup : ∀ x, u x - v x ≤ S := fun x => le_csSup hbounded ⟨x, rfl⟩
  intro x
  by_contra h
  have hpos : 0 < S := lt_of_lt_of_le (sub_pos.mpr (lt_of_not_ge h)) (hsup x)
  have hstep : ∀ y, u y - v y ≤ β * S := by
    intro y
    have hq (a : Fin 2) := q_shift a u v S (fun z => by linarith [hsup z]) y
    have hstop : K ≤ v y := (le_max_left _ _).trans (hv y)
    have h0 : paBandit 0 y + β * QaBandit 0 v y ≤ v y :=
      (le_max_of_le_right (le_max_left _ _)).trans (hv y)
    have h1 : paBandit 1 y + β * QaBandit 1 v y ≤ v y :=
      (le_max_of_le_right (le_max_right _ _)).trans (hv y)
    have hbu : B β K u y ≤ v y + β * S := by
      apply max_le
      · nlinarith
      · apply max_le <;> nlinarith [mul_le_mul_of_nonneg_left (hq 0) hβ0.le,
          mul_le_mul_of_nonneg_left (hq 1) hβ0.le]
    linarith [hu y]
  have hS : S ≤ β * S := csSup_le (Set.range_nonempty _) (by
    rintro y ⟨z, rfl⟩; exact hstep z)
  nlinarith

private lemma lower {β : ℝ} (J : JointKStoppingValue β) (K : ℝ) (x : BanditState2) :
    K ≤ J.Jt K x := by rw [J.hJt_fix]; exact le_max_left _ _

private lemma arm_le {β : ℝ} (J : JointKStoppingValue β) (K : ℝ) (a : Fin 2)
    (x : BanditState2) : paBandit a x + β * QaBandit a (J.Jt K) x ≤ J.Jt K x := by
  rw [J.hJt_fix]
  by_cases h : a = 0
  · subst a; exact le_max_of_le_right (le_max_left _ _)
  · have ha : a = 1 := by omega
    subst a; exact le_max_of_le_right (le_max_right _ _)

private lemma monotone_value {β : ℝ} (J : JointKStoppingValue β) (x : BanditState2) :
    Monotone (J.Jt · x) := by
  intro K L hKL
  obtain ⟨C, hC⟩ := J.hJt_bdd K
  obtain ⟨D, hD⟩ := J.hJt_bdd L
  refine comparison (K := K) J.hβ0 J.hβ1 (J.Jt K) (J.Jt L) ?_ ?_ ?_ x
  · exact ⟨C + D, fun y => by linarith [(abs_le.mp (hC y)).2, (abs_le.mp (hD y)).1]⟩
  · intro y; exact (J.hJt_fix K y).le
  · intro y
    exact max_le (hKL.trans (lower J L y))
      (max_le (arm_le J L 0 y) (arm_le J L 1 y))

private lemma shift_value {β : ℝ} (J : JointKStoppingValue β) {K L : ℝ} (hKL : K ≤ L)
    (x : BanditState2) : J.Jt L x ≤ J.Jt K x + (L - K) := by
  obtain ⟨C, hC⟩ := J.hJt_bdd K
  obtain ⟨D, hD⟩ := J.hJt_bdd L
  let v := fun y => J.Jt K y + (L - K)
  refine comparison (K := L) J.hβ0 J.hβ1 (J.Jt L) v ?_ ?_ ?_ x
  · refine ⟨C + D - (L - K), fun y => ?_⟩
    dsimp [v]; linarith [(abs_le.mp (hC y)).1, (abs_le.mp (hD y)).2]
  · intro y; exact (J.hJt_fix L y).le
  · intro y
    have hq (a : Fin 2) : QaBandit a v y = QaBandit a (J.Jt K) y + (L - K) := by
      simpa [v] using q_affine a (J.Jt K) (J.Jt K) 1 0 (L - K) y
    apply max_le
    · dsimp [v]; linarith [lower J K y]
    · apply max_le
      all_goals
        rw [hq]
        dsimp [v]
        nlinarith [arm_le J K 0 y, arm_le J K 1 y, J.hβ1]

private lemma regularity {β : ℝ} (J : JointKStoppingValue β) (x : BanditState2) :
    (Monotone (J.Jt · x) ∧ Continuous (J.Jt · x) ∧ ConvexOn ℝ Set.univ (J.Jt · x)) ∧
      Antitone (fun K => J.Jt K x - K) := by
  have hmono := monotone_value J x
  have hanti : Antitone (fun K => J.Jt K x - K) := by
    intro K L hKL
    linarith [shift_value J hKL x]
  have hlip : LipschitzWith 1 (J.Jt · x) := by
    apply LipschitzWith.of_dist_le_mul
    intro K L
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rcases le_total K L with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr (hmono h)), abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [shift_value J h x]
    · rw [abs_of_nonneg (sub_nonneg.mpr (hmono h)), abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [shift_value J h x]
  refine ⟨⟨hmono, hlip.continuous, ?_⟩, hanti⟩
  refine ⟨convex_univ, ?_⟩
  intro K _ L _ s t hs ht hst
  obtain ⟨C, hC⟩ := J.hJt_bdd K
  obtain ⟨D, hD⟩ := J.hJt_bdd L
  obtain ⟨E, hE⟩ := J.hJt_bdd (s * K + t * L)
  let v := fun y => s * J.Jt K y + t * J.Jt L y
  change J.Jt (s * K + t * L) x ≤ v x
  refine comparison (K := s*K+t*L) J.hβ0 J.hβ1 (J.Jt (s * K + t * L)) v ?_ ?_ ?_ x
  · refine ⟨E + s * C + t * D, fun y => ?_⟩
    dsimp [v]
    nlinarith [(abs_le.mp (hE y)).2,
      mul_le_mul_of_nonneg_left (abs_le.mp (hC y)).1 hs,
      mul_le_mul_of_nonneg_left (abs_le.mp (hD y)).1 ht]
  · intro y; exact (J.hJt_fix _ y).le
  · intro y
    apply max_le
    · dsimp [v]
      exact add_le_add (mul_le_mul_of_nonneg_left (lower J K y) hs)
        (mul_le_mul_of_nonneg_left (lower J L y) ht)
    · have ha (a : Fin 2) : paBandit a y + β * QaBandit a v y ≤ v y := by
        have hq : QaBandit a v y = s * QaBandit a (J.Jt K) y +
            t * QaBandit a (J.Jt L) y := by
          simpa [v] using q_affine a (J.Jt K) (J.Jt L) s t 0 y
        rw [hq]
        have hr := congrArg (fun z : ℝ => z * paBandit a y) hst
        have heq : paBandit a y + β * (s * QaBandit a (J.Jt K) y +
            t * QaBandit a (J.Jt L) y) =
            s * (paBandit a y + β * QaBandit a (J.Jt K) y) +
            t * (paBandit a y + β * QaBandit a (J.Jt L) y) := by
          nlinarith only [hr]
        rw [heq]
        exact add_le_add (mul_le_mul_of_nonneg_left (arm_le J K a y) hs)
          (mul_le_mul_of_nonneg_left (arm_le J L a y) ht)
      exact max_le (ha 0) (ha 1)

/-- The sum of the two single-arm excess values is a joint Bellman supersolution. -/
private lemma sum_supersolution {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) :
    ∀ x, B β K (fun y => KS.J K y.1 + KS.J K y.2 - K) x ≤
      KS.J K x.1 + KS.J K x.2 - K := by
  have hlo (i : ℕ × ℕ) : K ≤ KS.J K i := by
    rw [KS.hJ_fix]; exact le_max_left _ _
  have hcont (i : ℕ × ℕ) : pMN i + β * PQ pMN (KS.J K) i ≤ KS.J K i := by
    rw [KS.hJ_fix K i]; exact le_max_right _ _
  intro x
  apply max_le
  · linarith [hlo x.1, hlo x.2]
  · apply max_le
    · have heq : QaBandit 0 (fun y => KS.J K y.1 + KS.J K y.2 - K) x =
          PQ pMN (KS.J K) x.1 + KS.J K x.2 - K := by
        simp only [QaBandit, ↓reduceIte, Q1Bandit, PQ]
        ring
      rw [heq]
      simp only [paBandit, ↓reduceIte]
      nlinarith [hcont x.1, hlo x.2, KS.hβ1]
    · have heq : QaBandit 1 (fun y => KS.J K y.1 + KS.J K y.2 - K) x =
          PQ pMN (KS.J K) x.2 + KS.J K x.1 - K := by
        norm_num [QaBandit, Q2Bandit, PQ]
        ring
      rw [heq]
      norm_num [paBandit]
      nlinarith [hcont x.2, hlo x.1, KS.hβ1]

private lemma stopping_forward {β : ℝ} (KS : KStoppingValue β pMN)
    (J : JointKStoppingValue β) (K : ℝ) (x : BanditState2)
    (hK : max (GittinsIndex KS x.1) (GittinsIndex KS x.2) ≤ K) : J.Jt K x = K := by
  obtain ⟨C, hC⟩ := J.hJt_bdd K
  obtain ⟨D, hD⟩ := KS.hJ_bdd K
  have hcompare : ∀ y, J.Jt K y ≤ KS.J K y.1 + KS.J K y.2 - K := by
    refine comparison (K := K) J.hβ0 J.hβ1 _ _ ?_ ?_ (sum_supersolution KS K)
    · refine ⟨C + 2*D + K, fun y => ?_⟩
      linarith [(abs_le.mp (hC y)).2, (abs_le.mp (hD y.1)).1,
        (abs_le.mp (hD y.2)).1]
    · intro y; exact (J.hJt_fix K y).le
  have hindex := (corollary_7_6_8 KS).1
  have h1 := (hindex K x.1.1 x.1.2).mpr ((le_max_left _ _).trans hK)
  have h2 := (hindex K x.2.1 x.2.2).mpr ((le_max_right _ _).trans hK)
  have hu := hcompare x
  rw [h1, h2] at hu
  linarith [lower J K x]

/-- Either isolated arm's value can be attained without playing the other arm. -/
private lemma single_le_joint {β : ℝ} (KS : KStoppingValue β pMN)
    (J : JointKStoppingValue β) (K : ℝ) (x : BanditState2) :
    KS.J K x.1 ≤ J.Jt K x ∧ KS.J K x.2 ≤ J.Jt K x := by
  obtain ⟨C, hC⟩ := J.hJt_bdd K
  obtain ⟨D, hD⟩ := KS.hJ_bdd K
  constructor
  · refine comparison (K := K) J.hβ0 J.hβ1 (fun y => KS.J K y.1) (J.Jt K) ?_ ?_ ?_ x
    · exact ⟨C+D, fun y => by linarith [(abs_le.mp (hD y.1)).2, (abs_le.mp (hC y)).1]⟩
    · intro y
      have heq : QaBandit 0 (fun z => KS.J K z.1) y = PQ pMN (KS.J K) y.1 := by
        simp [QaBandit, Q1Bandit, PQ]
      rw [KS.hJ_fix K y.1]
      apply max_le_max_left
      apply le_max_of_le_left
      simp only [heq, paBandit, ↓reduceIte, le_refl]
    · intro y; exact (J.hJt_fix K y).ge
  · refine comparison (K := K) J.hβ0 J.hβ1 (fun y => KS.J K y.2) (J.Jt K) ?_ ?_ ?_ x
    · exact ⟨C+D, fun y => by linarith [(abs_le.mp (hD y.2)).2, (abs_le.mp (hC y)).1]⟩
    · intro y
      have heq : QaBandit 1 (fun z => KS.J K z.2) y = PQ pMN (KS.J K) y.2 := by
        norm_num [QaBandit, Q2Bandit, PQ]
      rw [KS.hJ_fix K y.2]
      apply max_le_max_left
      apply le_max_of_le_right
      norm_num [heq, paBandit]
    · intro y; exact (J.hJt_fix K y).ge

private lemma stopping_iff {β : ℝ} (KS : KStoppingValue β pMN)
    (J : JointKStoppingValue β) (K : ℝ) (x : BanditState2) :
    J.Jt K x = K ↔ max (GittinsIndex KS x.1) (GittinsIndex KS x.2) ≤ K := by
  refine ⟨?_, stopping_forward KS J K x⟩
  intro h
  have hs := single_le_joint KS J K x
  rw [h] at hs
  have hlo (i : ℕ × ℕ) : K ≤ KS.J K i := by rw [KS.hJ_fix]; exact le_max_left _ _
  exact max_le ((corollary_7_6_8 KS).1 K x.1.1 x.1.2 |>.mp (le_antisymm hs.1 (hlo x.1)))
    ((corollary_7_6_8 KS).1 K x.2.1 x.2.2 |>.mp (le_antisymm hs.2 (hlo x.2)))

end JointStructure

theorem solution {β : ℝ} (KS : KStoppingValue β pMN) (JKS : JointKStoppingValue β)
    (x : BanditState2) :
    (Monotone (JKS.Jt · x) ∧ Continuous (JKS.Jt · x) ∧ ConvexOn ℝ Set.univ (JKS.Jt · x)) ∧
      Antitone (fun K => JKS.Jt K x - K) ∧
      (∀ astar : Fin 2, (astar = 0 → GittinsIndex KS x.2 ≤ GittinsIndex KS x.1) →
        (astar = 1 → GittinsIndex KS x.1 ≤ GittinsIndex KS x.2) →
        max (GittinsIndex KS x.1) (GittinsIndex KS x.2) =
          (if astar = 0 then GittinsIndex KS x.1 else GittinsIndex KS x.2) →
        (∀ K, max (GittinsIndex KS x.1) (GittinsIndex KS x.2) ≤ K → JKS.Jt K x = K) ∧
          ∀ K, K < max (GittinsIndex KS x.1) (GittinsIndex KS x.2) →
            JKS.Jt K x = paBandit astar x + β * QaBandit astar (JKS.Jt K) x) := by
  obtain ⟨hr, ha⟩ := JointStructure.regularity JKS x
  refine ⟨hr, ha, ?_⟩
  intro astar h0 h1 _
  refine ⟨fun K hK => JointStructure.stopping_forward KS JKS K x hK, ?_⟩
  intro K hK
  have hdom := joint_index_action_dominates KS JKS x astar h0 h1 K hK
  have hmax : max (paBandit 0 x + β * QaBandit 0 (JKS.Jt K) x)
      (paBandit 1 x + β * QaBandit 1 (JKS.Jt K) x) =
      paBandit astar x + β * QaBandit astar (JKS.Jt K) x := by
    apply le_antisymm (max_le (hdom 0) (hdom 1))
    by_cases h : astar = 0
    · subst astar; exact le_max_left _ _
    · have h' : astar = 1 := by omega
      subst astar; exact le_max_right _ _
  have hf := JKS.hJt_fix K x
  rw [hmax] at hf
  have hne : JKS.Jt K x ≠ K := by
    intro he
    exact (not_le_of_gt hK) ((JointStructure.stopping_iff KS JKS K x).mp he)
  have hcont : K ≤ paBandit astar x + β * QaBandit astar (JKS.Jt K) x := by
    by_contra h
    exact hne (hf.trans (max_eq_left (le_of_not_ge h)))
  exact hf.trans (max_eq_right hcont)
