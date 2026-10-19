-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.joint_index_action_dominates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:01:27.369409+00:00
-- url     : https://prove2.me/submissions/1ce83d42-bbc7-47e1-9a9e-38134ebda66a

import Theorems.Thm_MDPFinance_InfiniteHorizonApplications_proposition_7_6_7
import Theorems.Thm_MDPFinance_InfiniteHorizonApplications_corollary_7_6_8

set_option autoImplicit false
open MeasureTheory Set Filter
open MDPFinance.InfiniteHorizonApplications
open scoped Topology

namespace GittinsAction

private noncomputable def d {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ) : ℝ :=
  derivWithin (fun K => KS.J K i) (Ici t) t

private lemma prob (i : ℕ × ℕ) : 0 ≤ pMN i ∧ pMN i ≤ 1 := by
  unfold pMN
  have hm : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ i.2 := Nat.cast_nonneg _
  constructor
  · positivity
  · apply (div_le_one (by positivity)).2; linarith

private lemma d_bounds {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ) :
    0 ≤ d KS i t ∧ d KS i t ≤ 1 :=
  (proposition_7_6_7 KS i.1 i.2).2.2.2.choose_spec.2.2.2.1 t

private lemma d_mono {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) : Monotone (d KS i) :=
  (proposition_7_6_7 KS i.1 i.2).2.2.2.choose_spec.2.2.2.2

private lemma d_has {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ) :
    HasDerivWithinAt (fun K => KS.J K i) (d KS i t) (Ici t) t :=
  ((proposition_7_6_7 KS i.1 i.2).2.2.2.choose_spec.2.2.1 t).1.hasDerivWithinAt

private lemma d_stop {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ)
    (ht : GittinsIndex KS i ≤ t) : d KS i t = 1 := by
  have heq : ∀ s ∈ Ici t, KS.J s i = s := by
    intro s hs
    exact (corollary_7_6_8 KS).1 s i.1 i.2 |>.2 (ht.trans hs)
  exact ((hasDerivWithinAt_id t (Ici t)).congr_of_mem heq (mem_Ici.mpr le_rfl)).derivWithin
    (uniqueDiffWithinAt_Ici t)

private lemma d_continue {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ)
    (ht : t < GittinsIndex KS i) :
    d KS i t = β * PQ pMN (fun j => d KS j t) i := by
  have hder : HasDerivWithinAt
      (fun s => pMN i + β * PQ pMN (KS.J s) i)
      (β * PQ pMN (fun j => d KS j t) i) (Ici t) t := by
    simpa only [PQ, Pi.smul_apply, smul_eq_mul] using
      HasDerivWithinAt.const_add (pMN i)
        (HasDerivWithinAt.const_smul β
          ((HasDerivWithinAt.const_smul (pMN i) (d_has KS (i.1+1,i.2) t)).fun_add
            (HasDerivWithinAt.const_smul (1-pMN i) (d_has KS (i.1,i.2+1) t))))
  have heq : (fun s => KS.J s i) =ᶠ[𝓝[Ici t] t]
      (fun s => pMN i + β * PQ pMN (KS.J s) i) := by
    filter_upwards [(eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds] with s hs
    exact (proposition_7_6_7 KS i.1 i.2).2.2.1.2.1 s hs
  have heqx := (proposition_7_6_7 KS i.1 i.2).2.2.1.2.1 t ht
  exact (hder.congr_of_eventuallyEq heq heqx).derivWithin (uniqueDiffWithinAt_Ici t)

private noncomputable def ed {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ) : ℝ :=
  PQ pMN (fun j => d KS j t) i

private noncomputable def g {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ) : ℝ :=
  d KS i t - β * ed KS i t

private lemma ed_bounds {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ) :
    0 ≤ ed KS i t ∧ ed KS i t ≤ 1 := by
  have hp := prob i
  have hs := d_bounds KS (i.1+1,i.2) t
  have hf := d_bounds KS (i.1,i.2+1) t
  dsimp [ed, PQ]
  constructor
  · exact add_nonneg (mul_nonneg hp.1 hs.1) (mul_nonneg (sub_nonneg.mpr hp.2) hf.1)
  · nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hs.2),
      mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hf.2)]

private lemma g_nonneg {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ) :
    0 ≤ g KS i t := by
  by_cases ht : t < GittinsIndex KS i
  · dsimp [g, ed]; rw [d_continue KS i t ht]; simp
  · dsimp [g]; rw [d_stop KS i t (le_of_not_gt ht)]
    have he := ed_bounds KS i t
    nlinarith [KS.hβ0, KS.hβ1]

private lemma g_zero {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (t : ℝ)
    (ht : t < GittinsIndex KS i) : g KS i t = 0 := by
  dsimp [g, ed]; rw [d_continue KS i t ht]; ring

private lemma ed_mono {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) : Monotone (ed KS i) := by
  intro a b hab
  dsimp [ed, PQ]
  exact add_le_add (mul_le_mul_of_nonneg_left (d_mono KS _ hab) (prob i).1)
    (mul_le_mul_of_nonneg_left (d_mono KS _ hab) (sub_nonneg.mpr (prob i).2))

private lemma g_int {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (a b : ℝ) :
    IntervalIntegrable (g KS i) volume a b :=
  (d_mono KS i).intervalIntegrable.sub ((ed_mono KS i).intervalIntegrable.const_mul β)

private lemma dd_int {β : ℝ} (KS : KStoppingValue β pMN) (i j : ℕ × ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => d KS i t * d KS j t) volume a b := by
  apply Monotone.intervalIntegrable
  intro s t hst
  exact mul_le_mul (d_mono KS i hst) (d_mono KS j hst) (d_bounds KS j s).1 (d_bounds KS i t).1

private lemma edd_int {β : ℝ} (KS : KStoppingValue β pMN) (i j : ℕ × ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => ed KS i t * d KS j t) volume a b := by
  apply Monotone.intervalIntegrable
  intro s t hst
  exact mul_le_mul (ed_mono KS i hst) (d_mono KS j hst) (d_bounds KS j s).1 (ed_bounds KS i t).1

private lemma gd_int {β : ℝ} (KS : KStoppingValue β pMN) (i j : ℕ × ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => g KS i t * d KS j t) volume a b := by
  have := (dd_int KS i j a b).sub ((edd_int KS i j a b).const_mul β)
  convert this using 1
  ext t; dsimp [g]; ring

private noncomputable def U (β : ℝ) : ℝ := 1 / (1 - β)

private lemma U_identity {β : ℝ} (KS : KStoppingValue β pMN) : (1-β) * U β = 1 := by
  exact mul_one_div_cancel (by linarith [KS.hβ1])

private lemma index_le_U {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) :
    GittinsIndex KS i ≤ U β := (corollary_7_6_8 KS).2.2.1 i.1 i.2 |>.2

private lemma J_U {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) :
    KS.J (U β) i = U β := (corollary_7_6_8 KS).1 _ i.1 i.2 |>.2 (index_le_U KS i)

private lemma integral_d {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (K : ℝ) :
    (∫ t in K..U β, d KS i t) = U β - KS.J K i := by
  calc
    _ = KS.J (U β) i - KS.J K i :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right
        (proposition_7_6_7 KS i.1 i.2).1.2.1.continuousOn
        (fun t _ => (d_has KS i t).Ioi_of_Ici) (d_mono KS i).intervalIntegrable
    _ = _ := by rw [J_U]

private lemma integral_ed {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (K : ℝ) :
    (∫ t in K..U β, ed KS i t) = U β - PQ pMN (KS.J K) i := by
  dsimp [ed, PQ]
  rw [intervalIntegral.integral_add ((d_mono KS _).intervalIntegrable.const_mul _)
    ((d_mono KS _).intervalIntegrable.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_d, integral_d]
  ring

private lemma integral_g {β : ℝ} (KS : KStoppingValue β pMN) (i : ℕ × ℕ) (K : ℝ) :
    (∫ t in K..U β, g KS i t) = 1 - KS.J K i + β * PQ pMN (KS.J K) i := by
  dsimp [g]
  rw [intervalIntegral.integral_sub (d_mono KS i).intervalIntegrable
    ((ed_mono KS i).intervalIntegrable.const_mul β), intervalIntegral.integral_const_mul,
    integral_d, integral_ed]
  nlinarith [U_identity KS]

private noncomputable def V {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (x : BanditState2) : ℝ :=
  U β - ∫ t in K..U β, d KS x.1 t * d KS x.2 t

private lemma V_swap {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (i j : ℕ × ℕ) :
    V KS K (i,j) = V KS K (j,i) := by
  dsimp [V]; congr 1; apply intervalIntegral.integral_congr; intro t _; ring

private lemma V_bounds {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (hK : K ≤ U β)
    (x : BanditState2) : K ≤ V KS K x ∧ V KS K x ≤ U β := by
  have hi := dd_int KS x.1 x.2 K (U β)
  have hlo := intervalIntegral.integral_mono hK (intervalIntegrable_const (c := (0:ℝ))) hi
    (fun t => mul_nonneg (d_bounds KS x.1 t).1 (d_bounds KS x.2 t).1)
  have hhi := intervalIntegral.integral_mono hK hi (intervalIntegrable_const (c := (1:ℝ)))
    (fun t => by
      simpa using mul_le_mul (d_bounds KS x.1 t).2 (d_bounds KS x.2 t).2
        (d_bounds KS x.2 t).1 (by norm_num : (0:ℝ) ≤ 1))
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero, mul_one] at hlo hhi
  dsimp [V]; constructor <;> linarith

private lemma V_stopped {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (x : BanditState2)
    (h1 : GittinsIndex KS x.1 ≤ K) (h2 : GittinsIndex KS x.2 ≤ K) : V KS K x = K := by
  dsimp [V]
  have heq : (∫ t in K..U β, d KS x.1 t * d KS x.2 t) = ∫ t in K..U β, (1:ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hl : min K (U β) ≤ t := ht.1
    have hi1 : GittinsIndex KS x.1 ≤ min K (U β) := le_min h1 (index_le_U KS _)
    have hi2 : GittinsIndex KS x.2 ≤ min K (U β) := le_min h2 (index_le_U KS _)
    dsimp only
    rw [d_stop KS _ t (hi1.trans hl), d_stop KS _ t (hi2.trans hl), one_mul]
  rw [heq, intervalIntegral.integral_const]; simp

private lemma action_identity {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (i j : ℕ × ℕ) :
    pMN i + β * PQ pMN (fun k => V KS K (k,j)) i - V KS K (i,j) =
      pMN i - 1 + ∫ t in K..U β, g KS i t * d KS j t := by
  have he : (∫ t in K..U β, ed KS i t * d KS j t) =
      pMN i * (∫ t in K..U β, d KS (i.1+1,i.2) t * d KS j t) +
      (1-pMN i) * (∫ t in K..U β, d KS (i.1,i.2+1) t * d KS j t) := by
    calc
      _ = ∫ t in K..U β,
          pMN i * (d KS (i.1+1,i.2) t * d KS j t) +
            (1-pMN i) * (d KS (i.1,i.2+1) t * d KS j t) := by
        apply intervalIntegral.integral_congr
        intro t _; dsimp [ed, PQ]; ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((dd_int KS _ j K (U β)).const_mul _)
          ((dd_int KS _ j K (U β)).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hg : (∫ t in K..U β, g KS i t * d KS j t) =
      (∫ t in K..U β, d KS i t * d KS j t) -
        β * (∫ t in K..U β, ed KS i t * d KS j t) := by
    calc
      _ = ∫ t in K..U β, d KS i t * d KS j t - β * (ed KS i t * d KS j t) := by
        apply intervalIntegral.integral_congr
        intro t _; dsimp [g]; ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (dd_int KS i j K (U β))
          ((edd_int KS i j K (U β)).const_mul β), intervalIntegral.integral_const_mul]
  rw [hg, he]
  dsimp only [PQ, V]
  have hU := U_identity KS
  linear_combination -hU

private lemma action_le {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (hK : K ≤ U β)
    (i j : ℕ × ℕ) : pMN i + β * PQ pMN (fun k => V KS K (k,j)) i ≤ V KS K (i,j) := by
  have hg := intervalIntegral.integral_mono hK (gd_int KS i j K (U β)) (g_int KS i K (U β))
    (fun t => mul_le_of_le_one_right (g_nonneg KS i t) (d_bounds KS j t).2)
  rw [integral_g] at hg
  have hj : pMN i + β * PQ pMN (KS.J K) i ≤ KS.J K i := by
    rw [KS.hJ_fix]; exact le_max_right _ _
  linarith [action_identity KS K i j]

private lemma action_eq {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (i j : ℕ × ℕ)
    (hij : GittinsIndex KS j ≤ GittinsIndex KS i) (hK : K < GittinsIndex KS i) :
    pMN i + β * PQ pMN (fun k => V KS K (k,j)) i = V KS K (i,j) := by
  have he : (∫ t in K..U β, g KS i t * d KS j t) = ∫ t in K..U β, g KS i t := by
    apply intervalIntegral.integral_congr
    intro t _; dsimp only
    by_cases ht : t < GittinsIndex KS i
    · rw [g_zero KS i t ht, zero_mul]
    · rw [d_stop KS j t (hij.trans (le_of_not_gt ht)), mul_one]
  have hj := (proposition_7_6_7 KS i.1 i.2).2.2.1.2.1 K hK
  have ha := action_identity KS K i j
  rw [he, integral_g] at ha
  change KS.J K i = pMN i + β * PQ pMN (KS.J K) i at hj
  linarith

private lemma qa0 {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (x : BanditState2) :
    paBandit 0 x + β * QaBandit 0 (V KS K) x =
      pMN x.1 + β * PQ pMN (fun k => V KS K (k,x.2)) x.1 := by
  simp [paBandit, QaBandit, Q1Bandit, PQ]

private lemma qa1 {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (x : BanditState2) :
    paBandit 1 x + β * QaBandit 1 (V KS K) x =
      pMN x.2 + β * PQ pMN (fun k => V KS K (k,x.1)) x.2 := by
  simp only [paBandit, QaBandit, show (1:Fin 2) ≠ 0 by decide, if_false, Q2Bandit, PQ]
  rw [V_swap KS K x.1 (x.2.1+1,x.2.2), V_swap KS K x.1 (x.2.1,x.2.2+1)]

private lemma V_arm_le {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (hK : K ≤ U β)
    (a : Fin 2) (x : BanditState2) :
    paBandit a x + β * QaBandit a (V KS K) x ≤ V KS K x := by
  by_cases ha : a = 0
  · subst a; rw [qa0]; exact action_le KS K hK x.1 x.2
  · have ha : a = 1 := by omega
    subst a; rw [qa1, V_swap KS K x.1 x.2]; exact action_le KS K hK x.2 x.1

private lemma V_arm_eq {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (x : BanditState2)
    (astar : Fin 2)
    (h0 : astar = 0 → GittinsIndex KS x.2 ≤ GittinsIndex KS x.1)
    (h1 : astar = 1 → GittinsIndex KS x.1 ≤ GittinsIndex KS x.2)
    (hK : K < max (GittinsIndex KS x.1) (GittinsIndex KS x.2)) :
    paBandit astar x + β * QaBandit astar (V KS K) x = V KS K x := by
  by_cases ha : astar = 0
  · subst astar
    have hh := h0 rfl
    rw [max_eq_left hh] at hK
    rw [qa0]; exact action_eq KS K x.1 x.2 hh hK
  · have ha : astar = 1 := by omega
    subst astar
    have hh := h1 rfl
    rw [max_eq_right hh] at hK
    rw [qa1, V_swap KS K x.1 x.2]; exact action_eq KS K x.2 x.1 hh hK

private lemma V_fix {β : ℝ} (KS : KStoppingValue β pMN) (K : ℝ) (hK : K ≤ U β)
    (x : BanditState2) :
    V KS K x = max K (max (paBandit 0 x + β * QaBandit 0 (V KS K) x)
      (paBandit 1 x + β * QaBandit 1 (V KS K) x)) := by
  apply le_antisymm
  · by_cases h : K < max (GittinsIndex KS x.1) (GittinsIndex KS x.2)
    · by_cases hi : GittinsIndex KS x.2 ≤ GittinsIndex KS x.1
      · rw [← V_arm_eq KS K x 0 (fun _ => hi) (by simp) h]
        exact le_max_of_le_right (le_max_left _ _)
      · have hi := le_of_not_ge hi
        rw [← V_arm_eq KS K x 1 (by simp) (fun _ => hi) h]
        exact le_max_of_le_right (le_max_right _ _)
    · have hh := le_of_not_gt h
      rw [V_stopped KS K x ((le_max_left _ _).trans hh) ((le_max_right _ _).trans hh)]
      exact le_max_left _ _
  · exact max_le (V_bounds KS K hK x).1
      (max_le (V_arm_le KS K hK 0 x) (V_arm_le KS K hK 1 x))

private lemma q_shift (a : Fin 2) (u v : BanditState2 → ℝ) (d : ℝ)
    (h : ∀ y, u y ≤ v y + d) (x : BanditState2) :
    QaBandit a u x ≤ QaBandit a v x + d := by
  unfold QaBandit Q1Bandit Q2Bandit
  split
  · have hp := prob x.1
    nlinarith [mul_le_mul_of_nonneg_left (h ((x.1.1+1,x.1.2),x.2)) hp.1,
      mul_le_mul_of_nonneg_left (h ((x.1.1,x.1.2+1),x.2)) (sub_nonneg.mpr hp.2)]
  · have hp := prob x.2
    nlinarith [mul_le_mul_of_nonneg_left (h (x.1,(x.2.1+1,x.2.2))) hp.1,
      mul_le_mul_of_nonneg_left (h (x.1,(x.2.1,x.2.2+1))) (sub_nonneg.mpr hp.2)]

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


private lemma V_eq {β : ℝ} (KS : KStoppingValue β pMN) (J : JointKStoppingValue β)
    (K : ℝ) (hK : K ≤ U β) (x : BanditState2) : J.Jt K x = V KS K x := by
  obtain ⟨C, hC⟩ := J.hJt_bdd K
  apply le_antisymm
  · refine comparison (K := K) J.hβ0 J.hβ1 (J.Jt K) (V KS K) ?_ ?_ ?_ x
    · exact ⟨C-K, fun y => by linarith [(abs_le.mp (hC y)).2, (V_bounds KS K hK y).1]⟩
    · intro y; exact (J.hJt_fix K y).le
    · intro y; exact (V_fix KS K hK y).ge
  · refine comparison (K := K) J.hβ0 J.hβ1 (V KS K) (J.Jt K) ?_ ?_ ?_ x
    · exact ⟨U β+C, fun y => by linarith [(abs_le.mp (hC y)).1, (V_bounds KS K hK y).2]⟩
    · intro y; exact (V_fix KS K hK y).le
    · intro y; exact (J.hJt_fix K y).ge

end GittinsAction

open GittinsAction

theorem solution
    {β : ℝ} (KS : KStoppingValue β pMN) (JKS : JointKStoppingValue β)
    (x : BanditState2) (astar : Fin 2)
    (h0 : astar = 0 → GittinsIndex KS x.2 ≤ GittinsIndex KS x.1)
    (h1 : astar = 1 → GittinsIndex KS x.1 ≤ GittinsIndex KS x.2)
    (K : ℝ) (hK : K < max (GittinsIndex KS x.1) (GittinsIndex KS x.2)) (a : Fin 2) :
    paBandit a x + β * QaBandit a (JKS.Jt K) x ≤
      paBandit astar x + β * QaBandit astar (JKS.Jt K) x := by
  have hKU : K ≤ U β := hK.le.trans (max_le (index_le_U KS _) (index_le_U KS _))
  have he : JKS.Jt K = V KS K := funext (V_eq KS JKS K hKU)
  rw [he, V_arm_eq KS K x astar h0 h1 hK]
  exact V_arm_le KS K hKU a x
