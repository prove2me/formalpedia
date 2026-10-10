-- Prove2me | solution 1 for IntMul.EndParkRecursiveAmortizedWork.kappa_bound_of_word_work
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T05:02:53.586737+00:00
-- url     : https://prove2.me/submissions/a81ebecf-3254-4b97-a6f4-7498e9e630a4

import Definitions.Def_IntMul_EndParkRecursiveAmortizedWork
import Theorems.Thm_IntMul_EndParkRecursiveTraffic_kappa_bound_of_traffic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem amortized_kappa_internal_blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step M _ _ ih

private theorem amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step c).cells j p = M.startSym ↔ p = 0 := by
  classical
  intro j p
  change Function.update (c.cells j) (c.head j)
    ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = M.startSym ↔ p = 0
  by_cases hp : p = c.head j
  · rw [hp,Function.update_self]
    by_cases hz : c.head j = 0
    · have hs := (M.start_preserved c.state (fun j => c.cells j (c.head j)) j ((unique j _).mpr hz)).1
      simp only [hs,hz,iff_true]
    · have hn := M.start_only_at_start c.state (fun j => c.cells j (c.head j)) j
        (mt (unique j _).mp hz)
      simp only [hn,hz,iff_false]
  · rw [Function.update_of_ne hp]
    exact unique j p

/-- Local markers stay unique in every actual child run, so a physical
rewind cannot stop at an interior payload cell. -/
private theorem amortized_kappa_internal_unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step M _ ih

private theorem amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem amortized_kappa_internal_heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact amortized_kappa_internal_solutions_intmultrackedbankedspaceinvariants_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.EndParkRecursiveAmortizedWork

open IntMul.EndParkRecursiveTraffic
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankedSimulation (nextExtent)

private theorem amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_le (M : MultitapeTM) (E : Fin M.k → ℕ) (B : ℕ)
    (h : ∀ j, E j≤ B) : span M E≤ B := by
  apply Finset.sup_le
  intro j _
  exact h j

private theorem amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_component (M : MultitapeTM) (E : Fin M.k → ℕ) (j : Fin M.k) :
    E j≤ span M E := Finset.le_sup (f:=E) (Finset.mem_univ j)

private theorem amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_slack_le_sum (M : MultitapeTM) (E : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    headSlack M E c j≤∑ i, headSlack M E c i :=
  Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)

/-- One body transition replenishes the potential by at most a fixed amount. -/
private theorem amortized_kappa_internal_potential_step (M : MultitapeTM) (E : Fin M.k → ℕ) (c : M.Cfg)
    (live : c.state≠M.qHalt) (near : ∀ j, c.head j≤ E j+1) :
    potential M (nextExtent M c E) (M.step c)≤ potential M E c+(2*M.k+3) := by
  have hs : span M (nextExtent M c E)≤ span M E+1 := by
    apply amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_le
    intro j
    have := near j
    have := amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_component M E j
    simp only [nextExtent,if_neg live]
    omega
  have ho : nextExtent M c E M.outTape≤ E M.outTape+1 := by
    have := near M.outTape
    simp only [nextExtent,if_neg live]
    omega
  have hslack : ∀ j, headSlack M (nextExtent M c E) (M.step c) j≤ headSlack M E c j+2 := by
    intro j
    by_cases hj : j=M.outTape
    · simp [headSlack,hj]
    · have hh : c.head j≤ (M.step c).head j+1 := by
        simp only [MultitapeTM.step]
        split <;> omega
      simp only [headSlack,if_neg hj,nextExtent,if_neg live]
      omega
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hslack j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  unfold potential
  omega

/-- Resumption releases all nonresult head-distance potential. -/
private theorem amortized_kappa_internal_potential_resume (M : MultitapeTM) (labels : ℕ) (resume : Fin labels → M.K)
    (E : Fin M.k → ℕ) (c : M.Cfg) (label : Fin labels) (w : List Bool) :
    potential M (parentAfterChildExtent M E w) (resumedParent M labels resume label E c w)≤
      span M E+3*w.length := by
  have hs : span M (parentAfterChildExtent M E w)≤ span M E+w.length := by
    apply amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_le
    intro j
    have := amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_component M E j
    simp only [parentAfterChildExtent]
    split <;> omega
  have hz : ∀ j, headSlack M (parentAfterChildExtent M E w)
      (resumedParent M labels resume label E c w) j=0 := by
    intro j
    by_cases hj : j=M.outTape <;> simp [headSlack,parentAfterChildExtent,resumedParent,hj]
  unfold potential
  simp only [parentAfterChildExtent,if_true]
  simp_rw [hz]
  simp only [Finset.sum_const_zero]
  omega

/-- Native child initialization has potential linear in its input packet. -/
private theorem amortized_kappa_internal_potential_initial (M : MultitapeTM) (x y : List Bool) :
    potential M (initialExtent M x y) (M.initCfg x y)≤
      (M.k+1)*(inputWord M x y).length+M.k := by
  have hs : span M (initialExtent M x y)≤ (inputWord M x y).length := by
    apply amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_le
    intro j
    simp only [initialExtent]
    split <;> omega
  have hio : M.outTape≠M.inTape := by
    simp [MultitapeTM.outTape,MultitapeTM.inTape,Fin.ext_iff]
  have ho : initialExtent M x y M.outTape=0 := by simp [initialExtent,hio]
  have hslack : ∀ j, headSlack M (initialExtent M x y) (M.initCfg x y) j≤ (inputWord M x y).length+1 := by
    intro j
    simp only [headSlack,MultitapeTM.initCfg,Nat.sub_zero,initialExtent]
    split
    · omega
    · split <;> omega
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hslack j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  unfold potential
  rw [ho]
  nlinarith

private theorem amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_reservation_le_slack (M : MultitapeTM) (E : Fin M.k → ℕ) (c : M.Cfg) :
    reservationDistance M E c≤ E M.outTape+1+∑ j, headSlack M E c j := by
  apply amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_space_le
  intro j
  by_cases hj : j=M.outTape
  · subst j
    simp [TrackedBankReservation.distance,parentAfterInput]
  · have h := amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_slack_le_sum M E c j
    rw [show headSlack M E c j=E j+1-c.head j by simp [headSlack,hj]] at h
    simp only [TrackedBankReservation.distance,parentAfterInput,if_neg hj]
    omega

/-- Call traffic, remaining parent potential and initial child potential
are paid by the old potential plus simple argument/result word lengths. -/
private theorem amortized_kappa_internal_call_balance (M : MultitapeTM) (labels : ℕ) (resume : Fin labels → M.K)
    (E : Fin M.k → ℕ) (c : M.Cfg) (label : Fin labels) (v x y childWord : List Bool)
    (near : ∀ j, c.head j≤ E j+1) :
    callTraffic M labels E c v x y childWord+
      potential M (parentAfterChildExtent M E childWord)
        (resumedParent M labels resume label E c childWord)+
      potential M (initialExtent M x y) (M.initCfg x y)≤
      potential M E c+callWordWork M labels v x y childWord := by
  have hr := amortized_kappa_internal_solutions_intmulendparkrecursiveamortizedcosts_reservation_le_slack M E c
  have hp := amortized_kappa_internal_potential_resume M labels resume E c label childWord
  have hi := amortized_kappa_internal_potential_initial M x y
  have hh := near M.outTape
  unfold callTraffic potential callWordWork at *
  nlinarith

end IntMul.EndParkRecursiveAmortizedWork



namespace IntMul.EndParkRecursiveAmortizedWork

open IntMul.EndParkRecursiveTraffic
open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- Amortization removes retained extents and head distances from the
recursive word-work charge. Only an initial potential and fixed cost per
ordinary body step remain. -/
private theorem amortized_kappa_internal_traffic_of_word_work (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps work : ℕ)
    (certificate : HasWordWork M labels request resume extent c v w steps work) :
    (∀ j, c.head j≤ extent j+1) →
      ∃ mass : ℕ, mass≤ work+potential M extent c+(2*M.k+3)*steps ∧
        HasTraffic M labels request resume extent c v w steps mass := by
  induction certificate with
  | halt extent c v w halt out =>
    intro near
    refine ⟨returnTraffic M extent v w,?_,HasTraffic.halt extent c v w halt out⟩
    unfold returnTraffic potential
    omega
  | step extent c v w steps work live ordinary rest ih =>
    intro near
    have hnear := TrackedBankedSpace.amortized_kappa_internal_heads_near_run M c extent 1 near
    simp only [Function.iterate_one,TrackedBankedSimulation.extents,
      Function.iterate_zero,Function.id_def] at hnear
    obtain ⟨mass,hm,htraffic⟩ := ih hnear
    refine ⟨mass,?_,HasTraffic.step extent c v w steps mass live ordinary htraffic⟩
    have hp := amortized_kappa_internal_potential_step M extent c live near
    nlinarith
  | call extent c v x y childWord w label childSteps childWork parentSteps parentWork live request_label packet child parent ihchild ihparent =>
    intro near
    obtain ⟨childMass,hchildMass,hchild⟩ := ihchild (by intro j; simp [MultitapeTM.initCfg])
    have hpnear : ∀ j, (resumedParent M labels resume label extent c childWord).head j≤
        parentAfterChildExtent M extent childWord j+1 := by
      intro j
      by_cases hj : j=M.outTape <;> simp [resumedParent,parentAfterChildExtent,hj]
    obtain ⟨parentMass,hparentMass,hparent⟩ := ihparent hpnear
    refine ⟨childMass+parentMass+callTraffic M labels extent c v x y childWord,?_,
      HasTraffic.call extent c v x y childWord w label childSteps childMass parentSteps parentMass
        live request_label packet hchild hparent⟩
    have hp := amortized_kappa_internal_call_balance M labels resume extent c label v x y childWord near
    nlinarith

end IntMul.EndParkRecursiveAmortizedWork


namespace IntMul.EndParkRecursiveAmortizedWork

open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- Word-only certificates suffice for the campaign's exact time predicate;
all head-distance and retained-space estimates are discharged by amortization. -/
private theorem kappa_bound_of_word_work (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ≤ 1)
    (total : ∀ width : ℕ, 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps work : ℕ, HasWordWork M labels request resume (initialExtent M x y)
          (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps work)
    (C : ℝ) (hC : 0< C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold≤ width → 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps work : ℕ, ((steps+32*(work+(2*M.k+3)*steps):ℕ):ℝ)≤
          C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          HasWordWork M labels request resume (initialExtent M x y)
            (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps work) :
    KappaBound κ := by
  let A : ℕ := 128*M.k+96
  refine EndParkRecursiveTraffic.kappa_bound_of_traffic M labels request resume κ hκ ?_
    (C+(A:ℝ)) (by positivity) threshold ?_
  · intro width hwidth x y hx hy
    obtain ⟨steps,work,certificate⟩ := total width hwidth x y hx hy
    obtain ⟨mass,_,htraffic⟩ := amortized_kappa_internal_traffic_of_word_work M labels request resume
      (initialExtent M x y) (M.initCfg x y) [] (bin (2*width) (val x*val y))
      steps work certificate (by intro j; simp [MultitapeTM.initCfg])
    exact ⟨steps,mass,htraffic⟩
  · intro width hthreshold hwidth x y hx hy
    obtain ⟨steps,work,hclock,certificate⟩ := fast width hthreshold hwidth x y hx hy
    obtain ⟨mass,hm,htraffic⟩ := amortized_kappa_internal_traffic_of_word_work M labels request resume
      (initialExtent M x y) (M.initCfg x y) [] (bin (2*width) (val x*val y))
      steps work certificate (by intro j; simp [MultitapeTM.initCfg])
    have hp := amortized_kappa_internal_potential_initial M x y
    have hL : (inputWord M x y).length=2*width+1 := by simp [inputWord,hx,hy]; omega
    rw [hL] at hp
    have hnat : steps+32*mass≤ steps+32*(work+(2*M.k+3)*steps)+A*width := by
      dsimp only [A]
      have hk : (128*M.k+96)≤ (128*M.k+96)*width := by
        exact Nat.le_mul_of_pos_right _ hwidth
      nlinarith
    have hb : ((steps+32*mass:ℕ):ℝ)≤
        ((steps+32*(work+(2*M.k+3)*steps):ℕ):ℝ)+(A:ℝ)*(width:ℝ) := by
      exact_mod_cast hnat
    have hlog : (1:ℝ)≤ (lg width:ℝ) := by
      exact_mod_cast (Nat.le_max_right (Nat.clog 2 width) 1)
    have hpow : (1:ℝ)≤ (lg width:ℝ)^(1-κ) := Real.one_le_rpow hlog (by linarith)
    have hn : (0:ℝ)≤ (width:ℝ) := by positivity
    have hg : (width:ℝ)≤ (width:ℝ)*((lg width:ℝ)^(1-κ)) := by nlinarith
    have ha : (0:ℝ)≤ (A:ℝ) := by positivity
    refine ⟨steps,mass,?_,htraffic⟩
    nlinarith

end IntMul.EndParkRecursiveAmortizedWork


open IntMul IntMul.EndParkRecursiveAmortizedWork IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ≤ 1)
    (total : ∀ width : ℕ, 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps work : ℕ, HasWordWork M labels request resume (initialExtent M x y)
          (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps work)
    (C : ℝ) (hC : 0< C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold≤ width → 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps work : ℕ, ((steps+32*(work+(2*M.k+3)*steps):ℕ):ℝ)≤
          C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          HasWordWork M labels request resume (initialExtent M x y)
            (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps work) :
    KappaBound κ :=
  IntMul.EndParkRecursiveAmortizedWork.kappa_bound_of_word_work M labels request resume κ hκ total C hC threshold fast

#print axioms solution
