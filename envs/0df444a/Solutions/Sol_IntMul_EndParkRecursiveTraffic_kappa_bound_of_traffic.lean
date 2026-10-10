-- Prove2me | solution 1 for IntMul.EndParkRecursiveTraffic.kappa_bound_of_traffic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T04:43:03.971818+00:00
-- url     : https://prove2.me/submissions/ea7a124a-3435-4531-8e05-2c5741c4f957

import Definitions.Def_IntMul_EndParkRecursiveTraffic
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_evaluates_correct
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem traffic_kappa_internal_blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step M _ _ ih

private theorem traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
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
private theorem traffic_kappa_internal_unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step M _ ih

private theorem traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem traffic_kappa_internal_heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact traffic_kappa_internal_solutions_intmultrackedbankedspaceinvariants_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.EndParkRecursiveTraffic

open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveReturn
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem traffic_kappa_internal_solutions_intmulendparkrecursivetrafficcosts_component_le_span (M : MultitapeTM) (extent : Fin M.k → ℕ) (j : Fin M.k) :
    extent j ≤ span M extent := Finset.le_sup (f:=extent) (Finset.mem_univ j)

private theorem traffic_kappa_internal_solutions_intmulendparkrecursivetrafficcosts_span_le (M : MultitapeTM) (f : Fin M.k → ℕ) (B : ℕ) (bound : ∀ j, f j ≤ B) :
    span M f ≤ B := by
  apply Finset.sup_le
  intro j _
  exact bound j

private theorem traffic_kappa_internal_return_cost_le_traffic (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (near : ∀ j, c.head j ≤ extent j+1) :
    returnCost M extent c v w ≤ 14*returnTraffic M extent v w := by
  have hhead : c.head M.outTape ≤ span M extent+1 := by
    have := near M.outTape
    have := traffic_kappa_internal_solutions_intmulendparkrecursivetrafficcosts_component_le_span M extent M.outTape
    omega
  have hscan : span M (returnedHeads M c) ≤ span M extent+1 := by
    apply traffic_kappa_internal_solutions_intmulendparkrecursivetrafficcosts_span_le
    intro j
    have := near j
    have := traffic_kappa_internal_solutions_intmulendparkrecursivetrafficcosts_component_le_span M extent j
    simp only [returnedHeads]
    split <;> omega
  have hfirst : max (c.head M.outTape) (v.length+1) ≤ span M extent+v.length+1 := by
    apply max_le <;> omega
  have hwords : max w.length v.length ≤ w.length+v.length := by
    apply max_le <;> omega
  unfold returnCost returnTraffic
  omega

private theorem traffic_kappa_internal_result_extent_le_distance (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) :
    extent M.outTape+1 ≤ reservationDistance M extent c := by
  have h := Finset.le_sup (s:=Finset.univ)
    (f:=TrackedBankReservation.distance M extent (parentAfterInput M c).head)
    (Finset.mem_univ M.outTape)
  simpa only [reservationDistance,span,TrackedBankReservation.distance,parentAfterInput,
    if_true,Nat.sub_zero] using h

private theorem traffic_kappa_internal_call_resume_cost_le_traffic (M : MultitapeTM) (labels : ℕ) (extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y childWord : List Bool) :
    callCost M labels extent c v x y+resumeCost M labels extent childWord ≤
      32*callTraffic M labels extent c v x y childWord := by
  have hout := traffic_kappa_internal_result_extent_le_distance M extent c
  have hfirst : max (c.head M.outTape) (v.length+1) ≤ c.head M.outTape+v.length+1 := by
    apply max_le <;> omega
  have hwords : max (inputWord M x y).length v.length ≤ (inputWord M x y).length+v.length := by
    apply max_le <;> omega
  have hresult : max childWord.length (extent M.outTape) ≤ childWord.length+reservationDistance M extent c := by
    apply max_le <;> omega
  unfold callCost resumeCost callTraffic
  change max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
    3*(inputWord M x y).length+reservationDistance M extent c+labels+16+
    (extent M.outTape+labels+childWord.length+2*max childWord.length (extent M.outTape)+13) ≤ _
  omega

/-- Parked untouched heads incur no reservation distance at the next call. -/
private theorem traffic_kappa_internal_parked_reservation_distance (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (parked : ∀ j, j≠M.outTape → c.head j=extent j+1) :
    reservationDistance M extent c=extent M.outTape+1 := by
  apply Nat.le_antisymm
  · apply traffic_kappa_internal_solutions_intmulendparkrecursivetrafficcosts_span_le
    intro j
    by_cases hj : j=M.outTape
    · subst j
      simp [TrackedBankReservation.distance,parentAfterInput]
    · simp [TrackedBankReservation.distance,parentAfterInput,hj,parked j hj]
  · exact traffic_kappa_internal_result_extent_le_distance M extent c

/-- Repeated calls after a child return pay only the preceding child word,
new packet and new result, with no retained unrelated parent space charge. -/
private theorem traffic_kappa_internal_call_traffic_after_resume (M : MultitapeTM) (labels : ℕ) (resume : Fin labels → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin labels)
    (previousWord x y childWord : List Bool) :
    callTraffic M labels (parentAfterChildExtent M extent previousWord)
      (resumedParent M labels resume label extent c previousWord) previousWord x y childWord=
      2*previousWord.length+(inputWord M x y).length+childWord.length+labels+2 := by
  have hd := traffic_kappa_internal_parked_reservation_distance M (parentAfterChildExtent M extent previousWord)
    (resumedParent M labels resume label extent c previousWord) (by
      intro j hj
      simp [parentAfterChildExtent,resumedParent,hj])
  unfold callTraffic
  rw [hd]
  simp only [resumedParent,parentAfterChildExtent,if_true]
  omega

/-- Linear physical overhead in an additive recursive word/space workload.
The counted ordinary body transitions are actual transitions of M. -/
private theorem traffic_kappa_internal_budget_of_traffic (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps mass : ℕ)
    (workload : HasTraffic M labels request resume extent c v w steps mass) :
    (∀ j, c.head j ≤ extent j+1) →
      ∃ budget, budget ≤ steps+32*mass ∧ Evaluates M labels request resume extent c v w budget := by
  induction workload with
  | halt extent c v w halt out =>
    intro near
    refine ⟨returnCost M extent c v w,?_,Evaluates.halt extent c v w halt out⟩
    have h := traffic_kappa_internal_return_cost_le_traffic M extent c v w near
    omega
  | step extent c v w steps mass live ordinary rest ih =>
    intro near
    have hnear := TrackedBankedSpace.traffic_kappa_internal_heads_near_run M c extent 1 near
    simp only [Function.iterate_one,TrackedBankedSimulation.extents,Function.iterate_zero,Function.id_def] at hnear
    obtain ⟨budget,hbudget,heval⟩ := ih hnear
    exact ⟨budget+1,by omega,Evaluates.step extent c v w budget live ordinary heval⟩
  | call extent c v x y childWord w label childSteps childMass parentSteps parentMass live request_label packet child parent ihchild ihparent =>
    intro near
    obtain ⟨childBudget,hchildBudget,hchild⟩ := ihchild (by intro j; simp [MultitapeTM.initCfg])
    have hpnear : ∀ j, (resumedParent M labels resume label extent c childWord).head j ≤
        parentAfterChildExtent M extent childWord j+1 := by
      intro j
      by_cases hj : j=M.outTape <;> simp [resumedParent,parentAfterChildExtent,hj]
    obtain ⟨parentBudget,hparentBudget,hparent⟩ := ihparent hpnear
    refine ⟨callCost M labels extent c v x y+childBudget+resumeCost M labels extent childWord+parentBudget,
      ?_,Evaluates.call extent c v x y childWord w label childBudget parentBudget live request_label packet hchild hparent⟩
    have h := traffic_kappa_internal_call_resume_cost_le_traffic M labels extent c v x y childWord
    omega

end IntMul.EndParkRecursiveTraffic



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem traffic_kappa_internal_multiplies_at_of_evaluations (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (width : ℕ) (T : ℝ)
    (evaluations : ∀ x y : List Bool, x.length=width → y.length=width →
      ∃ budget : ℕ, (budget:ℝ)≤ T ∧
        Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
          (bin (2*width) (val x*val y)) budget) :
    MultipliesAt (machine M labels request resume) width (T+18*(width:ℝ)+23) := by
  intro x y hx hy
  obtain ⟨budget,hbudget,heval⟩ := evaluations x y hx hy
  obtain ⟨t,ht,hrun,hout⟩ := native_evaluates_correct M labels request resume x y
    (bin (2*width) (val x*val y)) budget heval
  have hL : (inputWord M x y).length=2*width+1 := by simp [inputWord,hx,hy]; omega
  have hW : (bin (2*width) (val x*val y)).length=2*width := by simp [bin]
  have hnat : t≤ budget+18*width+23 := by rw [hL,hW] at ht; omega
  have hreal : (t:ℝ)≤ (budget:ℝ)+18*(width:ℝ)+23 := by exact_mod_cast hnat
  exact ⟨t,by linarith,hout⟩

/-- Pointwise finite evaluation already supplies a uniform clock at any
fixed input width: there are only finitely many pairs of bit words. -/
private theorem traffic_kappa_internal_uniform_evaluation_budget (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (width : ℕ)
    (total : ∀ x y : List Bool, x.length=width → y.length=width →
      ∃ budget : ℕ,
        Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
          (bin (2*width) (val x*val y)) budget) :
    ∃ B : ℕ, ∀ x y : List Bool, x.length=width → y.length=width →
      ∃ budget : ℕ, budget ≤ B ∧
        Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
          (bin (2*width) (val x*val y)) budget := by
  classical
  let Inputs := (Fin width → Bool) × (Fin width → Bool)
  have finiteTotal : ∀ a : Inputs, ∃ budget : ℕ,
      Evaluates M labels request resume
        (initialExtent M (List.ofFn a.1) (List.ofFn a.2))
        (M.initCfg (List.ofFn a.1) (List.ofFn a.2)) []
        (bin (2*width) (val (List.ofFn a.1)*val (List.ofFn a.2))) budget := by
    intro a
    exact total _ _ (List.length_ofFn) (List.length_ofFn)
  let clock : Inputs → ℕ := fun a => Classical.choose (finiteTotal a)
  refine ⟨Finset.univ.sup clock,?_⟩
  intro x y hx hy
  have xrep : ∃ f : Fin width → Bool, List.ofFn f=x := by
    rw [← hx]
    exact ⟨x.get,List.ofFn_get x⟩
  have yrep : ∃ f : Fin width → Bool, List.ofFn f=y := by
    rw [← hy]
    exact ⟨y.get,List.ofFn_get y⟩
  obtain ⟨xf,hxf⟩ := xrep
  obtain ⟨yf,hyf⟩ := yrep
  refine ⟨clock (xf,yf),Finset.le_sup (f:=clock) (Finset.mem_univ (xf,yf)),?_⟩
  have heval := Classical.choose_spec (finiteTotal (xf,yf))
  change Evaluates M labels request resume
    (initialExtent M (List.ofFn xf) (List.ofFn yf))
    (M.initCfg (List.ofFn xf) (List.ofFn yf)) []
    (bin (2*width) (val (List.ofFn xf)*val (List.ofFn yf))) (clock (xf,yf)) at heval
  simpa only [hxf,hyf] using heval

/-- A real compiled machine witnesses the campaign time predicate once the
body's finite evaluations have the required budget. The compiler adds only
a fixed linear native-input/output term, with no change of machine per size. -/
private theorem traffic_kappa_internal_mul_time_bound_of_evaluations (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (g : ℕ → ℝ)
    (total : ∀ width : ℕ, 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ budget : ℕ,
          Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
            (bin (2*width) (val x*val y)) budget)
    (C : ℝ) (hC : 0< C) (threshold : ℕ)
    (growth : ∀ width : ℕ, threshold≤ width → 1≤ width → (width:ℝ)≤ g width)
    (fast : ∀ width : ℕ, threshold≤ width → 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ budget : ℕ, (budget:ℝ)≤ C*g width ∧
          Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
            (bin (2*width) (val x*val y)) budget) :
    MulTimeBound g := by
  refine ⟨machine M labels request resume,?_,C+41,by linarith,threshold,?_⟩
  · intro width hwidth
    obtain ⟨B,hB⟩ := traffic_kappa_internal_uniform_evaluation_budget M labels request resume width (total width hwidth)
    refine ⟨(B:ℝ)+18*(width:ℝ)+23,traffic_kappa_internal_multiplies_at_of_evaluations M labels request resume width B ?_⟩
    intro x y hx hy
    obtain ⟨budget,hbudget,heval⟩ := hB x y hx hy
    exact ⟨budget,by exact_mod_cast hbudget,heval⟩
  · intro width hthreshold hwidth
    have h := traffic_kappa_internal_multiplies_at_of_evaluations M labels request resume width (C*g width) (fast width hthreshold hwidth)
    intro x y hx hy
    obtain ⟨t,ht,hout⟩ := h x y hx hy
    have hw : (1:ℝ)≤ (width:ℝ) := by exact_mod_cast hwidth
    have hg := growth width hthreshold hwidth
    exact ⟨t,by nlinarith,hout⟩

/-- The shared compiler produces the campaign's exact kappa predicate from
total recursive evaluations and their eventual sub-n-log-n charged budget. -/
private theorem traffic_kappa_internal_kappa_bound_of_evaluations (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ ≤ 1)
    (total : ∀ width : ℕ, 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ budget : ℕ,
          Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
            (bin (2*width) (val x*val y)) budget)
    (C : ℝ) (hC : 0 < C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold ≤ width → 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ budget : ℕ, (budget:ℝ) ≤ C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
            (bin (2*width) (val x*val y)) budget) :
    KappaBound κ := by
  unfold KappaBound
  apply traffic_kappa_internal_mul_time_bound_of_evaluations M labels request resume
    (fun width => (width:ℝ)*((lg width:ℝ)^(1-κ))) total C hC threshold
  · intro width _ _
    have hlog : (1:ℝ) ≤ (lg width:ℝ) := by
      exact_mod_cast (Nat.le_max_right (Nat.clog 2 width) 1)
    have hp : (1:ℝ) ≤ (lg width:ℝ)^(1-κ) := Real.one_le_rpow hlog (by linarith)
    have hn : (0:ℝ) ≤ (width:ℝ) := by positivity
    nlinarith
  · intro width hthreshold hwidth x y hx hy
    obtain ⟨budget,hbudget,heval⟩ := fast width hthreshold hwidth x y hx hy
    exact ⟨budget,by simpa only [mul_assoc] using hbudget,heval⟩

end IntMul.EndParkRecursiveEvaluation



namespace IntMul.EndParkRecursiveTraffic

open IntMul.TrackedBankPreparation (initialExtent)

/-- The exact campaign predicate follows from pointwise total same-body
traffic certificates and the required eventual ordinary-step/traffic bound. -/
private theorem kappa_bound_of_traffic (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ ≤ 1)
    (total : ∀ width : ℕ, 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps mass : ℕ, HasTraffic M labels request resume (initialExtent M x y)
          (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass)
    (C : ℝ) (hC : 0 < C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold ≤ width → 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps mass : ℕ, ((steps+32*mass:ℕ):ℝ) ≤ C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          HasTraffic M labels request resume (initialExtent M x y)
            (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass) :
    KappaBound κ := by
  refine EndParkRecursiveEvaluation.traffic_kappa_internal_kappa_bound_of_evaluations M labels request resume κ hκ ?_ C hC threshold ?_
  · intro width hwidth x y hx hy
    obtain ⟨steps,mass,htraffic⟩ := total width hwidth x y hx hy
    obtain ⟨budget,_,heval⟩ := traffic_kappa_internal_budget_of_traffic M labels request resume
      (initialExtent M x y) (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass htraffic
      (by intro j; simp [MultitapeTM.initCfg])
    exact ⟨budget,heval⟩
  · intro width hthreshold hwidth x y hx hy
    obtain ⟨steps,mass,hclock,htraffic⟩ := fast width hthreshold hwidth x y hx hy
    obtain ⟨budget,hbudget,heval⟩ := traffic_kappa_internal_budget_of_traffic M labels request resume
      (initialExtent M x y) (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass htraffic
      (by intro j; simp [MultitapeTM.initCfg])
    have hb : (budget:ℝ) ≤ (steps+32*mass:ℕ) := by exact_mod_cast hbudget
    exact ⟨budget,le_trans hb hclock,heval⟩

end IntMul.EndParkRecursiveTraffic


open IntMul IntMul.EndParkRecursiveTraffic IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ ≤ 1)
    (total : ∀ width : ℕ, 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps mass : ℕ, HasTraffic M labels request resume (initialExtent M x y)
          (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass)
    (C : ℝ) (hC : 0 < C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold ≤ width → 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps mass : ℕ, ((steps+32*mass:ℕ):ℝ) ≤ C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          HasTraffic M labels request resume (initialExtent M x y)
            (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass) :
    KappaBound κ :=
  IntMul.EndParkRecursiveTraffic.kappa_bound_of_traffic M labels request resume κ hκ total C hC threshold fast

#print axioms solution
