-- Prove2me | solution 1 for IntMul.FlatRecursiveEvaluation.kappa_bound_of_evaluations
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T03:50:50.099663+00:00
-- url     : https://prove2.me/submissions/938f3252-bba3-494e-bba2-ef21b7d4e783

import Theorems.Thm_IntMul_FlatRecursiveEvaluation_native_evaluates_correct
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic


namespace IntMul.FlatRecursiveEvaluation

open IntMul.FlatRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem multiplier_internal_multiplies_at_of_evaluations (M : MultitapeTM) (labels : ℕ)
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
private theorem multiplier_internal_uniform_evaluation_budget (M : MultitapeTM) (labels : ℕ)
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
private theorem multiplier_internal_mul_time_bound_of_evaluations (M : MultitapeTM) (labels : ℕ)
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
    obtain ⟨B,hB⟩ := multiplier_internal_uniform_evaluation_budget M labels request resume width (total width hwidth)
    refine ⟨(B:ℝ)+18*(width:ℝ)+23,multiplier_internal_multiplies_at_of_evaluations M labels request resume width B ?_⟩
    intro x y hx hy
    obtain ⟨budget,hbudget,heval⟩ := hB x y hx hy
    exact ⟨budget,by exact_mod_cast hbudget,heval⟩
  · intro width hthreshold hwidth
    have h := multiplier_internal_multiplies_at_of_evaluations M labels request resume width (C*g width) (fast width hthreshold hwidth)
    intro x y hx hy
    obtain ⟨t,ht,hout⟩ := h x y hx hy
    have hw : (1:ℝ)≤ (width:ℝ) := by exact_mod_cast hwidth
    have hg := growth width hthreshold hwidth
    exact ⟨t,by nlinarith,hout⟩

/-- The shared compiler produces the campaign's exact kappa predicate from
total recursive evaluations and their eventual sub-n-log-n charged budget. -/
private theorem kappa_bound_of_evaluations (M : MultitapeTM) (labels : ℕ)
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
  apply multiplier_internal_mul_time_bound_of_evaluations M labels request resume
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

end IntMul.FlatRecursiveEvaluation


open IntMul IntMul.FlatRecursiveEvaluation IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (labels : ℕ)
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
    KappaBound κ :=
  IntMul.FlatRecursiveEvaluation.kappa_bound_of_evaluations M labels request resume κ hκ total C hC threshold fast

#print axioms solution
