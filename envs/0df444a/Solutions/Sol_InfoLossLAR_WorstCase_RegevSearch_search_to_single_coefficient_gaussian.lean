-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.search_to_single_coefficient_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T23:27:33.1776+00:00
-- url     : https://prove2.me/submissions/3c121a93-f383-47df-a41e-d4eebbb2b859
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_search_to_shared_pool_bdd
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_shared_pool_bdd_to_gaussian_events
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02

section BudgetSection

set_option autoImplicit false
namespace InfoLossLAR.WorstCase.RegevSearch
open scoped BigOperators

private theorem polynomial_eventually_le_power (p : Polynomial ℕ) :
    ∃ d N : ℕ, ∀ n ≥ N, p.eval n ≤ n ^ d := by
  refine ⟨p.natDegree+1, max 1 (p.eval 1), ?_⟩
  intro n hn
  have h1 := (le_max_left 1 (p.eval 1)).trans hn
  calc
    p.eval n = ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * n^i := p.eval_eq_sum_range n
    _ ≤ ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * n^p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (pow_le_pow_right' h1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = p.eval 1 * n^p.natDegree := by
      rw [← Finset.sum_mul]
      congr 1
      simpa using (p.eval_eq_sum_range 1).symm
    _ ≤ n * n^p.natDegree := Nat.mul_le_mul_right _ ((le_max_right _ _).trans hn)
    _ = _ := by rw [pow_succ, mul_comm]

private theorem calls_sqrt_negligible (p : Polynomial ℕ) (e : ℕ → ℝ) (he : Negligible e) :
    Negligible (fun n => 4 * (p.eval n : ℕ) * Real.sqrt (e n)) := by
  refine ⟨fun _ => by positivity, ?_⟩
  intro c hc
  obtain ⟨d,N,hp⟩ := polynomial_eventually_le_power (4*p)
  obtain ⟨M,hm⟩ := he.2 (2*(c+d)) (by positivity)
  refine ⟨max (max M N) 1, ?_⟩
  intro n hn
  have hnM : M ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN : N ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hbound := hp n hnN
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat] at hbound
  have hscale : (4 : ℝ) * (p.eval n : ℕ) ≤ (n : ℝ)^(d : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hbound
  have hs : Real.sqrt (e n) ≤ (n : ℝ)^(-(c+d)) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨(Real.rpow_pos_of_pos hpos _).le, ?_⟩
    rw [← Real.rpow_two, ← Real.rpow_mul hpos.le]
    convert hm n hnM using 2
    ring
  calc
    _ ≤ (n : ℝ)^(d : ℝ) * (n : ℝ)^(-(c+d)) :=
      mul_le_mul hscale hs (Real.sqrt_nonneg _) ((Real.rpow_pos_of_pos hpos _).le)
    _ = _ := by rw [← Real.rpow_add hpos]; congr 1; ring

private theorem spend_precision (a e : ℝ) (t k : ℕ)
    (h : a ≤ e + 1/((poolBDDPrecision t k : ℝ)+1)) (he : 0 ≤ e) :
    4*(t : ℝ)*Real.sqrt a ≤ 4*(t : ℝ)*Real.sqrt e + 1/(4*((k : ℝ)+1)) := by
  let D : ℝ := 16*((t : ℝ)+1)*((k : ℝ)+1)
  have hD : 0 < D := by dsimp [D]; positivity
  have heq : (poolBDDPrecision t k : ℝ) = D^2 := by
    simp [poolBDDPrecision,D]
  have hfrac : 1 / ((poolBDDPrecision t k : ℝ)+1) ≤ (1/D)^2 := by
    rw [heq,div_pow,one_pow]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hD) (by linarith)
  have hs : Real.sqrt a ≤ Real.sqrt e + 1/D := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hsum := h.trans (add_le_add_right hfrac e)
    nlinarith only [hsum,Real.sq_sqrt he,mul_nonneg (Real.sqrt_nonneg e) (one_div_nonneg.mpr hD.le)]
  have hnumeric : 4*(t:ℝ)*(1/D) ≤ 1/(4*((k:ℝ)+1)) := by
    rw [mul_one_div,div_le_div_iff₀ hD (by positivity)]
    dsimp only [D]
    nlinarith [show 0 ≤ (k:ℝ) by positivity]
  calc
    _ ≤ 4*(t:ℝ)*(Real.sqrt e+1/D) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ _ := by rw [mul_add]; exact add_le_add_right hnumeric _

theorem coherent_budget_of_decoder {C : MFamily} {P : Polynomial ℕ} {e : ℕ → ℝ}
    {N : ℕ} {S : Set ℕ} (he : Negligible e) (h : SharedPoolBDD C P e N S) :
    CoherentPoolBDDBudget C P N S := by
  intro p
  refine ⟨fun n => 4 * (p.eval n : ℕ) * Real.sqrt (e n), calls_sqrt_negligible p e he, ?_⟩
  intro n hn hN B hB R hR hs k x u z hz hx
  exact spend_precision _ _ _ _ (h n hn hN B hB R hR hs _ x u z hz hx) (he.1 n)

end InfoLossLAR.WorstCase.RegevSearch

end BudgetSection

section FiniteEventsSection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace SingleSampleReadout
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

theorem finite_l1 {X : Type*} (p q : X → ℝ) (ε : ℝ)
    (h : ∀ t : Finset X, |(∑ x ∈ t, p x) - ∑ x ∈ t, q x| ≤ ε) :
    (∑' x, |p x-q x|) ≤ 2*ε := by
  apply Real.tsum_le_of_sum_le (fun _ => abs_nonneg _)
  intro t
  let a (x : X) := q x ≤ p x
  have hpos := (abs_le.mp (h (t.filter a))).2
  have hneg := (abs_le.mp (h (t.filter (fun x => ¬a x)))).1
  rw [←Finset.sum_sub_distrib,Finset.sum_filter] at hpos hneg
  have abs_split (x : X) : |p x-q x| = (if a x then p x-q x else 0) -
      (if ¬a x then p x-q x else 0) := by
    by_cases hx : a x
    · rw [if_pos hx,if_neg (not_not_intro hx),sub_zero,abs_of_nonneg (sub_nonneg.mpr hx)]
    · rw [if_neg hx,if_pos hx,zero_sub,abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hx))]
  simp_rw [abs_split]
  rw [Finset.sum_sub_distrib]
  linarith

theorem prefix_unique {n : ℕ} (word : Str) {x y : Fin n → ℤ}
    (hx : encVec encI x <+: word) (hy : encVec encI y <+: word) : x=y := by
  let read := Integration9_9.TM2NativeAffineEncoding.readVector
  have hit (z : Fin n → ℤ) (hz : encVec encI z <+: word) : (read word).2 = List.ofFn z := by
    rcases hz with ⟨s, rfl⟩
    rw [show read = Integration9_9.TM2NativeAffineEncoding.readVector from rfl,
      Integration9_9.TM2NativeAffineEncoding.readVector_append]
  exact List.ofFn_inj.mp ((hit x hx).symm.trans (hit y hy))

end SingleSampleReadout

end FiniteEventsSection

section ReadoutSection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace SingleSampleReadout
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

private theorem one_fiber {X : Type*} (R : X → Prop) (single : ∀ a b, R a → R b → a=b) (v : ℝ) :
    HasSum (fun x => if R x then v else 0) (if ∃ x, R x then v else 0) := by
  classical
  by_cases h : ∃ x, R x
  · rw [if_pos h]
    obtain ⟨a,ha⟩ := h
    have iff (x : X) : R x ↔ x=a := ⟨fun hx => single _ _ hx ha,fun hh => hh ▸ ha⟩
    simpa only [iff] using hasSum_ite_eq a v
  · have hx (x : X) : ¬ R x := fun hh => h ⟨_,hh⟩
    simp only [if_neg h, if_neg (hx _),hasSum_zero]

private theorem finite_fiber {X : Type*} (R : X → Prop) (single : ∀ a b, R a → R b → a=b) (v : ℝ)
    (T : Finset X) :
    (∑ x ∈ T, if R x then v else 0) = @ite ℝ (∃ x∈T, R x) (Classical.propDecidable _) v 0 := by
  classical
  by_cases h : ∃ x∈T, R x
  · rw [if_pos h]
    obtain ⟨a,ha,hR⟩ := h
    have iff (x : X) : R x ↔ x=a := ⟨fun hx => single _ _ hx hR,fun hh => hh ▸ hR⟩
    simp only [iff,Finset.sum_ite_eq',ha,if_true]
  · rw [if_neg h]
    exact Finset.sum_eq_zero (fun x hx => if_neg (fun hh => h ⟨x,hx,hh⟩))

theorem draw_hasSum {n : ℕ} (H : MFamily) (w : Str) :
    HasSum (fun z : Fin n → ℤ => outputProb H w (fun out => encVec encI z <+: out))
      (outputProb H w (fun out => ∃ z : Fin n → ℤ, encVec encI z <+: out)) := by
  unfold outputProb
  apply hasSum_sum
  intro y _
  apply one_fiber
  intro a b ha hb
  exact prefix_unique _ ha hb

theorem draw_sum {n : ℕ} (H : MFamily) (w : Str) (T : Finset (Fin n → ℤ)) :
    (∑ z ∈ T, outputProb H w (fun out => encVec encI z <+: out)) =
       outputProb H w (fun out => ∃ z∈T, encVec encI z <+: out) := by
  unfold outputProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply finite_fiber
  intro a b ha hb
  exact prefix_unique _ ha hb

theorem readout_correct {n : ℕ} (H : MFamily) (w : Str) (q : (Fin n → ℤ) → ℝ) (ε : ℝ)
    (valid : outputProb H w (fun out => ∃ z : Fin n → ℤ, encVec encI z <+: out) = 1)
    (events : ∀ T : Finset (Fin n → ℤ), |outputProb H w (fun out => ∃ z∈T, encVec encI z <+: out) -
        ∑ z ∈ T, q z| ≤ ε / 2) :
    let p := fun z : Fin n → ℤ => outputProb H w (fun out => encVec encI z <+: out)
    HasSum p 1 ∧ (∑' z, |p z-q z|) ≤ ε := by
  refine ⟨valid ▸ draw_hasSum H w, ?_⟩
  have hb := finite_l1 (fun z : Fin n → ℤ => outputProb H w (fun out => encVec encI z <+: out)) q
    (ε / 2) (fun t => by rw [draw_sum]; exact events t)
  simpa only [mul_div_cancel₀ ε (show (2:ℝ) ≠ 0 by norm_num),mul_comm] using hb

end SingleSampleReadout

end ReadoutSection

section OperationalSection
set_option autoImplicit false
open scoped Classical BigOperators
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
namespace SingleSampleReadout

def Operational (S : Set ℕ) : Prop :=
  ∃ H : MFamily, IsMQPT H ∧ ∃ error : ℕ → ℝ, Negligible error ∧
    ∃ threshold : ℕ, ∀ n ∈ S, threshold ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
      ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
      ∀ precision : ℕ,
        let w := dgsInput B r 1 precision
        outputProb H w (fun out => ∃ z : Fin n → ℤ, encVec encI z <+: out) = 1 ∧
        ∀ T : Finset (Fin n → ℤ),
          |outputProb H w (fun out => ∃ z ∈ T, encVec encI z <+: out) -
            ∑ z ∈ T, coefficientMass B r z| ≤ (error n + 1 / ((precision : ℝ)+1))/2

theorem of_operational (S : Set ℕ) (h : Operational S) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ error : ℕ → ℝ, Negligible error ∧
      ∃ threshold : ℕ, ∀ n ∈ S, threshold ≤ n →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∀ precision : ℕ,
          let draw (z : Fin n → ℤ) := outputProb H (dgsInput B r 1 precision)
            (fun out => encVec encI z <+: out)
          HasSum draw 1 ∧
            (∑' z, |draw z - coefficientMass B r z|) ≤
              error n + 1 / ((precision : ℝ) + 1) := by
  obtain ⟨H,hH,error,he,N,hn⟩ := h
  refine ⟨H,hH,error,he,N,?_⟩
  intro n hS hN B hB r hr hwidth k
  obtain ⟨valid,events⟩ := hn n hS hN B hB r hr hwidth k
  exact readout_correct H (dgsInput B r 1 k) (coefficientMass B r) _ valid events
end SingleSampleReadout

end OperationalSection

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

open InfoLossLAR.WorstCase.RegevSearch

theorem solution
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (A : MFamily) (hA : IsMQPT A) (samples : Polynomial ℕ) (cutoff : ℕ)
    (hsearch : SearchOn A samples cutoff S) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ error : ℕ → ℝ, Negligible error ∧
      ∃ threshold : ℕ, ∀ n ∈ S, threshold ≤ n →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∀ precision : ℕ,
          let draw (z : Fin n → ℤ) := outputProb H (dgsInput B r 1 precision)
            (fun out => encVec encI z <+: out)
          HasSum draw 1 ∧
            (∑' z, |draw z - coefficientMass B r z|) ≤
              error n + 1 / ((precision : ℝ) + 1) := by
  obtain ⟨C,hC,P,e,he,N,hdecoder⟩ := search_to_shared_pool_bdd S hS hpos A hA samples cutoff hsearch
  exact SingleSampleReadout.of_operational S (shared_pool_bdd_to_gaussian_events S hS hpos C hC P N
    (coherent_budget_of_decoder he hdecoder))


