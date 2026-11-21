-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.shared_pool_decoder_coherent_copy
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:34:42.103229+00:00
-- url     : https://prove2.me/submissions/eaae2e27-bda9-4b09-a7df-3afce74eb196

import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05

set_option autoImplicit false
set_option maxHeartbeats 700000
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch RegevLWE.GaussConv
open scoped BigOperators Classical

namespace SharedPoolCoherence
noncomputable section
variable {n : ℕ}

private theorem row_error {β : Type*} [Fintype β] [DecidableEq β] (z : ℂ) (a b : β) :
    (∑ y : β, ‖(if y = a then z else 0) - (if y = b then z else 0)‖ ^ 2) =
      if a = b then 0 else 2 * ‖z‖ ^ 2 := by
  classical
  by_cases hab : a = b
  · simp [hab]
  · have hrow (y : β) :
        ‖(if y = a then z else 0) - (if y = b then z else 0)‖ ^ 2 =
          (if y = a then ‖z‖ ^ 2 else 0) + (if y = b then ‖z‖ ^ 2 else 0) := by
      by_cases hya : y = a <;> by_cases hyb : y = b <;> simp_all
    simp_rw [hrow]
    simp [Finset.sum_add_distrib, hab, two_mul]

/-- Exact error of copying a computed answer rather than the unique desired answer.
The answer may depend on a preserved query register, so the assertion applies to a
superposition of queries as well as to a single classical input. -/
theorem copied_error_sq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ψ : α → ℂ) (readout desired : α → β) :
    ‖copied ψ readout - copied ψ desired‖ ^ 2 =
      2 * ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, copied, PiLp.sub_apply]
  simp_rw [row_error]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Dividing nonnegative weights by their total gives a summable subprobability.
For the Jensen estimate only the upper bound on total mass is needed. -/
theorem coeff_subprob (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) :
    (∀ z, 0 ≤ coefficientMass B r z) ∧ Summable (coefficientMass B r) ∧
      (∑' z, coefficientMass B r z) ≤ 1 := by
  classical
  let g (z : Fin n → ℤ) := rhoInt r (B.mulVec z)
  have hp (z) : 0 ≤ g z := (Real.exp_pos _).le
  have hZ : 0 ≤ ∑' z, g z := tsum_nonneg hp
  change (∀ z, 0 ≤ g z / ∑' y, g y) ∧ Summable (fun z => g z / ∑' y, g y) ∧ _
  refine ⟨fun z => div_nonneg (hp z) hZ, ?_⟩
  change Summable (fun z => g z / ∑' y, g y) ∧ (∑' z, g z / ∑' y, g y) ≤ 1
  by_cases hs : Summable g
  · refine ⟨hs.div_const _, ?_⟩
    rw [tsum_div_const]
    by_cases hz : (∑' z,g z)=0 <;> simp [hz]
  · rw [tsum_eq_zero_of_not_summable hs]
    simp

theorem outputProb_bounds (G : MFamily) (w : Str) (event : Str → Prop) :
    0 ≤ outputProb G w event ∧ outputProb G w event ≤ 1 := by
  classical
  unfold outputProb
  let state := runLayered (G.circ w.length) (basisInput (toBits w))
  have total : (∑ y, ‖state y‖^2) = 1 := by
    simpa only [state, ← Complex.normSq_eq_norm_sq] using
      (runLayered_mass (G.circ w.length) (basisInput (toBits w))).trans
        (basisInput_mass (a := G.anc w.length) (toBits w))
  constructor
  · exact Finset.sum_nonneg (by intro y _; split_ifs <;> positivity)
  · apply le_trans _ total.le
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> first | exact le_rfl | positivity

/-- Full jointly independent countable family normalization, allowing
coordinate-dependent channels and output tests in every factor. -/
theorem dependentProductMass_hasSum {Index : Type*} (dimension : ℕ)
    (mass : Fin dimension → Index → ℝ)
    (hnonnegative : ∀ index value,0 ≤ mass index value) (hsummable : ∀ index,Summable (mass index)) :
    HasSum (fun word : Fin dimension → Index => ∏ index,mass index (word index))
      (∏ index,∑' value,mass index value) := by
  classical
  induction dimension with
  | zero =>
    have heq : (fun word : Fin 0 → Index => ∏ index,mass index (word index))=(fun _ => (1 : ℝ)) := by
      funext word
      simp
    rw [heq]
    simpa only [Finset.univ_eq_empty,Finset.prod_empty,Fintype.sum_unique] using
      (hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)))
  | succ dimension ih =>
    have htail := ih (fun index => mass index.succ) (fun index => hnonnegative index.succ)
      (fun index => hsummable index.succ)
    have htailNonnegative (word : Fin dimension → Index) : 0 ≤ ∏ index,mass index.succ (word index) :=
      Finset.prod_nonneg (fun _ _ => hnonnegative _ _)
    have hs := (hsummable 0).mul_of_nonneg htail.summable (hnonnegative 0) htailNonnegative
    have hp := (hsummable 0).hasSum.mul htail hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass 0 pair.1*(∏ index,mass index.succ (pair.2 index)))=
        (fun word : Fin (dimension+1) → Index => ∏ index,mass index (word index)) ∘
          (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [Fin.prod_univ_succ] using h

theorem poolWeight_subprob (m : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ) :
    (∀ p, 0 ≤ poolWeight m B R p) ∧ Summable (poolWeight m B R) ∧ (∑' p, poolWeight m B R p) ≤ 1 := by
  obtain ⟨h,hs,hm⟩ := coeff_subprob B R
  have he := dependentProductMass_hasSum m (fun _ => coefficientMass B R) (fun _ => h) (fun _ => hs)
  refine ⟨fun p => Finset.prod_nonneg (fun j _ => h (p j)), he.summable, he.tsum_eq.trans_le ?_⟩
  exact Finset.prod_le_one (fun _ _ => tsum_nonneg h) (fun _ _ => hm)

/-- Transfer fixed-query rms error to an arbitrary coherent query distribution
independent of the stored countable pool. The same sample is used on every branch. -/
theorem mixture_rms_bound {Ω I : Type*} [Fintype I] [Nonempty I]
    (ρ : Ω → ℝ) (hρ : ∀ ω, 0 ≤ ρ ω) (hsum : Summable ρ) (hmass_le : ∑' ω, ρ ω ≤ 1)
    (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1)
    (p : Ω → I → ℝ) (hp : ∀ ω i, 0 ≤ p ω i ∧ p ω i ≤ 1)
    (scale bound : ℝ) (hscale : 0 ≤ scale)
    (hquery : ∀ i, scale * Real.sqrt (∑' ω, ρ ω * p ω i) ≤ bound) :
    (∑' ω, ρ ω * (scale * Real.sqrt (∑ i, μ i * p ω i))) ≤ bound := by
  classical
  let q (ω : Ω) := ∑ i, μ i * p ω i
  have hq (ω) : 0 ≤ q ω := Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (hp ω i).1
  have hbound : 0 ≤ bound :=
    (mul_nonneg hscale (Real.sqrt_nonneg _)).trans (hquery (Classical.arbitrary I))
  have hs (i) : Summable (fun ω => ρ ω * p ω i) :=
    Summable.of_nonneg_of_le (fun ω => mul_nonneg (hρ ω) (hp ω i).1)
      (fun ω => mul_le_of_le_one_right (hρ ω) (hp ω i).2) hsum
  have hpoint (i) (s : Finset Ω) : scale^2 * (∑ ω ∈ s, ρ ω * p ω i) ≤ bound^2 := by
    have hfin := (hs i).sum_le_tsum s (fun ω _ => mul_nonneg (hρ ω) (hp ω i).1)
    have hfull := sq_le_sq₀ (mul_nonneg hscale (Real.sqrt_nonneg _)) hbound |>.mpr (hquery i)
    rw [mul_pow, Real.sq_sqrt (tsum_nonneg (fun ω => mul_nonneg (hρ ω) (hp ω i).1))] at hfull
    exact (mul_le_mul_of_nonneg_left hfin (sq_nonneg scale)).trans hfull
  apply Real.tsum_le_of_sum_le (fun ω => mul_nonneg (hρ ω) (mul_nonneg hscale (Real.sqrt_nonneg _)))
  intro s
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun ω _ => hρ ω) (fun ω _ => mul_nonneg (hρ ω) (hq ω))
    (r:=fun ω => ρ ω * Real.sqrt (q ω)) (fun ω _ => by
      rw [mul_pow,Real.sq_sqrt (hq ω)]
      ring_nf
      exact le_rfl)
  have hmass : ∑ ω ∈ s, ρ ω ≤ 1 := (hsum.sum_le_tsum s (fun ω _ => hρ ω)).trans hmass_le
  have hcs' : (∑ ω ∈ s, ρ ω * Real.sqrt (q ω))^2 ≤ ∑ ω ∈ s, ρ ω * q ω :=
    hcs.trans (mul_le_of_le_one_left (Finset.sum_nonneg (fun ω _ => mul_nonneg (hρ ω) (hq ω))) hmass)
  have hex : scale^2 * (∑ ω ∈ s, ρ ω * q ω) = ∑ i, μ i * (scale^2 * ∑ ω ∈ s, ρ ω * p ω i) := by
    simp only [q,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hmix : scale^2 * (∑ ω ∈ s, ρ ω * q ω) ≤ bound^2 := by
    rw [hex]
    calc _ ≤ ∑ i, μ i * bound^2 :=
           Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i s) (hμ i)
         _ = _ := by rw [← Finset.sum_mul, hμsum, one_mul]
  have hsq : (scale * (∑ ω ∈ s, ρ ω * Real.sqrt (q ω)))^2 ≤ bound^2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hcs' (sq_nonneg scale)).trans hmix
  have hle := (sq_le_sq₀ (mul_nonneg hscale (Finset.sum_nonneg (fun ω _ =>
    mul_nonneg (hρ ω) (Real.sqrt_nonneg _)))) hbound).mp hsq
  rw [Finset.mul_sum] at hle
  simpa only [mul_left_comm scale, q] using hle

/-- Failure conditional on one stored pool, before making any correctness claim
for that pool. -/
def wrong {n m : ℕ} (C : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ)
    (precision : ℕ) (pool : Fin m → Fin n → ℤ) (q : Query B R) : ℝ :=
  outputProb C (poolBDDInput B R precision pool q.input) (fun out => ¬encVec encI q.answer <+: out)

/-- Weighted coherent query errors for a countable Gaussian pool, with the
decoder's public precision schedule. The ideal query weights cannot inspect
the pool. The coefficient 4 accounts for uncomputation and final measurement. -/
def MixedBudget (C : MFamily) (P calls : Polynomial ℕ) (N : ℕ) (S : Set ℕ) (e : ℕ → ℝ) : Prop :=
  ∀ n ∈ S, N ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
  ∀ R : ℚ, 0 < R →
    Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ) →
  ∀ (k m : ℕ) (query : Fin (m+1) → Query B R) (μ : Fin (m+1) → ℝ),
    (∀ i, 0 ≤ μ i) → (∑ i, μ i = 1) →
    (∑' pool : Fin (P.eval n) → Fin n → ℤ, poolWeight (P.eval n) B R pool *
      (4 * ((calls.eval n : ℕ) : ℝ) * Real.sqrt (∑ i, μ i *
        wrong C B R (poolBDDPrecision (calls.eval n) k) pool (query i)))) ≤
      e n + 1/(4*((k:ℝ)+1))

theorem mixed_budget {C : MFamily} {P : Polynomial ℕ} {N : ℕ} {S : Set ℕ}
    (hb : CoherentPoolBDDBudget C P N S) (calls : Polynomial ℕ) :
    ∃ e : ℕ → ℝ, Negligible e ∧ MixedBudget C P calls N S e := by
  obtain ⟨e,he,hquery⟩ := hb calls
  refine ⟨e,he,?_⟩
  intro n hn hN B hB R hR hsource k m query μ hμ hμsum
  obtain ⟨hw,hs,hm⟩ := poolWeight_subprob (P.eval n) B (R:ℝ)
  apply mixture_rms_bound _ hw hs hm μ hμ hμsum _ (fun pool i => outputProb_bounds _ _ _) _ _ (mul_nonneg (by norm_num : (0:ℝ)≤4) (Nat.cast_nonneg (calls.eval n)))
  intro i
  exact hquery n hn hN B hB R hR hsource k (query i).input (query i).nearest
    (query i).answer (query i).coords (query i).close

/-- Exact squared norm error of a native decoder's copied answer on a finite
superposition of inputs. Any common isometric uncomputation preserves it. -/
theorem native_copy_error_sq {I β : Type} [Fintype I] [Fintype β] [DecidableEq β]
    (C : MFamily) (w : I → Str) (good : I → Str → Prop) (a : I → ℂ)
    (read : Outcomes C w → β) (target : I → β)
    (hread : ∀ x : Outcomes C w, read x = target x.1 ↔ good x.1 (nativeOutput C (w x.1) x.2)) :
    let ψ (x : Outcomes C w) := a x.1 * nativeAmplitude C (w x.1) x.2
    ‖SharedPoolCoherence.copied ψ read - SharedPoolCoherence.copied ψ (fun x => target x.1)‖^2 =
      2 * ∑ i, ‖a i‖^2 * outputProb C (w i) (fun y => ¬ good i y) := by
  classical
  dsimp only
  rw [SharedPoolCoherence.copied_error_sq, Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold outputProb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : good i (nativeOutput C (w i) y)
  · have hg := (hread ⟨i,y⟩).mpr h
    simp only [hg, if_true, nativeOutput] at *
    simp [h]
  · have hg := mt (hread ⟨i,y⟩).mp h
    simp only [hg, if_false, norm_mul, mul_pow]
    simp only [nativeOutput] at h
    simp [h, nativeAmplitude]

theorem copyGap_uncompute {I : Type} [Fintype I] (C : MFamily) (w : I → Str) (a : I → ℂ)
    {b : ℕ} (read : Outcomes C w → Bits b) (target : I → Bits b)
    {E : Type} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (U : EuclideanSpace ℂ (Outcomes C w × Bits b) →ₗᵢ[ℂ] E) :
    let ψ (x : Outcomes C w) := a x.1 * nativeAmplitude C (w x.1) x.2
    ‖U (SharedPoolCoherence.copied ψ read) - U (SharedPoolCoherence.copied ψ (fun x => target x.1))‖ =
      copyGap C w a read target := by
  dsimp only
  rw [← map_sub, LinearIsometry.norm_map]
  rfl

theorem copy_budget_of_mixed {C : MFamily} {P calls : Polynomial ℕ} {N : ℕ} {S : Set ℕ}
    {e : ℕ → ℝ} (hmix : MixedBudget C P calls N S e) : CopyBudget C P calls N S e := by
  intro n hn hN B hB R hR hsource k t q a ha
  dsimp only
  intro regs
  let prec := poolBDDPrecision (calls.eval n) k
  let W := poolWeight (P.eval n) B (R:ℝ)
  let f (p : Fin (P.eval n) → Fin n → ℤ) := ∑ i, ‖a i‖^2 * wrong C B R prec p (q i)
  let v (p : Fin (P.eval n) → Fin n → ℤ) :=
    copyGap C (fun i => word prec p (q i)) a (regs p).read (regs p).answer
  let c : ℝ := (calls.eval n : ℕ)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hf (p) : 0 ≤ f p := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (sq_nonneg _) (outputProb_bounds _ _ _).1)
  have hf1 (p) : f p ≤ 1 := by
    rw [←ha]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_of_le_one_right (sq_nonneg _) (outputProb_bounds _ _ _).2)
  have hs (p) : (v p)^2 = 2 * f p := native_copy_error_sq C (fun i => word prec p (q i))
    (fun i out => encVec encI (q i).answer <+: out) a (regs p).read (regs p).answer (regs p).correct
  have hv (p) : v p ≤ 2 * Real.sqrt (f p) := by
    have h := Real.sq_sqrt (hf p)
    have hvpos : 0 ≤ v p := norm_nonneg _
    apply (sq_le_sq₀ hvpos (by positivity)).mp
    rw [hs, mul_pow, h]
    nlinarith [hf p]
  have hcap (p) : Real.sqrt (f p) ≤ 1 := Real.sqrt_le_one.mpr (hf1 p)
  obtain ⟨hW,hWs,_⟩ := poolWeight_subprob (P.eval n) B (R:ℝ)
  have hsR : Summable (fun p => W p * (4*c*Real.sqrt (f p))) := by
    apply Summable.of_nonneg_of_le (fun p => mul_nonneg (hW p) (by positivity)) _ (hWs.mul_right (4*c))
    intro p
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) (hcap p)) (hW p)
  have hstep (p) : W p * (2*c*v p) ≤ W p * (4*c*Real.sqrt (f p)) := by
    apply mul_le_mul_of_nonneg_left _ (hW p)
    have h := mul_le_mul_of_nonneg_left (hv p) (mul_nonneg (by norm_num : (0:ℝ)≤2) hc)
    linarith only [h]
  have hsL : Summable (fun p => W p * (2*c*v p)) := Summable.of_nonneg_of_le
    (fun p => mul_nonneg (hW p) (mul_nonneg (by positivity) (norm_nonneg _))) hstep hsR
  apply le_trans (hsL.tsum_le_tsum hstep hsR)
  exact hmix n hn hN B hB R hR hsource k t q (fun i => ‖a i‖^2) (fun _ => sq_nonneg _) ha

theorem copy_budget {C : MFamily} {P : Polynomial ℕ} {N : ℕ} {S : Set ℕ}
    (hb : CoherentPoolBDDBudget C P N S) (calls : Polynomial ℕ) :
    ∃ e : ℕ → ℝ, Negligible e ∧ CopyBudget C P calls N S e := by
  obtain ⟨e,he,hm⟩ := mixed_budget hb calls
  exact ⟨e,he,copy_budget_of_mixed hm⟩

end
end SharedPoolCoherence

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch
open scoped BigOperators Classical

theorem solution
    {C : MFamily} {P : Polynomial ℕ} {N : ℕ} {S : Set ℕ}
    (h : CoherentPoolBDDBudget C P N S) (calls : Polynomial ℕ) :
    ∃ e : ℕ → ℝ, Negligible e ∧ SharedPoolCoherence.CopyBudget C P calls N S e :=
  SharedPoolCoherence.copy_budget h calls
