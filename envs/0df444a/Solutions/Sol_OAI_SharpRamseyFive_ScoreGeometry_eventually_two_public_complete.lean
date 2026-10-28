-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:24:38.313175+00:00
-- url     : https://prove2.me/submissions/5396118e-2801-4010-b140-d229572a747e

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_two_oriented

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

lemma finite_bounds {η σ D R : ℝ} (hη : 0 < η) (_hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) :
    0 < D ∧ 0 < R ∧ 1 ≤ σ ^ beta η ∧
    σ ^ (9 * beta η) ≤ L η σ D ∧ L η σ D ≤ σ ∧
    σ ^ (10 * beta η) ≤ P η σ D R ∧
    P η σ D R ≤ 4 * σ ^ (1 - η/2 + 9 * beta η) := by
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hb : 0 < beta η := beta_pos hη
  have hx : 1 ≤ σ ^ beta η := Real.one_le_rpow hσ hb.le
  have hd : 0 < D := (Real.rpow_pos_of_pos hs _).trans_le h.dlo
  have hr : 0 < R := (Real.rpow_pos_of_pos hs _).trans_le h.rlo
  have hlo : σ ^ (9 * beta η) ≤ L η σ D := by
    dsimp [L]
    calc
      _ = σ ^ beta η * σ ^ (8 * beta η) := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.dlo (Real.rpow_nonneg hs.le _)
  have hhi : L η σ D ≤ σ := by
    dsimp [L]
    calc
      _ ≤ σ ^ (1-η/2) * σ ^ (8*beta η) := mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)
      _ = σ ^ (1-η/2+8*beta η) := (Real.rpow_add hs _ _).symm
      _ ≤ σ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hσ (by dsimp [beta]; linarith)
      _ = σ := Real.rpow_one _
  refine ⟨hd,hr,hx,hlo,hhi,?_,?_⟩
  · calc
      _ = σ ^ (9*beta η) * σ ^ beta η := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ L η σ D * R := mul_le_mul hlo h.rlo (Real.rpow_nonneg hs.le _) (by dsimp [L]; positivity)
  · have hR : R ≤ 4 * σ ^ beta η := h.rhi.trans (by linarith)
    calc
      _ ≤ (σ ^ (1-η/2) * σ ^ (8*beta η)) * (4*σ ^ beta η) := by
        dsimp [P,L]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)) hR hr.le (by positivity)
      _ = 4 * σ ^ (1-η/2+9*beta η) := by
        rw [show σ ^ (1-η/2) * σ ^ (8*beta η) * (4*σ ^ beta η) =
          4 * ((σ ^ (1-η/2) * σ ^ (8*beta η)) * σ ^ beta η) by ring,
          ← Real.rpow_add hs, ← Real.rpow_add hs]
        congr 2
        ring

lemma ratio_bounds {η σ D R b τ : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) (Cb : ℝ) (_hCb : 0 ≤ Cb)
    (hb : b ≤ Cb * D * σ ^ (6*beta η)) (hτ : τ ≤ σ ^ (-200*beta η)) :
    P η σ D R / σ ≤ 4*σ ^ (-(η/2-9*beta η)) ∧
    Real.log σ / P η σ D R ≤ Real.log σ / σ ^ (10*beta η) ∧
    R * Real.log (L η σ D) / P η σ D R ≤ Real.log σ / σ ^ (9*beta η) ∧
    (b + P η σ D R * τ) / L η σ D ≤ Cb*σ ^ (-2*beta η) + 4*σ ^ (-199*beta η) ∧
    L η σ D / P η σ D R ≤ σ ^ (-beta η) := by
  obtain ⟨hD,hR,hx,hL,hLhi,hP,hPhi⟩ := finite_bounds hη hη' hσ h
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hLp : 0 < L η σ D := (Real.rpow_pos_of_pos hs _).trans_le hL
  have hPp : 0 < P η σ D R := (Real.rpow_pos_of_pos hs _).trans_le hP
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ (4*σ ^ (1-η/2+9*beta η))/σ := div_le_div_of_nonneg_right hPhi hs.le
      _ = _ := by
        rw [mul_div_assoc]
        have he : σ ^ (1-η/2+9*beta η) / σ = σ ^ (1-η/2+9*beta η-1) := by
          simpa only [Real.rpow_one] using (Real.rpow_sub hs (1-η/2+9*beta η) 1).symm
        rw [he]
        congr 2
        ring
  · exact div_le_div_of_nonneg_left (Real.log_nonneg hσ) (Real.rpow_pos_of_pos hs _) hP
  · have he : R * Real.log (L η σ D) / P η σ D R = Real.log (L η σ D) / L η σ D := by
      dsimp [P]; field_simp
    rw [he]
    exact (div_le_div_of_nonneg_right (Real.log_le_log hLp hLhi) hLp.le).trans
      (div_le_div_of_nonneg_left (Real.log_nonneg hσ) (Real.rpow_pos_of_pos hs _) hL)
  · have hRhi : R ≤ 4*σ ^ beta η := h.rhi.trans (by linarith)
    have hf : (b + P η σ D R*τ)/L η σ D = b/L η σ D + R*τ := by
      dsimp [P]; field_simp
    rw [hf]
    have hb' : b/L η σ D ≤ Cb*σ ^ (-2*beta η) := by
      apply (div_le_iff₀ hLp).mpr
      calc
        b ≤ Cb*D*σ ^ (6*beta η) := hb
        _ = _ := by
          dsimp [L]
          rw [show Cb*σ ^ (-2*beta η)*(D*σ ^ (8*beta η)) =
            Cb*D*(σ ^ (-2*beta η)*σ ^ (8*beta η)) by ring, ← Real.rpow_add hs]
          congr 2
          ring
    have ht' : R*τ ≤ 4*σ ^ (-199*beta η) := by
      calc
        _ ≤ R*σ ^ (-200*beta η) := mul_le_mul_of_nonneg_left hτ hR.le
        _ ≤ (4*σ ^ beta η)*σ ^ (-200*beta η) :=
          mul_le_mul_of_nonneg_right hRhi (Real.rpow_nonneg hs.le _)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hs]; congr 2; ring
    exact add_le_add hb' ht'
  · apply (div_le_iff₀ hPp).mpr
    change L η σ D ≤ σ ^ (-beta η) * (L η σ D * R)
    have he : σ ^ (-beta η)*σ ^ beta η = 1 := by rw [← Real.rpow_add hs]; simp
    have hh := mul_le_mul_of_nonneg_left h.rlo (Real.rpow_nonneg hs.le (-beta η))
    rw [he] at hh
    nlinarith

theorem eventually_hierarchy {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb c A : ℝ) (hCb : 0 ≤ Cb) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ D R b τ : ℝ, Range η σ D R →
      b ≤ Cb*D*σ ^ (6*beta η) → τ ≤ σ ^ (-200*beta η) →
      A ≤ L η σ D ∧ P η σ D R ≤ c*σ ∧
      Real.log σ ≤ c*P η σ D R ∧
      R*Real.log (L η σ D) ≤ c*P η σ D R ∧
      b+P η σ D R*τ ≤ c*L η σ D ∧ L η σ D ≤ c*P η σ D R := by
  have hb : 0 < beta η := beta_pos hη
  have he : 0 < η/2-9*beta η := by dsimp [beta]; linarith
  have h1 : Tendsto (fun σ : ℝ => 4*σ ^ (-(η/2-9*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop he).const_mul 4
  have h2 := (isLittleO_log_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<10) hb)).tendsto_div_nhds_zero
  have h3 := (isLittleO_log_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<9) hb)).tendsto_div_nhds_zero
  have h4 : Tendsto (fun σ : ℝ => Cb*σ ^ (-2*beta η)+4*σ ^ (-199*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul, mul_zero, zero_add] using
      ((tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<2) hb)).const_mul Cb).add
      ((tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<199) hb)).const_mul 4)
  have h5 := tendsto_rpow_neg_atTop hb
  have h6 := (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<9) hb)).eventually (eventually_ge_atTop A)
  filter_upwards [eventually_ge_atTop (1:ℝ), h1.eventually_lt_const hc,
    h2.eventually_lt_const hc, h3.eventually_lt_const hc, h4.eventually_lt_const hc,
    h5.eventually_lt_const hc, h6] with σ hσ h1' h2' h3' h4' h5' h6'
  intro D R b τ h hb' hτ
  obtain ⟨hD,hR,_,hL,_,hP,_⟩ := finite_bounds hη hη' hσ h
  obtain ⟨hr1,hr2,hr3,hr4,hr5⟩ := ratio_bounds hη hη' hσ h Cb hCb hb' hτ
  have hLp : 0 < L η σ D := by dsimp [L]; positivity
  have hPp : 0 < P η σ D R := mul_pos hLp hR
  exact ⟨h6'.trans hL, (div_le_iff₀ (zero_lt_one.trans_le hσ)).mp (hr1.trans h1'.le),
    (div_le_iff₀ hPp).mp (hr2.trans h2'.le), (div_le_iff₀ hPp).mp (hr3.trans h3'.le),
    (div_le_iff₀ hLp).mp (hr4.trans h4'.le), (div_le_iff₀ hPp).mp (hr5.trans h5'.le)⟩

theorem eventually_power_absorption {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (C k c : ℝ) (hC : 0 < C) (_hk : 0 ≤ k) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ D R : ℝ, Range η σ D R →
      C*σ ^ k ≤ Real.exp (c*P η σ D R) := by
  have hb : 0 < 10*beta η := mul_pos (by norm_num) (beta_pos hη)
  have hlog : Tendsto (fun σ : ℝ => (Real.log C+k*Real.log σ)/σ ^ (10*beta η)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun σ : ℝ => Real.log C/σ ^ (10*beta η)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hb)
    have hvar := ((isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero).const_mul k
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hconst.add hvar
  filter_upwards [eventually_ge_atTop (1:ℝ), hlog.eventually_lt_const hc] with σ hσ hh
  intro D R h
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hPs := (finite_bounds hη hη' hσ h).2.2.2.2.2.1
  have hcost : Real.log C+k*Real.log σ ≤ c*P η σ D R :=
    ((div_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp hh.le).trans
      (mul_le_mul_of_nonneg_left hPs hc.le)
  apply (Real.log_le_iff_le_exp (mul_pos hC (Real.rpow_pos_of_pos hs _))).mp
  rwa [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hs k).ne', Real.log_rpow hs]

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FinitePiLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι→Type*} [∀i,Fintype (β i)]

lemma piLaw_prod (p : ∀i,Law (β i)) (f : ∀i,β i→ℝ) :
    (∑x,piLaw p x*(∏i,f i (x i)))=∏i,∑a,p i a*f i a := by
  simp only [piLaw,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a=>p i a*f i a)).symm

lemma piLaw_eval_expectation (p : ∀i,Law (β i)) (i : ι) (f : β i→ℝ) :
    (∑x,piLaw p x*f (x i))=∑a,p i a*f a := by
  let g : ∀j,β j→ℝ := fun j a=>if h : j=i then f (h ▸ a) else 1
  have hx (x : ∀j,β j) : (∏j,g j (x j))=f (x i) := by
    have he : (fun j=>g j (x j))=Function.update (fun _=>1) i (f (x i)) := by
      funext j
      by_cases hj : j=i
      · subst j;simp [g]
      · simp [g,hj]
    rw [he,Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hs : (fun j=>∑a,p j a*g j a)=Function.update (fun _=>1) i (∑a,p i a*f a) := by
    funext j
    by_cases hj : j=i
    · subst j;simp [g]
    · simp [g,hj,(p j).sum_one]
  have hh := piLaw_prod p g
  simp_rw [hx] at hh
  rw [hs,Finset.prod_update_of_mem (Finset.mem_univ i)] at hh
  simpa using hh

lemma piLaw_eval (p : ∀i,Law (β i)) (i : ι) : map (piLaw p) (fun x=>x i)=p i := by
  apply Law.ext
  funext a
  have hm := piLaw_eval_expectation p i (fun b=>if b=a then 1 else 0)
  simpa only [map,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hm
end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SequentialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

open MeasureTheory
open scoped Classical BigOperators
variable {Ω α : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α]

lemma finiteImageLaw_event (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) (E : Finset α) :
    eventMass (finiteImageLaw μ f) E=μ.real {ω | f ω∈E} := by
  have hd : Set.PairwiseDisjoint (E:Set α) (fun a=>{ω | f ω=a}) := by
    intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have he : (⋃a∈E,{ω | f ω=a})={ω | f ω∈E} := by ext ω;simp
  have hh := measureReal_biUnion_finset (μ:=μ) hd
    (fun _ _=>Set.Countable.measurableSet (Set.to_countable _))
  rw [he] at hh
  exact hh.symm

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_sound (P : Ω→α→Prop) (ω : Ω) (a : α)
    (h : chooseMessage P ω=some a) : P ω a := by
  unfold chooseMessage at h
  split at h
  next hh => exact (Option.some.inj h) ▸ hh.choose_spec
  next hh => contradiction

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_OwnFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity

open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma Q_le_two_pow (q k : ℕ) (hq : 2≤q) : (Q q k:ℝ) ≤ 2*(q:ℝ)^k-1 := by
  induction k with
  | zero => norm_num [Q]
  | succ k ih =>
    have he : (Q q (k+1):ℝ)=(Q q k:ℝ)+(q:ℝ)^(k+1) := by
      unfold Q
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_pow]
    rw [he,pow_succ]
    have hq' : (2:ℝ)≤q := by exact_mod_cast hq
    have hp := pow_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) k
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A]

lemma ceil_ratio_log (q a : ℝ) (hq : 1 ≤ q) (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.log (⌈q/a⌉₊:ℝ) ≤ Real.log (2*q)-Real.log a := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hx : 1 ≤ q/a := (le_div_iff₀ ha).mpr (by simpa using ha1.trans hq)
  have hcpos : (0:ℝ) < ⌈q/a⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (div_pos hqpos ha)
  have hh : (⌈q/a⌉₊:ℝ) ≤ (2*q)/a := by
    have ht := Nat.ceil_lt_add_one (div_pos hqpos ha).le
    have he : 2*(q/a)=(2*q)/a := by ring
    linarith
  have hl := Real.log_le_log hcpos hh
  rwa [Real.log_div (by positivity : (2*q:ℝ) ≠ 0) ha.ne'] at hl

omit [Fintype A] in
theorem uniformCutoff_log (q : ℝ) (hq : 1 ≤ q) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W) (n : ℕ) :
    Real.log (uniformCutoff q C W n) ≤
      Real.log (2*q)-Real.log ((9:ℝ)/10)+(n:ℝ)*Real.log ((W.card:ℝ)/C.card) := by
  have hc : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hw : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hratio : (C.card:ℝ)/W.card ≤ 1 := (div_le_one hw).mpr (by exact_mod_cast Finset.card_le_card hCW)
  have hpow := pow_le_one₀ (n := n) (by positivity : (0:ℝ) ≤ (C.card:ℝ)/W.card) hratio
  have hh := ceil_ratio_log q ((9:ℝ)/10*((C.card:ℝ)/W.card)^n) hq (by positivity) (by nlinarith)
  change Real.log (uniformCutoff q C W n) ≤ _ at hh
  rw [Real.log_mul (by norm_num : (9:ℝ)/10 ≠ 0) (by positivity),Real.log_pow,
    Real.log_div hc.ne' hw.ne'] at hh
  rw [Real.log_div hw.ne' hc.ne']
  linarith

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreSearchCost_nonneg (S U : Finset (ℙ K V)) (hS : S.Nonempty)
    (hSU : S⊆U) (P τ : ℝ) (hP : 0≤P) (hτ : 0≤τ) :
    0 ≤ scoreSearchCost S U P τ := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hs).mpr (by simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
  unfold scoreSearchCost
  exact add_nonneg (mul_nonneg (Real.log_nonneg hr) (by positivity))
    (add_nonneg (by positivity) (Real.log_nonneg (by norm_num)))

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreCutoff_pos (S U : Finset (ℙ K V)) (P τ : ℝ) : 0 < scoreCutoff S U P τ := by
  apply Nat.ceil_pos.mpr
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  positivity

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AmbientPublicTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma cap_inter (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    U∩cap R Finset.univ q row=cap R U q row := by
  ext a
  simp [cap]

lemma ambientCapLaw_restrict (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    map (ambientCapLaw R S U C W hW n q M) (Option.map fun Y=>U∩Y)=
      publicCapLaw R S U C W hW n q M := by
  unfold ambientCapLaw publicCapLaw
  rw [map_comp]
  congr 1
  funext row
  cases row with
  | none => rfl
  | some row =>
    change some (U∩cap R Finset.univ q row)=some (cap R U q row)
    rw [cap_inter]

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshPublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}
lemma acceptedIndex_decode {n : ℕ} (E : Finset A) (t : Fin n→A) :
    Option.map t (acceptedIndex E t)=firstAccepted E t :=
  Classical.choose_spec (exists_accepted_index E t)
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma freshEncoded_decoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q) :
    Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t)=
      Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M)
          (t ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩)) := by
  unfold freshEncoded freshDecoded
  rw [←acceptedIndex_decode]
  simp only [Option.map_map]
  rfl

theorem fresh_public_law (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    map (freshTapeLaw W hW n q)
      (fun t=>Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t))=
    ambientCapLaw R S U C W hW n q M := by
  let m : Fin (W.card+1) := ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩
  have hm := piLaw_eval (fun m : Fin (W.card+1)=>
    iid (iid (uniformOn W hW) (Fin n)) (Fin (cardCutoff q m W.card n))) m
  have ht := congrArg (fun p=>map (map p (firstAccepted (validationRows R S U C n q M)))
    (Option.map (cap R Finset.univ q))) hm
  simp only [map_comp] at ht
  unfold ambientCapLaw
  rw [map_comp]
  calc
    _ = map (freshTapeLaw W hW n q) (fun t=>Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M) (t m))) := by
      congr 1
      funext t
      exact freshEncoded_decoded R S U C W hCW n q M t
    _ = _ := ht

omit [Fintype B] in
theorem fresh_payload_cost (q : ℝ) (hq : 1≤q) (C W : Finset B)
    (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W) (n : ℕ) :
    Real.log (Fintype.card (Fin (cardCutoff q C.card W.card n)):ℝ)≤
      Real.log (2*q)-Real.log ((9:ℝ)/10)+n*Real.log ((W.card:ℝ)/C.card) := by
  rw [Fintype.card_fin]
  simpa only [cardCutoff,uniformCutoff] using
    uniformCutoff_log q hq C W hC hW hCW n
end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TwoCapCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical

lemma capture_log_ratio (a c w z T : ℝ) (ha : 0<a) (hc : 0 < c)
    (hw : 0<w) (hz : 0<z) (hcap : c*a≤z) (hsize : w≤a*Real.exp T) :
    Real.log (w/z)≤T-Real.log c := by
  have hlw := Real.log_le_log hw hsize
  have hlz := Real.log_le_log (mul_pos hc ha) hcap
  rw [Real.log_mul ha.ne' (Real.exp_pos _).ne',Real.log_exp] at hlw
  rw [Real.log_mul hc.ne' ha.ne'] at hlz
  rw [Real.log_div hw.ne' hz.ne']
  linarith

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_FreshPublicValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
theorem general_reverse_payload (T UT W : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (c B P : ℝ) (hc : 0 < c)
    (hv : CaptureBound T UT c ((T.card:ℝ)*Real.exp (B*P)) W)
    (q : ℝ) (hq : 1≤q) (n : ℕ) :
    Real.log (Fintype.card (Fin (cardCutoff q (T∩W).card W.card n)):ℝ)≤
      Real.log (2*q)-Real.log ((9:ℝ)/10)+n*(B*P-Real.log c) := by
  have hC := hv.nonempty hT hc
  have hW := hC.mono Finset.inter_subset_right
  have hu := fresh_payload_cost q hq (T∩W) W hC hW Finset.inter_subset_right n
  have hr := capture_log_ratio T.card c W.card (T∩W).card (B*P)
    (by exact_mod_cast hT.card_pos) hc (by exact_mod_cast hW.card_pos)
    (by exact_mod_cast hC.card_pos) hv.2.2 hv.2.1
  have hm := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤n by positivity)
  linarith

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ReverseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

theorem eventually_reverse_parameters {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D R b τ : ℝ), Range η σ D R →
      b≤Cb*D*σ^(6*beta η) → 0≤τ → τ≤σ^(-200*beta η) →
      1≤P η σ D R ∧ b≤P η σ D R ∧ 1000≤Real.exp (P η σ D R) ∧
      1000*τ≤(9:ℝ)/10 ∧ 3≤Real.exp σ := by
  have hh := eventually_hierarchy hη hη' Cb 1 1 hCb (by norm_num)
  have hc := eventually_power_absorption hη hη' 1000 0 1 (by norm_num) (by norm_num) (by norm_num)
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)<(9:ℝ)/10000 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const (by norm_num : (0:ℝ)<9/10000)
  filter_upwards [hh,hc,ht,eventually_ge_atTop (10:ℝ)] with σ hh hc ht hσ
  intro D R b τ hr hb hτ hτhi
  have hv := hh D R b τ hr hb hτhi
  have hP : 1≤P η σ D R := by linarith only [hv.1,hv.2.2.2.2.2]
  have hbP : b≤P η σ D R := by
    have hn : 0≤P η σ D R*τ := mul_nonneg (le_trans (by norm_num) hP) hτ
    linarith only [hv.2.2.2.2.1,hv.2.2.2.2.2,hn]
  refine ⟨hP,hbP,?_,?_,?_⟩
  · simpa only [Real.rpow_zero,mul_one,one_mul] using hc D R hr
  · linarith only [hτhi,ht]
  · linarith only [Real.add_one_le_exp σ,hσ]

end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma universalFresh_marginal (H : ℕ) (q : ℝ) (i : FreshIndex B H) :
    map (universalFreshLaw B H q) (fun t=>t i)=freshTapeLaw i.1.1 i.1.2 i.2 q :=
  piLaw_eval _ i

lemma universalFresh_output (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (hCW : C⊆W) (H n : ℕ) (hn : n≤H)
    (q M : ℝ) :
    let i : FreshIndex B H := (⟨W,hW⟩,⟨n,Nat.lt_succ_of_le hn⟩)
    map (universalFreshLaw B H q)
      (fun t=>Option.map (freshDecoded R W n q (t i)) (freshEncoded R S U C W hCW n q M (t i)))=
      ambientCapLaw R S U C W hW n q M := by
  dsimp only
  rw [←fresh_public_law R S U C W hCW hW n q M]
  have hm := universalFresh_marginal (B:=B) H q
    ((⟨W,hW⟩,⟨n,Nat.lt_succ_of_le hn⟩) : FreshIndex B H)
  rw [←hm,map_comp]
  rfl

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PublicComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma map_const (p : Law α) (b : β) : map p (fun _=>b)=pureLaw b := by
  apply Law.ext
  funext x
  by_cases hx : b=x
  · subst x
    simp [map,pureLaw,p.sum_one]
  · simp [map,pureLaw,hx,Ne.symm hx]

lemma adaptive_output_mass (p : Law α) (next : α→Law β) (out : α→β→γ) (c : γ) :
    map (adaptiveLaw p next) (fun z=>out z.1 z.2) c=
      ∑a,p a*map (next a) (out a) c := by
  simp only [map,adaptiveLaw,Fintype.sum_prod_type,Finset.mul_sum,mul_ite,mul_zero]

lemma public_composition (p : Law α) (tape : Law β) (firstOut : α→γ)
    (out : γ→β→δ) (next : γ→Law δ)
    (hm : ∀c,map tape (out c)=next c) :
    map (adaptiveLaw p (fun _=>tape)) (fun z=>out (firstOut z.1) z.2)=
      map (adaptiveLaw (map p firstOut) next) Prod.snd := by
  apply Law.ext
  funext d
  rw [adaptive_output_mass (out:=fun a b=>out (firstOut a) b)]
  have hr := adaptive_output_mass (map p firstOut) next (fun _ x=>x) d
  change map (adaptiveLaw (map p firstOut) next) Prod.snd d = ∑ a, map p firstOut a * map (next a) id d at hr
  simp only [map_id] at hr
  rw [hr,sum_map]
  apply Finset.sum_congr rfl
  intro a _
  rw [hm]

lemma optionCompose_eq_second (p : Law (Option α))
    (next : Option α→Law (Option β)) (hn : next none=pureLaw none) :
    optionCompose p next=map (adaptiveLaw p next) Prod.snd := by
  apply Law.ext
  funext b
  have h₁ := adaptive_output_mass p next (fun a b=>a.bind fun _=>b) b
  have h₂ := adaptive_output_mass p next (fun _ b=>b) b
  rw [optionCompose,h₁,h₂]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  cases a with
  | none =>
    change map (next none) (fun _ : Option β => (none : Option β)) b = map (next none) id b
    rw [map_const,map_id,hn]
  | some a => rfl
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma universalFreshEncoded_exact (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) :
    (universalFreshEncoded R S U C W hCW H n q M t).map (universalFreshDecoded R W H q t)=
      (freshEncoded R S U C W hCW n q M (t (⟨W,hW⟩,n))).map
        (freshDecoded R W n q (t (⟨W,hW⟩,n))) := by
  simp only [universalFreshEncoded,dite_eq_left hW,Option.map_map]
  congr 1
  funext m
  exact dite_eq_left hW

lemma universalFreshEncoded_law (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (H : ℕ) (n : Fin (H+1)) (q M : ℝ) :
    map (universalFreshLaw B H q) (fun t=>
      (universalFreshEncoded R S U C W hCW H n q M t).map (universalFreshDecoded R W H q t))=
      ambientCapLaw R S U C W hW n q M := by
  simp only [universalFreshEncoded_exact R S U C W hCW hW]
  exact universalFresh_output R S U C W hW hCW H n (Nat.le_of_lt_succ n.isLt) q M
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
theorem publicReverseResult_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) :
    map (universalFreshLaw (ℙ K (Dual K V)) H q) (publicReverseResult A UA B UB hB H n q MA MB Y)=
      nextCapLaw A UA B UB hB n q MA MB Y := by
  cases Y with
  | none => exact map_const _ none
  | some W =>
    change map (universalFreshLaw (ℙ K (Dual K V)) H q)
      (fun t=>if _hW : ValidCap B UB MB W then
        (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
          (fun m=>UA∩universalFreshDecoded Incident W H q t m) else none) = _
    dsimp only [nextCapLaw]
    split_ifs with hv
    · have hW := (hv.source_nonempty hB).mono Finset.inter_subset_right
      have hh := congrArg (fun p=>map p (Option.map fun Z=>UA∩Z))
        (universalFreshEncoded_law Incident A UA (B∩W) W Finset.inter_subset_right hW H n q MA)
      rw [ambientCapLaw_restrict,map_comp] at hh
      simpa only [Function.comp_def,Option.map_map] using hh
    · exact map_const _ none
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SubsetEncoding
open scoped Classical BigOperators

lemma log_factorial_lower (n : ℕ) :
    (n:ℝ)*Real.log n-n≤Real.log (n.factorial:ℝ) := by
  by_cases hn : n=0
  · subst n;norm_num
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h := Stirling.le_log_factorial_stirling hn
  have hp : (1:ℝ)≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hl := Real.log_nonneg hp
  have hl' := Real.log_nonneg hn1
  linarith

lemma log_choose_le (m n : ℕ) (hnm : n ≤ m) :
    Real.log (m.choose n:ℝ)≤(n:ℝ)*(Real.log ((m:ℝ)/n)+1) := by
  by_cases hn : n=0
  · subst n;simp
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmpos : (0:ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hn).trans_le hnm
  have hcp : (0:ℝ) < m.choose n := by exact_mod_cast Nat.choose_pos hnm
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := Real.log_le_log hcp (Nat.choose_le_pow_div n m : (m.choose n:ℝ)≤(m:ℝ)^n/n.factorial)
  rw [Real.log_div (pow_ne_zero _ hmpos.ne') hfact.ne',Real.log_pow] at h
  rw [Real.log_div hmpos.ne' hnpos.ne']
  have hf := log_factorial_lower n
  nlinarith

variable {α : Type*} [Fintype α]

lemma alphabet_card (U : Finset α) (n : ℕ) :
    Fintype.card (Alphabet U n)=U.card.choose n := by
  classical
  unfold Alphabet
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun A : Finset α=>A⊆U ∧ A.card=n)=U.powersetCard n := by
    ext A;simp
  rw [he,Finset.card_powersetCard]

lemma decode_encode (S U : Finset α) (hSU : S⊆U) : decode U S.card (encode S U hSU)=S := by
  exact congrArg Subtype.val ((Fintype.equivFin (Alphabet U S.card)).symm_apply_apply ⟨S,hSU,rfl⟩)

theorem small_set_description (S U : Finset α) (hSU : S⊆U)
    (q P : ℝ) (hn : (S.card:ℝ)≤100*q*P) :
    decode U S.card (encode S U hSU)=S ∧
    Real.log (Fintype.card (Alphabet U S.card):ℝ)≤
      100*q*P*(Real.log ((U.card:ℝ)/S.card)+1) := by
  refine ⟨decode_encode S U hSU,?_⟩
  rw [alphabet_card]
  have h := log_choose_le U.card S.card (Finset.card_le_card hSU)
  apply h.trans
  apply mul_le_mul_of_nonneg_right hn
  by_cases hs : S.card=0
  · simp [hs]
  · have hp : (0:ℝ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hp).mpr (by
      simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
    linarith [Real.log_nonneg hr]

end SharpRamseyFive.SubsetEncoding

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma base_cost_scalar (q P gap τ : ℝ) (hq : 2≤q) (hP : 1≤P)
    (hgap : 0≤gap) (_hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (2*q) + gap*(2*q*P)+(8*P*τ+Real.log 4)+Real.log (2*q^2) ≤
      20*q*P*(gap+P) := by
  have hp : 0<P := by linarith
  have hq' : 0<q := by linarith
  have hl := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<2*q)
  have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  have hlq := Real.log_le_sub_one_of_pos hq'
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have he : Real.log (2*q^2)=Real.log 2+2*Real.log q := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hq'.ne'),Real.log_pow]
    norm_num
  rw [he]
  have ht := mul_le_mul_of_nonneg_left hτ1 (by positivity : (0:ℝ)≤8*P)
  have hqp : q≤q*P := by nlinarith
  have hpp : q*P≤q*P*P := by nlinarith
  have hgp : 0≤q*P*gap := by positivity
  nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BaseAlphabetCost
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureBaseTapeBaseTapeMeasure _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureForallFinSizeScoreCutoffForallForallProjectivizationNatBaseRowMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding CellVariance ScoreRegularity
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseAlphabet_small_card (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ)
    (hn : (n:ℝ)≤100*(Nat.card K:ℝ)*P) :
    Fintype.card (baseAlphabet U n P τ)=Fintype.card (Alphabet U n) := by
  calc
    _ = Fintype.card (Fin (Fintype.card (Alphabet U n))) :=
      Fintype.card_congr (Equiv.cast (by simp only [baseAlphabet,hn,ite_true]))
    _ = _ := Fintype.card_fin _

omit [Finite K] [FiniteDimensional K V] in
lemma baseAlphabet_large_card (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ)
    (hn : ¬(n:ℝ)≤100*(Nat.card K:ℝ)*P) :
    Fintype.card (baseAlphabet U n P τ)=
      sizeScoreCutoff U n P τ*(Fintype.card (ℙ K (Dual K V))+1) := by
  calc
    _ = Fintype.card (Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) :=
      Fintype.card_congr (Equiv.cast (by simp only [baseAlphabet,hn,ite_false]))
    _ = _ := by rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

omit [FiniteDimensional K V] in
theorem baseAlphabet_cost (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (Fintype.card (baseAlphabet U S.card P τ):ℝ)≤
      100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  have hqN : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast hqN
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hp : 0≤P := by linarith
  have hgap : 0≤Real.log ((U.card:ℝ)/S.card) := Real.log_nonneg ((le_div_iff₀ hs).mpr (by
    simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  by_cases hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P
  · rw [baseAlphabet_small_card U _ P τ hn]
    apply (small_set_description S U hSU (Nat.card K:ℝ) P hn).2.trans
    apply mul_le_mul_of_nonneg_left (by linarith : Real.log ((U.card:ℝ)/S.card)+1≤
      Real.log ((U.card:ℝ)/S.card)+P)
    positivity
  · rw [baseAlphabet_large_card U _ P τ hn,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hN : 0 < sizeScoreCutoff U S.card P τ := scoreCutoff_pos S U P τ
    have hD : (0:ℝ)<Fintype.card (ℙ K (Dual K V))+1 := by positivity
    rw [Real.log_mul (by exact_mod_cast Nat.ne_of_gt hN) hD.ne']
    have hA := scoreSearchCost_nonneg S U hS hSU P τ hp hτ
    have hl := FiniteEntropy.ceil_ratio_log (Nat.card K:ℝ)
      (Real.exp (-scoreSearchCost S U P τ)) (by linarith) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA))
    rw [Real.log_exp,sub_neg_eq_add] at hl
    have hlogN : Real.log (sizeScoreCutoff U S.card P τ)≤
        Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ := by
      simpa only [sizeScoreCutoff,scoreSearchCost,Real.exp_neg,div_inv_eq_mul] using hl
    have hlogD : Real.log (Fintype.card (ℙ K (Dual K V))+1:ℝ)≤
        Real.log (2*(Nat.card K:ℝ)^2) := by
      apply Real.log_le_log hD
      rw [card_hyperplanes (d:=2) hdim]
      have hh := Q_le_two_pow (Nat.card K) 2 hqN
      linarith
    have hscalar := base_cost_scalar (Nat.card K:ℝ) P (Real.log ((U.card:ℝ)/S.card)) τ
      hq hP hgap hτ hτ1
    unfold scoreSearchCost at hlogN
    have hlast : 0≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by positivity
    nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BaseMessageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding CellVariance ScoreRegularity
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] in
theorem baseMessage_cost (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)+
      Real.log (Fintype.card (baseAlphabet U S.card P τ):ℝ)≤
      110*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  have hqN : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast hqN
  have hqp : (0:ℝ)<Nat.card K := by linarith
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hgap : 0≤Real.log ((U.card:ℝ)/S.card) := Real.log_nonneg ((le_div_iff₀ hs).mpr (by
    simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  have hheader : Real.log (Fintype.card (ℙ K V)+1:ℝ)≤3*(Nat.card K:ℝ) := by
    have hcard : (Fintype.card (ℙ K V)+1:ℝ)≤2*(Nat.card K:ℝ)^2 := by
      rw [card_points (d:=2) hdim]
      have hh := Q_le_two_pow (Nat.card K) 2 hqN
      linarith
    have hh := Real.log_le_log (by positivity : (0:ℝ)<Fintype.card (ℙ K V)+1) hcard
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hqp.ne'),Real.log_pow] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have h3 := Real.log_le_sub_one_of_pos hqp
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hcost := baseAlphabet_cost hdim S U hS hSU P τ hP hτ hτ1
  have hprod : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
    have hp : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P := by nlinarith
    have hgap' : 1≤Real.log ((U.card:ℝ)/S.card)+P := by linarith
    exact hp.trans (le_mul_of_one_le_right (by positivity) hgap')
  nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndependentLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
lemma independent_second (p : Law α) (q : Law β) :
    map (adaptiveLaw p (fun _=>q)) Prod.snd=q := by
  apply Law.ext
  funext b
  change (∑z : α×β,if z.2=b then p z.1*q z.2 else 0)=q b
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [←Finset.sum_mul,p.sum_one,one_mul]
lemma independent_first (p : Law α) (q : Law β) :
    map (adaptiveLaw p (fun _=>q)) Prod.fst=p := by
  apply Law.ext
  funext a
  simp [map,adaptiveLaw,Fintype.sum_prod_type,←Finset.mul_sum,q.sum_one]
lemma map_independent_left (p : Law α) (q : Law β) (f : α→γ) :
    map (adaptiveLaw p (fun _=>q)) (fun z=>f z.1)=map p f := by
  have h := congrArg (fun r=>map r f) (independent_first p q)
  simpa only [map_comp,Function.comp_def] using h
lemma map_independent_right (p : Law α) (q : Law β) (f : β→γ) :
    map (adaptiveLaw p (fun _=>q)) (fun z=>f z.2)=map q f := by
  have h := congrArg (fun r=>map r f) (independent_second p q)
  simpa only [map_comp,Function.comp_def] using h
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoredMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype (ℙ K (Dual K V))] in

lemma projective_header_le (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)≤6*(Nat.card K:ℝ) := by
  have hv := vector_card_le_exp (K:=K) (V:=V) σ hq hd
  have hp : (Fintype.card (ℙ K V):ℝ)≤Nat.card V := by
    exact_mod_cast projective_card_le_vectors (Finset.univ : Finset (ℙ K V))
  have he : Real.exp (5*σ)+1≤Real.exp (6*σ) := by
    have h1 : 1≤Real.exp (5*σ) := Real.one_le_exp_iff.mpr (by linarith)
    have h2 : 2≤Real.exp σ := (by linarith : (2:ℝ)≤σ+1).trans (Real.add_one_le_exp σ)
    have hx : Real.exp (6*σ)=Real.exp (5*σ)*Real.exp σ := by
      rw [←Real.exp_add];congr 1;ring
    rw [hx]
    nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<Fintype.card (ℙ K V)+1)
    (show (Fintype.card (ℙ K V)+1:ℝ)≤Real.exp (6*σ) by linarith)
  rw [Real.log_exp] at hl
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  linarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReverseMessageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open Module ScoreGeometry Metadata ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma length_header_cost (q : ℕ) (hq : 1≤q) :
    Real.log (1000*q^2+1:ℝ)≤1002*(q:ℝ) := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hq0 : (0:ℝ)<q := by linarith
  have hb : (1000*q^2+1:ℝ)≤1001*(q:ℝ)^2 := by nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<1000*q^2+1) hb
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),Real.log_pow] at hl
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1001)
  have hlog := Real.log_le_sub_one_of_pos hq0
  norm_num at hl
  linarith

lemma general_reverse_cost_scalar (q P gap c B n : ℝ) (hq : 1≤q) (hP : 1≤P)
    (hg : 0≤gap) (hc : 0 < c) (hc1 : c≤1) (hB : 0≤B)
    (hn : 0≤n) (hnhi : n≤21*q*(gap+1)) :
    1008*q+Real.log (2*q)-Real.log ((9:ℝ)/10)+n*(B*P-Real.log c)≤
      (1010+21*(B-Real.log c))*q*P*(gap+P) := by
  have hq0 : 0<q := by linarith
  have hP0 : 0≤P := by linarith
  have hlc : Real.log c≤0 := Real.log_nonpos hc.le hc1
  have hln := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<9/10)
  norm_num at hln
  have hlq := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<2*q)
  have hcP : B*P-Real.log c≤(B-Real.log c)*P := by nlinarith only [hP,hlc]
  have hnP := mul_le_mul_of_nonneg_left hcP hn
  have hnn := mul_le_mul_of_nonneg_right hnhi (mul_nonneg (by linarith : 0≤B-Real.log c) hP0)
  have hBc : 0≤B-Real.log c := by linarith
  have hgg := mul_le_mul_of_nonneg_left (by linarith : gap+1≤gap+P)
    (show 0≤21*q*(B-Real.log c)*P by positivity)
  have hqp : q≤q*P := by nlinarith
  have hqpp : q*P≤q*P*(gap+P) := by nlinarith
  nlinarith only [hlq,hln,hnP,hnn,hgg,hqp,hqpp]

theorem general_reverse_message_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT W : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (c B P : ℝ) (hc : 0 < c) (hc1 : c≤1) (hB : 0≤B) (hP : 1≤P)
    (hv : CaptureBound T UT c ((T.card:ℝ)*Real.exp (B*P)) W) :
    let n := reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))
    Real.log (1000*(Nat.card K)^2+1:ℝ)+Real.log (W.card+1:ℝ)+
      Real.log (Fintype.card (Fin (cardCutoff (Nat.card K) (T∩W).card W.card n)):ℝ)≤
      (1010+21*(B-Real.log c))*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hgap := projective_enclosure_gap σ hq hd S U hS hSU
  have hlen := (reverseLength_spec (Nat.card K) _ hq1 hgap.1).2.2
  have hhead := length_header_cost (Nat.card K) (Nat.card_pos (α:=K))
  have hproj := projective_header_le (K:=K) (V:=Dual K V) σ hσ hq (by simpa using hd)
  have hWhead : Real.log (W.card+1:ℝ)≤6*(Nat.card K:ℝ) := by
    exact (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (Finset.card_le_univ W) 1)).trans hproj
  have hcost := general_reverse_payload T UT W hT c B P hc hv (Nat.card K) hq1
    (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)))
  have hh := general_reverse_cost_scalar (Nat.card K) P _ c B _ hq1 hP hgap.1 hc hc1 hB
    (Nat.cast_nonneg _) hlen
  dsimp only
  linarith
end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniversalFreshCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

lemma universalFresh_headers (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q)
    (hm : universalFreshEncoded R S U C W hCW H n q M t=some m) :
    m.1=n ∧ m.2.1.val=C.card := by
  unfold universalFreshEncoded at hm
  split_ifs at hm with hW
  · obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    refine ⟨rfl,?_⟩
    unfold freshEncoded at hf
    obtain ⟨i,hi,he⟩ := Option.map_eq_some_iff.mp hf
    exact congrArg (fun z : FreshMessage W n q=>z.1.val) he.symm

lemma universalFresh_cost_exact (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q)
    (hm : universalFreshEncoded R S U C W hCW H n q M t=some m) :
    universalFreshCost W H q m=Real.log (H+1:ℝ)+Real.log (W.card+1:ℝ)+
      Real.log (Fintype.card (Fin (cardCutoff q C.card W.card n)):ℝ) := by
  have hh := universalFresh_headers R S U C W hCW H n q M t m hm
  unfold universalFreshCost
  rw [hh.2,hh.1]
end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GenericFreshCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open MeasureTheory
open scoped Classical BigOperators
variable {Ω α β : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α] [DecidableEq α] [Fintype β]

omit [DecidableEq α] in
lemma finiteImageLaw_map (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) (g : α→β) :
    map (finiteImageLaw μ f) g=finiteImageLaw μ (g∘f) := by
  apply Law.ext
  funext b
  have hh := finiteImageLaw_event μ f (Finset.univ.filter fun a=>g a=b)
  change (∑ a, if g a=b then finiteImageLaw μ f a else 0)=μ.real {ω | g (f ω)=b}
  simpa only [eventMass,Finset.sum_filter,Finset.mem_filter,Finset.mem_univ,true_and,
    Set.mem_ofPred_eq,Function.comp_apply] using hh

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_exact (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) :
    (baseFiniteEncoded S U P τ (baseMessageDecoded U P τ R L₀ t)).map
        (baseMessageDecoded U P τ R L₀ t)=baseOutcome S U P τ R L₀ t := by
  simp only [baseFiniteEncoded,baseTableEncoded,baseOutcome,Option.map_map]
  rfl

omit [Finite K] [FiniteDimensional K V] in
theorem baseFinite_law (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    map (baseTableLaw U P τ R L₀) (fun t=>(baseFiniteEncoded S U P τ t).map t)=
      baseCaptureLaw S U P τ R L₀ := by
  rw [baseTableLaw,publicTableLaw,finiteImageLaw_map]
  unfold baseCaptureLaw
  congr 1
  funext t
  exact baseFinite_exact S U P τ R L₀ t

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_header (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) : m.1.val=S.card := by
  obtain ⟨x,hx,he⟩ := Option.map_eq_some_iff.mp hm
  exact congrArg (fun z : BaseMessage U P τ=>z.1.val) he.symm
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ReversedBasePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [FiniteDimensional K V] in
lemma reversedBase_exact (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : ReversedBaseTape UT P τ H q) :
    (reversedBaseEncoded S U T UT P τ H n q MA MB t).map (reversedBaseDecoded U UT P τ H q t)=
      publicReverseResult S U T UT hT H n q MA MB ((baseFiniteEncoded T UT P τ t.1).map t.1) t.2 := by
  cases h : baseFiniteEncoded T UT P τ t.1 with
  | none => simp [reversedBaseEncoded,h,publicReverseResult]
  | some m =>
    simp only [reversedBaseEncoded,h,Option.bind_some,Option.map_some,publicReverseResult]
    split_ifs with hv
    · simp only [Option.map_map,reversedBaseDecoded,Function.comp_def]
    · rfl

omit [Finite K] [FiniteDimensional K V] in
theorem reversedBase_law (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ) :
    map (adaptiveLaw (baseTableLaw UT P τ R L₀) (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
      (fun t=>(reversedBaseEncoded S U T UT P τ H n q MA MB t).map (reversedBaseDecoded U UT P τ H q t))=
      optionCompose (baseCaptureLaw T UT P τ R L₀) (nextCapLaw S U T UT hT n q MA MB) := by
  simp only [reversedBase_exact S U T UT hT]
  rw [optionCompose_eq_second (baseCaptureLaw T UT P τ R L₀)
    (nextCapLaw S U T UT hT n q MA MB) (by rfl),←baseFinite_law T UT P τ R L₀]
  exact public_composition (baseTableLaw UT P τ R L₀) (universalFreshLaw (ℙ K (Dual K V)) H q)
    (fun t=>(baseFiniteEncoded T UT P τ t).map t)
    (publicReverseResult S U T UT hT H n q MA MB) (nextCapLaw S U T UT hT n q MA MB)
    (fun Y=>publicReverseResult_law S U T UT hT H n q MA MB Y)
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [FiniteDimensional K V] in
theorem twoPublic_output_law (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ) :
    map (twoPublicLaw U UT P τ R L₀ H q)
      (fun t=>(twoPublicEncoded S U T UT P τ H n q MA MB t).map (twoPublicDecoded U UT P τ H q t))=
      if S.card≤T.card then baseCaptureLaw S U P τ R L₀ else
        optionCompose (baseCaptureLaw T UT P τ R L₀) (nextCapLaw S U T UT hT n q MA MB) := by
  by_cases h : S.card≤T.card
  · simp only [twoPublicEncoded,ite_eq_left h,Option.map_map,twoPublicDecoded,Function.comp_def]
    rw [twoPublicLaw]
    exact (map_independent_left _ _ (fun t : BaseTable U P τ=>(baseFiniteEncoded S U P τ t).map t)).trans
      (baseFinite_law S U P τ R L₀)
  · simp only [twoPublicEncoded,ite_eq_right h,Option.map_map,twoPublicDecoded,Function.comp_def]
    rw [twoPublicLaw]
    exact (map_independent_right _ _ (fun t : ReversedBaseTape UT P τ H q=>
      (reversedBaseEncoded S U T UT P τ H n q MA MB t).map (reversedBaseDecoded U UT P τ H q t))).trans
        (reversedBase_law S U T UT hT P τ R L₀ H n q MA MB)

omit [Finite K] [FiniteDimensional K V] in
theorem twoPublic_oriented (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤H) :
    map (twoPublicLaw U UT P τ R L₀ H (Nat.card K))
      (fun t=>(twoPublicEncoded S U T UT P τ H ⟨_,Nat.lt_succ_of_le hn⟩ (Nat.card K)
        ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card) ((T.card:ℝ)*Real.exp (2*P)) t).map
          (twoPublicDecoded U UT P τ H (Nat.card K) t))=twoOrientedLaw S U T UT hT P τ R L₀ := by
  rw [twoPublic_output_law S U T UT hT]
  rfl
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BaseFiniteCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_sound (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) :
    ValidCap S U ((S.card:ℝ)*Real.exp (2*P)) (t m) := by
  obtain ⟨m',hm',he⟩ := Option.map_eq_some_iff.mp hm
  unfold baseTableEncoded at hm'
  have hs := chooseMessage_sound _ t m' hm'
  simpa only [he,ValidCap,Finset.inter_comm] using hs

omit [FiniteDimensional K V] in
theorem baseFinite_cost (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) :
    baseFiniteCost U P τ m≤110*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  unfold baseFiniteCost
  rw [baseFinite_header S U P τ t m hm]
  exact baseMessage_cost hdim S U hS hSU P τ hP hτ hτ1
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma reversedBase_prefixes (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : ReversedBaseTape UT P τ H q) (m : ReversedBaseMessage UT P τ H q t)
    (hm : reversedBaseEncoded S U T UT P τ H n q MA MB t=some m) :
    baseFiniteEncoded T UT P τ t.1=some m.1 ∧
      universalFreshEncoded Incident S U (T∩t.1 m.1) (t.1 m.1) Finset.inter_subset_right
        H n q MA t.2=some m.2 := by
  unfold reversedBaseEncoded at hm
  cases hb : baseFiniteEncoded T UT P τ t.1 with
  | none => simp [hb] at hm
  | some b =>
    rw [hb] at hm
    change (if _hv : ValidCap T UT MB (t.1 b) then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hf⟩

theorem reversedBase_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (hTU : T⊆UT)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) (MA : ℝ)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2)
    (t : ReversedBaseTape UT P τ (1000*(Nat.card K)^2) (Nat.card K))
    (m : ReversedBaseMessage UT P τ (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : reversedBaseEncoded S U T UT P τ (1000*(Nat.card K)^2) ⟨_,Nat.lt_succ_of_le hn⟩
      (Nat.card K) MA ((T.card:ℝ)*Real.exp (2*P)) t=some m) :
    reversedBaseCost UT P τ (1000*(Nat.card K)^2) (Nat.card K) t m≤
      1200*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  obtain ⟨hb,hf⟩ := reversedBase_prefixes S U T UT P τ _ _ _ _ _ t m hm
  have hbase := baseFinite_cost (K:=K) (V:=Dual K V) (by simpa using hdim)
    T UT hT hTU P τ hP hτ hτ1 t.1 m.1 hb
  have hvalid := baseFinite_sound T UT P τ t.1 m.1 hb
  have hc : CaptureBound T UT (9/10) ((T.card:ℝ)*Real.exp (2*P)) (t.1 m.1) := hvalid
  have hcost := general_reverse_message_cost σ hσ hq (by omega : finrank K V≤5)
    S U hS hSU T UT (t.1 m.1) hT (9/10) 2 P (by norm_num) (by norm_num) (by norm_num) hP hc
  have hh := universalFresh_cost_exact Incident S U (T∩t.1 m.1) (t.1 m.1)
    Finset.inter_subset_right _ _ _ MA t.2 m.2 hf
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<9/10)
  norm_num at hlog
  have hcst : 1010+21*((2:ℝ)-Real.log (9/10))≤1080 := by linarith
  have hgs := (projective_enclosure_gap σ hq (by omega : finrank K V≤5) S U hS hSU).1
  have hgt := (projective_enclosure_gap σ hq (by simpa using (show finrank K V≤5 by omega)) T UT hT hTU).1
  have hpq : 0≤(Nat.card K:ℝ)*P := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcst hpq) (show 0≤Real.log ((U.card:ℝ)/S.card)+P by linarith)
  unfold reversedBaseCost
  rw [hh]
  dsimp only at hcost
  nlinarith [mul_nonneg hpq hgs,mul_nonneg hpq hgt,mul_nonneg hpq (show 0≤P by linarith)]
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem twoPublic_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (hTU : T⊆UT)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) (MA : ℝ)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2)
    (t : TwoPublicTape U UT P τ (1000*(Nat.card K)^2) (Nat.card K))
    (m : TwoPublicMessage U UT P τ (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : twoPublicEncoded S U T UT P τ (1000*(Nat.card K)^2) ⟨_,Nat.lt_succ_of_le hn⟩
      (Nat.card K) MA ((T.card:ℝ)*Real.exp (2*P)) t=some m) :
    twoPublicCost U UT P τ (1000*(Nat.card K)^2) (Nat.card K) t m≤
      1300*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) := by
  let gS := Real.log ((U.card:ℝ)/S.card)
  let gT := Real.log ((UT.card:ℝ)/T.card)
  have hgs : 0≤gS := Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hS.card_pos)).mpr
    (by simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  have hgt : 0≤gT := Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr
    (by simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hqp : 1≤(Nat.card K:ℝ)*P := one_le_mul_of_one_le_of_one_le hq1 hP
  have hall : 1≤(Nat.card K:ℝ)*P*(gS+gT+P) := one_le_mul_of_one_le_of_one_le hqp (by linarith)
  have ht := mul_nonneg (show 0≤(Nat.card K:ℝ)*P by linarith) hgt
  have hl : Real.log 2≤1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2);norm_num at this;exact this
  unfold twoPublicEncoded at hm
  split_ifs at hm with hST
  · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    have hc := baseFinite_cost hdim S U hS hSU P τ hP hτ hτ1 t.1 b hb
    change Real.log 2+baseFiniteCost U P τ b≤1300*(Nat.card K:ℝ)*P*(gS+gT+P)
    change _≤110*(Nat.card K:ℝ)*P*(gS+P) at hc
    nlinarith
  · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    have hc := reversedBase_cost σ hσ hq hdim S U hS hSU T UT hT hTU P τ hP hτ hτ1 MA hn t.2 b hb
    change Real.log 2+reversedBaseCost UT P τ _ _ t.2 b≤1300*(Nat.card K:ℝ)*P*(gS+gT+P)
    change _≤1200*(Nat.card K:ℝ)*P*(gS+gT+P) at hc
    nlinarith
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_two_public_complete_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [∀x : ℙ K V,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K V),Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (_hT : T.Nonempty),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → T⊆UT →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      ∃ n : Fin (1000*(Nat.card K)^2+1),
        n.val=reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) ∧
        let P₀ := P η σ D R
        let H := 1000*(Nat.card K)^2
        let encode := twoPublicEncoded S U T UT P₀ τ H n (Nat.card K)
          ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card) ((T.card:ℝ)*Real.exp (2*P₀))
        let decode := twoPublicDecoded U UT P₀ τ H (Nat.card K)
        let p := map (twoPublicLaw U UT P₀ τ R L₀ H (Nat.card K))
          (fun t=>(encode t).map (decode t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→ValidCap S U ((S.card:ℝ)*Real.exp (2*P₀)) W) ∧
        (∀t m,encode t=some m → twoPublicCost U UT P₀ τ H (Nat.card K) t m≤
          1300*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_two_oriented hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb,eventually_ge_atTop (1:ℝ)] with σ hgood hpar hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ _ _ S U T UT hT hdim hq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  have hn := reverseLength_universal_bound σ hσ hq.symm (by omega : finrank K V≤5) S U hS hSU
  refine ⟨⟨_,Nat.lt_succ_of_le hn⟩,rfl,?_⟩
  dsimp only
  have heq := twoPublic_oriented S U T UT hT (P η σ D R) τ R L₀ (1000*(Nat.card K)^2) hn
  have hg := hgood D b τ R L₀ K V S U T UT hT hdim hq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  refine ⟨?_,?_,?_⟩
  · simpa only [heq] using hg.1
  · simpa only [heq] using hg.2
  · intro t m hm
    obtain ⟨hP,hbP,heP,hτsmall,hq3⟩ := hpar D R b τ hr hbhi hτ.le hτhi
    exact twoPublic_cost σ hσ hq.symm hdim S U hS hSU T UT hT hTU (P η σ D R) τ
      hP hτ.le (by linarith) _ hn t m hm
end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete_oai
