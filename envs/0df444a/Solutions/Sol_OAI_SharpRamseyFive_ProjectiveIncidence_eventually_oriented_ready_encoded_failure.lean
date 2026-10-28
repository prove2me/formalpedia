-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:32:42.190287+00:00
-- url     : https://prove2.me/submissions/905c5ca3-139c-4ec2-b9c8-062fe9e0f84a

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_producedPairLaw_spec
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_four_finite_predictor

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

section
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem adaptive_option_failure (p : Law (Option α))
    (next : Option α→Law (Option β)) (ε₁ ε₂ : ℝ) (hε₂ : 0≤ε₂)
    (hfirst : p none≤ε₁) (hnext : ∀a,0 < p (some a) → next (some a) none≤ε₂) :
    eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none) ≤ ε₁+ε₂ := by
  have hinner (a : Option α) (ha : 0 < p a) :
      (∑b : Option β,if a=none ∨ b=none then next a b else 0) ≤
        (if a=none then 1 else 0)+ε₂ := by
    cases a with
    | none => simpa only [true_or,ite_true] using
        (show (∑b,next none b)≤1+ε₂ by rw [(next none).sum_one];linarith)
    | some a => simpa using hnext a ha
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a (_ : a∈Finset.univ)=>
    show p a*(∑b : Option β,if a=none ∨ b=none then next a b else 0) ≤
      p a*((if a=none then 1 else 0)+ε₂) from by
      by_cases hz : p a=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hinner a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz))) (p.nonneg a))
  have hl : eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none)=
      ∑a : Option α,p a*(∑b : Option β,if a=none ∨ b=none then next a b else 0) := by
    simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw,
      Finset.mul_sum,mul_ite,mul_zero]
  rw [hl]
  calc
    _ ≤ ∑a : Option α,p a*((if a=none then 1 else 0)+ε₂) := hsum
    _ = p none+ε₂ := by
      simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
      rw [←Finset.sum_mul,p.sum_one,one_mul]
      simp
    _ ≤ ε₁+ε₂ := by linarith

end

open MeasureTheory
open scoped Classical BigOperators

end SharpRamseyFive.FiniteEntropy

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OptionComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

lemma optionCompose_failure (p : Law (Option α)) (next : Option α→Law (Option β))
    (ε₁ ε₂ : ℝ) (hε₂ : 0≤ε₂) (hp : p none≤ε₁)
    (hn : ∀a,0<p (some a)→next (some a) none≤ε₂) :
    optionCompose p next none≤ε₁+ε₂ := by
  have he : optionCompose p next none=eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none) := by
    unfold optionCompose map eventMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ab _
    rcases ab with ⟨a,b⟩
    cases a <;> cases b <;> simp
  rw [he]
  exact adaptive_option_failure p next ε₁ ε₂ hε₂ hp hn

lemma optionCompose_positive (p : Law (Option α)) (next : Option α→Law (Option β))
    (b : β) (hb : 0<optionCompose p next (some b)) :
    ∃a,0<p (some a) ∧ 0<next (some a) (some b) := by
  obtain ⟨⟨a,b'⟩,hab,he⟩ := map_positive (adaptiveLaw p next) _ _ hb
  cases a with
  | none => simp at he
  | some a =>
    have he' : b'=some b := by simpa using he
    subst b'
    change 0<p (some a)*next (some a) (some b) at hab
    rcases mul_pos_iff.mp hab with h | h
    · exact ⟨a,h⟩
    · exact False.elim ((not_lt_of_ge (p.nonneg _)) h.1)

end SharpRamseyFive.FiniteEntropy

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

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseSmallLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma incidences_bidual (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    incidences T (S.map bidualPoint.toEmbedding)=incidences S T := by
  have hh : (incidences T (S.map bidualPoint.toEmbedding):ℝ)=(incidences S T:ℝ) := by
    rw [incidences_eq_sum,incidences_eq_sum,Finset.sum_comm]
    simp only [Finset.sum_map,Equiv.toEmbedding_apply,incidenceEntry,incident_bidual]
  exact_mod_cast hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ReverseAfterCapture
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

lemma source_product_to_cap (Q s t b C : ℝ) (hs : 0 ≤ s) (ht : 0<t) (hC : 0≤C)
    (hp : Q*Real.exp (-b)≤ s*t) : C*Q/t≤ s*(C*Real.exp b) := by
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos b).le
  have he : Real.exp (-b)*Real.exp b=1 := by rw [←Real.exp_add];simp
  have hq : Q≤ s*t*Real.exp b := by simpa only [mul_assoc,he,mul_one] using hh
  apply (div_le_iff₀ ht).mpr
  have hmul := mul_le_mul hq (le_refl C) hC
    (mul_nonneg (mul_nonneg hs ht.le) (Real.exp_pos b).le)
  nlinarith only [hmul]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RecursivePlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma map_option_none (p : Law (Option α)) (f : α→β) : map p (Option.map f) none=p none := by
  simp only [map,Fintype.sum_option,Option.map_none,ite_true,Option.map_some,
    Option.some_ne_none,ite_false,Finset.sum_const_zero,add_zero]
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoAmbientCaps
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


lemma incidence_density_le {d : ℕ} (hd : 1≤d) :
    (Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d≤1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  rw [one_mul,Q_recurrence hd]
  push_cast
  nlinarith

lemma reciprocal_rectangle_flags (hdim : finrank K V=5)
    (U : Finset (ℙ K V)) (W : Finset (ℙ K (Dual K V)))
    (C b : ℝ) (hC : 1≤C) (hb : 0≤b)
    (hprod : (U.card:ℝ)*W.card≤C*(Nat.card K:ℝ)^5*Real.exp b) :
    (incidences U W:ℝ)≤2*C*(Nat.card K:ℝ)^4*Real.exp b := by
  let q : ℝ := Nat.card K
  have hq : 0<q := by dsimp [q];exact_mod_cast Nat.card_pos (α:=K)
  have hmix := incidence_mixing (d:=4) hdim (by norm_num) U W
  norm_num only [Nat.reduceSub] at hmix
  have hden := incidence_density_le (K:=K) (d:=4) (by norm_num)
  norm_num only [Nat.reduceSub] at hden
  have hmean := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden
    (show (0:ℝ)≤U.card by positivity)) (show (0:ℝ)≤W.card by positivity)
  have hmain : (1/q)*(U.card:ℝ)*W.card≤C*q^4*Real.exp b := by
    rw [show (1/q)*(U.card:ℝ)*W.card=((U.card:ℝ)*W.card)/q by ring]
    apply (div_le_iff₀ hq).mpr
    simpa only [show C*q^4*Real.exp b*q=C*q^5*Real.exp b by ring] using hprod
  have hcb : 1≤C*Real.exp b := by
    have he : 1≤Real.exp b := Real.one_le_exp_iff.mpr hb
    nlinarith
  have hcb2 : C*Real.exp b≤(C*Real.exp b)^2 := by nlinarith
  have hbase := mul_le_mul_of_nonneg_left hprod (pow_nonneg hq.le 3)
  have hupper := mul_le_mul_of_nonneg_left hcb2 (pow_nonneg hq.le 8)
  have hsquare : q^3*(U.card:ℝ)*W.card≤(C*q^4*Real.exp b)^2 := by
    dsimp [q] at hbase
    nlinarith only [hbase,hupper]
  have hsqrt : Real.sqrt (q^3*(U.card:ℝ)*W.card)≤C*q^4*Real.exp b :=
    (Real.sqrt_le_left (by positivity)).mpr hsquare
  have hm := le_abs_self ((incidences U W:ℝ)-
    (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card)
  change |(incidences U W:ℝ)-
    (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card|≤
      Real.sqrt (q^3*(U.card:ℝ)*W.card) at hmix
  change (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card≤(1/q)*U.card*W.card at hmean
  linarith

lemma reciprocal_cap_product (Q a b x y C D loss : ℝ)
    (hQ : 0<Q) (ha : 0<a) (hb : 0<b) (_hx : 0≤x) (hy : 0≤y)
    (hC : 0≤C) (hD : 0≤D) (hp : Q*Real.exp (-loss)≤a*b)
    (hxc : x≤C*Q/b) (hyc : y≤D*Q/a) :
    x*y≤C*D*Q*Real.exp loss := by
  have hx' := (le_div_iff₀ hb).mp hxc
  have hy' := (le_div_iff₀ ha).mp hyc
  have hxy := mul_le_mul hx' hy' (mul_nonneg hy ha.le) (mul_nonneg hC hQ.le)
  have hp' : Q≤a*b*Real.exp loss := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos loss).le
    rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hp' (mul_nonneg hC hD)
  have hh' := mul_le_mul_of_nonneg_right hh hQ.le
  have hab : 0<a*b := mul_pos ha hb
  apply (mul_le_mul_iff_left₀ hab).mp
  nlinarith only [hxy,hh']

theorem validated_caps_flags (hdim : finrank K V=5)
    (A UA Z : Finset (ℙ K V)) (B UB Y : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (c b : ℝ) (hc : 0 < c) (hb : 0≤b)
    (hprod : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card)
    (hZ : ValidCap A UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card) Z)
    (hY : ValidCap B UB ((320/c+320)*(Nat.card K:ℝ)^5/A.card) Y) :
    (incidences Z Y:ℝ)≤
      2*((320/((9:ℝ)/10)+320)*(320/c+320))*(Nat.card K:ℝ)^4*Real.exp b := by
  have hconst : 1≤(320/((9:ℝ)/10)+320)*(320/c+320) := by
    have : 0≤320/c := by positivity
    nlinarith
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  apply reciprocal_rectangle_flags hdim Z Y _ b hconst hb
  exact reciprocal_cap_product ((Nat.card K:ℝ)^5) A.card B.card Z.card Y.card
      (320/((9:ℝ)/10)+320) (320/c+320) b (pow_pos hq _)
      (by exact_mod_cast hA.card_pos) (by exact_mod_cast hB.card_pos)
      (by positivity) (by positivity) (by norm_num) (by positivity) hprod hZ.2.1 hY.2.1

end SharpRamseyFive.ProjectiveIncidence

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientPairPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma public_joint_composition (p : Law α) (tape : Law β) (firstOut : α→γ)
    (out : γ→β→δ) (next : γ→Law δ)
    (hm : ∀c,map tape (out c)=next c) :
    map (adaptiveLaw p (fun _=>tape)) (fun z=>(firstOut z.1,out (firstOut z.1) z.2))=
      adaptiveLaw (map p firstOut) next := by
  apply Law.ext
  funext cd
  rcases cd with ⟨c,d⟩
  rw [adaptive_output_mass (out:=fun a b=>(firstOut a,out (firstOut a) b))]
  change _=(∑a,if firstOut a=c then p a else 0)*next c d
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : firstOut a=c
  · simp only [hc,ite_true]
    have hs : map tape (fun b=>(c,out c b)) (c,d)=map tape (out c) d := by
      simp only [map,Prod.mk.injEq,true_and]
    rw [hs,hm]
  · simp only [map,Prod.mk.injEq,hc,false_and,ite_false,Finset.sum_const_zero,mul_zero,zero_mul]
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma publicAmbientSecond_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) :
    map (universalFreshLaw (ℙ K (Dual K V)) H q) (publicAmbientSecond A UA B UB H n q MA MB Y)=
      nextAmbientCapLaw A UA B UB hB n q MA MB Y := by
  cases Y with
  | none => exact map_const _ none
  | some W =>
    change map (universalFreshLaw (ℙ K (Dual K V)) H q)
      (fun t=>if _hW : ValidCap B UB MB (UB∩W) then
        (universalFreshEncoded Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right H n q MA t).map
          (universalFreshDecoded Incident (UB∩W) H q t) else none)=_
    dsimp only [nextAmbientCapLaw]
    split_ifs with hv
    · exact universalFreshEncoded_law Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right
        ((hv.source_nonempty hB).mono Finset.inter_subset_right) H n q MA
    · exact map_const _ none

omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_exact (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q) :
    (ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t)=
      let Y := (universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1).map
        (universalFreshDecoded (fun b a=>Incident a b) W H q t.1)
      pairOptions (Y,publicAmbientSecond A UA B UB H nA q MA MB Y t.2) := by
  cases hf : universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1 with
  | none => simp [ambientPairEncoded,hf,pairOptions]
  | some f =>
    simp only [ambientPairEncoded,hf,Option.bind_some,Option.map_some,publicAmbientSecond,pairOptions]
    split_ifs <;> simp only [Option.map_none,Option.map_map,ambientPairDecoded,Function.comp_def]

omit [Finite K] [FiniteDimensional K V] in
theorem ambientPair_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (W : Finset (ℙ K V)) (hW : W.Nonempty)
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) :
    map (ambientPairTapeLaw (K:=K) (V:=V) H q)
      (fun t=>(ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t))=
    map (adaptiveLaw (ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB)
      (nextAmbientCapLaw A UA B UB hB nA q MA MB)) pairOptions := by
  simp only [ambientPair_exact]
  have hh := public_joint_composition (universalFreshLaw (ℙ K V) H q)
    (universalFreshLaw (ℙ K (Dual K V)) H q)
    (fun t=>(universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t).map
      (universalFreshDecoded (fun b a=>Incident a b) W H q t))
    (publicAmbientSecond A UA B UB H nA q MA MB)
    (nextAmbientCapLaw A UA B UB hB nA q MA MB)
    (publicAmbientSecond_law A UA B UB hB H nA q MA MB)
  rw [universalFreshEncoded_law _ _ _ _ _ _ hW] at hh
  have hm := congrArg (fun p=>map p pairOptions) hh
  simpa only [map_comp,Function.comp_def,ambientPairTapeLaw] using hm

omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_prefixes (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q)
    (m : AmbientPairMessage UB W H q t)
    (hm : ambientPairEncoded A UA B UB W H nA nB q MA MB t=some m) :
    universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1=some m.1 ∧
    let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1
    ValidCap B UB MB (UB∩Y) ∧
    universalFreshEncoded Incident A UA (B∩(UB∩Y)) (UB∩Y) Finset.inter_subset_right H nA q MA t.2=some m.2 := by
  unfold ambientPairEncoded at hm
  cases hf : universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hv : ValidCap B UB MB _ then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hv,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GenericFreshCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] in
theorem universalFresh_cost_bound (R : A→B→Prop) (S U : Finset A)
    (X UX W : Finset B) (hX : X.Nonempty) (q : ℕ) (hq : 1≤q)
    (P gap c B₀ : ℝ) (hP : 1≤P) (hg : 0≤gap) (hc : 0 < c) (hc1 : c≤1) (hB : 0≤B₀)
    (hv : CaptureBound X UX c ((X.card:ℝ)*Real.exp (B₀*P)) W)
    (hhead : Real.log (W.card+1:ℝ)≤6*(q:ℝ))
    (n : Fin (1000*q^2+1)) (hn : (n:ℝ)≤21*(q:ℝ)*(gap+1)) (M : ℝ)
    (t : UniversalFresh B (1000*q^2) (q:ℝ))
    (m : UniversalFreshMessage W (1000*q^2) (q:ℝ))
    (hm : universalFreshEncoded R S U (X∩W) W Finset.inter_subset_right (1000*q^2) n (q:ℝ) M t=some m) :
    universalFreshCost W (1000*q^2) (q:ℝ) m≤
      (1010+21*(B₀-Real.log c))*(q:ℝ)*P*(gap+P) := by
  have hC := hv.nonempty hX hc
  have hW := hC.mono Finset.inter_subset_right
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hu := fresh_payload_cost (q:ℝ) hq' (X∩W) W hC hW Finset.inter_subset_right n
  have hr := capture_log_ratio X.card c W.card (X∩W).card (B₀*P)
    (by exact_mod_cast hX.card_pos) hc (by exact_mod_cast hW.card_pos)
    (by exact_mod_cast hC.card_pos) hv.2.2 hv.2.1
  have hrn := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤(n:ℕ) by positivity)
  have hs := general_reverse_cost_scalar (q:ℝ) P gap c B₀ (n:ℕ) hq' hP hg hc hc1 hB
    (Nat.cast_nonneg _) hn
  have hh := length_header_cost q hq
  have he := universalFresh_cost_exact R S U (X∩W) W Finset.inter_subset_right (1000*q^2) n (q:ℝ) M t m hm
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at he
  rw [he]
  linarith
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem ambientPair_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hAU : A⊆UA) (hB : B.Nonempty) (hBU : B⊆UB)
    (W : Finset (ℙ K V)) (c P b : ℝ) (hc : 0 < c) (hc1 : c≤1) (hP : 1≤P) (hb : b≤P)
    (hprod : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card)
    (hcoef : 320/c+320≤Real.exp P)
    (hcap : CaptureBound A UA c ((A.card:ℝ)*Real.exp (10*P)) W)
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))≤1000*(Nat.card K)^2)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))≤1000*(Nat.card K)^2)
    (t : AmbientPairTape K V (1000*(Nat.card K)^2) (Nat.card K))
    (m : AmbientPairMessage UB W (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : ambientPairEncoded A UA B UB W _ ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
      (Nat.card K) ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) t=some m) :
    ambientPairCost UB W (1000*(Nat.card K)^2) (Nat.card K) t m≤
      (2020+21*(12-Real.log c-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*P*
        (Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  let : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  have hqnat : 1≤Nat.card K := Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast hqnat
  have hga := projective_enclosure_gap σ hq hd A UA hA hAU
  have hgb := projective_enclosure_gap σ hq (show finrank K (Dual K V)≤5 by simpa using hd) B UB hB hBU
  have hnAl := (reverseLength_spec (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)) hq1 hga.1).2.2
  have hnBl := (reverseLength_spec (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)) hq1 hgb.1).2.2
  obtain ⟨hfirst,hvalid,hsecond⟩ := ambientPair_prefixes A UA B UB W _ _ _ _ _ _ t m hm
  let Y := universalFreshDecoded (fun b a=>Incident a b) W (1000*(Nat.card K)^2) (Nat.card K) t.1 m.1
  have hWhd : Real.log (W.card+1:ℝ)≤6*(Nat.card K:ℝ) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (Finset.card_le_univ W) 1)).trans
      (projective_header_le (K:=K) (V:=V) σ hσ hq hd)
  have hfirstCost := universalFresh_cost_bound (fun b a=>Incident a b) B UB A UA W hA (Nat.card K) hqnat
    P (Real.log ((UB.card:ℝ)/B.card)) c 10 hP hgb.1 hc hc1 (by norm_num) hcap hWhd
    ⟨_,Nat.lt_succ_of_le hnB⟩ hnBl _ t.1 m.1 hfirst
  have hYhd : Real.log ((UB∩Y).card+1:ℝ)≤6*(Nat.card K:ℝ) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (Finset.card_le_univ (UB∩Y)) 1)).trans
      (projective_header_le (K:=K) (V:=Dual K V) σ hσ hq (by simpa using hd))
  have hcapB : (320/c+320)*(Nat.card K:ℝ)^5/A.card≤(B.card:ℝ)*Real.exp (2*P) := by
    have hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(B.card:ℝ)*A.card := by simpa only [mul_comm] using hprod
    have ho := source_product_to_cap ((Nat.card K:ℝ)^5) B.card A.card b (320/c+320)
      (Nat.cast_nonneg _) (by exact_mod_cast hA.card_pos) (by positivity) hp
    have he : (320/c+320)*Real.exp b≤Real.exp (2*P) := by
      calc
        _≤Real.exp P*Real.exp P := mul_le_mul hcoef (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (Real.exp_pos _).le
        _=Real.exp (2*P) := by rw [←Real.exp_add];congr 1;ring
    exact ho.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))
  have hvcap : CaptureBound B UB ((9:ℝ)/10) ((B.card:ℝ)*Real.exp (2*P)) (UB∩Y) :=
    ⟨hvalid.1,hvalid.2.1.trans hcapB,hvalid.2.2⟩
  have hsecondCost := universalFresh_cost_bound Incident A UA B UB (UB∩Y) hB (Nat.card K) hqnat
    P (Real.log ((UA.card:ℝ)/A.card)) ((9:ℝ)/10) 2 hP hga.1 (by norm_num) (by norm_num) (by norm_num) hvcap hYhd
    ⟨_,Nat.lt_succ_of_le hnA⟩ hnAl _ t.2 m.2 hsecond
  have hlc : Real.log c≤0 := Real.log_nonpos hc.le hc1
  have hl9 : Real.log ((9:ℝ)/10)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hP0 : 0≤P := le_trans (by norm_num) hP
  have hcA : 0≤1010+21*(2-Real.log ((9:ℝ)/10)) := by linarith only [hl9]
  have hcB : 0≤1010+21*(10-Real.log c) := by linarith only [hlc]
  have hCa : 0≤(1010+21*(2-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*P := by positivity
  have hCb : 0≤(1010+21*(10-Real.log c))*(Nat.card K:ℝ)*P := by positivity
  have h₁ := mul_le_mul_of_nonneg_left (show Real.log ((UB.card:ℝ)/B.card)+P≤
    Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P by linarith only [hga.1]) hCb
  have h₂ := mul_le_mul_of_nonneg_left (show Real.log ((UA.card:ℝ)/A.card)+P≤
    Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P by linarith only [hgb.1]) hCa
  unfold ambientPairCost
  dsimp only [Y] at hfirstCost hsecondCost
  nlinarith only [hfirstCost,hsecondCost,h₁,h₂]
end SharpRamseyFive.ProjectiveIncidence

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FourFinitePredictor
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_exact (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q) :
    (finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t).map (finiteNodeDecoded pred UB H q t)=
      finiteNodeNextOut A UA B UB H nA nB q MA MB c M ((pred.encoded A B t.1).map (pred.decoded t.1)) t.2 := by
  cases hm : pred.encoded A B t.1 with
  | none => simp [finiteNodeEncoded,hm,finiteNodeNextOut]
  | some m =>
    simp only [finiteNodeEncoded,hm,Option.bind_some,Option.map_some,finiteNodeNextOut]
    split_ifs <;> simp only [Option.map_none,Option.map_map,Function.comp_def,finiteNodeDecoded]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_law (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) :
    finiteNodeOutput pred A UA B UB H nA nB q MA MB c M=
      optionCompose (pred.output A B) (finiteNodeNextLaw A UA B UB H nA nB q MA MB c M) := by
  rw [optionCompose_eq_second _ _ (by exact map_const _ none)]
  unfold finiteNodeOutput
  simp only [finiteNode_exact]
  exact public_composition pred.tapeLaw (ambientPairTapeLaw H q)
    (fun t=>(pred.encoded A B t).map (pred.decoded t))
    (finiteNodeNextOut A UA B UB H nA nB q MA MB c M)
    (finiteNodeNextLaw A UA B UB H nA nB q MA MB c M) (fun _=>rfl)

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_prefixes (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t)
    (hm : finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t=some m) :
    pred.encoded A B t.1=some m.1 ∧ CaptureBound A UA c M (pred.decoded t.1 m.1) ∧
    ambientPairEncoded A UA B UB (pred.decoded t.1 m.1) H nA nB q MA MB t.2=some m.2 := by
  unfold finiteNodeEncoded at hm
  cases hf : pred.encoded A B t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hc : CaptureBound A UA c M _ then _ else none)=some m at hm
    split_ifs at hm with hc
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hc,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteNodeCost
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNodeNextLaw_produced (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (c M : ℝ) (hc : 0 < c)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (H : ℕ)
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))<H+1)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))<H+1) :
    finiteNodeNextLaw A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M (some W)=
        producedPairLaw A UA B UB hB c (some W) := by
  have hW : W.Nonempty := (hcap.nonempty hA hc).mono Finset.inter_subset_right
  unfold finiteNodeNextLaw finiteNodeNextOut
  simp only [Option.bind_some,dite_eq_left hcap]
  rw [ambientPair_law _ _ _ _ hB _ hW]
  simp only [producedPairLaw,dite_eq_left hW]

theorem finiteNode_cost (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hAU : A⊆UA) (hB : B.Nonempty) (hBU : B⊆UB)
    (c P b C : ℝ) (hc : 0 < c) (hc1 : c≤1) (hP : 1≤P) (hb : b≤P)
    (hprod : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card)
    (hcoef : 320/c+320≤Real.exp P)
    (hcost : ∀t m,pred.encoded A B t=some m → pred.cost t m≤
      C*(Nat.card K:ℝ)*P*(Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P))
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))≤1000*(Nat.card K)^2)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))≤1000*(Nat.card K)^2)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : finiteNodeEncoded pred A UA B UB _ ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
      (Nat.card K) ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c ((A.card:ℝ)*Real.exp (10*P)) t=some m) :
    finiteNodeCost pred UB (1000*(Nat.card K)^2) (Nat.card K) t m≤
      (C+2020+21*(12-Real.log c-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*P*
        (Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P) := by
  obtain ⟨hp,hcap,hr⟩ := finiteNode_prefixes pred A UA B UB _ _ _ _ _ _ _ _ t m hm
  have h₁ := hcost t.1 m.1 hp
  have h₂ := ambientPair_cost σ hσ hq hd A UA B UB hA hAU hB hBU _ c P b hc hc1 hP hb hprod hcoef
    hcap hnA hnB t.2 m.2 hr
  unfold finiteNodeCost
  nlinarith only [h₁,h₂]
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteNode
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Metadata Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_finite_node {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=5) (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → A⊆UA → B⊆UB → A.card≤B.card →
      (Nat.card K:ℝ)*(incidences A B:ℝ)≤τ*A.card*B.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card →
      ∃(hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))≤1000*(Nat.card K)^2)
       (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))≤1000*(Nat.card K)^2),
        let pred := fourFinitePredictor hd σ UA UB (P η σ D R) τ R L₀
        let H := 1000*(Nat.card K)^2
        let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
        let MB := (320/((9:ℝ)/100000)+320)*(Nat.card K:ℝ)^5/A.card
        let p := finiteNodeOutput pred A UA B UB H ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
          (Nat.card K) MA MB (9/100000) ((A.card:ℝ)*Real.exp (10*P η σ D R))
        p none≤5*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀Y Z,0<p (some (Y,Z))→
          ValidCap B UB MB (UB∩Y) ∧ ValidCap A UA MA (UA∩Z) ∧
          (incidences (UA∩Z) (UB∩Y):ℝ)≤
            2*((320/((9:ℝ)/10)+320)*(320/((9:ℝ)/100000)+320))*(Nat.card K:ℝ)^4*Real.exp b) ∧
        (∀t m,finiteNodeEncoded pred A UA B UB H ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
          (Nat.card K) MA MB (9/100000) ((A.card:ℝ)*Real.exp (10*P η σ D R)) t=some m →
          finiteNodeCost pred UB H (Nat.card K) t m≤
            (32120+21*(12-Real.log ((9:ℝ)/100000)-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*(P η σ D R)*
              (Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+(P η σ D R))) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-800*beta η)<(9:ℝ)/100000000 := by
    have hp : 0<800*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const (by norm_num : (0:ℝ)<9/100000000)
  have hc := eventually_power_absorption hη hη' (320/((9:ℝ)/100000)+320) 0 1
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_four_finite_predictor hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb,hc,ht,eventually_ge_atTop (10:ℝ)] with σ hh hv hc ht hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ hd A UA B UB hcard hσq hr hL hb hbhi hτ hτhi hAU hBU hAB hdens hprod
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  let : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hq3 : 3≤Nat.card K := by
    have he : (3:ℝ)≤Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
    rw [←hq] at he
    exact_mod_cast he
  have hab : 0<(A.card:ℝ)*B.card := lt_of_lt_of_le (by rw [hq];positivity) hprod
  have hA : A.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hab (Nat.cast_nonneg _)))
  have hB : B.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_right hab (Nat.cast_nonneg _)))
  have hσ1 : 1≤σ := by linarith only [hσ]
  have hnA := reverseLength_universal_bound σ hσ1 hq.symm (by omega : finrank K V≤5) A UA hA hAU
  have hnB := reverseLength_universal_bound σ hσ1 hq.symm (show finrank K (Dual K V)≤5 by simpa using hd.le) B UB hB hBU
  refine ⟨hnA,hnB,?_⟩
  let pred := fourFinitePredictor hd σ UA UB (P η σ D R) τ R L₀
  let H := 1000*(Nat.card K)^2
  let nA : Fin (H+1) := ⟨_,Nat.lt_succ_of_le hnA⟩
  let nB : Fin (H+1) := ⟨_,Nat.lt_succ_of_le hnB⟩
  let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
  let MB := (320/((9:ℝ)/100000)+320)*(Nat.card K:ℝ)^5/A.card
  let next := finiteNodeNextLaw A UA B UB H nA nB (Nat.card K) MA MB (9/100000)
    ((A.card:ℝ)*Real.exp (10*P η σ D R))
  obtain ⟨hf,hgood,hcost⟩ := hh D b τ R L₀ q K V hd A UA B UB hcard hσq hr hL hb hbhi hτ hτhi hAU hBU hAB hdens hprod
  have hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/100000*A.card*B.card := by
    have hτc : 1000*τ≤(9:ℝ)/100000 := by linarith only [hτhi,ht]
    have h1 := mul_le_mul_of_nonneg_left hdens (by norm_num : (0:ℝ)≤1000)
    have h2 := mul_le_mul_of_nonneg_right hτc (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    nlinarith only [h1,h2]
  have hnext (W) (hW : 0<pred.output A B (some W)) : next (some W)=producedPairLaw A UA B UB hB (9/100000) (some W) :=
    finiteNodeNextLaw_produced A UA B UB hA hB (9/100000) _ (by norm_num) W (hgood W hW) H _ _
  have hs (W) (hW : 0<pred.output A B (some W)) :=
    producedPairLaw_spec hd hq3 A UA B UB hA hB hAU hBU (9/100000) _ (by norm_num) (by norm_num) W (hgood W hW) hsparse
  change finiteNodeOutput pred A UA B UB H nA nB (Nat.card K) MA MB _ _ none≤_ ∧ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · rw [finiteNode_law]
    have hfresh : ∀W,0<pred.output A B (some W)→next (some W) none≤2*Real.exp (-(Nat.card K:ℝ)) := by
      intro W hW
      rw [hnext W hW]
      exact (hs W hW).1
    have hh := optionCompose_failure (pred.output A B) next (3*Real.exp (-(Nat.card K:ℝ)))
      (2*Real.exp (-(Nat.card K:ℝ))) (by positivity) hf hfresh
    simpa only [show (3:ℝ)*Real.exp (-(Nat.card K:ℝ))+2*Real.exp (-(Nat.card K:ℝ))=5*Real.exp (-(Nat.card K:ℝ)) by ring] using hh
  · intro Y Z hYZ
    rw [finiteNode_law] at hYZ
    obtain ⟨W,hW,hout⟩ := optionCompose_positive (pred.output A B) next (Y,Z) hYZ
    rw [hnext W hW] at hout
    obtain ⟨hy,hz⟩ := (hs W hW).2 Y Z hout
    exact ⟨hy,hz,validated_caps_flags hd A UA (UA∩Z) B UB (UB∩Y) hA hB (9/100000) b (by norm_num) hb hprod hz hy⟩
  · intro t m hm
    have hτ200 := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ1 (by have := beta_pos hη;linarith : -800*beta η≤-200*beta η))
    obtain ⟨hP,hbP,_⟩ := hv D R b τ hr hbhi hτ.le hτ200
    have hcoef : 320/((9:ℝ)/100000)+320≤Real.exp (P η σ D R) := by
      simpa only [Real.rpow_zero,mul_one,one_mul] using hc D R hr
    have hh := finiteNode_cost pred σ hσ1 hq.symm hd.le A UA B UB hA hAU hB hBU
      (9/100000) (P η σ D R) b 30100 (by norm_num) (by norm_num) hP hbP hprod hcoef hcost hnA hnB t m hm
    norm_num only [show (30100:ℝ)+2020=32120 by norm_num] at hh
    exact hh
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma original_ready_sparse (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (c δ τ : ℝ) (hc : 0 ≤ c) (hδ : 0≤δ) (hτ : 1000*τ ≤ c*δ^2)
    (hr : OriginalNodeReady A₀ UA B₀ UB δ τ) :
    1000*(Nat.card K:ℝ)*incidences (A₀∩UA) (B₀∩UB) ≤ c*(A₀∩UA).card*(B₀∩UB).card := by
  have hi : incidences (A₀∩UA) (B₀∩UB)≤ incidences A₀ B₀ := by
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    exact Finset.product_subset_product Finset.inter_subset_left Finset.inter_subset_left
  have hp := mul_le_mul hr.1 hr.2.1 (mul_nonneg hδ (Nat.cast_nonneg B₀.card))
    (Nat.cast_nonneg (A₀∩UA).card)
  have hp' : δ^2*(A₀.card:ℝ)*B₀.card≤(A₀∩UA).card*(B₀∩UB).card := by nlinarith only [hp]
  have h₁ := mul_le_mul_of_nonneg_left (show (incidences (A₀∩UA) (B₀∩UB):ℝ)≤ incidences A₀ B₀ by exact_mod_cast hi)
    (show (0:ℝ)≤1000*(Nat.card K:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hr.2.2 (by norm_num : (0:ℝ)≤1000)
  have h₃ := mul_le_mul_of_nonneg_right hτ (show (0:ℝ)≤(A₀.card:ℝ)*B₀.card by positivity)
  have h₄ := mul_le_mul_of_nonneg_left hp' hc
  nlinarith only [h₁,h₂,h₃,h₄]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeEncoder
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma guardedNode_encoder_law (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ) :
    map (finiteNodeTapeLaw pred (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t).map
        (finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t))=
      guardedNodeLaw pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ := by
  unfold guardedNodeEncoded guardedNodeLaw
  split_ifs
  · rfl
  · simp only [Option.map_none]
    exact map_const _ none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeSent
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

lemma orientedGuardedNode_law
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ) :
    map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))=
    if (A₀∩UA).card≤(B₀∩UB).card then
      guardedNodeLaw f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ
    else map
      (guardedNodeLaw r σ hσ hq (by simpa using hd) B₀ UB
        (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
        hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ)
      (Option.map reverseNodePair) := by
  unfold orientedGuardedNodeEncoded
  split_ifs with h
  · simp only [Option.map_map,Function.comp_def,orientedNodeDecoded]
    exact (map_independent_left
      (finiteNodeTapeLaw f (1000*(Nat.card K)^2) (Nat.card K))
      (finiteNodeTapeLaw r (1000*(Nat.card K)^2) (Nat.card K)) _).trans
      (guardedNode_encoder_law f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
        (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ)
  · simp only [Option.map_map,Function.comp_def,orientedNodeDecoded]
    have hh := congrArg (fun p=>map p (Option.map reverseNodePair))
      (guardedNode_encoder_law r σ hσ hq (by simpa using hd) B₀ UB
        (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
        hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ)
    rw [map_comp] at hh
    simp only [Option.map_map,Function.comp_def] at hh
    exact (map_independent_right
      (finiteNodeTapeLaw f (1000*(Nat.card K)^2) (Nat.card K))
      (finiteNodeTapeLaw r (1000*(Nat.card K)^2) (Nat.card K)) _).trans hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ReadyRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_trimmed_product (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (τ b : ℝ) (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card) :
    (Nat.card K:ℝ)^5*Real.exp (-(b+1))≤((A₀∩UA).card:ℝ)*(B₀∩UB).card := by
  have hmul := mul_le_mul hr.1 hr.2.1
    (show (0:ℝ)≤(9/10:ℝ)*B₀.card by positivity) (Nat.cast_nonneg (A₀∩UA).card)
  have he : Real.exp (-1)≤(81:ℝ)/100 := by
    rw [Real.exp_neg]
    rw [←one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := Real.add_one_le_exp (1:ℝ)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left he
    (show (0:ℝ)≤(Nat.card K:ℝ)^5*Real.exp (-b) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤81/100)
  rw [neg_add,Real.exp_add]
  nlinarith only [hmul,h1,h2]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_trimmed_density (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (τ ε : ℝ) (hε : 0≤ε) (hτε : τ≤ε*(9/10:ℝ)^2)
    (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ) :
    (Nat.card K:ℝ)*incidences (A₀∩UA) (B₀∩UB)≤ε*(A₀∩UA).card*(B₀∩UB).card := by
  have hh := original_ready_sparse A₀ UA B₀ UB (1000*ε) (9/10) τ
    (by positivity) (by norm_num) (by nlinarith only [hτε]) hr
  nlinarith only [hh]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_bidual (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V))) (δ τ : ℝ) :
    OriginalNodeReady B₀ UB (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) δ τ ↔
      OriginalNodeReady A₀ UA B₀ UB δ τ := by
  simp only [OriginalNodeReady,←Finset.map_inter,Finset.card_map,incidences_bidual]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨h2,h1,?_⟩ <;> nlinarith only [h3]

end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNode
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_guarded_node_failure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (A₀∩UA).card≤(B₀∩UB).card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      guardedNodeLaw f σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ (9/100000) (9/10)
        (σ^(-1000*beta η)) (((A₀∩UA).card:ℝ)*Real.exp (10*P η σ D R)) (by norm_num) none≤
          5*Real.exp (-(Nat.card K:ℝ)) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)≤(9/10:ℝ)^2 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<(9/10:ℝ)^2)).mono (fun σ h=>by simpa only [neg_mul] using h.le)
  filter_upwards [eventually_finite_node hη hη' (Cb+1) (by linarith),ht] with σ hn ht
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hAB hprod
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hD : 1≤D := (Real.one_le_rpow hσ (beta_pos hη).le).trans hr.dlo
  have hF : 1≤σ^(6*beta η) := Real.one_le_rpow hσ (by positivity [beta_pos hη])
  have hb' : b+1≤(Cb+1)*D*σ^(6*beta η) := by
    have hx := mul_le_mul hD hF (by norm_num : (0:ℝ)≤1) (by linarith : 0≤D)
    nlinarith only [hbhi,hx]
  have hτ : σ^(-1000*beta η)≤σ^(-800*beta η)*(9/10:ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hs.le (-800*beta η))
    rw [←Real.rpow_add hs] at hm
    simpa only [show -800*beta η+(-200*beta η)=-1000*beta η by ring] using hm
  have hdens := ready_trimmed_density A₀ UA B₀ UB _ _ (Real.rpow_nonneg hs.le _) hτ hready
  have hp := ready_trimmed_product A₀ UA B₀ UB _ b hready hprod
  obtain ⟨hnA,hnB,hf,_,_⟩ := hn D (b+1) (σ^(-800*beta η)) R L₀ q K V hd (A₀∩UA) UA (B₀∩UB) UB
    hcard (hq.trans (by exact_mod_cast hcard)) hr hL (by linarith) hb'
    (Real.rpow_pos_of_pos hs _) le_rfl Finset.inter_subset_right Finset.inter_subset_right hAB hdens hp
  simpa only [guardedNodeLaw,dite_eq_left hready] using hf

theorem eventually_oriented_guarded_node_failure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ UB
        (UA.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
        (orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ (9/100000)
          (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t).map
          (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)) none≤
            5*Real.exp (-(Nat.card K:ℝ)) := by
  filter_upwards [eventually_guarded_node_failure hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hprod
  dsimp only
  rw [orientedGuardedNode_law]
  split_ifs with hAB
  · exact hn D b R L₀ q K V hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hAB hprod
  · rw [map_option_none]
    apply hn D b R L₀ q K (Dual K V) (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map
      hσ hq hcard hr hL hb hbhi
    · exact (ready_bidual A₀ UA B₀ UB _ _).mpr hready
    · simpa only [←Finset.map_inter,Finset.card_map] using (le_of_not_ge hAB)
    · simpa only [Finset.card_map,mul_comm (B₀.card:ℝ) (A₀.card:ℝ)] using hprod
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReadyFailure
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {Ω α : Type*} [Fintype Ω] [Fintype α]
lemma map_decoded_none_event {M : Ω → Type*} (p : Law Ω)
    (enc : ∀ t, Option (M t)) (dec : ∀ t, M t → α) :
    map p (fun t => (enc t).map (dec t)) none =
      eventMass p (Finset.univ.filter (fun t => enc t = none)) := by
  simp only [map, eventMass, Finset.sum_filter, Option.map_eq_none_iff]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
noncomputable section

local instance (priority := high) actualReadyFailurePropDecidable_ra17666_1 (P : Prop) : Decidable P := Classical.propDecidable P
theorem eventually_oriented_ready_encoded_failure_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ UB
        (UA.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      eventMass (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K))
        (Finset.univ.filter (fun t => orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
          (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t = none)) ≤
            5*Real.exp (-(Nat.card K:ℝ)) := by
  filter_upwards [eventually_oriented_guarded_node_failure hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hprod
  have hh := hn D b R L₀ q K V hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hprod
  dsimp only at hh ⊢
  rw [map_decoded_none_event] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext t
  simp only [Finset.mem_filter]
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure_oai := @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure_oai
