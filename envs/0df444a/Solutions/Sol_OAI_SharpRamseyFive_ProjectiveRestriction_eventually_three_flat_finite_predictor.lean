-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:16:29.402948+00:00
-- url     : https://prove2.me/submissions/1e8eb104-d0f0-4e14-b8f1-cb9c3e7a628e

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_reverse_after_general_capture
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_three_coordinates_certified

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma mem_flatPoints (A : Submodule K V) (x : ℙ K V) :
    x ∈ flatPoints A ↔ x.submodule ≤ A := by
  simp [flatPoints]

end SharpRamseyFive.ProjectiveTraining

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionTwoOriented
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

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
  [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma enclosure_gap_nonneg (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U) :
    0≤Real.log ((U.card:ℝ)/S.card) := by
  exact Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hS.card_pos)).mpr
    (by simpa only [one_mul] using (show (S.card:ℝ)≤U.card from by exact_mod_cast Finset.card_le_card hSU)))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometricRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma mk_normalized (f : V→ₗ[K]W) (b : ℙ K W)
    (p : {p : Domain f // image f p=b}) :
    Projectivization.mk K (normalized f b p).val (normalized_nonzero f b p)=p.val.val := by
  rw [←p.val.val.mk_rep,Projectivization.mk_eq_mk_iff]
  exact ⟨_,rfl⟩

lemma normalized_injective (f : V→ₗ[K]W) (b : ℙ K W) :
    Function.Injective (normalized f b) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  rw [←mk_normalized f b p,←mk_normalized f b q]
  have hh := congrArg Subtype.val hpq
  congr 1

lemma affine_fiber_card_le [Finite K] [FiniteDimensional K V]
    (f : V→ₗ[K]W) (w : W) : Nat.card {v : V // f v=w}≤Nat.card f.ker := by
  classical
  let : Finite V := Module.finite_of_finite K
  by_cases h : ∃v,f v=w
  · obtain ⟨v₀,hv₀⟩:=h
    let g : {v : V // f v=w}→f.ker := fun v=>⟨v.val-v₀,by
      rw [LinearMap.mem_ker,map_sub,v.property,hv₀,sub_self]⟩
    apply Nat.card_le_card_of_injective g
    intro a b hab
    apply Subtype.ext
    have hh := congrArg Subtype.val hab
    change a.val-v₀=b.val-v₀ at hh
    have hhh := congrArg (fun x : V=>x+v₀) hh
    simpa only [sub_add_cancel] using hhh
  · have hi : IsEmpty {v : V // f v=w} := ⟨fun v=>h ⟨v.val,v.property⟩⟩
    let := hi
    simp

theorem fiber_card_le [Finite K] [FiniteDimensional K V]
    (f : V→ₗ[K]W) (b : ℙ K W) :
    Nat.card {p : Domain f // image f p=b}≤(Nat.card K)^(finrank K f.ker) := by
  let : Finite V := Module.finite_of_finite K
  have hh := (Nat.card_le_card_of_injective (normalized f b) (normalized_injective f b)).trans
    (affine_fiber_card_le f b.rep)
  have hn : Nat.card f.ker=(Nat.card K)^(finrank K f.ker) :=
    Module.natCard_eq_pow_finrank (K:=K)
  exact hh.trans_eq hn

theorem dual_restriction_fiber_card_le [Finite K] [FiniteDimensional K V]
    (U : Submodule K V) (b : ℙ K (Dual K U)) :
    Nat.card {p : Domain U.dualRestrict // image U.dualRestrict p=b}≤
      (Nat.card K)^(finrank K V-finrank K U) := by
  have hh := fiber_card_le U.dualRestrict b
  have hr := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have hk : finrank K U.dualRestrict.ker=finrank K V-finrank K U := by
    change finrank K U.dualAnnihilator=_
    omega
  rwa [hk] at hh

end

open Module ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incident_restriction (U : Submodule K V) (x : ℙ K U)
    (p : Domain U.dualRestrict) :
    Incident (Projectivization.map U.subtype U.injective_subtype x) p.val ↔
      Incident x (image U.dualRestrict p) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [Projectivization.map_mk]
  unfold Incident image
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,
    LinearMap.mem_ker,Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K
    (U.dualRestrict p.val.rep) p.property
  rw [←ha]
  simp only [Units.smul_def,LinearMap.smul_apply,Submodule.dualRestrict_apply,
    smul_eq_mul,mul_eq_zero,Units.ne_zero,false_or,Submodule.subtype_apply]

lemma incident_of_zero_restriction (U : Submodule K V) (x : ℙ K U)
    (p : ℙ K (Dual K V)) (hp : U.dualRestrict p.rep=0) :
    Incident (Projectivization.map U.subtype U.injective_subtype x) p := by
  induction x using Projectivization.ind with | h v hv =>
  rw [Projectivization.map_mk]
  unfold Incident
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]
  exact congrArg (fun f : Dual K U=>f v) hp

lemma restriction_nonzero_of_degree_lt
    (U : Submodule K V) (S : Finset (ℙ K U)) (p : ℙ K (Dual K V))
    (h : (S.filter fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p).card<S.card) :
    U.dualRestrict p.rep≠0 := by
  intro hp
  have he : S.filter (fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p)=S := by
    apply Finset.filter_eq_self.mpr
    intro x _
    exact incident_of_zero_restriction U x p hp
  rw [he] at h
  exact lt_irrefl _ h

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.DyadicLifts
open scoped Classical BigOperators
variable {A B : Type*}

lemma multiplicity_pos (f : A→B) (T : Finset A) {a : A} (ha : a∈T) :
    0 < multiplicity f T (f a) :=
  Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩

lemma multiplicity_mono (f : A→B) {T U : Finset A} (hTU : T⊆U) (b : B) :
    multiplicity f T b ≤ multiplicity f U b :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTU)

lemma bin_fiber (f : A→B) (T : Finset A) (k : ℕ) {b : B}
    (hb : b∈restrictions f T k) :
    multiplicity f (bin f T k) b=multiplicity f T b := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  have hak := (Finset.mem_filter.mp ha).2
  unfold multiplicity
  congr 1
  ext x
  simp only [bin,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx,_⟩,he⟩;exact ⟨hx,he⟩
  · rintro ⟨hx,he⟩;exact ⟨⟨hx,by rw [he];exact hak⟩,he⟩

lemma bin_multiplicity_bounds (f : A→B) (T : Finset A) (k : ℕ) {b : B}
    (hb : b∈restrictions f T k) :
    2^k ≤ multiplicity f T b ∧ multiplicity f T b < 2*(2^k) := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ha,hk⟩ := Finset.mem_filter.mp ha
  have hp := multiplicity_pos f T ha
  constructor
  · rw [←hk];exact Nat.pow_log_le_self 2 (ne_of_gt hp)
  · have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (multiplicity f T (f a))
    rw [hk,pow_succ,mul_comm] at hh
    exact hh

lemma bin_mass_bounds (f : A→B) (T : Finset A) (k : ℕ) :
    2^k*(restrictions f T k).card ≤ (bin f T k).card ∧
      (bin f T k).card ≤ 2*(2^k)*(restrictions f T k).card := by
  have he : (bin f T k).card=∑b∈restrictions f T k,multiplicity f T b := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=f) (t:=restrictions f T k)
      (fun a ha=> Finset.mem_image.mpr ⟨a,ha,rfl⟩)]
    apply Finset.sum_congr rfl
    intro b hb
    exact bin_fiber f T k hb
  rw [he]
  constructor
  · calc
      _ = ∑b∈restrictions f T k,2^k := by simp [mul_comm]
      _  ≤  _ := Finset.sum_le_sum fun b hb=> (bin_multiplicity_bounds f T k hb).1
  · calc
      _  ≤  ∑b∈restrictions f T k,2*(2^k) :=
        Finset.sum_le_sum fun b hb=> (bin_multiplicity_bounds f T k hb).2.le
      _ = _ := by simp [mul_comm]

lemma restrictions_subset_enclosure (f : A→B) {T U : Finset A} (hTU : T⊆U) (k : ℕ) :
    restrictions f T k⊆enclosure f U (2^k) := by
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_image.mpr ⟨a,hTU (Finset.mem_filter.mp ha).1,rfl⟩,
    (bin_multiplicity_bounds f T k hb).1.trans (multiplicity_mono f hTU _)⟩

lemma enclosure_mass (f : A→B) (U : Finset A) (l : ℕ) :
    l*(enclosure f U l).card ≤ U.card := by
  have hs : enclosure f U l⊆U.image f := Finset.filter_subset _ _
  calc
    _ = ∑b∈enclosure f U l,l := by simp [mul_comm]
    _  ≤  ∑b∈enclosure f U l,multiplicity f U b :=
      Finset.sum_le_sum fun b hb=> (Finset.mem_filter.mp hb).2
    _  ≤  ∑b∈U.image f,multiplicity f U b :=
      Finset.sum_le_sum_of_subset hs
    _ = U.card := (Finset.card_eq_sum_card_fiberwise (fun a ha=> Finset.mem_image.mpr ⟨a,ha,rfl⟩)).symm

theorem exists_massive_bin (f : A→B) (T : Finset A) (M : ℕ)
    (hM : ∀a∈T,multiplicity f T (f a) ≤ M) :
    ∃ k ≤ Nat.log 2 M, T.card ≤ (Nat.log 2 M+1)*(bin f T k).card := by
  let keys := Finset.range (Nat.log 2 M+1)
  have maps : ∀a∈T,Nat.log 2 (multiplicity f T (f a))∈keys := by
    intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hM a ha)))
  have hn : keys.Nonempty := ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  have hp : (0:ℝ) < keys.card := by exact_mod_cast Finset.card_pos.mpr hn
  obtain ⟨k,hk,hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s:=T) (t:=keys) (f:=fun a=> Nat.log 2 (multiplicity f T (f a)))
    (b:=(T.card:ℝ)/keys.card) maps hn (by
      rw [nsmul_eq_mul,mul_div_cancel₀ _ (ne_of_gt hp)])
  refine ⟨k,Nat.le_of_lt_succ (Finset.mem_range.mp hk),?_⟩
  have hh : (T.card:ℝ) ≤ (keys.card:ℝ)*(bin f T k).card := by
    have := (div_le_iff₀ hp).mp hc
    simpa only [bin,mul_comm] using this
  have hkeys : keys.card=Nat.log 2 M+1 := Finset.card_range _
  rw [hkeys] at hh
  exact_mod_cast hh

end SharpRamseyFive.DyadicLifts

namespace SharpRamseyFive.ProjectiveRestriction
open Module DyadicLifts
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

lemma finite_lift_bound (U : Submodule K V) (T : Finset (Domain U.dualRestrict))
    (b : ℙ K (Dual K U)) :
    multiplicity (image U.dualRestrict) T b ≤ (Nat.card K)^(finrank K V-finrank K U) := by
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Finite (Domain U.dualRestrict) := by unfold Domain; infer_instance
  let f := image U.dualRestrict
  let A := T.filter fun p=>f p=b
  let g : A→{p : Domain U.dualRestrict // f p=b} := fun p=>⟨p.val,(Finset.mem_filter.mp p.prop).2⟩
  have hi : Function.Injective g := by
    intro a c hac
    have hh := congrArg (fun x : {p : Domain U.dualRestrict // f p=b}=>x.val) hac
    exact Subtype.ext hh
  have hn := Nat.card_le_card_of_injective g hi
  have he : Nat.card A=A.card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [he] at hn
  exact hn.trans (dual_restriction_fiber_card_le U b)

theorem exists_restriction_dyad (U : Submodule K V)
    (T UT : Finset (Domain U.dualRestrict)) (hTU : T⊆UT) (hT : T.Nonempty) :
    ∃ k ≤ Nat.log 2 ((Nat.card K)^(finrank K V-finrank K U)),
      2^k ≤ (Nat.card K)^(finrank K V-finrank K U) ∧
      T.card ≤ 2*(Nat.log 2 ((Nat.card K)^(finrank K V-finrank K U))+1)*(2^k)*
        (restrictions (image U.dualRestrict) T k).card ∧
      restrictions (image U.dualRestrict) T k ⊆ enclosure (image U.dualRestrict) UT (2^k) ∧
      (2^k)*(enclosure (image U.dualRestrict) UT (2^k)).card ≤ UT.card ∧
      ∀b∈restrictions (image U.dualRestrict) T k,
        2^k ≤ multiplicity (image U.dualRestrict) T b ∧
        multiplicity (image U.dualRestrict) T b < 2*(2^k) := by
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let f := image U.dualRestrict
  have hl : ∀a∈T,multiplicity f T (f a) ≤ M := fun a _=>finite_lift_bound U T (f a)
  obtain ⟨k,hk,hc⟩ := exists_massive_bin f T M hl
  have hM : M≠0 := by
    obtain ⟨a,ha⟩ := hT
    exact ne_of_gt ((multiplicity_pos f T ha).trans_le (hl a ha))
  refine ⟨k,hk,Nat.pow_le_of_le_log hM hk,?_,
    restrictions_subset_enclosure f hTU k,enclosure_mass f UT (2^k),
    fun b hb=>bin_multiplicity_bounds f T k hb⟩
  have hm := (bin_mass_bounds f T k).2
  have hh := hc.trans (Nat.mul_le_mul_left (Nat.log 2 M+1) hm)
  simpa only [M,f,mul_assoc,mul_left_comm,mul_comm] using hh

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.FiniteRemoval
open scoped Classical BigOperators
variable {A : Type*}

theorem retain_card (T : Finset A) (d : A→ℝ) (c δ : ℝ) (hc : 0 < c)
    (hd : ∀a∈T,0 ≤ d a) (hsum : ∑a∈T,d a ≤ δ*c*T.card) :
    (1-δ)*(T.card:ℝ) ≤ (T.filter fun a=>d a ≤ c).card := by
  let G := T.filter fun a=>d a ≤ c
  let B := T.filter fun a=>c < d a
  have hpartition : G.card+B.card=T.card := by
    have he : B=T.filter (fun a=>¬d a ≤ c) := by simp only [B,not_le]
    rw [he]
    exact Finset.card_filter_add_card_filter_not _
  have hB : c*(B.card:ℝ) ≤ ∑a∈B,d a := by
    calc
      _ = ∑a∈B,c := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun a ha=>(Finset.mem_filter.mp ha).2.le
  have hBT : ∑a∈B,d a ≤ ∑a∈T,d a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a ha _=>hd a ha)
  have hcard : (G.card:ℝ)+(B.card:ℝ)=T.card := by exact_mod_cast hpartition
  have hbad : (B.card:ℝ) ≤ δ*T.card := by
    have hh := hB.trans (hBT.trans hsum)
    nlinarith
  change (1-δ)*(T.card:ℝ) ≤ (G.card:ℝ)
  nlinarith

theorem large_cell_retains_half (T : Finset A) (d : A→ℝ)
    (n s q τ : ℝ) (hq : 0 < q) (hs : 0 < s) (hτ : 0 < τ)
    (hsmall : Real.sqrt τ ≤ 1/200) (hsize : n ≤ 100*s)
    (hd : ∀a∈T,0 ≤ d a) (hsum : ∑a∈T,d a ≤ τ*n*T.card/q) :
    (T.card:ℝ)/2 ≤ (T.filter fun a=>d a ≤ Real.sqrt τ*s/q).card := by
  have hr : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hr2 := Real.sq_sqrt hτ.le
  have hc : 0 < Real.sqrt τ*s/q := div_pos (mul_pos hr hs) hq
  have hcs : τ*n/q ≤ (1/2:ℝ)*(Real.sqrt τ*s/q) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hq).mpr
    have hτn : τ*n ≤ τ*(100*s) := mul_le_mul_of_nonneg_left hsize hτ.le
    have hsτ : τ*(100*s) ≤ (1/2:ℝ)*(Real.sqrt τ*s) := by
      have hτr : τ ≤ Real.sqrt τ/200 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hτr hs.le
      nlinarith
    nlinarith
  have hh : ∑a∈T,d a ≤ (1/2:ℝ)*(Real.sqrt τ*s/q)*T.card := by
    calc
      _ ≤ τ*n*T.card/q := hsum
      _ = (τ*n/q)*T.card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcs (Nat.cast_nonneg _)
  have hz := retain_card T d (Real.sqrt τ*s/q) (1/2) hc hd hh
  linarith

end SharpRamseyFive.FiniteRemoval

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma goodLifts_nonzero (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (hκ : κ < 1) (hS : S.Nonempty)
    {p : ℙ K (Dual K V)} (hp : p∈goodLifts U S T κ) : U.dualRestrict p.rep≠0 := by
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hcut := (Finset.mem_filter.mp hp).2
  have hdeg : (flatDegree U S p:ℝ) < S.card := by nlinarith
  apply restriction_nonzero_of_degree_lt U S p
  exact_mod_cast hdeg

lemma card_nonzeroLifts (U : Submodule K V) (T : Finset (ℙ K (Dual K V)))
    (hT : ∀p∈T,U.dualRestrict p.rep≠0) : (nonzeroLifts U T).card=T.card := by
  change (T.subtype (fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0)).card=T.card
  rw [Finset.card_subtype,Finset.filter_eq_self.mpr hT]

lemma nonzeroLifts_mono (U : Submodule K V) {T UT : Finset (ℙ K (Dual K V))}
    (hTU : T⊆UT) : nonzeroLifts U T⊆nonzeroLifts U UT := Finset.subtype_mono hTU

lemma card_nonzeroLifts_le (U : Submodule K V) (T : Finset (ℙ K (Dual K V))) :
    (nonzeroLifts U T).card ≤ T.card := by
  change (T.subtype (fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0)).card ≤ T.card
  rw [Finset.card_subtype]
  exact Finset.card_filter_le _ _

lemma restricted_flatDegree (U : Submodule K V) (S : Finset (ℙ K U))
    (p : Domain U.dualRestrict) :
    (S.filter fun x=>Incident x (image U.dualRestrict p)).card=flatDegree U S p.val := by
  unfold flatDegree
  congr 1
  ext x
  simp only [Finset.mem_filter,incident_restriction]

lemma restricted_degree_bound (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (k : ℕ)
    {b : ℙ K (Dual K U)}
    (hb : b∈restrictions (image U.dualRestrict) (nonzeroLifts U (goodLifts U S T κ)) k) :
    ((S.filter fun x=>Incident x b).card:ℝ) ≤ κ*S.card := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
  have hpT : p∈nonzeroLifts U (goodLifts U S T κ) := (Finset.mem_filter.mp hp).1
  have hg : p.val∈goodLifts U S T κ := Finset.mem_subtype.mp hpT
  rw [restricted_flatDegree]
  exact (Finset.mem_filter.mp hg).2

lemma reduced_incidence_bound (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (k : ℕ) :
    (incidences S (restrictions (image U.dualRestrict)
      (nonzeroLifts U (goodLifts U S T κ)) k):ℝ) ≤
      κ*S.card*(restrictions (image U.dualRestrict)
        (nonzeroLifts U (goodLifts U S T κ)) k).card := by
  rw [incidences_eq_sum]
  calc
    _ ≤ ∑b∈restrictions (image U.dualRestrict) (nonzeroLifts U (goodLifts U S T κ)) k,
        κ*S.card := by
      apply Finset.sum_le_sum
      intro b hb
      have hh := restricted_degree_bound U S T κ k hb
      simpa only [Finset.sum_boole,incidenceEntry] using hh
    _ = _ := by simp [mul_comm]

end

section
open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem large_cell_restriction (U : Submodule K V) (S : Finset (ℙ K U))
    (T UT : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hTU : T⊆UT) (n τ : ℝ) (hτ : 0 < τ) (hsmall : Real.sqrt τ ≤ 1/200)
    (hsize : n ≤ 100*S.card)
    (hsum : ∑p∈T,(flatDegree U S p:ℝ) ≤ τ*n*T.card/(Nat.card K)) :
    let M := (Nat.card K)^(finrank K V-finrank K U)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
    ∃ k ≤ Nat.log 2 M,
      2^k ≤ M ∧
      (T.card:ℝ) ≤ 4*L*(2^k)*(restrictions (image U.dualRestrict) G k).card ∧
      (restrictions (image U.dualRestrict) G k).Nonempty ∧
      restrictions (image U.dualRestrict) G k ⊆
        enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k) ∧
      ((enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card:ℝ)*T.card ≤
        4*L*UT.card*(restrictions (image U.dualRestrict) G k).card ∧
      n*T.card ≤ 400*L*M*S.card*(restrictions (image U.dualRestrict) G k).card := by
  dsimp only
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let L := Nat.log 2 M+1
  let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hqpos : (0:ℝ) < Nat.card K := by linarith
  have hscard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htcard : (0:ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hκ : Real.sqrt τ/(Nat.card K) < 1 := by
    apply (div_lt_one hqpos).mpr
    linarith
  have hGcard : G.card=(goodLifts U S T (Real.sqrt τ/Nat.card K)).card :=
    card_nonzeroLifts U _ (fun p hp=>goodLifts_nonzero U S T _ hκ hS hp)
  have hhalf : (T.card:ℝ)/2 ≤ G.card := by
    rw [hGcard]
    have hh := large_cell_retains_half T (fun p=>(flatDegree U S p:ℝ))
      n S.card (Nat.card K) τ hqpos hscard hτ hsmall hsize
      (fun _ _=>Nat.cast_nonneg _) hsum
    simpa only [goodLifts,div_mul_eq_mul_div] using hh
  have hG : G.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0:ℝ)<(T.card:ℝ)/2) hhalf)
  have hGUT : G⊆nonzeroLifts U UT :=
    nonzeroLifts_mono U ((Finset.filter_subset _ _).trans hTU)
  obtain ⟨k,hk,hkm,hm,hsub,hencl,hdyad⟩ := exists_restriction_dyad U G (nonzeroLifts U UT) hGUT hG
  have hm' : (G.card:ℝ) ≤ 2*L*(2^k)*(restrictions (image U.dualRestrict) G k).card := by
    exact_mod_cast hm
  have hmass : (T.card:ℝ) ≤ 4*L*(2^k)*(restrictions (image U.dualRestrict) G k).card := by
    linarith
  have h0 : (restrictions (image U.dualRestrict) G k).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hz
    have he : (restrictions (image U.dualRestrict) G k).card=0 := by omega
    rw [he,Nat.cast_zero,mul_zero] at hmass
    linarith
  refine ⟨k,hk,hkm,hmass,h0,hsub,?_,?_⟩
  · have he : (2:ℝ)^k*(enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card ≤ UT.card := by
      have hh := hencl.trans (card_nonzeroLifts_le U UT)
      exact_mod_cast hh
    have h1 := mul_le_mul_of_nonneg_left hmass
      (Nat.cast_nonneg (enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card)
    have h2 := mul_le_mul_of_nonneg_left he
      (by positivity : (0:ℝ) ≤ 4*L*(restrictions (image U.dualRestrict) G k).card)
    nlinarith
  · have hkm' : (2:ℝ)^k ≤ M := by exact_mod_cast hkm
    have h1 := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg T.card)
    have h2 := mul_le_mul_of_nonneg_left hmass
      (by positivity : (0:ℝ) ≤ 100*S.card)
    have h3 := mul_le_mul_of_nonneg_left hkm'
      (by positivity : (0:ℝ) ≤ 400*L*S.card*(restrictions (image U.dualRestrict) G k).card)
    nlinarith

end

open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators

lemma logarithmic_gap_of_cross {a b c d C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hC : 0 < C)
    (hcross : a*d ≤ C*c*b) :
    Real.log (a/b) ≤ Real.log (c/d)+Real.log C := by
  have hh : a/b ≤ C*(c/d) := by
    apply (div_le_iff₀ hb).mpr
    calc
      a  ≤  (C*c*b)/d := (le_div_iff₀ hd).mpr hcross
      _ = C*(c/d)*b := by ring
  have hl := Real.log_le_log (div_pos ha hb) hh
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (div_pos hc hd))] at hl
  linarith only [hl]

lemma restriction_product_loss (q n t s t₀ b L : ℝ) (D j : ℕ)
    (hq : 0 < q) (hL : 0 < L) (hjd : j ≤ D)
    (horig : q^D*Real.exp (-b) ≤ n*t)
    (hred : n*t ≤ 400*L*q^(D-j)*s*t₀) :
    q^j*Real.exp (-(b+Real.log (400*L))) ≤ s*t₀ := by
  have hpow : 0 < q^(D-j) := pow_pos hq _
  have hmul : q^(D-j)*(q^j*Real.exp (-b)) ≤ q^(D-j)*(400*L*s*t₀) := by
    have he : q^D=q^(D-j)*q^j := by rw [←pow_add,Nat.sub_add_cancel hjd]
    rw [he] at horig
    nlinarith only [horig,hred]
  have hc : q^j*Real.exp (-b) ≤ 400*L*s*t₀ := (mul_le_mul_iff_of_pos_left hpow).mp hmul
  rw [neg_add,Real.exp_add,Real.exp_neg (Real.log (400*L)),Real.exp_log (by positivity)]
  rw [←mul_assoc,mul_inv_le_iff₀ (by positivity : (0:ℝ)<400*L)]
  nlinarith only [hc]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem large_cell_pair_with_losses (U : Submodule K V) (S : Finset (ℙ K U))
    (T UT : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hTU : T⊆UT) (n τ b : ℝ) (hn : 0 < n) (hτ : 0 < τ) (hsmall : Real.sqrt τ ≤ 1/200)
    (hsize : n ≤ 100*S.card)
    (horig : (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b) ≤ n*T.card)
    (hsum : ∑p∈T,(flatDegree U S p:ℝ) ≤ τ*n*T.card/(Nat.card K)) :
    let M := (Nat.card K)^(finrank K V-finrank K U)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
    ∃ k ≤ Nat.log 2 M,
      let T₀ := restrictions (image U.dualRestrict) G k
      let UT₀ := enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)
      T₀.Nonempty ∧ T₀⊆UT₀ ∧
      (Nat.card K:ℝ)^(finrank K U)*Real.exp (-(b+Real.log (400*L))) ≤ (S.card:ℝ)*T₀.card ∧
      (∀p∈T₀,((S.filter fun x=>Incident x p).card:ℝ) ≤ (Real.sqrt τ/(Nat.card K))*S.card) ∧
      (Nat.card K:ℝ)*(incidences S T₀:ℝ) ≤ Real.sqrt τ*S.card*T₀.card ∧
      Real.log ((UT₀.card:ℝ)/T₀.card) ≤ Real.log ((UT.card:ℝ)/T.card)+Real.log (4*L) ∧
      ∀u v : ℝ,0 < u → u ≤ v →
        Real.log (u/S.card) ≤ Real.log (v/n)+Real.log 100 := by
  dsimp only
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let L := Nat.log 2 M+1
  let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
  obtain ⟨k,hk,_,hm,hT₀,hsub,hgap,hprod⟩ :=
    large_cell_restriction U S T UT hS hT hTU n τ hτ hsmall hsize hsum
  let T₀ := restrictions (image U.dualRestrict) G k
  let UT₀ := enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  have hL : (0:ℝ)<L := by dsimp [L];positivity
  have htc : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  have ht₀ : (0:ℝ)<T₀.card := by exact_mod_cast hT₀.card_pos
  have hut : (0:ℝ)<UT.card := by exact_mod_cast (hT.card_pos.trans_le (Finset.card_le_card hTU))
  have hut₀ : (0:ℝ)<UT₀.card := by exact_mod_cast (hT₀.card_pos.trans_le (Finset.card_le_card hsub))
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hp := restriction_product_loss (Nat.card K) n T.card S.card T₀.card b L
    (finrank K V) (finrank K U) hq hL (Submodule.finrank_le U) horig (by
      simpa only [M,Nat.cast_pow] using hprod)
  refine ⟨k,hk,hT₀,hsub,hp,fun p hp=>restricted_degree_bound U S T _ k hp,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (reduced_incidence_bound U S T (Real.sqrt τ/Nat.card K) k) hq.le
    calc
      _  ≤  (Nat.card K:ℝ)*(Real.sqrt τ/Nat.card K*S.card*T₀.card) := hh
      _ = _ := by field_simp;ring
  · exact logarithmic_gap_of_cross hut₀ ht₀ hut htc (by positivity : (0:ℝ)<4*L) hgap
  · intro u v hu huv
    apply logarithmic_gap_of_cross hu hs (hu.trans_le huv) hn (by norm_num : (0:ℝ)<100)
    have hh := mul_le_mul_of_nonneg_left hsize hu.le
    have hh' := mul_le_mul_of_nonneg_right huv (by positivity : (0:ℝ) ≤ 100*S.card)
    nlinarith only [hh,hh']

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence ProjectiveTraining
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma section_mono (A : Submodule K V) {X Y : Finset (ℙ K V)} (hXY : X⊆Y) :
    flatSection A X⊆flatSection A Y := by
  intro x hx
  simpa only [flatSection,Finset.mem_preimage] using hXY (Finset.mem_preimage.mp hx)

lemma range_flatEmbedding (A : Submodule K V) (p : ℙ K V) :
    p∈Set.range (flatEmbedding A) ↔ p.submodule≤A := by
  constructor
  · rintro ⟨x,rfl⟩
    induction x using Projectivization.ind with | h v hv =>
    change (Projectivization.map A.subtype A.injective_subtype (Projectivization.mk K v hv)).submodule≤A
    rw [Projectivization.map_mk,Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    exact v.property
  · intro hp
    have hm : p.rep∈A := hp (by rw [p.submodule_eq]; exact Submodule.mem_span_singleton_self p.rep)
    have hn : (⟨p.rep,hm⟩:A)≠0 := fun hz=>p.rep_nonzero (congrArg Subtype.val hz)
    refine ⟨Projectivization.mk K (⟨p.rep,hm⟩:A) hn,?_⟩
    change Projectivization.map A.subtype A.injective_subtype (Projectivization.mk K (⟨p.rep,hm⟩:A) hn)=p
    rw [Projectivization.map_mk]
    exact p.mk_rep

variable [Finite K] [FiniteDimensional K V]

lemma section_map (A : Submodule K V) (X : Finset (ℙ K V)) :
    (flatSection A X).map (flatEmbedding A)=X∩flatPoints A := by
  ext x
  simp only [Finset.mem_map,flatSection,Finset.mem_preimage,Finset.mem_inter,mem_flatPoints]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,(range_flatEmbedding A _).mp ⟨a,rfl⟩⟩
  · rintro ⟨hx,hflat⟩
    obtain ⟨a,rfl⟩ := (range_flatEmbedding A x).mpr hflat
    exact ⟨a,hx,rfl⟩

lemma section_card (A : Submodule K V) (X : Finset (ℙ K V)) :
    (flatSection A X).card=(X∩flatPoints A).card := by
  rw [←section_map,Finset.card_map]

lemma section_degree_sum (A : Submodule K V) (X : Finset (ℙ K V))
    (T : Finset (ℙ K (Dual K V))) :
    ∑p∈T,(flatDegree A (flatSection A X) p:ℝ)=incidences (X∩flatPoints A) T := by
  rw [←section_map,incidences_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_map]
  simp only [flatDegree, incidenceEntry, Finset.sum_boole]
  rfl

omit [Finite K] [FiniteDimensional K V] in
lemma incidences_mono_left {X Y : Finset (ℙ K V)} (T : Finset (ℙ K (Dual K V))) (hXY : X⊆Y) :
    incidences X T ≤ incidences Y T := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.product_subset_product hXY (Finset.Subset.refl _)

lemma section_density (A : Submodule K V) (X : Finset (ℙ K V))
    (T : Finset (ℙ K (Dual K V))) (τ : ℝ)
    (h : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    ∑p∈T,(flatDegree A (flatSection A X) p:ℝ)≤τ*X.card*T.card/(Nat.card K) := by
  rw [section_degree_sum]
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  apply (le_div_iff₀ hq).mpr
  have hi : (incidences (X∩flatPoints A) T:ℝ) ≤ incidences X T := by
    exact_mod_cast incidences_mono_left T (Finset.inter_subset_left (s₁:=X) (s₂:=flatPoints A))
  nlinarith only [mul_le_mul_of_nonneg_left hi hq.le,h]

omit [Finite K] [FiniteDimensional K V] in
lemma section_decoder (A : Submodule K V) (X U : Finset (ℙ K V)) (Z : Finset (ℙ K A))
    (hZU : Z⊆flatSection A U) :
    Z.map (flatEmbedding A)⊆U ∧ (Z.map (flatEmbedding A)).card=Z.card ∧
    ((Z.map (flatEmbedding A))∩X).card=(Z∩flatSection A X).card := by
  refine ⟨?_,Finset.card_map _,?_⟩
  · rintro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_map.mp hx
    exact Finset.mem_preimage.mp (hZU hy)
  · have he : ((Z.map (flatEmbedding A))∩X)=(Z∩flatSection A X).map (flatEmbedding A) := by
      ext x
      simp only [Finset.mem_inter,Finset.mem_map,flatSection,Finset.mem_preimage]
      constructor
      · rintro ⟨⟨y,hy,rfl⟩,hx⟩
        exact ⟨y,⟨hy,hx⟩,rfl⟩
      · rintro ⟨y,⟨hy,hx⟩,rfl⟩
        exact ⟨⟨y,hy,rfl⟩,hx⟩
    rw [he,Finset.card_map]

end

open Module ProjectiveIncidence ProjectiveTraining DyadicLifts
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem original_large_cell (A : Submodule K V)
    (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (hX : X.Nonempty) (hT : T.Nonempty) (hXU : X⊆UX) (hTU : T⊆UT)
    (τ b : ℝ) (hτ : 0<τ) (hsmall : Real.sqrt τ≤1/200)
    (hflat : (X.card:ℝ)≤100*(X∩flatPoints A).card)
    (hprod : (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card)
    (hdens : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    let S := flatSection A X
    let US := flatSection A UX
    let M := (Nat.card K)^(finrank K V-finrank K A)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
    S.Nonempty ∧ S⊆US ∧ S.card≤X.card ∧ (X.card:ℝ)≤100*S.card ∧
    ∃k≤Nat.log 2 M,
      let T₀ := restrictions (image A.dualRestrict) G k
      let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
      T₀.Nonempty ∧ T₀⊆UT₀ ∧
      (Nat.card K:ℝ)^(finrank K A)*Real.exp (-(b+Real.log (400*L)))≤(S.card:ℝ)*T₀.card ∧
      (∀p∈T₀,((S.filter fun x=>Incident x p).card:ℝ)≤(Real.sqrt τ/(Nat.card K))*S.card) ∧
      (Nat.card K:ℝ)*(incidences S T₀:ℝ)≤Real.sqrt τ*S.card*T₀.card ∧
      Real.log ((UT₀.card:ℝ)/T₀.card)≤Real.log ((UT.card:ℝ)/T.card)+Real.log (4*L) ∧
      Real.log ((US.card:ℝ)/S.card)≤Real.log ((UX.card:ℝ)/X.card)+Real.log 100 := by
  dsimp only
  have hx : (0:ℝ)<X.card := by exact_mod_cast hX.card_pos
  have hxs : (X.card:ℝ)≤100*(flatSection A X).card := by simpa only [section_card] using hflat
  have hs : (0:ℝ)<(flatSection A X).card := by nlinarith only [hx,hxs]
  have hS : (flatSection A X).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hs)
  have hSU := section_mono A hXU
  have hsX : (flatSection A X).card≤X.card := by rw [section_card];exact Finset.card_le_card Finset.inter_subset_left
  have huX : (flatSection A UX).card≤UX.card := by rw [section_card];exact Finset.card_le_card Finset.inter_subset_left
  obtain ⟨k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ := large_cell_pair_with_losses
    A (flatSection A X) T UT hS hT hTU X.card τ b hx hτ hsmall hxs hprod
    (section_density A X T τ hdens)
  refine ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,?_⟩
  apply hsgap (flatSection A UX).card UX.card
  · exact_mod_cast (hS.mono hSU).card_pos
  · exact_mod_cast huX

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_RestrictionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma dyadic_levels_le (q r : ℕ) (σ : ℝ) (hσ : 1 ≤ σ)
    (hq : (q:ℝ)=Real.exp σ) (hr : r ≤ 5) :
    (Nat.log 2 (q^r)+1:ℝ) ≤ (5/Real.log 2+1)*σ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : 0 ≤ σ := le_trans (by norm_num) hσ
  have hh := Real.natLog_le_logb (q^r) 2
  norm_num only [Nat.cast_ofNat] at hh
  have he : Real.logb (2:ℝ) ((q^r:ℕ):ℝ) = (r:ℝ)*σ/Real.log 2 := by
    rw [Real.logb,Nat.cast_pow,hq,Real.log_pow,Real.log_exp]
  rw [he] at hh
  have hr' : (r:ℝ)≤5 := by exact_mod_cast hr
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr' hs) hl.le
  calc
    _ ≤ (r:ℝ)*σ/Real.log 2+1 := by linarith only [hh]
    _ ≤ 5*σ/Real.log 2+σ := add_le_add hm hσ
    _ = _ := by ring

lemma root_density_scale {σ τ β : ℝ} {j d : ℕ} (hσ : 1≤σ) (hτ : 0≤τ)
    (hβ : 0≤β) (hj : 2≤j) (hjd : j<d)
    (h : τ≤σ^(-200*(2:ℝ)^(d-2)*β)) :
    Real.sqrt τ ≤ σ^(-200*(2:ℝ)^(j-2)*β) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hpow : (2:ℝ)^(j-2)*2≤(2:ℝ)^(d-2) := by
    rw [←pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have he : -200*(2:ℝ)^(d-2)*β ≤ 2*(-200*(2:ℝ)^(j-2)*β) := by
    have := mul_le_mul_of_nonneg_right hpow hβ
    nlinarith
  have h' := h.trans (Real.rpow_le_rpow_of_exponent_le hσ he)
  have hh : σ^(2*(-200*(2:ℝ)^(j-2)*β))=(σ^(-200*(2:ℝ)^(j-2)*β))^2 := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hs.le (-200*(2:ℝ)^(j-2)*β) 2)
  rw [hh] at h'
  exact (sq_le_sq₀ (Real.sqrt_nonneg τ) (Real.rpow_nonneg hs.le _)).mp
    (by simpa only [Real.sq_sqrt hτ] using h')

theorem eventually_restriction_overheads {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D R b Cb : ℝ) (q r : ℕ), Range η σ D R →
      (q:ℝ)=Real.exp σ → r≤5 → b≤Cb*D*σ^(6*beta η) →
      Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤D*σ^(6*beta η) ∧
      Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤P η σ D R ∧
      b+Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤(Cb+1)*D*σ^(6*beta η) := by
  let C : ℝ := 400*(5/Real.log 2+1)
  have hC : 0<C := by dsimp [C]; positivity
  have hb : 0<7*beta η := mul_pos (by norm_num) (beta_pos hη)
  have hlog : Tendsto (fun σ : ℝ=>(Real.log C+Real.log σ)/σ^(7*beta η)) atTop (𝓝 0) := by
    have hc : Tendsto (fun σ : ℝ=>Real.log C/σ^(7*beta η)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hb)
    have hv := (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero
    simpa only [add_div,add_zero] using hc.add hv
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hσ hh
  intro D R b Cb q r hr hq hd hbb
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hbound : Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤σ^(7*beta η) := by
    have hl := Real.log_le_log (by positivity : (0:ℝ)<400*(Nat.log 2 (q^r)+1:ℝ))
      (mul_le_mul_of_nonneg_left (dyadic_levels_le q r σ hσ hq hd) (by norm_num : (0:ℝ)≤400))
    have he : 400*((5/Real.log 2+1)*σ)=C*σ := by dsimp [C];ring
    rw [he,Real.log_mul hC.ne' hs.ne'] at hl
    exact hl.trans (by simpa only [one_mul] using (div_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp hh.le)
  have hdlo : σ^(7*beta η)≤D*σ^(6*beta η) := by
    calc
      _ = σ^beta η*σ^(6*beta η) := by rw [←Real.rpow_add hs];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hr.dlo (Real.rpow_nonneg hs.le _)
  have hp : σ^(7*beta η)≤P η σ D R :=
    (Real.rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη;linarith)).trans
      (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  refine ⟨hbound.trans hdlo,hbound.trans hp,?_⟩
  nlinarith only [hbb,hbound,hdlo]

end SharpRamseyFive.ParameterHierarchy

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeOriented
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

lemma three_cap_size_absorb (Q s t b P : ℝ) (hs : 0≤ s) (ht : 0<t)
    (hp : Q*Real.exp (-b)≤ s*t) (hP : 0≤P) (hb : b≤P) (hexp : 1000≤Real.exp P) :
    (320/((9:ℝ)/1000)+320)*Q/t≤ s*Real.exp (10*P) := by
  have hh := source_product_to_cap Q s t b (320/((9:ℝ)/1000)+320) hs ht (by norm_num) hp
  have hh2 : (1000000:ℝ)≤Real.exp (2*P) := by
    calc
      _ = (1000:ℝ)*1000 := by norm_num
      _ ≤ Real.exp P*Real.exp P := mul_le_mul hexp hexp (by norm_num) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hc : 320/((9:ℝ)/1000)+320≤Real.exp (2*P) := by linarith only [hh2]
  have he : (320/((9:ℝ)/1000)+320)*Real.exp b≤Real.exp (10*P) := by
    calc
      _ ≤ Real.exp (2*P)*Real.exp P := mul_le_mul hc (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (3*P) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact hh.trans (mul_le_mul_of_nonneg_left he hs)

end SharpRamseyFive.ScoreGeometry

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeCoordinateCertified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
theorem publicGeneralReverseResult_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (hc : 0 < c)
    (Y : Option (Finset (ℙ K (Dual K V)))) :
    map (universalFreshLaw (ℙ K (Dual K V)) H q) (publicGeneralReverseResult A UA B UB hB H n q MA MB c hc Y)=
      generalNextCapLaw A UA B UB hB c hc n q MA MB Y := by
  cases Y with
  | none => exact map_const _ none
  | some W =>
    change map (universalFreshLaw (ℙ K (Dual K V)) H q)
      (fun t=>if _hW : CaptureBound B UB c MB W then
        (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
          (fun m=>UA∩universalFreshDecoded Incident W H q t m) else none) = _
    dsimp only [generalNextCapLaw]
    split_ifs with hv
    · have hW := (hv.nonempty hB hc).mono Finset.inter_subset_right
      have hh := congrArg (fun p=>map p (Option.map fun Z=>UA∩Z))
        (universalFreshEncoded_law Incident A UA (B∩W) W Finset.inter_subset_right hW H n q MA)
      rw [ambientCapLaw_restrict,map_comp] at hh
      simpa only [Function.comp_def,Option.map_map] using hh
    · exact map_const _ none
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeneralReversedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype Ω]

omit [Finite K] [FiniteDimensional K V] [Fintype Ω] in
lemma generalReversed_exact (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (hc : 0 < c)
    (t : GeneralReversedTape Ω K V H q) :
    (generalReversedEncoded M dec enc S U T UT H n q MA MB c t).map
      (generalReversedDecoded M dec U H q t)=
    publicGeneralReverseResult S U T UT hT H n q MA MB c hc ((enc t.1).map (dec t.1)) t.2 := by
  cases h : enc t.1 with
  | none => simp [generalReversedEncoded,h,publicGeneralReverseResult]
  | some m =>
    simp only [generalReversedEncoded,h,Option.bind_some,Option.map_some,publicGeneralReverseResult]
    split_ifs with hv
    · simp only [Option.map_map,generalReversedDecoded,Function.comp_def]
    · rfl

omit [Finite K] [FiniteDimensional K V] in
theorem generalReversed_law (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (p : Law Ω) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (hc : 0 < c) :
    map (adaptiveLaw p (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
      (fun t=>(generalReversedEncoded M dec enc S U T UT H n q MA MB c t).map
        (generalReversedDecoded M dec U H q t))=
    optionCompose (map p (fun t=>(enc t).map (dec t)))
      (generalNextCapLaw S U T UT hT c hc n q MA MB) := by
  simp only [generalReversed_exact M dec enc S U T UT hT H n q MA MB c hc]
  rw [optionCompose_eq_second _ (generalNextCapLaw S U T UT hT c hc n q MA MB) (by rfl)]
  exact public_composition p (universalFreshLaw (ℙ K (Dual K V)) H q)
    (fun t=>(enc t).map (dec t))
    (publicGeneralReverseResult S U T UT hT H n q MA MB c hc)
    (generalNextCapLaw S U T UT hT c hc n q MA MB)
    (fun Y=>publicGeneralReverseResult_law S U T UT hT H n q MA MB c hc Y)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype Ω] in
lemma generalReversed_prefixes (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (t : GeneralReversedTape Ω K V H q)
    (m : GeneralReversedMessage M dec H q t)
    (hm : generalReversedEncoded M dec enc S U T UT H n q MA MB c t=some m) :
    enc t.1=some m.1 ∧ CaptureBound T UT c MB (dec t.1 m.1) ∧
      universalFreshEncoded Incident S U (T∩dec t.1 m.1) (dec t.1 m.1) Finset.inter_subset_right
        H n q MA t.2=some m.2 := by
  unfold generalReversedEncoded at hm
  cases hb : enc t.1 with
  | none => simp [hb] at hm
  | some b =>
    rw [hb] at hm
    change (if _hv : CaptureBound T UT c MB (dec t.1 b) then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hv,hf⟩

omit [Fintype Ω] in
theorem generalReversed_cost (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (cost : ∀t,M t→ℝ)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hdim : finrank K V≤5)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P c B MA : ℝ) (hP : 1≤P) (hc : 0 < c) (hc1 : c≤1) (hB : 0≤B)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2)
    (t : GeneralReversedTape Ω K V (1000*(Nat.card K)^2) (Nat.card K))
    (m : GeneralReversedMessage M dec (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : generalReversedEncoded M dec enc S U T UT _ ⟨_,Nat.lt_succ_of_le hn⟩
      (Nat.card K) MA ((T.card:ℝ)*Real.exp (B*P)) c t=some m) :
    generalReversedCost M dec cost (1000*(Nat.card K)^2) (Nat.card K) t m≤
      cost t.1 m.1+(1010+21*(B-Real.log c))*(Nat.card K:ℝ)*P*
        (Real.log ((U.card:ℝ)/S.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  obtain ⟨hb,hv,hf⟩ := generalReversed_prefixes M dec enc S U T UT _ _ _ _ _ _ t m hm
  have hcost := general_reverse_message_cost σ hσ hq hdim S U hS hSU T UT (dec t.1 m.1) hT
    c B P hc hc1 hB hP hv
  have hh := universalFresh_cost_exact Incident S U (T∩dec t.1 m.1) (dec t.1 m.1)
    Finset.inter_subset_right _ _ _ MA t.2 m.2 hf
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  unfold generalReversedCost
  rw [hh]
  dsimp only at hcost
  linarith
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal

attribute [instance] FinitePredictor.tapeFintype FinitePredictor.messageFintype

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeFinitePredictor
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_three_finite_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=4) (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let pred := threeFinitePredictor hd σ U UT (P η σ D R) τ R L₀
        let p := pred.output X T
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W) ∧
        (∀t m,pred.encoded X T t=some m → pred.cost t m≤
          4100*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  filter_upwards [eventually_three_coordinates_certified hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ hd X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K A) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 4→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact hh D b τ R L₀ q K V e X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] in
lemma orientedFinite_output
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (d H : ℕ) (q P c B : ℝ) (hc : 0 < c)
    (hn : reverseLength q (Real.log ((U.card:ℝ)/S.card))≤H) :
    (orientedFinitePredictor f r U UT d H q P c B).output S T=
      if S.card≤T.card then f.output S T else
        optionCompose (r.output T (S.map bidualPoint.toEmbedding))
          (generalNextCapLaw S U T UT hT c hc
            (reverseLength q (Real.log ((U.card:ℝ)/S.card))) q
            ((320/c+320)*q^d/T.card) ((T.card:ℝ)*Real.exp (B*P))) := by
  by_cases h : S.card≤T.card
  · simp only [FinitePredictor.output,orientedFinitePredictor,ite_eq_left h,Option.map_map,Function.comp_def]
    exact map_independent_left _ _ (fun t=>(f.encoded S T t).map (f.decoded t))
  · simp only [FinitePredictor.output,orientedFinitePredictor,ite_eq_right h,dite_eq_left hn,Option.map_map,Function.comp_def]
    exact (map_independent_right _ _ (fun t=>
      (generalReversedEncoded r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) S U T UT H
        ⟨_,Nat.lt_succ_of_le hn⟩ q ((320/c+320)*q^d/T.card) ((T.card:ℝ)*Real.exp (B*P)) c t).map
          (generalReversedDecoded r.Message r.decoded U H q t))).trans
      (generalReversed_law r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) r.tapeLaw
        S U T UT hT H ⟨_,Nat.lt_succ_of_le hn⟩ q ((320/c+320)*q^d/T.card)
          ((T.card:ℝ)*Real.exp (B*P)) c hc)
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrientedFiniteCost
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem orientedFinite_cost
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hdim : finrank K V≤5)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (hTU : T⊆UT)
    (P : ℝ) (hP : 1≤P) (d : ℕ)
    (hf : S.card≤T.card → ∀t m,f.encoded S T t=some m →
      f.cost t m≤4100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P))
    (hr : T.card≤S.card → ∀t m,r.encoded T (S.map bidualPoint.toEmbedding) t=some m →
      r.cost t m≤4100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P))
    (t : (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).Tape)
    (m : (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).Message t)
    (hm : (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).encoded S T t=some m) :
    (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).cost t m≤
      9000*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  have hgs := (projective_enclosure_gap σ hq hdim S U hS hSU).1
  have hgt := (projective_enclosure_gap σ hq (by simpa using hdim) T UT hT hTU).1
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hqp : 1≤(Nat.card K:ℝ)*P := by nlinarith [mul_nonneg (show 0≤(Nat.card K:ℝ)-1 by linarith) (show 0≤P-1 by linarith)]
  have hh : 1≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) :=
    by nlinarith [mul_nonneg (show 0≤(Nat.card K:ℝ)*P-1 by linarith) (show 0≤Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P-1 by linarith)]
  have hlog2 : Real.log 2≤1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hn := reverseLength_universal_bound σ hσ hq hdim S U hS hSU
  dsimp only [orientedFinitePredictor] at hm ⊢
  by_cases hST : S.card≤T.card
  · rw [ite_eq_left hST] at hm
    obtain ⟨m',hm',he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    have hb := hf hST t.1 m' hm'
    dsimp only
    nlinarith only [hb,hh,hlog2]
  · rw [ite_eq_right hST,dite_eq_left hn] at hm
    obtain ⟨m',hm',he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    obtain ⟨hpre,_,_⟩ := generalReversed_prefixes r.Message r.decoded
      (r.encoded T (S.map bidualPoint.toEmbedding)) S U T UT _ _ _ _ _ _ t.2 m' hm'
    have hb := hr (by omega) t.2.1 m'.1 hpre
    have hc := generalReversed_cost r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) r.cost
      σ hσ hq hdim S U hS hSU T UT hT P (9/1000) 10
      ((320/((9:ℝ)/1000)+320)*(Nat.card K:ℝ)^d/T.card) hP (by norm_num) (by norm_num) (by norm_num)
      hn t.2 m' hm'
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<9/1000)
    norm_num at hl
    have hco : 1010+21*((10:ℝ)-Real.log (9/1000))≤3600 := by linarith
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hco (show 0≤(Nat.card K:ℝ)*P by positivity))
      (show 0≤Real.log ((U.card:ℝ)/S.card)+P by linarith)
    have hmon := mul_nonneg (show 0≤(Nat.card K:ℝ)*P by positivity) hgt
    dsimp only
    nlinarith only [hb,hc,hmul,hmon,hh,hlog2]
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeFiniteOriented
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem eventually_three_finite_oriented {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=4) (S U : Finset (ℙ K V))
       (T UT : Finset (ℙ K (Dual K V))) (_hT : T.Nonempty),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → S.Nonempty → S⊆U → T⊆UT →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(S.card:ℝ)*T.card →
        let pred := threeOrientedFinitePredictor hd σ U UT (P η σ D R) τ R L₀
        let p := pred.output S T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→CaptureBound S U (9/1000) ((S.card:ℝ)*Real.exp (10*P η σ D R)) W) ∧
        (∀t m,pred.encoded S T t=some m→pred.cost t m≤
          9000*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  have hsparse : ∀ᶠ σ : ℝ in atTop,σ^(-400*beta η)≤(9:ℝ)/1000000 := by
    have hp : 0<400*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact (Filter.Eventually.mono ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<9/1000000))) fun σ h=>by simpa only [neg_mul] using h.le
  filter_upwards [eventually_three_finite_predictor hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb,hsparse,eventually_ge_atTop (1:ℝ)] with σ hbase hrev hsparse hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ _ hd S U T UT hT hcard hσq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hτ200 := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ
    (by have := beta_pos hη;linarith : -400*beta η≤-200*beta η))
  obtain ⟨hP,hbP,heP,_,hq3⟩ := hrev D R b τ hr hbhi hτ.le hτ200
  have hqnat : 3≤Nat.card K := by exact_mod_cast (hq ▸ hq3 : (3:ℝ)≤Nat.card K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  have hn := reverseLength_universal_bound σ hσ hq.symm (by omega : finrank K V≤5) S U hS hSU
  have hgeom :
      let p := (threeOrientedFinitePredictor hd σ U UT (P η σ D R) τ R L₀).output S T
      p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
      ∀W,0<p (some W)→CaptureBound S U (9/1000) ((S.card:ℝ)*Real.exp (10*P η σ D R)) W := by
    rw [threeOrientedFinitePredictor,orientedFinite_output _ _ S U T UT hT 4 _ _ _ _ _ (by norm_num) hn]
    split_ifs with hST
    · obtain ⟨hf,hg,_⟩ := hbase D b τ R L₀ q K V hd S U T UT hcard hσq hr hL hb hbhi hτ hτhi hSU hTU hST hdens hprod
      exact ⟨hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))]),hg⟩
    · have hddual : finrank K (Dual K V)=4 := Subspace.dual_finrank_eq.trans hd
      have hTS : T.card≤(S.map bidualPoint.toEmbedding).card := by rw [Finset.card_map];omega
      have hSU' : S.map bidualPoint.toEmbedding⊆U.map bidualPoint.toEmbedding := Finset.map_subset_map.mpr hSU
      have hdens' : (Nat.card K:ℝ)*(incidences T (S.map bidualPoint.toEmbedding):ℝ)≤
          τ*T.card*(S.map bidualPoint.toEmbedding).card := by
        rw [incidences_bidual,Finset.card_map]
        nlinarith only [hdens]
      have hprod' : (Nat.card K:ℝ)^4*Real.exp (-b)≤(T.card:ℝ)*(S.map bidualPoint.toEmbedding).card := by
        rw [Finset.card_map];nlinarith only [hprod]
      obtain ⟨hf,hg,_⟩ := hbase D b τ R L₀ q K (Dual K V) hddual T UT
        (S.map bidualPoint.toEmbedding) (U.map bidualPoint.toEmbedding)
        hcard hσq hr hL hb hbhi hτ hτhi hTU hSU' hTS hdens' hprod'
      have hsparse' : 1000*(Nat.card K:ℝ)*incidences S T≤(9:ℝ)/1000*S.card*T.card := by
        have htau := hτhi.trans hsparse
        have hh := mul_le_mul_of_nonneg_left hdens (by norm_num : (0:ℝ)≤1000)
        have hh' := mul_le_mul_of_nonneg_right htau (show (0:ℝ)≤(S.card:ℝ)*T.card from mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        nlinarith only [hh,hh']
      have hl := reverseLength_spec (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) hq1 (enclosure_gap_nonneg S U hS hSU)
      obtain ⟨hf',hg'⟩ := reverse_after_general_capture (d:=3) hd (by norm_num) hqnat S U hS hSU T UT hT
        (9/1000) (by norm_num) (by norm_num)
        ((T.card:ℝ)*Real.exp (10*P η σ D R)) (2*Real.exp (-(Nat.card K:ℝ)))
        ((threeFinitePredictor hddual σ UT (U.map bidualPoint.toEmbedding) (P η σ D R) τ R L₀).output T (S.map bidualPoint.toEmbedding))
        hf hg hsparse' (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))) hl.1 hl.2.1
      refine ⟨by convert hf' using 1; ring,?_⟩
      intro W hW
      have hw := hg' W hW
      refine ⟨hw.1,hw.2.1.trans ?_,?_⟩
      · exact three_cap_size_absorb _ _ _ _ _ (Nat.cast_nonneg _) (by exact_mod_cast hT.card_pos) hprod (by linarith) hbP heP
      · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/10) (Nat.cast_nonneg _)).trans hw.2.2
  refine ⟨hgeom.1,hgeom.2,?_⟩
  apply orientedFinite_cost _ _ σ hσ hq.symm (by omega : finrank K V≤5) S U hS hSU T UT hT hTU
    (P η σ D R) hP 4
  · intro hST
    exact (hbase D b τ R L₀ q K V hd S U T UT hcard hσq hr hL hb hbhi hτ hτhi hSU hTU hST hdens hprod).2.2
  · intro hTS t m hm
    have hddual : finrank K (Dual K V)=4 := Subspace.dual_finrank_eq.trans hd
    have hTS' : T.card≤(S.map bidualPoint.toEmbedding).card := by simpa using hTS
    have hSU' : S.map bidualPoint.toEmbedding⊆U.map bidualPoint.toEmbedding := Finset.map_subset_map.mpr hSU
    have hdens' : (Nat.card K:ℝ)*(incidences T (S.map bidualPoint.toEmbedding):ℝ)≤
        τ*T.card*(S.map bidualPoint.toEmbedding).card := by
      rw [incidences_bidual,Finset.card_map]
      nlinarith only [hdens]
    have hprod' : (Nat.card K:ℝ)^4*Real.exp (-b)≤(T.card:ℝ)*(S.map bidualPoint.toEmbedding).card := by
      rw [Finset.card_map];nlinarith only [hprod]
    have hh := (hbase D b τ R L₀ q K (Dual K V) hddual T UT
      (S.map bidualPoint.toEmbedding) (U.map bidualPoint.toEmbedding)
      hcard hσq hr hL hb hbhi hτ hτhi hTU hSU' hTS' hdens' hprod').2.2 t m hm
    simpa only [Finset.card_map,add_comm,add_left_comm,add_assoc] using hh
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open FiniteEntropy
open scoped Classical
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
lemma FinitePredictor.transform_output (p : FinitePredictor A B) (e : A↪C)
    (inputs : Finset C→Finset D→Finset A×Finset B) (S : Finset C) (T : Finset D) :
    (p.transform e inputs).output S T=
      map (p.output (inputs S T).1 (inputs S T).2) (Option.map fun W=>W.map e) := by
  simp only [FinitePredictor.output,FinitePredictor.transform,map_comp,Option.map_map,Function.comp_def]
  rfl
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_three_flat_finite_predictor_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (A : Submodule K V) (hA : finrank K A=4)
      (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K V≤5 → Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
        let pred := threeFlatFinitePredictor A hA σ UX UT τ (P η σ D R) R L₀ k
        let p := pred.output X T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/100000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,pred.encoded X T t=some m→pred.cost t m≤
          30000*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-400*beta η)<(1:ℝ)/200 := by
    have hp : 0<400*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<1/200)
  filter_upwards [eventually_three_finite_oriented hη hη' (Cb+1) (by linarith),
    eventually_restriction_overheads hη hη',ht,eventually_ge_atTop (1:ℝ)] with σ hbase hover ht hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ A hA X UX T UT hV hcard hσq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  let : Finite A := Module.finite_of_finite K
  let : Finite (Dual K A) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let : Fintype (ℙ K A) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have htroot : Real.sqrt τ≤σ^(-400*beta η) := by
    have hh := root_density_scale (j:=3) (d:=4) hσ hτ.le (beta_pos hη).le (by norm_num) (by norm_num)
      (show τ≤σ^(-200*(2:ℝ)^(4-2)*beta η) by norm_num;simpa only [neg_mul] using hτhi)
    convert hh using 1; norm_num
  have hsmall : Real.sqrt τ≤1/200 := htroot.trans ht.le
  obtain ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ :=
    original_large_cell A X UX T UT hX hT hXU hTU τ b hτ hsmall hflat hprod hdens
  let S := flatSection A X
  let US := flatSection A UX
  let M := (Nat.card K)^(finrank K V-finrank K A)
  let B := b+Real.log (400*(Nat.log 2 M+1:ℝ))
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  let pp := (threeOrientedFinitePredictor hA σ US UT₀ (P η σ D R) (Real.sqrt τ) R L₀).output S T₀
  have hB : 0≤B := by
    refine add_nonneg hb (Real.log_nonneg ?_)
    have hn : (0:ℝ)≤Nat.log 2 M := by positivity
    linarith only [hn]
  have hBhi : B≤(Cb+1)*D*σ^(6*beta η) :=
    (hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi).2.2
  have hp' : (Nat.card K:ℝ)^4*Real.exp (-B)≤(S.card:ℝ)*T₀.card := by
    simpa only [S,T₀,G,B,M,hA,Nat.cast_add,Nat.cast_one] using hp
  obtain ⟨hfail,hgood,hcost⟩ := hbase D B (Real.sqrt τ) R L₀ q K A hA S US T₀ UT₀ hT₀ hcard hσq hr hL
    hB hBhi (Real.sqrt_pos.mpr hτ) htroot hS hSU hTU₀ hd hp'
  refine ⟨k,hk,?_,?_,?_⟩
  · rw [threeFlatFinitePredictor,FinitePredictor.transform_output,map_option_none]
    exact hfail
  · intro W hW
    rw [threeFlatFinitePredictor,FinitePredictor.transform_output] at hW
    obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) hW
    cases Z with
    | none => simp at he
    | some Z =>
      have he' : Z.map (flatEmbedding A)=W := Option.some.inj he
      subst W
      have hz := hgood Z hZ
      obtain ⟨hu,hcard',hcap⟩ := section_decoder A X UX Z hz.1
      refine ⟨hu,?_,?_⟩
      · rw [hcard']
        exact hz.2.1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsX) (Real.exp_pos _).le)
      · rw [hcap,Finset.inter_comm]
        have hc := hz.2.2
        nlinarith only [hc,hxs]
  · intro t m hm
    have hc := hcost t m hm
    have hov := hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi
    have hP : 1≤P η σ D R :=
      (Real.one_le_rpow hσ (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
        (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
    have hlog : Real.log (400*(Nat.log 2 M+1:ℝ))≤P η σ D R := hov.2.1
    have h100 : Real.log (100:ℝ)≤P η σ D R := (Real.log_le_log (by norm_num) (by
      have hn : (0:ℝ)≤Nat.log 2 M := by positivity
      linarith : (100:ℝ)≤400*(Nat.log 2 M+1:ℝ))).trans hlog
    have h4 : Real.log (4*(Nat.log 2 M+1:ℝ))≤P η σ D R :=
      (Real.log_le_log (by positivity) (by
        have hn : (0:ℝ)≤Nat.log 2 M := by positivity
        linarith : (4:ℝ)*(Nat.log 2 M+1)≤400*(Nat.log 2 M+1:ℝ))).trans hlog
    have hgX : 0≤Real.log ((UX.card:ℝ)/X.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr (by
        simpa using (show (X.card:ℝ)≤UX.card by exact_mod_cast Finset.card_le_card hXU)))
    have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr (by
        simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
    have hsum : Real.log ((US.card:ℝ)/S.card)+Real.log ((UT₀.card:ℝ)/T₀.card)+P η σ D R≤
        3*(Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
      simp only [Nat.cast_add,Nat.cast_one] at hgap
      change _≤Real.log ((UT.card:ℝ)/T.card)+Real.log (4*(Nat.log 2 M+1:ℝ)) at hgap
      change _≤Real.log ((UX.card:ℝ)/X.card)+Real.log (100:ℝ) at hsgap
      linarith
    have hm' := mul_le_mul_of_nonneg_left hsum
      (by positivity : (0:ℝ)≤9000*(Nat.card K:ℝ)*P η σ D R)
    have hpos : 0≤(Nat.card K:ℝ)*P η σ D R*
        (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by positivity
    change (threeOrientedFinitePredictor hA σ US UT₀ (P η σ D R) (Real.sqrt τ) R L₀).cost t m≤_
    nlinarith only [hc,hm',hpos]
end SharpRamseyFive.ProjectiveRestriction

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor_oai := @OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor_oai
