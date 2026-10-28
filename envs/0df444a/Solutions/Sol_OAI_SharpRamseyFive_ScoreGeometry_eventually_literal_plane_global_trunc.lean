-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:20:00.846738+00:00
-- url     : https://prove2.me/submissions/1f804d2c-b0dd-40f1-9de1-65dcfb041837

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveRichLines_quantitative_card_mul_le
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_captured_global_trunc_exp_bound

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Best
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

lemma best_spec (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V) :
    best F hF shape X ∈ F ∧
      ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape (best F hF shape X)).card :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma maximal_cell (k : ℕ) (a : I) (ha : a ∈ F) :
    (remaining F hF shape X k ∩ shape a).card ≤ (cell F hF shape X k).card :=
  (best_spec F hF shape _).2 a ha

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma stopIndex_stops (threshold : ℕ) (hthreshold : 0 < threshold) :
    Stop F hF shape X threshold (stopIndex F hF shape X threshold hthreshold) := Nat.find_spec _

lemma before_stop (threshold : ℕ) (hthreshold : 0 < threshold) {j : ℕ}
    (hj : j < stopIndex F hF shape X threshold hthreshold) :
    (cell F hF shape X j).card ≥ threshold ∧
      2*(X.card-(remaining F hF shape X j).card) < X.card := by
  have h := Nat.find_min (Exists.imp (fun _ hk => hk.2)
    (exists_stop F hF shape X threshold hthreshold)) hj
  simpa only [Stop, not_or, not_le, not_lt, and_comm] using h

lemma list_length_bound (threshold : ℕ) (hthreshold : 0 < threshold) :
    stopIndex F hF shape X threshold hthreshold * threshold ≤ X.card := by
  let J := stopIndex F hF shape X threshold hthreshold
  change J*threshold ≤ X.card
  have hs := Finset.sum_le_sum (s := Finset.range J) (fun j hj =>
    (before_stop F hF shape X threshold hthreshold (Finset.mem_range.mp hj)).1)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hc := sum_card_add_remaining F hF shape X J
  omega

lemma retained_subset (threshold : ℕ) (hthreshold : 0 < threshold) :
    retained F hF shape X threshold hthreshold ⊆ X := by
  unfold retained
  split
  · exact Finset.sdiff_subset
  · exact remaining_subset F hF shape X _

lemma residual_cap (threshold : ℕ) (hthreshold : 0 < threshold)
    (hn : ¬X.card ≤ 2*(X.card-(remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)).card))
    (a : I) (ha : a ∈ F) :
    (retained F hF shape X threshold hthreshold ∩ shape a).card < threshold := by
  rw [retained,ite_eq_right hn]
  have hc := (stopIndex_stops F hF shape X threshold hthreshold).resolve_left hn
  exact (maximal_cell F hF shape X _ a ha).trans_lt hc

end SharpRamseyFive.GreedyTraining

end OAI
end

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace RadialLine

lemma through_eq_iff [FiniteDimensional K V] {x y : ℙ K V} (hxy : x ≠ y)
    (l : RadialLine x) : through x y hxy = l ↔ y.submodule ≤ l.val := by
  constructor
  · intro h
    rw [← h]
    exact le_sup_right
  · intro h
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq (sup_le l.property.2 h)
      ((finrank_sup_points hxy).trans l.property.1.symm)

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

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
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ScalarConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.RichRegime
open scoped Real

theorem scalar_conditions (σ g N M K : ℝ)
    (hNhi : N ≤ Real.exp (3*σ/2+g))
    (hMlo : Real.exp (σ/2+19*g/20)/4 ≤ M)
    (hKhi : K ≤ 2*Real.exp (σ+17*g/15))
    (hg : g ≤ 2*σ)
    (hlarge : 64*1024^2 ≤ Real.exp (37*g/20))
    (hcap : 256 ≤ Real.exp (23*g/30))
    (hchar : 102 < Real.exp (9*σ/20)) :
    1024^2*N ≤ M^3 ∧ 8*K ≤ M^2 ∧
      51*Real.sqrt (N/M) < Real.exp σ := by
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hMlo
  have hcube : (Real.exp (σ/2+19*g/20)/4)^3 ≤ M^3 :=
    pow_le_pow_left₀ (by positivity) hMlo 3
  have hsq : (Real.exp (σ/2+19*g/20)/4)^2 ≤ M^2 :=
    pow_le_pow_left₀ (by positivity) hMlo 2
  have he3 : Real.exp (3*σ/2+g)*Real.exp (37*g/20) = (Real.exp (σ/2+19*g/20))^3 := by
    rw [← Real.exp_add,← Real.exp_nat_mul]
    congr 1
    ring
  have he2 : Real.exp (σ+17*g/15)*Real.exp (23*g/30) = (Real.exp (σ/2+19*g/20))^2 := by
    rw [← Real.exp_add,← Real.exp_nat_mul]
    congr 1
    ring
  have hn3 := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (3*σ/2+g)).le
  have hk2 := mul_le_mul_of_nonneg_left hcap (Real.exp_pos (σ+17*g/15)).le
  rw [he3] at hn3
  rw [he2] at hk2
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · have hratio : N/M ≤ 4*Real.exp (11*σ/10) := by
      apply (div_le_iff₀ hM).mpr
      have hs : Real.exp (3*σ/2+g) ≤
          Real.exp (11*σ/10)*Real.exp (σ/2+19*g/20) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        linarith
      have ht := mul_le_mul_of_nonneg_left hMlo (show 0 ≤ 4*Real.exp (11*σ/10) by positivity)
      nlinarith
    have hsqrt : Real.sqrt (N/M) ≤ 2*Real.exp (11*σ/20) := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity,hratio.trans_eq ?_⟩
      rw [mul_pow,← Real.exp_nat_mul]
      norm_num
      ring
    have he : Real.exp (11*σ/20)*Real.exp (9*σ/20) = Real.exp σ := by
      rw [← Real.exp_add]
      congr 1
      ring
    have ht := mul_lt_mul_of_pos_left hchar (Real.exp_pos (11*σ/20))
    rw [he] at ht
    linarith

theorem source_substitution (σ g n' a : ℝ)
    (hn' : Real.exp (3*σ/2+g)/4 ≤ n')
    (ha : Real.exp (-g/20) ≤ a) :
    Real.exp (σ/2+19*g/20)/4 ≤ n'*a/Real.exp σ ∧
    (Real.exp (3*σ/2+g)) ^ (4/3:ℝ) / Real.exp σ * Real.exp (-g/5) =
      Real.exp (σ+17*g/15) := by
  have hn0 : 0 ≤ n' := le_trans (by positivity) hn'
  constructor
  · apply (le_div_iff₀ (Real.exp_pos σ)).mpr
    have hh := mul_le_mul hn' ha (by positivity) hn0
    apply le_trans _ hh
    have he : Real.exp (σ/2+19*g/20)*Real.exp σ =
        Real.exp (3*σ/2+g)*Real.exp (-g/20) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    have he' : Real.exp (σ/2+19*g/20)/4*Real.exp σ =
        Real.exp (3*σ/2+g)/4*Real.exp (-g/20) := by nlinarith [he]
    exact he'.le
  · rw [← Real.exp_mul,← Real.exp_sub,← Real.exp_add]
    congr 1
    ring

theorem sufficiently_large_conditions (σ g N M K : ℝ)
    (hσ : 1000 ≤ σ) (hglo : 100000000 ≤ g) (hghi : g ≤ 2*σ)
    (hNhi : N ≤ Real.exp (3*σ/2+g))
    (hMlo : Real.exp (σ/2+19*g/20)/4 ≤ M)
    (hKhi : K ≤ 2*Real.exp (σ+17*g/15)) :
    2 ≤ M ∧ 1024^2*N ≤ M^3 ∧ 8*K ≤ M^2 ∧
      51*Real.sqrt (N/M) < Real.exp σ := by
  have hm := Real.add_one_le_exp (σ/2+19*g/20)
  refine ⟨by linarith,scalar_conditions σ g N M K hNhi hMlo hKhi hghi ?_ ?_ ?_⟩
  · linarith [Real.add_one_le_exp (37*g/20)]
  · linarith [Real.add_one_le_exp (23*g/30)]
  · linarith only [hσ, Real.add_one_le_exp (9*σ/20)]

end SharpRamseyFive.RichRegime

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CardIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SharpRamseyFive.ProjectiveRichLines
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K I : Type*} [Field K] [Fintype I]

omit [Fintype I] in
lemma card_indexed (X : Finset (ℙ K (I → K))) (U : Submodule K (I → K)) :
    (Finset.univ.filter (fun y : X => y.val.rep ∈ U)).card =
      (X.filter (fun y => y.submodule ≤ U)).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    refine Finset.mem_filter.mpr ⟨y.property,?_⟩
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
    exact (Finset.mem_filter.mp hy).2
  · intro y _ z _ h
    exact Subtype.ext h
  · intro y hy
    obtain ⟨hy,hU⟩ := Finset.mem_filter.mp hy
    refine ⟨⟨y,hy⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    rwa [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem] at hU

theorem source_rich_lines {q : ℕ} [CharP K q] (hq : 2 < q)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (σ g n' a : ℝ) (hσq : Real.exp σ = q)
    (hσ : 1000 ≤ σ) (hg : 100000000 ≤ g) (hghi : g ≤ 2*σ)
    (hn' : Real.exp (3*σ/2+g)/4 ≤ n') (ha : Real.exp (-g/20) ≤ a)
    (X : Finset (ℙ K (I → K))) (hX : (X.card:ℝ) ≤ Real.exp (3*σ/2+g))
    (F : Finset (Submodule K (I → K))) (hF : ∀ U ∈ F, finrank K U = 2)
    (hrich : ∀ U ∈ F, n'*a/Real.exp σ ≤ (X.filter fun y => y.submodule ≤ U).card)
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      ((X.filter fun y => y.submodule ≤ U).card:ℝ) ≤
        (Real.exp (3*σ/2+g)) ^ (4/3:ℝ) / Real.exp σ * Real.exp (-g/5)) :
    (F.card:ℝ)*(n'*a/Real.exp σ) ≤ 20814*Real.exp (3*σ/2+g) := by
  classical
  obtain ⟨hMlo,hCeq⟩ := RichRegime.source_substitution σ g n' a hn' ha
  let M : ℕ := ⌈n'*a/Real.exp σ⌉₊
  let C : ℕ := ⌊Real.exp (σ+17*g/15)⌋₊
  have hMM : n'*a/Real.exp σ ≤ (M:ℝ) := Nat.le_ceil _
  have hC : (C:ℝ) ≤ Real.exp (σ+17*g/15) := Nat.floor_le (by positivity)
  obtain ⟨hM2,hlarge,hCM,hchar⟩ := RichRegime.sufficiently_large_conditions σ g
    (X.card:ℝ) M C hσ hg hghi hX (hMlo.trans hMM) (hC.trans (by nlinarith [Real.exp_pos (σ+17*g/15)]))
  by_cases hFn : F.Nonempty
  · obtain ⟨U,hU⟩ := hFn
    have hMU : M ≤ (X.filter fun y => y.submodule ≤ U).card := Nat.ceil_le.mpr (hrich U hU)
    have hMN : M ≤ X.card := hMU.trans (Finset.card_filter_le _ _)
    have hXp : (0:ℝ) < X.card := lt_of_lt_of_le (by linarith : (0:ℝ)<M) (by exact_mod_cast hMN)
    have hXn : X.Nonempty := Finset.card_pos.mp (by exact_mod_cast hXp)
    let : Nonempty X := hXn.coe_sort
    have h2 : (2 : AlgebraicClosure K) ≠ 0 := by
      intro he
      have hd := (CharP.cast_eq_zero_iff (AlgebraicClosure K) q 2).mp he
      have hh := Nat.le_of_dvd (by decide : 0<2) hd
      omega
    have hh := quantitative_card_mul_le (L := AlgebraicClosure K) h2 hI
      (fun y : X => y.val) Subtype.val_injective (fun U : F => U.val)
      (fun U => hF U.val U.property) Subtype.val_injective M C
      (by exact_mod_cast hM2) (by simpa only [Fintype.card_coe] using hMN)
      (by
        intro U
        rw [card_indexed]
        exact Nat.ceil_le.mpr (hrich U.val U.property))
      (by
        intro U hU
        rw [card_indexed]
        apply Nat.le_floor
        rw [← hCeq]
        exact hcap U hU)
      (by simpa only [Fintype.card_coe] using hlarge)
      (by simpa only [Fintype.card_coe,hσq] using hchar)
      (by exact_mod_cast hCM)
    have hh' : (F.card:ℝ)*(M:ℝ) ≤ 20814*(X.card:ℝ) := by
      exact_mod_cast (by simpa only [Fintype.card_coe] using hh : F.card * M ≤ 20814 * X.card)
    exact (mul_le_mul_of_nonneg_left hMM (by positivity)).trans
      (hh'.trans (mul_le_mul_of_nonneg_left hX (by norm_num)))
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hFn
    rw [hF0,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity

end SharpRamseyFive.ProjectiveRichLines

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_RichCentersCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma richCenters_card_le (X : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (A : Submodule K V) (hA : finrank K A = 2) :
    (richCenters X O δ a A).card ≤ Nat.card K+1 := by
  let : Finite V := Module.finite_of_finite K
  let C := richCenters X O δ a A
  let f (x : C) : {y : ℙ K V // y.submodule ≤ A} :=
    ⟨x.val,(mem_flatPoints A x.val).mp (Finset.mem_filter.mp x.property).1⟩
  have hi : Function.Injective f := fun _ _ he => Subtype.ext (show _ = _ from congrArg (fun z : {y : ℙ K V // y.submodule ≤ A} => z.val) he)
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,card_subspacePoints,hA] at hc
  simpa only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,pow_zero,pow_one,
    zero_add,add_comm] using hc

lemma centers_empty_of_not_rich (X : Finset (ℙ K V))
    (O : ℙ K V → Finset (ℙ K V)) {δ a : ℝ} (hδ : 0 ≤ δ)
    (A : Submodule K V) (ha : ¬a ≤ δ*(X.filter fun y => y.submodule ≤ A).card) :
    richCenters X O δ a A = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  apply ha
  apply (Finset.mem_filter.mp hx).2.trans
  apply mul_le_mul_of_nonneg_left _ hδ
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)

theorem residual_rich_centers {I : Type*} [Fintype I] {q : ℕ} [CharP K q]
    (hq : 2 < q) (hcard : Nat.card K = q)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (σ g n' a : ℝ) (hσq : Real.exp σ = q)
    (hσ : 1000 ≤ σ) (hg : 100000000 ≤ g) (hghi : g ≤ 2*σ)
    (hn' : Real.exp (3*σ/2+g)/4 ≤ n') (ha : Real.exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (X : Finset (ℙ K (I → K))) (hX : (X.card:ℝ) ≤ Real.exp (3*σ/2+g))
    (L : Finset (Submodule K (I → K))) (hL : ∀ A ∈ L, finrank K A = 2)
    (O : ℙ K (I → K) → Finset (ℙ K (I → K)))
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      ((X.filter fun y => y.submodule ≤ U).card:ℝ) ≤
        (Real.exp (3*σ/2+g)) ^ (4/3:ℝ) / Real.exp σ * Real.exp (-g/5)) :
    (∑ A ∈ L, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ))*a^2 ≤ 333024*(q:ℝ)^2 := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast lt_trans (by decide : 0<2) hq
  have hn0 : 0<n' := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hn'
  have ha0 : 0<a := (Real.exp_pos _).trans_le ha
  let F := L.filter fun A => n'*a/(q:ℝ) ≤ (X.filter fun y => y.submodule ≤ A).card
  have hr := ProjectiveRichLines.source_rich_lines hq hI σ g n' a hσq hσ hg hghi
    hn' ha X hX F (fun A hA => hL A (Finset.mem_filter.mp hA).1)
    (fun A hA => by simpa only [hσq] using (Finset.mem_filter.mp hA).2) hcap
  rw [hσq] at hr
  have hsum : (∑ A ∈ L, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ)) ≤
      (F.card:ℝ)*((q:ℝ)+1) := by
    have he : (∑ A ∈ L, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ)) =
        ∑ A ∈ F, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A hA hn
      have hnrich : ¬n'*a/(q:ℝ) ≤ (X.filter fun y => y.submodule ≤ A).card := by
        intro hh
        exact hn (Finset.mem_filter.mpr ⟨hA,hh⟩)
      rw [centers_empty_of_not_rich X O (by positivity) A ?_,Finset.card_empty,Nat.cast_zero]
      intro hh
      apply hnrich
      apply (div_le_iff₀ hq0).mpr
      have hh' := (le_div_iff₀ hn0).mp (show a ≤
          (q:ℝ)*(X.filter fun y => y.submodule ≤ A).card/n' by simpa only [div_mul_eq_mul_div] using hh)
      nlinarith
    rw [he]
    calc
      _ ≤ ∑ _A ∈ F, ((q:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro A hA
        have hh := richCenters_card_le X O ((q:ℝ)/n') a A (hL A (Finset.mem_filter.mp hA).1)
        rw [hcard] at hh
        exact_mod_cast hh
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hr' : (F.card:ℝ)*n'*a ≤ 20814*Real.exp (3*σ/2+g)*(q:ℝ) := by
    have hh := (div_le_iff₀ hq0).mp (show (F.card:ℝ)*n'*a/(q:ℝ) ≤ _ by
      simpa only [mul_div_assoc,mul_assoc] using hr)
    simpa only [mul_div_assoc] using hh
  have hn : Real.exp (3*σ/2+g) ≤ 4*n' := by linarith
  have hr'' : (F.card:ℝ)*a ≤ 83256*(q:ℝ) := by
    have hh := hr'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hq0.le)
    nlinarith
  have hq1 : (q:ℝ)+1 ≤ 2*(q:ℝ) := by exact_mod_cast (by omega : q+1≤2*q)
  calc
    _ ≤ ((F.card:ℝ)*((q:ℝ)+1))*a^2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ = ((F.card:ℝ)*a)*(((q:ℝ)+1)*a) := by ring
    _ ≤ (83256*(q:ℝ))*((2*(q:ℝ))*2) := mul_le_mul hr''
      (mul_le_mul hq1 ha2 ha0.le (by positivity)) (by positivity) (by positivity)
    _ = _ := by ring

end SharpRamseyFive.GlobalRadial

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Training
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

lemma peel_subset (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk ⊆ X := by
  unfold peelSet
  split_ifs
  · exact retained_subset F hF shape X k hk
  · exact Finset.Subset.refl _

lemma peel_length_bound (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelLength e F hF shape X k hk*k≤X.card := by
  unfold peelLength
  split_ifs
  · exact list_length_bound F hF shape X k hk
  · simp

lemma peel_alternative (e : Prop) (he : e) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk = X\remaining F hF shape X (peelLength e F hF shape X k hk) ∨
    (peelLength e F hF shape X k hk=0 ∧ ∀i∈F,(peelSet e F hF shape X k hk∩shape i).card<k) := by
  by_cases hc : Captured F hF shape X k hk
  · left
    simp only [peelSet,ite_eq_left he,peelLength,ite_eq_left (And.intro he hc)]
    exact ite_eq_left hc
  · right
    refine ⟨by simp [peelLength,hc],?_⟩
    intro i hi
    simpa only [peelSet,ite_eq_left he] using residual_cap F hF shape X k hk hc i hi

lemma peel_length_real (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (t : ℝ) (ht : 0<t) :
    (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht):ℝ)*t≤X.card := by
  have hi := peel_length_bound e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  calc
    _ ≤ (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht):ℝ)*⌈t⌉₊ :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil t) (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast hi

lemma peel_residual_real (e : Prop) (he : e) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (t : ℝ) (ht : 0<t) :
    peelSet e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht) =
        X\remaining F hF shape X (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)) ∨
    (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)=0 ∧ ∀i∈F,
      ((peelSet e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)∩shape i).card:ℝ)<t) := by
  rcases peel_alternative e he F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht) with h|⟨hJ,hh⟩
  · exact Or.inl h
  · exact Or.inr ⟨hJ,fun i hi => Nat.lt_ceil.mp (hh i hi)⟩

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MomentWeightedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_weighted_cover (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (hx : ∀ v,0≤x v) (ha : ∀ i∈T,0≤a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i) :
    (∑ v,x v^K)≤2^K*∑ i∈T,
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K := by
  have hp (v : α) : x v^K≤∑ i∈T,if a i≤x v then (2*a i)^K else 0 := by
    by_cases hv : 0<x v
    · obtain ⟨i,hi,hix,hxi⟩:=hcover v hv
      apply (pow_le_pow_left₀ (hx v) hxi K).trans
      have hs:=Finset.single_le_sum (f := fun j => if a j≤x v then (2*a j)^K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa only [ite_eq_left hix] using hs
    · have hz : x v=0 := le_antisymm (le_of_not_gt hv) (hx v)
      rw [hz,zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hp v)).trans_eq
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ v,if a i≤x v then (2*a i)^K else 0)=
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*(2*a i)^K := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he,mul_pow]
  ring

end SharpRamseyFive.DyadicMoments

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_emptyEvent (s : Finset ι) : MeasurableSet (emptyEvent s) := by
  exact MeasurableSet.pi (s.finite_toSet.countable) (fun _ _ => measurableSet_singleton 0)

omit [DecidableEq ι] in
lemma measure_emptyEvent (rate : ι → ℝ≥0) (s : Finset ι) :
    batchMeasure rate (emptyEvent s) = ENNReal.ofReal (Real.exp (-mass rate s)) := by
  rw [batchMeasure, emptyEvent, Measure.pi_pi_finset]
  simp_rw [poissonMeasure_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl
omit [DecidableEq ι] in

lemma integral_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    ∫ ω, emptyIndicator s ω ∂batchMeasure rate = Real.exp (-mass rate s) := by
  simp only [emptyIndicator]
  rw [integral_indicator_const _ (measurableSet_emptyEvent s),
    Measure.real, measure_emptyEvent, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp
omit [DecidableEq ι] in

lemma integrable_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    Integrable (emptyIndicator s) (batchMeasure rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_emptyEvent s)

lemma one_sub_exp_neg_le (a : ℝ) : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_IntegralTypicalScoreSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

omit [DecidableEq ι] in
lemma integrable_schedule_of_abs_le (rate : ι → ℝ≥0) {R : ℕ}
    (f : (Fin R → ι → ℕ) → ℝ) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable f (scheduleMeasure rate R) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using h ω)

omit [Fintype ι] [DecidableEq ι] in
lemma hitIndicator_eq (i : ι) (ω : ι → ℕ) :
    hitIndicator i ω = if ω i = 0 then 0 else 1 := by
  simp only [hitIndicator, emptyIndicator, emptyEvent
    ]
  by_cases h : ω i = 0 <;> simp [h]
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_nonneg (i : ι) (ω : ι → ℕ) : 0 ≤ hitIndicator i ω := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_le_one (i : ι) (ω : ι → ℕ) : hitIndicator i ω ≤ 1 := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [DecidableEq ι] in

lemma integral_hitIndicator (rate : ι → ℝ≥0) (i : ι) :
    (∫ ω, hitIndicator i ω ∂batchMeasure rate) = 1 - Real.exp (-(rate i : ℝ)) := by
  unfold hitIndicator
  rw [integral_sub (integrable_const 1) (integrable_emptyIndicator rate {i}),
    integral_emptyIndicator]
  simp [mass]
omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_nonneg {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    0 ≤ forcedHits i T ω := Finset.prod_nonneg (fun _ _ => hitIndicator_nonneg _ _)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
omit [Fintype ι] [DecidableEq ι] in
lemma forcedHits_le_one {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    forcedHits i T ω ≤ 1 := Finset.prod_le_one (fun _ _ => hitIndicator_nonneg _ _)
      (fun _ _ => hitIndicator_le_one _ _)

omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_eq_one_of_subset {R : ℕ} (i : ι) (T : Finset (Fin R))
    (ω : Fin R → ι → ℕ) (h : T ⊆ hitBatches i ω) : forcedHits i T ω = 1 := by
  apply Finset.prod_eq_one
  intro r hr
  rw [hitIndicator_eq]
  have hz : ω r i ≠ 0 := (Finset.mem_filter.mp (h hr)).2
  simp [hz]
omit [Fintype ι] [DecidableEq ι] in

lemma overload_indicator_le_certificates {R : ℕ} (s : Finset ι) (J : ℕ)
    (ω : Fin R → ι → ℕ) :
    (overloaded s J).indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
  have hnonneg : ∀ i, 0 ≤ ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
    intro i
    exact Finset.sum_nonneg (fun T _ => forcedHits_nonneg i T ω)
  by_cases h : ω ∈ overloaded s J
  · rw [Set.indicator_of_mem h]
    obtain ⟨i, hi, hcard⟩ := h
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hcard
    have hTm : T ∈ (Finset.univ : Finset (Fin R)).powersetCard J := by
      simp only [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hTc⟩
    calc
      1 = forcedHits i T ω := (forcedHits_eq_one_of_subset i T ω hT).symm
      _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i U ω :=
        Finset.single_le_sum (fun U _ => forcedHits_nonneg i U ω) hTm
      _ ≤ _ := Finset.single_le_sum (fun i _ => hnonneg i) hi
  · rw [Set.indicator_of_notMem h]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)

omit [DecidableEq ι] in
lemma measurePreserving_uncurry_schedule (rate : ι → ℝ≥0) (R : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin R) ι ℕ).symm
      (scheduleMeasure rate R) (batchMeasure (fun p : Fin R × ι => rate p.2)) := by
  refine ⟨(MeasurableEquiv.curry (Fin R) ι ℕ).symm.measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi, scheduleMeasure, batchMeasure] using
    Measure.infinitePi_map_curry_symm (fun (_ : Fin R) i => poissonMeasure (rate i))

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.DyadicMoments

open scoped BigOperators

lemma dyadic_cover (δ x : ℝ) (hδ : 0 ≤ δ) (hx : δ ≤ x) (N : ℕ)
    (hN : x ≤ δ * 2 ^ N) :
    ∃ i ∈ Finset.range (N + 1), δ * 2 ^ i ≤ x ∧ x ≤ 2 * (δ * 2 ^ i) := by
  induction N with
  | zero =>
    refine ⟨0, by simp, ?_, ?_⟩
    · simpa using hx
    · simp only [pow_zero, mul_one] at hN ⊢
      linarith
  | succ N ih =>
    by_cases hh : x ≤ δ * 2 ^ N
    · obtain ⟨i, hi, hix, hxi⟩ := ih hh
      exact ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), hix, hxi⟩
    · refine ⟨N, Finset.mem_range.mpr (by omega), le_of_lt (lt_of_not_ge hh), ?_⟩
      rw [pow_succ] at hN
      nlinarith

end SharpRamseyFive.DyadicMoments

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (A : ℝ) (hx : ∀ v,0 ≤ x v) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i ≤ x v ∧ x v ≤ 2*a i)
    (hcount : ∀ i∈T,((Finset.univ.filter fun v => a i ≤ x v).card:ℝ)*a i^K ≤ A) :
    (∑ v,x v^K) ≤ 2^K*T.card*A := by
  apply (moment_weighted_cover x a T K hK hx ha hcover).trans
  have hh := Finset.sum_le_sum (fun i hi => hcount i hi)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

theorem pow_sum_from_lower (x : α → ℝ) (m A : ℝ) (K R : ℕ) (hm0 : 0 ≤ m) (hKR : K ≤ R)
    (hx : ∀ v,0 ≤ x v) (hm : ∀ v,x v ≤ m) (hA : (∑ v,x v^K) ≤ A) :
    (∑ v,x v^R) ≤ m^(R-K)*A := by
  have hpow (v : α) : x v^R ≤ m^(R-K)*x v^K := by
    have he : R=(R-K)+K := by omega
    calc
      _ = x v^(R-K)*x v^K := by rw [←pow_add,←he]
      _  ≤  _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hx v) (hm v) _) (pow_nonneg (hx v) _)
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpow v)).trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hA (pow_nonneg hm0 _)

end SharpRamseyFive.DyadicMoments

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LocalLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma sum_localLines_le (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V)) :
    ∑ x ∈ Q, (localLines S O δ a L x).card ≤
      ∑ A ∈ L, (richCenters S O δ a A).card := by
  simp_rw [localLines,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  rw [←Finset.card_filter]
  have hs : Q.filter (fun x => x ∈ richCenters S O δ a A) ⊆ richCenters S O δ a A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  exact Finset.card_le_card hs

end SharpRamseyFive.GlobalRadial
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_filter_card (S O : Finset (ℙ K V)) (A : Submodule K V) :
    ((outsideAt x S O).filter fun y => y.val.submodule ≤ A).card =
      ((S \ (O ∪ {x})).filter fun y => y.submodule ≤ A).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    have hm : y.val ∈ S \ O := Finset.mem_subtype.mp hy
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton]
    exact ⟨⟨(Finset.mem_sdiff.mp hm).1,not_or.mpr
      ⟨(Finset.mem_sdiff.mp hm).2,Ne.symm y.property⟩⟩,hyA⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
    have hn : x ≠ y := by
      intro he
      exact hyO (Finset.mem_union_right _ (Finset.mem_singleton.mpr he.symm))
    refine ⟨⟨y,hn⟩,Finset.mem_filter.mpr ⟨?_,hyA⟩,rfl⟩
    exact Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr
      ⟨hyS,fun h => hyO (Finset.mem_union_left _ h)⟩)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OutsideCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_card_le (S O : Finset (ℙ K V)) : (outsideAt x S O).card ≤ S.card := by
  unfold outsideAt
  rw [Finset.card_subtype]
  exact (Finset.card_filter_le _ _).trans (Finset.card_le_card Finset.sdiff_subset)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TrainingLineCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma training_line_card (X : Finset {y : ℙ K V // x≠y}) (l : RadialLine x) :
    (RadialLine.trainingOnLine X l).card ≤ Nat.card K+1 := by
  let : Finite V := Module.finite_of_finite K
  let f (y : RadialLine.trainingOnLine X l) : {p : ℙ K V // p.submodule ≤ l.val} :=
    ⟨y.val.val,(Finset.mem_filter.mp y.property).2⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : {p : ℙ K V // p.submodule ≤ l.val} => u.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [card_subspacePoints,l.property.1,Nat.card_eq_fintype_card,Fintype.card_coe] at hc
  simpa [Finset.sum_range_succ,Nat.add_comm] using hc

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveHighCapturedMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma radial_bounded_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (M : ℝ) (hmax : ∀ l : RadialLine x,(radialWeight x X δ l:ℝ) ≤ M)
    (l : RadialLine x) (hp : 0 < (radialWeight x X δ l:ℝ)) :
    ∃ i∈boundedOverlapDyads x X δ M,
      (δ:ℝ)*2^i ≤ (radialWeight x X δ l:ℝ) ∧
      (radialWeight x X δ l:ℝ) ≤ 2*((δ:ℝ)*2^i) := by
  have hc : 0 < (RadialLine.trainingOnLine X l).card := by
    by_contra hn
    have hz : (RadialLine.trainingOnLine X l).card=0 := by omega
    simp [radialWeight,hz] at hp
  have hfloor : (δ:ℝ) ≤ (radialWeight x X δ l:ℝ) := by
    have hh : (1:ℝ) ≤ (RadialLine.trainingOnLine X l).card := by exact_mod_cast hc
    simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast,mul_one] using
      mul_le_mul_of_nonneg_left hh δ.coe_nonneg
  have hbound : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*2^Nat.clog 2 X.card := by
    have hh : (RadialLine.trainingOnLine X l).card ≤ 2^Nat.clog 2 X.card :=
      (Finset.card_filter_le _ _).trans (Nat.le_pow_clog (by norm_num) X.card)
    change (δ:ℝ)*((RadialLine.trainingOnLine X l).card:ℝ) ≤ (δ:ℝ)*(2:ℝ)^Nat.clog 2 X.card
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) δ.coe_nonneg
  obtain ⟨i,hi,hlo,hhi⟩ := dyadic_cover δ _ δ.coe_nonneg hfloor _ hbound
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (hmax l)⟩,hlo,hhi⟩

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentCutoffPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_cutoff_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (θ M A : ℝ) (K R : ℕ) (hK : K≠0) (hKR : K≤R)
    (hθ : 0≤θ) (hM : 0≤M) (hA : 0≤A)
    (hx : ∀ v,0≤x v) (hmax : ∀ v,x v≤M) (ha : ∀ i∈T,0<a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i)
    (htail : ∀ i∈T,θ≤2*a i →
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K≤A) :
    (∑ v,x v^R) ≤ (Fintype.card α:ℝ)*θ^R + M^(R-K)*(2^K*T.card*A) := by
  let y (v : α) : ℝ := if θ≤x v then x v else 0
  let U := T.filter fun i => θ≤2*a i
  have hy (v : α) : 0≤y v := by dsimp [y]; split_ifs; exact hx v; rfl
  have hym (v : α) : y v≤M := by dsimp [y]; split_ifs; exact hmax v; exact hM
  have hbase : (∑ v,y v^K) ≤ 2^K*U.card*A := by
    apply moment_polynomial_tail y a U K hK A hy
      (fun i hi => (ha i (Finset.mem_filter.mp hi).1).le)
    · intro v hv
      have hv' : θ≤x v := by by_contra hn; simp [y,hn] at hv
      have hpos : 0<x v := by simpa [y,hv'] using hv
      obtain ⟨i,hi,hlo,hhi⟩ := hcover v hpos
      exact ⟨i,Finset.mem_filter.mpr ⟨hi,hv'.trans hhi⟩,by simpa [y,hv'] using hlo,
        by simpa [y,hv'] using hhi⟩
    · intro i hi
      have hiT := (Finset.mem_filter.mp hi).1
      have hc : (Finset.univ.filter fun v => a i≤y v).card ≤
          (Finset.univ.filter fun v => a i≤x v).card := by
        apply Finset.card_le_card
        intro v hv
        have hv' := (Finset.mem_filter.mp hv).2
        have hyx : y v≤x v := by dsimp [y]; split_ifs; rfl; exact hx v
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv'.trans hyx⟩
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc)
        (pow_nonneg (ha i hiT).le K)).trans (htail i hiT (Finset.mem_filter.mp hi).2)
  have hbase' : (∑ v,y v^K) ≤ 2^K*T.card*A := by
    apply hbase.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.card_filter_le T _)) (by positivity)) hA
  have hhi := pow_sum_from_lower y M _ K R hM hKR hy hym hbase'
  have hpoint (v : α) : x v^R ≤ θ^R+y v^R := by
    by_cases hv : θ≤x v
    · simpa [y,hv] using (le_add_of_nonneg_left (a := x v^R) (pow_nonneg hθ R))
    · have hp := pow_le_pow_left₀ (hx v) (le_of_not_ge hv) R
      exact hp.trans (le_add_of_nonneg_right (pow_nonneg (hy v) R))
  calc
    _ ≤ ∑ v,(θ^R+y v^R) := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = (Fintype.card α:ℝ)*θ^R+∑ v,y v^R := by simp [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add_right hhi _

end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma radial_tail_le_localLines (x : ℙ K V) [Fintype (RadialLine x)]
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (hLines : ∀ l : RadialLine x,l.val∈Lines) :
    (Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)).card ≤
      (localLines S O δ a Lines x).card := by
  let A := Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)
  let E := localLines S O δ a Lines x
  let f (l : A) : E := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hLines l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      change a ≤ (δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule ≤ l.val.val).card:ℝ) at hr
      rwa [outsideAt_filter_card] at hr⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : E => z.val) he))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [∀ x : ℙ K V,Fintype (RadialLine x)]

lemma global_radial_tail (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines) :
    (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
      a ≤ (radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2:ℝ)).card ≤
      ∑ A∈Lines,(richCenters S O δ a A).card := by
  have he : (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
      a ≤ (radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2:ℝ)).card =
      ∑ x : Q,(Finset.univ.filter fun l : RadialLine x.val =>
        a ≤ (radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)).card := by
    simp only [Finset.card_filter,Fintype.sum_sigma]
  rw [he]
  calc
    _ ≤ ∑ x : Q,(localLines S O δ a Lines x.val).card :=
      Finset.sum_le_sum fun x _ => radial_tail_le_localLines x.val S O δ a Lines (hLines x.val x.property)
    _ = ∑ x∈Q,(localLines S O δ a Lines x).card := Finset.sum_coe_sort Q (fun x => (localLines S O δ a Lines x).card)
    _ ≤ _ := sum_localLines_le S O δ a Lines Q

theorem global_radial_moment (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0<δ) (θ A : ℝ) (hθ : 0≤θ) (hA : 0≤A)
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (htail : ∀ i∈Finset.range (Nat.clog 2 S.card+1),θ≤2*((δ:ℝ)*2^i) →
      (δ:ℝ)*2^i≤(δ:ℝ)*((Nat.card K:ℝ)+1) →
      (∑ l∈Lines,((richCenters S O δ ((δ:ℝ)*2^i) l).card:ℝ))*((δ:ℝ)*2^i)^2≤A)
    (J : ℕ) (hJ : 2≤J) :
    (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) ≤
      (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))*θ^J+
        ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-2)*(4*(Nat.clog 2 S.card+1)*A) := by
  let w (z : Σ x : Q,RadialLine x.val) : ℝ :=
    radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2
  have hw (z : Σ x : Q,RadialLine x.val) : 0≤w z := NNReal.coe_nonneg _
  have hmax (z : Σ x : Q,RadialLine x.val) : w z≤(δ:ℝ)*((Nat.card K:ℝ)+1) := by
    have hc := training_line_card z.1.val (outsideAt z.1.val S (O z.1.val)) z.2
    change (δ:ℝ)*((RadialLine.trainingOnLine _ _).card:ℝ) ≤ _
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) δ.coe_nonneg
  have hcS (x : ℙ K V) : (outsideAt x S (O x)).card≤S.card := outsideAt_card_le x S (O x)
  have hcover (z : Σ x : Q,RadialLine x.val) (hp : 0<w z) :
      ∃ i∈Finset.range (Nat.clog 2 S.card+1),(δ:ℝ)*2^i≤w z ∧ w z≤2*((δ:ℝ)*2^i) := by
    obtain ⟨i,hi,hlo,hhi⟩ := radial_bounded_cover z.1.val (outsideAt z.1.val S (O z.1.val)) δ
      ((δ:ℝ)*((Nat.card K:ℝ)+1)) (fun l => hmax ⟨z.1,l⟩) z.2 hp
    refine ⟨i,?_,hlo,hhi⟩
    have hir := (Finset.mem_filter.mp hi).1
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hir
    exact lt_of_lt_of_le this (Nat.add_le_add_right (Nat.clog_mono_right 2 (hcS z.1.val)) 1)
  have hh := moment_cutoff_polynomial_tail w (fun i : ℕ => (δ:ℝ)*2^i)
    (Finset.range (Nat.clog 2 S.card+1)) θ ((δ:ℝ)*((Nat.card K:ℝ)+1)) A 2 J
    (by norm_num) hJ hθ (by positivity) hA hw hmax
    (by intro i _; positivity) hcover (by
      intro i hi hcut
      by_cases hcap : (δ:ℝ)*2^i≤(δ:ℝ)*((Nat.card K:ℝ)+1)
      · have ht := global_radial_tail S O δ ((δ:ℝ)*2^i) Lines Q hLines
        have htr : ((Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
            (δ:ℝ)*2^i≤w z).card:ℝ) ≤
            ∑ l∈Lines,((richCenters S O δ ((δ:ℝ)*2^i) l).card:ℝ) := by
          exact_mod_cast ht
        exact (mul_le_mul_of_nonneg_right htr (sq_nonneg _)).trans (htail i hi hcut hcap)
      · have he : (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val => (δ:ℝ)*2^i≤w z)=∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro z hz
          exact hcap ((Finset.mem_filter.mp hz).2.trans (hmax z))
        simpa only [he,Finset.card_empty,Nat.cast_zero,zero_mul] using hA)
  simpa only [Fintype.sum_sigma,Finset.card_range,Nat.cast_add,Nat.cast_one,
    Fintype.card_sigma,Nat.cast_sum,show (2:ℝ)^2=4 by norm_num] using hh

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_IntegralForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma integral_forcedHits_le (rate : D→ℝ≥0) {R : ℕ} (d : D) (T : Finset (Fin R)) :
    (∫ ω,forcedHits d T ω ∂scheduleMeasure rate R) ≤ (rate d:ℝ)^T.card := by
  have he (ω : Fin R→D→ℕ) : forcedHits d T ω =
      ∏ r : Fin R,if r∈T then hitIndicator d (ω r) else 1 := by
    simp only [Finset.prod_ite_mem,Finset.univ_inter,forcedHits]
  simp_rw [he]
  unfold scheduleMeasure
  rw [integral_fintype_prod_eq_prod (f := fun r ω => if r∈T then hitIndicator d ω else 1)]
  have he' (r : Fin R) : (∫ ω : D→ℕ,(if r∈T then hitIndicator d ω else 1) ∂batchMeasure rate) =
      if r∈T then 1-Real.exp (-(rate d:ℝ)) else 1 := by
    split_ifs <;> simp [integral_hitIndicator]
  simp_rw [he']
  simp only [Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_const]
  exact pow_le_pow_left₀ (by have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rate d).coe_nonneg); linarith)
    (one_sub_exp_neg_le (rate d:ℝ)) _

omit [DecidableEq D] in
theorem overload_probability (rate : D→ℝ≥0) {R : ℕ} (s : Finset D) (J : ℕ) :
    (scheduleMeasure rate R).real (overloaded s J) ≤ ∑ d∈s,((R:ℝ)*(rate d:ℝ))^J := by
  have hint := integrable_schedule_of_abs_le (R := R) rate
    ((overloaded s J).indicator (fun _ => (1:ℝ))) 1 (by
      intro ω; by_cases he : ω∈overloaded s J <;> simp [he])
  have hf (d : D) (T : Finset (Fin R)) : Integrable (forcedHits d T) (scheduleMeasure rate R) :=
    integrable_schedule_of_abs_le rate _ 1 (fun ω => by
      rw [abs_of_nonneg (forcedHits_nonneg d T ω)]; exact forcedHits_le_one d T ω)
  have hset : MeasurableSet (overloaded s J : Set (Fin R→D→ℕ)) := Set.to_countable _ |>.measurableSet
  have heq := integral_indicator_const (μ := scheduleMeasure rate R) (1:ℝ) hset
  simp only [smul_eq_mul,mul_one] at heq
  rw [←heq]
  calc
    _ ≤ ∫ ω,∑ d∈s,∑ T∈(Finset.univ : Finset (Fin R)).powersetCard J,forcedHits d T ω
        ∂scheduleMeasure rate R := integral_mono hint
          (integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun T _ => hf d T)))
          (overload_indicator_le_certificates s J)
    _ = ∑ d∈s,∑ T∈(Finset.univ : Finset (Fin R)).powersetCard J,
        ∫ ω,forcedHits d T ω ∂scheduleMeasure rate R := by
      rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun T _ => hf d T))]
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_finsetSum _ (fun T _ => hf d T)]
    _ ≤ ∑ d∈s,((R:ℝ)*(rate d:ℝ))^J := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        _ ≤ ∑ _T∈(Finset.univ : Finset (Fin R)).powersetCard J,(rate d:ℝ)^J :=
          Finset.sum_le_sum fun T hT => by
            simpa only [(Finset.mem_powersetCard.mp hT).2] using integral_forcedHits_le rate d T
        _ = (R.choose J:ℝ)*(rate d:ℝ)^J := by simp
        _ ≤ _ := by
          rw [mul_pow]
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (rate d).coe_nonneg _)
          exact_mod_cast Nat.choose_le_pow R J

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory PoissonScore TupleComponents
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma allTrunc_indicator (R J : ℕ) (ω : Fin R→D→ℕ) :
    1-allTrunc R J (Function.uncurry ω) =
      (overloaded Finset.univ J).indicator (fun _ => (1:ℝ)) ω := by
  by_cases he : ω∈(overloaded Finset.univ J : Set (Fin R→D→ℕ))
  · rw [Set.indicator_of_mem he]
    obtain ⟨d,_,hd⟩ := he
    have hz : allTrunc R J (Function.uncurry ω)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      exact ite_eq_right (by exact not_lt.mpr hd)
    rw [hz,sub_zero]
  · rw [Set.indicator_of_notMem he]
    have ho : allTrunc R J (Function.uncurry ω)=1 := by
      apply Finset.prod_eq_one
      intro d _
      apply ite_eq_left
      by_contra hn
      exact he ⟨d,Finset.mem_univ _,le_of_not_gt hn⟩
    rw [ho,sub_self]

omit [DecidableEq D] in
theorem allTrunc_failure (rate : D→ℝ≥0) (R J : ℕ) :
    (∫ ω,1-allTrunc R J ω ∂batchMeasure (fun p : Fin R×D => rate p.2)) ≤
      ∑ d : D,((R:ℝ)*(rate d:ℝ))^J := by
  rw [←(measurePreserving_uncurry_schedule rate R).integral_comp' (fun ω => 1-allTrunc R J ω)]
  change (∫ ω,1-allTrunc R J (Function.uncurry ω) ∂scheduleMeasure rate R) ≤ _
  simp_rw [allTrunc_indicator]
  have hset : MeasurableSet (overloaded Finset.univ J : Set (Fin R→D→ℕ)) := Set.to_countable _ |>.measurableSet
  rw [integral_indicator_const (1:ℝ) hset]
  simp only [smul_eq_mul,mul_one]
  exact overload_probability rate Finset.univ J

end SharpRamseyFive.HighMoment

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CapturedGlobalRadialMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀ x : ℙ K V,Fintype (RadialLine x)]

open MeasureTheory

omit [FiniteDimensional K V] [Finite K] in
theorem global_trunc_failure (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ L : ℝ≥0) (Q : Finset (ℙ K V)) (R J : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val S (O x.val)) δ p.2)) ≤
      ((R:ℝ)*(L:ℝ))^J*
        (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) := by
  calc
    _ ≤ ∑ x : Q,∑ l : RadialLine x.val,((R:ℝ)*
        ((L*radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ≥0):ℝ))^J :=
      Finset.sum_le_sum fun x _ => HighMoment.allTrunc_failure
        (fun l => L*radialWeight x.val (outsideAt x.val S (O x.val)) δ l) R J
    _ = _ := by
      simp only [NNReal.coe_mul,←mul_assoc,mul_pow,Finset.mul_sum]

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I : Type} [Field K] [Finite K] [Fintype I]
  [∀ x : ℙ K (I→K),Fintype (RadialLine x)]

theorem residual_global_radial_moment {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g n' θ : ℝ) (hσq : Real.exp σ=q) (hσ : 1000≤σ)
    (hg : 100000000≤g) (hghi : g≤2*σ) (hn' : Real.exp (3*σ/2+g)/4≤n')
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ)≤Real.exp (3*σ/2+g))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (δ : ℝ≥0) (hδ : 0<δ) (hδeq : (δ:ℝ)=(q:ℝ)/n')
    (hmax : (δ:ℝ)*((q:ℝ)+1)≤2) (hθ : 2*Real.exp (-g/20)≤θ)
    (Lines : Finset (Submodule K (I→K))) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (hcap : ∀ U : Submodule K (I→K),finrank K U=3 →
      ((X.filter fun y => y.submodule≤U).card:ℝ)≤
        (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (J : ℕ) (hJ : 2≤J) :
    (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val X (O x.val)) δ l:ℝ)^J) ≤
      (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))*θ^J+
        ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-2)*
          (4*(Nat.clog 2 X.card+1)*(333024*(q:ℝ)^2)) := by
  have hθ0 : 0≤θ := (by positivity : 0≤2*Real.exp (-g/20)).trans hθ
  apply global_radial_moment X O δ hδ θ _ hθ0 (by positivity) Lines Q hLines _ J hJ
  intro i hi hcut hamax
  have ha : Real.exp (-g/20)≤(δ:ℝ)*2^i := by linarith
  have ha2 : (δ:ℝ)*2^i≤2 := hamax.trans (by simpa only [hcard] using hmax)
  have ht := residual_rich_centers hq hcard hI σ g n' ((δ:ℝ)*2^i) hσq hσ hg hghi hn'
    ha ha2 X hX Lines hrank O hcap
  simpa only [←hδeq] using ht

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DyadCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma dyad_count_le {m : ℕ} {σ : ℝ} (hσ : 1≤σ)
    (hm : (m:ℝ)≤Real.exp (3*σ)) : (Nat.clog 2 m:ℝ)+1≤8*σ := by
  by_cases hm1 : m≤1
  · rw [Nat.clog_of_right_le_one hm1]
    simp only [Nat.cast_zero,zero_add]
    linarith
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hml : 0≤Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmlhi : Real.log (m:ℝ)≤3*σ := (Real.log_le_iff_le_exp hm0).mpr hm
  have hlog : Real.logb 2 (m:ℝ)≤6*σ := by
    rw [Real.logb]
    apply (div_le_iff₀ (by linarith : 0<Real.log 2)).mpr
    nlinarith
  have hc := Nat.ceil_lt_add_one (show 0≤Real.logb 2 (m:ℝ) by
    rw [Real.logb]; exact div_nonneg hml (by linarith))
  have he := Real.natCeil_logb_natCast 2 m
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hc
  linarith

theorem eventually_global_trunc_scalar {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (C : ℝ) (hC : 0<C) :
    ∀ᶠ σ : ℝ in atTop,∀ D R g : ℝ,Range η σ D R → P η σ D R/10000≤g →
      C*(P η σ D R)^5000*Real.exp (8*σ-250*(g+σ/2))+
        C*(P η σ D R)^5000*σ*Real.exp (2*σ-4998*g)≤Real.exp (2*σ) := by
  have habs := eventually_power_absorption hη hη' (2*C) 5001 (1/10)
    (by positivity) (by norm_num) (by norm_num)
  have hsmall := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),habs,hsmall] with σ hσ habs hsmall
  intro D R g hr hg
  have hpar := finite_bounds hη hη' hσ hr
  have hD := hpar.1
  have hL : 0<L η σ D := by dsimp [L]; positivity
  have hP : 0<P η σ D R := mul_pos hL hpar.2.1
  have hPσ : P η σ D R≤σ := by
    have hh := hsmall D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hg0 : 0≤g := (by positivity : 0≤P η σ D R/10000).trans hg
  have hab : 2*C*σ^(5001:ℕ)≤Real.exp (P η σ D R/10) := by
    have hh := habs D R hr
    rw [show σ^(5001:ℝ)=σ^(5001:ℕ) from Real.rpow_natCast σ 5001] at hh
    simpa only [one_div,one_mul,mul_comm (10⁻¹:ℝ),div_eq_mul_inv] using hh
  have hpow : (P η σ D R)^5000≤σ^5000 := pow_le_pow_left₀ hP.le hPσ _
  have hcoeff2 : 2*(C*(P η σ D R)^5000*σ)≤Real.exp (P η σ D R/10) := by
    calc
      _ = 2*C*(P η σ D R)^5000*σ := by ring
      _ ≤ 2*C*σ^5000*σ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by linarith)
      _ = 2*C*σ^5001 := by rw [pow_succ]; ring
      _ ≤ _ := hab
  have hcoeff1 : 2*(C*(P η σ D R)^5000)≤Real.exp (P η σ D R/10) := by
    apply le_trans _ hcoeff2
    nlinarith [mul_nonneg (by positivity : 0≤C*(P η σ D R)^5000) (sub_nonneg.mpr hσ)]
  have h1 : 2*(C*(P η σ D R)^5000*Real.exp (8*σ-250*(g+σ/2)))≤Real.exp (2*σ) := by
    calc
      _ = (2*(C*(P η σ D R)^5000))*Real.exp (8*σ-250*(g+σ/2)) := by ring
      _ ≤ Real.exp (P η σ D R/10)*Real.exp (8*σ-250*(g+σ/2)) :=
        mul_le_mul_of_nonneg_right hcoeff1 (Real.exp_nonneg _)
      _ = Real.exp (P η σ D R/10+(8*σ-250*(g+σ/2))) := (Real.exp_add ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have h2 : 2*(C*(P η σ D R)^5000*σ*Real.exp (2*σ-4998*g))≤Real.exp (2*σ) := by
    calc
      _ = (2*(C*(P η σ D R)^5000*σ))*Real.exp (2*σ-4998*g) := by ring
      _ ≤ Real.exp (P η σ D R/10)*Real.exp (2*σ-4998*g) :=
        mul_le_mul_of_nonneg_right hcoeff2 (Real.exp_nonneg _)
      _ = Real.exp (P η σ D R/10+(2*σ-4998*g)) := (Real.exp_add ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometryScaleOrientedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

open Filter ParameterHierarchy
open scoped Topology

lemma globalTruncConstant_pos : 0<globalTruncConstant := by
  unfold globalTruncConstant
  exact add_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _))
    (mul_pos (by norm_num) (pow_pos (by norm_num) _))

lemma global_radial_numeric {σ g N M A θ : ℝ} {m : ℕ}
    (hσ : 1≤σ) (_hN0 : 0≤N) (hM0 : 0≤M) (hA0 : 0≤A) (hθ0 : 0≤θ)
    (hN : N≤4*Real.exp (8*σ)) (hM : M≤8*Real.exp (-g))
    (hA : A≤333024*Real.exp (2*σ))
    (hθ : θ≤2*Real.exp (-(g+σ/2)/20)) (hm : (m:ℝ)≤Real.exp (3*σ)) :
    N*θ^5000+M^4998*(4*((Nat.clog 2 m:ℝ)+1)*A) ≤
      globalTruncConstant*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*σ*Real.exp (2*σ-4998*g) := by
  have hc1 : 4*(2:ℝ)^5000≤globalTruncConstant := by
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hc2 : 32*333024*(8:ℝ)^4998≤globalTruncConstant := by
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hdy := dyad_count_le hσ hm
  apply add_le_add
  · calc
      _ ≤ (4*Real.exp (8*σ))*(2*Real.exp (-(g+σ/2)/20))^5000 :=
        mul_le_mul hN (pow_le_pow_left₀ hθ0 hθ _) (pow_nonneg hθ0 _) (by positivity)
      _ = (4*2^(5000:ℕ))*Real.exp (8*σ-250*(g+σ/2)) := by
        rw [mul_pow,←Real.exp_nat_mul]
        simp only [Nat.cast_ofNat]
        rw [show 4*Real.exp (8*σ)*(2^(5000:ℕ)*Real.exp (5000*(-(g+σ/2)/20))) =
          (4*2^(5000:ℕ))*(Real.exp (8*σ)*Real.exp (5000*(-(g+σ/2)/20))) by ac_rfl]
        rw [←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc1 (Real.exp_nonneg _)
  · calc
      _ ≤ (8*Real.exp (-g))^4998*(4*(8*σ)*(333024*Real.exp (2*σ))) := by
        apply mul_le_mul (pow_le_pow_left₀ hM0 hM _) _ (by positivity) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hdy (by norm_num)) hA hA0 (by positivity)
      _ = (32*333024*8^(4998:ℕ))*σ*Real.exp (2*σ-4998*g) := by
        rw [mul_pow,←Real.exp_nat_mul]
        simp only [Nat.cast_ofNat]
        rw [show 8^(4998:ℕ)*Real.exp (4998*(-g))*(4*(8*σ)*(333024*Real.exp (2*σ))) =
          (32*333024*8^(4998:ℕ))*σ*(Real.exp (2*σ)*Real.exp (4998*(-g))) by
            rw [show (32:ℝ)=4*8 by norm_num]
            ac_rfl]
        rw [←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (by linarith)) (Real.exp_nonneg _)

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighGeometryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma RadialLine.exists_other (x : ℙ K V) (l : RadialLine x) :
    ∃ y : ℙ K V,x≠y ∧ y.submodule≤l.val := by
  have hn : ¬l.val≤x.submodule := by
    intro h
    have hh := Submodule.finrank_mono h
    rw [l.property.1,x.finrank_submodule] at hh
    omega
  obtain ⟨v,hv,hvx⟩ := SetLike.not_le_iff_exists.mp hn
  have hv0 : v≠0 := by intro he; exact hvx (he▸x.submodule.zero_mem)
  refine ⟨Projectivization.mk K v hv0,?_,?_⟩
  · intro he
    apply hvx
    rw [he,Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self v
  · rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    exact hv

omit [Finite K] in
lemma radial_card_le_points (x : ℙ K V) [Fintype (ℙ K V)] [Fintype (RadialLine x)] :
    Fintype.card (RadialLine x)≤Fintype.card (ℙ K V) := by
  let y : RadialLine x→ℙ K V := fun l => (l.exists_other x).choose
  have hy (l : RadialLine x) : x≠y l ∧ (y l).submodule≤l.val :=
    (l.exists_other x).choose_spec
  apply Fintype.card_le_of_injective y
  intro l m he
  have hl : RadialLine.through x (y l) (hy l).1=l :=
    (RadialLine.through_eq_iff (hy l).1 l).mpr (hy l).2
  have hm : RadialLine.through x (y l) (hy l).1=m :=
    (RadialLine.through_eq_iff (hy l).1 m).mpr (he▸(hy m).2)
  exact hl.symm.trans hm

lemma center_radial_count_le [Fintype (ℙ K V)] [∀ x : ℙ K V,Fintype (RadialLine x)]
    {d : ℕ} (hdim : finrank K V=d+1) (hq : 2≤Nat.card K)
    (Q : Finset (ℙ K V)) :
    (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))≤4*(Nat.card K:ℝ)^(2*d) := by
  have hcard := projective_card_le_two_pow hdim hq
  have hQ : Q.card≤2*Nat.card K^d := (Finset.card_le_univ Q).trans hcard
  calc
    _ ≤ ∑ _x : Q,(2*(Nat.card K:ℝ)^d) := Finset.sum_le_sum fun x _ => by
      exact_mod_cast (radial_card_le_points x.val).trans hcard
    _ = (Q.card:ℝ)*(2*(Nat.card K:ℝ)^d) := by simp
    _ ≤ (2*(Nat.card K:ℝ)^d)*(2*(Nat.card K:ℝ)^d) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (by positivity)
    _ = _ := by rw [mul_comm 2 d,pow_mul]; ring

end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.ScoreGeometry

section
open Filter ParameterHierarchy
open scoped Topology

lemma high_density_bounds {σ g q n δ X : ℝ} (hσ : 0≤σ) (hδ : 0≤δ)
    (hq : q=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hX0 : 0≤X) (hX : X≤n) (hscale : n*δ≤4*q) :
    δ*(q+1)≤8*Real.exp (-g) ∧ 192*δ^2*X^2≤333024*Real.exp (2*σ) := by
  have hq1 : 1≤q := hq▸Real.one_le_exp_iff.mpr hσ
  have hn0 : 0<n := hn▸Real.exp_pos _
  have hq2 : q^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul]; norm_num
  have he : n*(4*Real.exp (-g))=4*q^2 := by
    rw [hn,hq2,mul_left_comm,←Real.exp_add]
    congr 2
    ring
  have hδq : δ*q≤4*Real.exp (-g) := by
    apply (mul_le_mul_iff_right₀ hn0).mp
    calc
      _ = (n*δ)*q := by ring
      _ ≤ (4*q)*q := mul_le_mul_of_nonneg_right hscale (by linarith)
      _ = _ := by rw [he]; ring
  constructor
  · calc
      _ ≤ 2*(δ*q) := by nlinarith
      _ ≤ 2*(4*Real.exp (-g)) := mul_le_mul_of_nonneg_left hδq (by norm_num)
      _ = _ := by ring
  · have hdX : δ*X≤4*q := (mul_le_mul_of_nonneg_left hX hδ).trans (by simpa only [mul_comm] using hscale)
    have hs := pow_le_pow_left₀ (mul_nonneg hδ hX0) hdX 2
    rw [mul_pow,mul_pow] at hs
    rw [←hq2]
    nlinarith [sq_nonneg q]

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I : Type} [Fintype I] [Field K] [Finite K]
  [∀ x : ℙ K (I→K),Fintype (RadialLine x)]

theorem residual_global_trunc_exp_bound_dim {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=5)
    (σ g n' : ℝ) (hqexp : (q:ℝ)=Real.exp σ) (hσ : 1000≤σ)
    (hglo : 100000000≤g+σ/2) (hg : g≤σ)
    (hn' : Real.exp (2*σ+g)/4≤n')
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ)≤Real.exp (2*σ+g))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (δ L : ℝ≥0) (hδ : 0<δ) (hδeq : (δ:ℝ)=(q:ℝ)/n')
    (hmax : (δ:ℝ)*((q:ℝ)+1)≤2)
    (Lines : Finset (Submodule K (I→K))) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (hcap : ∀ U : Submodule K (I→K),finrank K U=3 →
      ((X.filter fun y => y.submodule≤U).card:ℝ)≤
        (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5))
    (R : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val X (O x.val)) δ p.2)) ≤
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*σ*Real.exp (2*σ-4998*g) := by
  let : Fintype (ℙ K (I→K)) := Fintype.ofFinite _
  have he : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hN := center_radial_count_le (K:=K) (V:=I→K) (d:=4)
    (show finrank K (I→K)=5 by rw [Module.finrank_pi,hI]) (show 2≤Nat.card K by omega) Q
  norm_num only [show 2*4=8 from rfl] at hN
  have heq : (Nat.card K:ℝ)^8=Real.exp (8*σ) := by
    rw [hcard,hqexp,←Real.exp_nat_mul]; norm_num
  rw [heq] at hN
  have hnpos : 0<n' := (by positivity : 0<Real.exp (2*σ+g)/4).trans_le hn'
  have hscale : Real.exp (2*σ+g)*(δ:ℝ)≤4*(q:ℝ) := by
    have hnδ : n'*(δ:ℝ)=(q:ℝ) := by rw [hδeq, mul_div_cancel₀ _ hnpos.ne']
    calc
      _ ≤ (4*n')*(δ:ℝ) := mul_le_mul_of_nonneg_right (by linarith only [hn']) δ.coe_nonneg
      _ = _ := by rw [mul_assoc,hnδ]
  have hdens := high_density_bounds (by linarith : 0≤σ) δ.coe_nonneg hqexp rfl
    (Nat.cast_nonneg X.card) hX hscale
  have hm : (X.card:ℝ)≤Real.exp (3*σ) :=
    hX.trans (Real.exp_le_exp.mpr (by linarith only [hσ, hg]))
  have hnum := global_radial_numeric (by linarith : 1≤σ) (by positivity)
    (mul_nonneg δ.coe_nonneg (by positivity)) (by positivity) (by positivity)
    hN hdens.1 (le_refl (333024*Real.exp (2*σ))) (le_refl _) hm
  have hA : 333024*(q:ℝ)^2=333024*Real.exp (2*σ) := by
    rw [hqexp,←Real.exp_nat_mul]; norm_num
  have hrad := residual_global_radial_moment (K:=K) (I:=I) hq hcard (Or.inr hI)
    σ (g+σ/2) n' (2*Real.exp (-(g+σ/2)/20)) hqexp.symm hσ hglo
    (by linarith only [hσ, hg]) (by simpa only [he] using hn') X (by simpa only [he] using hX)
    O δ hδ hδeq hmax (le_refl _) Lines hrank Q hLines
    (by simpa only [he] using hcap) 5000 (by norm_num)
  simp only [Nat.reduceSub,hcard,hA] at hrad
  have hh := (global_trunc_failure X O δ L Q R 5000).trans
    (mul_le_mul_of_nonneg_left (hrad.trans hnum) (by positivity))
  apply hh.trans_eq
  rw [mul_add]
  ac_rfl

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PeelingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma plane_threshold_exp {σ g n q : ℝ} (hn : n=Real.exp (3*σ/2+g))
    (hq : q=Real.exp σ) :
    n^(4/3:ℝ)/q*Real.exp (-g/5)=Real.exp (σ+17*g/15) := by
  rw [hn,hq,←Real.exp_mul,←Real.exp_sub,←Real.exp_add]
  congr 1
  ring

lemma plane_list_cutoff {σ g n q δ k j : ℝ}
    (hn : n=Real.exp (3*σ/2+g)) (hq : q=Real.exp σ)
    (hk : k=Real.exp (σ+17*g/15)) (hg : 100≤g) (hghi : g≤2*σ)
    (hδ : 0≤δ) (_hj : 0≤j) (hlen : j*k≤n) (hscale : n*δ≤4*q) :
    8*δ*(j+1)≤Real.exp (-g/20) := by
  have hn0 : 0<n := hn▸Real.exp_pos _
  have hk0 : 0<k := hk▸Real.exp_pos _
  have hjδ : j*δ≤4*q/k := by
    apply (le_div_iff₀ hk0).mpr
    calc
      _ = (j*k)*δ := by ring
      _ ≤ n*δ := mul_le_mul_of_nonneg_right hlen hδ
      _ ≤ _ := hscale
  have hδ' : δ≤4*q/n := (le_div_iff₀ hn0).mpr (by simpa only [mul_comm δ] using hscale)
  have hqk : q/k=Real.exp (-17*g/15) := by
    rw [hq,hk,←Real.exp_sub]
    congr 1
    ring
  have hqn : q/n≤Real.exp (-17*g/15) := by
    rw [hq,hn,←Real.exp_sub]
    exact Real.exp_le_exp.mpr (by linarith only [hghi,hg])
  have h₁ : j*δ≤4*Real.exp (-17*g/15) := by
    simpa only [mul_div_assoc,hqk] using hjδ
  have h₂ : δ≤4*Real.exp (-17*g/15) := by
    apply hδ'.trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hqn (by norm_num : (0:ℝ)≤4)
  have hpay : (64:ℝ)≤Real.exp (13*g/12) := by
    linarith only [Real.add_one_le_exp (13*g/12),hg]
  calc
    _ ≤ 64*Real.exp (-17*g/15) := by linarith only [h₁,h₂]
    _ ≤ Real.exp (13*g/12)*Real.exp (-17*g/15) :=
      mul_le_mul_of_nonneg_right hpay (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add];congr 1;ring

end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.TrainingCells
open scoped Classical
variable {A : Type*} [DecidableEq A]

lemma sdiff_clip (S O : Finset A) : S\(S∩O)=S\O := by
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_inter]
  tauto

end SharpRamseyFive.TrainingCells

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial TrainingCells
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma outsideAt_clip (x : ℙ K V) (S O : Finset (ℙ K V)) :
    outsideAt x S (S∩O)=outsideAt x S O := by
  simp only [outsideAt,sdiff_clip]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma momentOrder_bounds {σ P : ℝ} (hσ : 1≤σ) (hP : 1≤P) :
    Even (momentOrder σ P) ∧ 0 < momentOrder σ P ∧
      10000*σ/P≤(momentOrder σ P:ℝ) ∧ (momentOrder σ P:ℝ)≤10000*σ/P+2 ∧
      (momentOrder σ P:ℝ)≤10002*σ := by
  have hσ0 : 0<σ := by linarith
  have hP0 : 0<P := by linarith
  have hlo := Nat.le_ceil (5000*σ/P)
  have hhi := Nat.ceil_lt_add_one (by positivity : 0≤5000*σ/P)
  have hn : 0<⌈5000*σ/P⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hdiv : 5000*σ/P≤5000*σ := div_le_self (by positivity) hP
  have heq : 10000*σ/P = 2*(5000*σ/P) := by ring
  unfold momentOrder
  push_cast
  rw [heq]
  refine ⟨even_two_mul _,by omega,?_,?_,?_⟩ <;> linarith

end

open Filter ParameterHierarchy
open scoped Topology

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneExceptionScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_plane_ambient_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
      let Q := P η σ D R
      let a := 1/(100*(momentOrder σ Q:ℝ))
      100000000≤Q/10000 ∧ Q/10000<σ/2-4*Q ∧
      20*Q≤σ/2-4*Q ∧ Real.exp (-Q)≤a ∧ a≤2 ∧ (1332096:ℝ)≤Real.exp Q := by
  have hh := eventually_hierarchy hη hη' 0 (1/100) 1000000000000 (by norm_num) (by norm_num)
  have ha := eventually_power_absorption hη hη' 1000200 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hc := eventually_power_absorption hη hη' 1332096 0 1 (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hh,ha,hc] with σ hσ hh ha hc
  intro D R hr
  have hh := hh D R 0 0 hr (by simp) (by positivity)
  have ha := ha D R hr
  have hc := hc D R hr
  dsimp only
  have hL : 0≤L η σ D := by linarith only [hh.1]
  have hLP : L η σ D≤P η σ D R := by linarith only [hh.2.2.2.2.2,hL]
  have hP : 1≤P η σ D R := by linarith only [hh.1,hLP]
  have hp := momentOrder_bounds hσ hP
  have hp0 : (0:ℝ)< momentOrder σ (P η σ D R) := Nat.cast_pos.mpr hp.2.1
  have hp1 : (1:ℝ)≤ momentOrder σ (P η σ D R) := by exact_mod_cast hp.2.1
  refine ⟨by linarith only [hh.1,hLP],by linarith only [hh.2.1,hP],by linarith only [hh.2.1,hP],?_,?_,?_⟩
  · rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ))
    calc
      _≤100*(10002*σ) := mul_le_mul_of_nonneg_left hp.2.2.2.2 (by norm_num)
      _=1000200*σ := by ring
      _≤_ := by simpa only [Real.rpow_one,one_mul] using ha
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ))).mpr
    linarith only [hp1]
  · simpa only [Real.rpow_zero,mul_one,one_mul] using hc
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HyperplaneHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_literal_plane_global_trunc_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ) (L₀ : ℝ≥0),Range η σ D R → (L₀:ℝ)=L η σ D →
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
      (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      P η σ D R/10000≤g → g≤σ →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
      (X.card:ℝ)≤Real.exp (2*σ+g) →
      t=(Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5) →
      S=peelSet (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
      Real.exp (2*σ+g)/4≤S.card → (q:ℝ)^2≤S.card →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
      (∀l∈Lines,finrank K l=2) → (∀x∈Q,∀l : RadialLine x,l.val∈Lines) →
    (∑x : Q,∫ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L₀*radialWeight x.val (outsideAt x.val S (S∩O x.val)) (pointStrength S) p.2))≤Real.exp (2*σ) := by
  have hs := eventually_global_trunc_scalar hη hη' globalTruncConstant globalTruncConstant_pos
  have hm := eventually_plane_ambient_margins hη hη'
  filter_upwards [eventually_ge_atTop (1000:ℝ),hs,hm] with σ hσ hs hm
  intro D R L₀ hr hL q K I J _ _ _ _ _ _ _ g F hF Flat X S t ht0 O Lines Q
    hq hcard hσq hI hg hg' hFlat hcover hX ht hS hquarter hS2 hO hLines hQ
  have hdim : finrank K (I→K)=5 := by rw [Module.finrank_pi,hI]
  let P := ParameterHierarchy.P η σ D R
  have hm := hm D R hr
  have hlow : 100000000≤P/10000 := hm.1
  have hg0 : 0≤g := by dsimp [P] at hlow;linarith only [hg,hlow]
  have hgp : 100000000≤g+σ/2 := by dsimp [P] at hlow;linarith only [hg,hlow,hσ]
  have he : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hen : P/10000<g+σ/2 := by dsimp [P];linarith only [hg,hσ]
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (2*σ+g)/4).trans_le hquarter
  have hδ : (pointStrength (K:=K) S:ℝ)=(q:ℝ)/S.card := by
    simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast,hcard]
  have hδ0 : 0<pointStrength (K:=K) S := by rw [←NNReal.coe_pos,hδ];positivity
  have hscale : Real.exp (2*σ+g)*(pointStrength (K:=K) S:ℝ)≤4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hquarter,(Nat.cast_nonneg q : (0:ℝ)≤q)]
  have hsub : S⊆X := hS▸peel_subset (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X _ _
  have hSn : (S.card:ℝ)≤Real.exp (2*σ+g) := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hX
  have htE : t=Real.exp (σ+17*(g+σ/2)/15) := by
    rw [←he] at ht
    exact ht.trans (ScoreScalars.plane_threshold_exp rfl rfl)
  have htq : (q:ℝ)≤t := by rw [htE,←hσq];exact Real.exp_le_exp.mpr (by linarith only [hgp])
  have hmax : (pointStrength (K:=K) S:ℝ)*((q:ℝ)+1)≤2 := by
    rw [hδ,div_mul_eq_mul_div]
    apply (div_le_iff₀ hn0).mpr
    have hq1 : (1:ℝ)≤q := by exact_mod_cast (by omega : 1≤q)
    nlinarith only [hS2,hq1]
  have hbound : (∑x : Q,∫ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L₀*radialWeight x.val (outsideAt x.val S (O x.val)) (pointStrength S) p.2))≤
      globalTruncConstant*((R:ℝ)*(L₀:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*((R:ℝ)*(L₀:ℝ))^5000*σ*Real.exp (2*σ-4998*g) := by
    rcases peel_residual_real (P/10000<g+σ/2) hen F hF (fun j=>flatPoints (Flat j)) X t ht0 with hcap|⟨hJ,hres⟩
    · have hc : S⊆X\remaining F hF (fun j=>flatPoints (Flat j)) X
          (peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) := by rw [hS,hcap]
      have hjt := peel_length_real (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X t ht0
      have hjq : (peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0):ℝ)*(Nat.card K:ℝ)≤X.card := by
        rw [hcard]
        exact (mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg _)).trans hjt
      have hcut := ScoreScalars.plane_list_cutoff (n:=Real.exp (2*σ+g)) (q:=(q:ℝ))
        (by rw [he]) hσq.symm htE (by linarith only [hgp]) (by linarith only [hg',hσ])
        (pointStrength (K:=K) S).coe_nonneg (Nat.cast_nonneg _) (hjt.trans hX) hscale
      apply captured_global_trunc_exp_bound hdim F hF Flat X S hFlat _ hc hjq O hO
        (pointStrength S) L₀ hδ0 σ g (Real.exp (2*σ+g)) (by linarith) (by rw [hcard];exact hσq.symm)
        rfl hg' hX (by rwa [hcard]) _ Lines hLines Q hQ R
      exact hcut.trans (by have hh:=Real.exp_nonneg (-(g+σ/2)/20);linarith only [hh])
    · apply residual_global_trunc_exp_bound_dim hq hcard hI σ g S.card hσq.symm hσ hgp hg'
        hquarter S hSn O (pointStrength S) L₀ hδ0 hδ hmax Lines hLines Q hQ _ R
      intro U hU
      obtain ⟨j,hj,hjU⟩ := hcover U hU
      have hh := hres j hj
      rw [←hS,ht] at hh
      have heq : (S.filter fun y=>y.submodule≤U)=S∩flatPoints (Flat j) := by
        ext y;simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hjU]
      rw [heq]
      exact hh.le
  simp only [outsideAt_clip] at ⊢
  apply hbound.trans
  have hP : (R:ℝ)*(L₀:ℝ)=P := by rw [mul_comm,hL];rfl
  rw [hP]
  exact hs D R g hr hg

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc_oai
