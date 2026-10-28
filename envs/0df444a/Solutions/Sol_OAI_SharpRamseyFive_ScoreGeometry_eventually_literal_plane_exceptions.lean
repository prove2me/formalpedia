-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:10:56.678996+00:00
-- url     : https://prove2.me/submissions/406eea68-9ad0-4fae-96b9-285ac7c383b6

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveRichLines_quantitative_card_mul_le

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

lemma chosen_mem (k : ℕ) : chosen F hF shape X k ∈ F :=
  (best_spec F hF shape _).1

lemma maximal_cell (k : ℕ) (a : I) (ha : a ∈ F) :
    (remaining F hF shape X k ∩ shape a).card ≤ (cell F hF shape X k).card :=
  (best_spec F hF shape _).2 a ha

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma cell_card_antitone : Antitone (fun k => (cell F hF shape X k).card) := by
  apply antitone_nat_of_succ_le
  intro k
  have hle : remaining F hF shape X (k+1) ∩ shape (chosen F hF shape X (k+1)) ⊆
      remaining F hF shape X k ∩ shape (chosen F hF shape X (k+1)) :=
    Finset.inter_subset_inter_right (remaining_succ_subset F hF shape X k)
  exact (Finset.card_le_card hle).trans (maximal_cell F hF shape X k _ (chosen_mem F hF shape X _))

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

lemma remaining_eq_sdiff_union (k : ℕ) :
    remaining F hF shape X k = X \ (Finset.range k).biUnion (fun j => shape (chosen F hF shape X j)) := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    change remaining F hF shape X k \ shape (chosen F hF shape X k) = _
    rw [ih]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
    change (x ∈ X ∧ ¬∃ j < k, x ∈ shape (chosen F hF shape X j)) ∧
        x ∉ shape (chosen F hF shape X k) ↔
      x ∈ X ∧ ¬∃ j < k+1, x ∈ shape (chosen F hF shape X j)
    constructor
    · rintro ⟨⟨hx,hn⟩,hk⟩
      refine ⟨hx,?_⟩
      rintro ⟨j,hj,hxj⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hj | rfl
      · exact hn ⟨j,hj,hxj⟩
      · exact hk hxj
    · rintro ⟨hx,hn⟩
      refine ⟨⟨hx,?_⟩,?_⟩
      · rintro ⟨j,hj,hxj⟩
        exact hn ⟨j,Nat.lt_succ_of_lt hj,hxj⟩
      · intro hxk
        exact hn ⟨k,Nat.lt_succ_self k,hxk⟩

lemma firstAt_mem (J : ℕ) (x : V) (h : firstAt F hF shape X J x < J) :
    x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) := by
  have hs := Nat.find_spec (show ∃ j, J ≤ j ∨ x ∈ shape (chosen F hF shape X j) from ⟨J,Or.inl le_rfl⟩)
  change J ≤ firstAt F hF shape X J x ∨ x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) at hs
  exact hs.resolve_left (not_le_of_gt h)

lemma firstAt_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    firstAt F hF shape X J x = j := by
  apply le_antisymm
  · exact Nat.find_min' _ (Or.inr hxj)
  · by_contra hn
    have hlt : firstAt F hF shape X J x < j := by omega
    exact hearlier _ hlt (firstAt_mem F hF shape X J x (hlt.trans hj))

lemma ownCell_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    ownCell F hF shape X J x = cell F hF shape X j := by
  rw [ownCell, firstAt_eq F hF shape X J j x hj hxj hearlier, ite_eq_left hj]

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndexMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyWeightedCount
open scoped BigOperators

lemma index_mul_le {J j : ℕ} (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hmono : Antitone s) (hj : j < J) :
    (j:ℝ)*s j ≤ ∑ i ∈ Finset.range J, s i := by
  have hsum : ∑ i ∈ Finset.range j, s j ≤ ∑ i ∈ Finset.range j, s i :=
    Finset.sum_le_sum (fun i hi => hmono (Finset.mem_range.mp hi).le)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj.le)
    (fun i _ _ => hs i))

theorem weighted_rich_count (J : ℕ) (s m : ℕ → ℝ) (q M n p N : ℝ)
    (hs : ∀ i, 0 ≤ s i) (hmono : Antitone s)
    (hm : ∀ i < J, 0 ≤ m i ∧ m i ≤ N)
    (hq : 0 ≤ q) (hM : 0 < M) (hp : 0 ≤ p) (hN : 0 ≤ N)
    (hpn : p*q ≤ 1) (hNq : N ≤ 3*q^2)
    (hbudget : ∑ i ∈ Finset.range J, s i ≤ n) (hJq : (J:ℝ)*q ≤ n)
    (hvariance : ∀ i < J, 2*p*s i ≤ M → m i*M^2 ≤ 4*q*s i) :
    (∑ i ∈ Finset.range J, (i:ℝ)*m i)*M^2 ≤ 12*n^2 := by
  have hn : 0 ≤ n := (mul_nonneg (Nat.cast_nonneg _) hq).trans hJq
  have hNp : N*p^2 ≤ 3 := by
    have hpq : (p*q)^2 ≤ 1 := by nlinarith [mul_nonneg hp hq]
    have hh := mul_le_mul_of_nonneg_right hNq (sq_nonneg p)
    nlinarith
  have hrow (i : ℕ) (hi : i ∈ Finset.range J) : (i:ℝ)*m i*M^2 ≤ 12*n*s i := by
    have hiJ := Finset.mem_range.mp hi
    have hiq : (i:ℝ)*q ≤ n :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hiJ.le) hq).trans hJq
    have his : (i:ℝ)*s i ≤ n := (index_mul_le s hs hmono hiJ).trans hbudget
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have hsi := hs i
    rcases hm i hiJ with ⟨hm0,hmN⟩
    by_cases hsmall : 2*p*s i ≤ M
    · have hh := mul_le_mul_of_nonneg_left (hvariance i hiJ hsmall) hi0
      have hq' := mul_le_mul_of_nonneg_right hiq (hs i)
      have hn' := mul_nonneg hn (hs i)
      nlinarith
    · have hsquare : M^2 ≤ 4*p^2*(s i)^2 := by
        have hh : M ≤ 2*p*s i := (lt_of_not_ge hsmall).le
        have hsq := pow_le_pow_left₀ hM.le hh 2
        nlinarith
      calc
        (i:ℝ)*m i*M^2 ≤ (i:ℝ)*N*(4*p^2*(s i)^2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hmN hi0) hsquare
            (sq_nonneg M) (mul_nonneg hi0 hN)
        _ = 4*(N*p^2)*((i:ℝ)*s i)*s i := by ring
        _ ≤ 4*3*n*s i := by gcongr
        _ = 12*n*s i := by ring
  rw [Finset.sum_mul]
  calc
    ∑ i ∈ Finset.range J, (i:ℝ)*m i*M^2 ≤ ∑ i ∈ Finset.range J, 12*n*s i :=
      Finset.sum_le_sum hrow
    _ = 12*n*(∑ i ∈ Finset.range J, s i) := by rw [Finset.mul_sum]
    _ ≤ 12*n*n := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = 12*n^2 := by ring
end SharpRamseyFive.GreedyWeightedCount

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

lemma through_le_iff {x y : ℙ K V} (hxy : x ≠ y) (W : Submodule K V) :
    (through x y hxy).val ≤ W ↔ x.submodule ≤ W ∧ y.submodule ≤ W :=
  sup_le_iff

section RadialMass

open scoped Classical

variable [FiniteDimensional K V] {x : ℙ K V} [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma trainingOnLine_eq_fiber (X : Finset {y : ℙ K V // x ≠ y})
    (l : RadialLine x) :
    trainingOnLine X l = X.filter (fun y => through x y.val y.property = l) := by
  classical
  ext y
  simp only [trainingOnLine, Finset.mem_filter, through_eq_iff]

lemma sum_trainingOnLine (X : Finset {y : ℙ K V // x ≠ y})
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    ∑ l ∈ inFlat W, (trainingOnLine X l).card =
      (X.filter (fun y => y.val.submodule ≤ W)).card := by
  classical
  simp_rw [trainingOnLine_eq_fiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter X (inFlat W)
    (fun y => through x y.val y.property)]
  congr 1
  ext y
  simp [inFlat, through_le_iff, hx]

end RadialMass

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ExceptionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma ker_dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) :
    LinearMap.ker (dualOfHyperplane hdim A hA).rep = A := by
  let b := dualOfHyperplane hdim A hA
  have he : b.submodule = A.dualAnnihilator := Projectivization.submodule_mk'' _ _
  have hmem : b.rep ∈ A.dualAnnihilator := by
    rw [← he, b.submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have hle : A ≤ LinearMap.ker b.rep := by
    intro a ha
    exact ((Submodule.mem_dualAnnihilator b.rep).mp hmem) a ha
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hA]; omega)).symm

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RichHyperplaneVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem rich_hyperplane_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (X : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) (M : ℕ)
    (hM : ∀ b ∈ B, M ≤ (X.filter fun x => Incident x b).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (B.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K V) := Fintype.ofFinite _
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let w (x : ℙ K V) : ℝ := if x ∈ X then 1 else 0
  have hw : ∑ x, w x = (X.card:ℝ) := by simp [w]
  have hw2 : ∑ x, w x^2 = (X.card:ℝ) := by simp [w]
  have hweight (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane w b = ((X.filter fun x => Incident x b).card:ℝ) := by
    simp [weightOnHyperplane, incidenceEntry, w, mul_ite]
  let μ : ℝ := ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card
  have hvariance := incidence_variance hdim hd w
  rw [hw,hw2] at hvariance
  have hrow (b : ℙ K (Module.Dual K V)) (hb : b ∈ B) :
      (M:ℝ)^2 ≤ 4*(weightOnHyperplane w b-μ)^2 := by
    have hm : (M:ℝ) ≤ weightOnHyperplane w b := by rw [hweight]; exact_mod_cast hM b hb
    have hmean' : 2*μ ≤ M := by dsimp [μ]; nlinarith [hmean]
    have hm0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hle : 0 ≤ 2*(weightOnHyperplane w b-μ)-(M:ℝ) := by linarith
    have hge : 0 ≤ 2*(weightOnHyperplane w b-μ)+(M:ℝ) := by linarith
    nlinarith [mul_nonneg hle hge]
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
  have hsub := Finset.sum_le_univ_sum_of_nonneg (s := B)
    (fun b => sq_nonneg (weightOnHyperplane w b-μ))
  have hvar : ∑ b, (weightOnHyperplane w b-μ)^2 ≤ (Nat.card K:ℝ)^(d-1)*X.card := hvariance
  linarith

theorem rich_subspaces_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (F.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let b (A : F) : ℙ K (Module.Dual K V) := dualOfHyperplane hdim A.val (hF A.val A.property)
  let B := F.attach.image b
  have hi : Function.Injective b := by
    intro A B hAB
    apply Subtype.ext
    have h := congrArg (fun c : ℙ K (Module.Dual K V) => LinearMap.ker c.rep) hAB
    simpa only [b,ker_dualOfHyperplane] using h
  have hBc : B.card = F.card := by simp [B,Finset.card_image_of_injective _ hi]
  have hrich (c : ℙ K (Module.Dual K V)) (hc : c ∈ B) :
      M ≤ (X.filter fun x => Incident x c).card := by
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hc
    simpa only [Incident,b,ker_dualOfHyperplane] using hM A.val A.property
  have h := rich_hyperplane_variance hdim hd X B M hrich hmean
  simpa only [hBc] using h

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma card_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) :
    (pointsInSubspace H X).card = (X.filter fun p => p.submodule ≤ H).card := by
  simp [pointsInSubspace]

lemma mem_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) (p : ℙ K H) :
    p ∈ pointsInSubspace H X ↔ ((subspacePointsEquiv H) p).val ∈ X := by
  simp [pointsInSubspace]

lemma subspacePointsEquiv_submodule (H A : Submodule K V) (p : ℙ K H) :
    p.submodule ≤ A.comap H.subtype ↔ ((subspacePointsEquiv H) p).val.submodule ≤ A := by
  induction p using Projectivization.ind with | h v hv =>
  change (Projectivization.mk K v hv).submodule ≤ A.comap H.subtype ↔
    (Projectivization.map H.subtype H.injective_subtype (Projectivization.mk K v hv)).submodule ≤ A
  rw [Projectivization.map_mk, Projectivization.submodule_mk,
    Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem,
    Submodule.span_singleton_le_iff_mem]
  rfl

lemma card_pointsInSubspace_filter (H A : Submodule K V) (hAH : A ≤ H)
    (X : Finset (ℙ K V)) :
    ((pointsInSubspace H X).filter fun p => p.submodule ≤ A.comap H.subtype).card =
      (X.filter fun p => p.submodule ≤ A).card := by
  apply Finset.card_bij (fun p _ => ((subspacePointsEquiv H) p).val)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(mem_pointsInSubspace H X p).mp hpX,
      (subspacePointsEquiv_submodule H A p).mp hpA⟩
  · intro p hp q hq hpq
    exact (subspacePointsEquiv H).injective (Subtype.ext hpq)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    let z : {p : ℙ K V // p.submodule ≤ H} := ⟨p,hpA.trans hAH⟩
    refine ⟨(subspacePointsEquiv H).symm z, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · rw [mem_pointsInSubspace, Equiv.apply_symm_apply]
        exact hpX
      · rw [subspacePointsEquiv_submodule, Equiv.apply_symm_apply]
        exact hpA
    · simp [z]

lemma comap_subtype_finrank [FiniteDimensional K V] (H A : Submodule K V) (hAH : A ≤ H) :
    finrank K (A.comap H.subtype) = finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq H, Submodule.map_comap_subtype, inf_eq_right.mpr hAH]

lemma comap_subtype_injOn (H : Submodule K V) :
    Set.InjOn (fun A : Submodule K V => A.comap H.subtype) {A | A ≤ H} := by
  intro A hA B hB hAB
  change A ≤ H at hA
  change B ≤ H at hB
  have he := congrArg (fun W : Submodule K H => W.map H.subtype) hAB
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr hA, inf_eq_right.mpr hB] using he

theorem rich_hyperplanes_inside_subspace [FiniteDimensional K V] [Finite K]
    {d : ℕ} (hd : 1 ≤ d) (H : Submodule K V) (hH : finrank K H = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*
      (X.filter fun p => p.submodule ≤ H).card ≤ M) :
    ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(X.filter fun p => p.submodule ≤ H).card := by
  let G := F.filter fun A => A ≤ H
  let FH := G.image (fun A => A.comap H.subtype)
  have hc : FH.card = G.card := Finset.card_image_iff.mpr (by
    intro A hA B hB he
    exact comap_subtype_injOn H (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 he)
  have hdimF (A : Submodule K H) (hA : A ∈ FH) : finrank K A = d := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [comap_subtype_finrank H B (Finset.mem_filter.mp hB).2]
    exact hF B (Finset.mem_filter.mp hB).1
  have hm (A : Submodule K H) (hA : A ∈ FH) :
      M ≤ ((pointsInSubspace H X).filter fun p => p.submodule ≤ A).card := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [card_pointsInSubspace_filter H B (Finset.mem_filter.mp hB).2]
    exact hM B (Finset.mem_filter.mp hB).1
  have hμ : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(pointsInSubspace H X).card ≤ M := by
    simpa only [card_pointsInSubspace] using hmean
  have hh := rich_subspaces_variance hH hd FH hdimF (pointsInSubspace H X) M hm hμ
  simpa only [hc, card_pointsInSubspace] using hh

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CardFilterContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma card_filter_containment_le (X : Finset (ℙ K V)) (A : Submodule K V) :
    (X.filter fun x => x.submodule ≤ A).card ≤ ∑ i ∈ Finset.range (finrank K A), Nat.card K^i := by
  let : Finite V := Module.finite_of_finite K
  let Y := X.filter fun x => x.submodule ≤ A
  have hi : Function.Injective (fun x : Y => (⟨x.val,(Finset.mem_filter.mp x.property).2⟩ :
      {p : ℙ K V // p.submodule ≤ A})) := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : {p : ℙ K V // p.submodule ≤ A} => z.val) he)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspacePoints] at hc
  exact hc

lemma card_filter_finrank_le_two (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A ≤ 2) :
    (X.filter fun x => x.submodule ≤ A).card ≤ Nat.card K+1 := by
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hA)
    (f := fun i => Nat.card K^i) (by intros; exact Nat.zero_le _)
  have hc := (card_filter_containment_le X A).trans hle
  simpa [Finset.sum_range_succ,add_comm] using hc

lemma card_filter_finrank_le_one (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A ≤ 1) :
    (X.filter fun x => x.submodule ≤ A).card ≤ 1 := by
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hA)
    (f := fun i => Nat.card K^i) (by intros; exact Nat.zero_le _)
  have hc := (card_filter_containment_le X A).trans hle
  simpa using hc

omit [Finite K] in
lemma finrank_inf_lt_of_not_le (A H : Submodule K V) (hn : ¬A ≤ H) :
    finrank K (A ⊓ H : Submodule K V) < finrank K A := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hn (he ▸ inf_le_right)

lemma line_noncontaining_flat_cap (X : Finset (ℙ K V)) (A H : Submodule K V)
    (hA : finrank K A = 2) (hn : ¬A ≤ H) :
    (X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ H).card ≤ 1 := by
  have hh := finrank_inf_lt_of_not_le A H hn
  rw [hA] at hh
  simpa only [le_inf_iff] using card_filter_finrank_le_one X (A ⊓ H) (by omega)

lemma card_hyperplane_family {d : ℕ} (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) :
    F.card ≤ Q (Nat.card K) d := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let f (A : F) := dualOfHyperplane hdim A.val (hF A.val A.property)
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hk := congrArg (fun b : ℙ K (Module.Dual K V) => LinearMap.ker b.rep) he
    simpa only [f,ker_dualOfHyperplane] using hk
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, card_hyperplanes hdim] using hc

lemma card_hyperplanes_inside {d : ℕ} (H : Submodule K V) (hH : finrank K H = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) :
    (F.filter fun A => A ≤ H).card ≤ Q (Nat.card K) d := by
  let G := F.filter fun A => A ≤ H
  let FH := G.image (fun A => A.comap H.subtype)
  have hc : FH.card = G.card := Finset.card_image_iff.mpr (by
    intro A hA B hB he
    exact comap_subtype_injOn H (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 he)
  have hdimF (A : Submodule K H) (hA : A ∈ FH) : finrank K A = d := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [comap_subtype_finrank H B (Finset.mem_filter.mp hB).2]
    exact hF B (Finset.mem_filter.mp hB).1
  have hh := card_hyperplane_family hH FH hdimF
  rwa [hc] at hh

end SharpRamseyFive.RichPlaneGeometry

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

lemma line_covered_cap {I : Type*} [DecidableEq I] (T : Finset I)
    (P : I → Submodule K V) (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A = 2) (hn : ∀ i ∈ T, ¬A ≤ P i)
    (hcover : ∀ x ∈ X, x.submodule ≤ A → ∃ i ∈ T, x.submodule ≤ P i) :
    (X.filter fun x => x.submodule ≤ A).card ≤ T.card := by
  let Y (i : I) := X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ P i
  have hsub : X.filter (fun x => x.submodule ≤ A) ⊆ T.biUnion Y := by
    intro x hx
    obtain ⟨hxX,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,hxi⟩ := hcover x hxX hxA
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hxX,hxA,hxi⟩⟩
  have hsum : ∑ i ∈ T, (Y i).card ≤ ∑ _i ∈ T, (1:ℕ) :=
    Finset.sum_le_sum (fun i hi => line_noncontaining_flat_cap X A (P i) hA (hn i hi))
  exact (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans (by simpa using hsum))

variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma captured_cover (J : ℕ) (x : ℙ K V)
    (hx : x ∈ X \ remaining F hF (fun i => flatPoints (P i)) X J) :
    ∃ j ∈ Finset.range J, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  rw [remaining_eq_sdiff_union] at hx
  have hxnot := (Finset.mem_sdiff.mp hx).2
  have hxX := (Finset.mem_sdiff.mp hx).1
  have hm : x ∈ (Finset.range J).biUnion (fun j => flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X j))) := by
    by_contra hn
    exact hxnot (Finset.mem_sdiff.mpr ⟨hxX,hn⟩)
  obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hm
  exact ⟨j,hj,(mem_flatPoints _ _).mp hxj⟩

lemma rich_line_has_containing_flat (J M : ℕ) (hJM : J < M)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hM : M ≤ ((X \ remaining F hF (fun i => flatPoints (P i)) X J).filter
      fun x => x.submodule ≤ A).card) :
    ∃ j < J, A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  by_contra hn
  push Not at hn
  have hc := line_covered_cap (Finset.range J)
    (fun j => P (chosen F hF (fun i => flatPoints (P i)) X j))
    (X \ remaining F hF (fun i => flatPoints (P i)) X J) A hA
    (fun j hj => hn j (Finset.mem_range.mp hj))
    (fun x hx _ => captured_cover F hF P X J x hx)
  rw [Finset.card_range] at hc
  omega

lemma outside_cell_earlier (j : ℕ) (A : Submodule K V)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (y : ℙ K V) (hyX : y ∈ X) (hyA : y.submodule ≤ A)
    (hycell : y ∉ cell F hF (fun i => flatPoints (P i)) X j) :
    y ∈ X \ remaining F hF (fun i => flatPoints (P i)) X j := by
  refine Finset.mem_sdiff.mpr ⟨hyX, ?_⟩
  intro hyr
  exact hycell (Finset.mem_inter.mpr ⟨hyr, (mem_flatPoints _ _).mpr (hyA.trans hAj)⟩)

lemma earliest_line_outside_cell_cap (j : ℕ) (A : Submodule K V)
    (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      fun y => y.submodule ≤ A).card ≤ j := by
  have hs : (X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      (fun y => y.submodule ≤ A) ⊆
      (X \ remaining F hF (fun i => flatPoints (P i)) X j).filter
        (fun y => y.submodule ≤ A) := by
    intro y hy
    obtain ⟨hy,hya⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyX,hyc⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_filter.mpr ⟨outside_cell_earlier F hF P X j A hAj y hyX hya hyc,hya⟩
  have hc := line_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i))
    (X \ remaining F hF (fun i => flatPoints (P i)) X j) A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi))
    (fun y hy _ => captured_cover F hF P X j y hy)
  exact (Finset.card_le_card hs).trans (by simpa only [Finset.card_range] using hc)

lemma surviving_line_center_earlier (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (x : ℙ K V) (hxA : x.submodule ≤ A)
    (hrich : j < ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card) :
    ∃ i < j, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
  by_contra hn
  push Not at hn
  have heq := ownCell_eq F hF (fun i => flatPoints (P i)) X J j x hj
    ((mem_flatPoints _ _).mpr (hxA.trans hAj))
    (fun i hi hmem => hn i hi ((mem_flatPoints _ _).mp hmem))
  rw [heq] at hrich
  exact (not_lt_of_ge (earliest_line_outside_cell_cap F hF P X j A hA hAj hearlier)) hrich

lemma surviving_line_centers_cap (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((flatPoints A).filter fun x => j <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card).card ≤ j := by
  let C := (flatPoints A).filter fun x => j <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card
  have hall (x : ℙ K V) (hx : x ∈ C) : x.submodule ≤ A :=
    (mem_flatPoints _ _).mp (Finset.mem_filter.mp hx).1
  have hc := line_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i)) C A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi)) (by
      intro x hx hxa
      obtain ⟨i,hi,hxi⟩ := surviving_line_center_earlier F hF P X J j hj A hA hAj hearlier
        x hxa (Finset.mem_filter.mp hx).2
      exact ⟨i,Finset.mem_range.mpr hi,hxi⟩)
  rw [Finset.filter_eq_self.mpr hall,Finset.card_range] at hc
  exact hc

lemma cell_filter_own_flat (j : ℕ) :
    ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y =>
      y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cell F hF (fun i => flatPoints (P i)) X j := by
  apply Finset.filter_eq_self.mpr
  intro y hy
  exact (mem_flatPoints _ _).mp (Finset.mem_inter.mp hy).2

lemma card_cellRichLines_le (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (j M : ℕ) :
    (cellRichLines F hF P X L j M).card ≤ ProjectiveIncidence.Q (Nat.card K) 2 := by
  apply (Finset.card_le_card (show cellRichLines F hF P X L j M ⊆
      L.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) from
      fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,(Finset.mem_filter.mp hA).2.1⟩)).trans
  exact card_hyperplanes_inside _ (hP _ (chosen_mem F hF _ X j)) L hL

lemma cellRichLines_variance (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (j M : ℕ)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 1:ℝ)/ProjectiveIncidence.Q (Nat.card K) 2)*
      (cell F hF (fun i => flatPoints (P i)) X j).card ≤ M) :
    ((cellRichLines F hF P X L j M).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)*(cell F hF (fun i => flatPoints (P i)) X j).card := by
  let C := cell F hF (fun i => flatPoints (P i)) X j
  let G := L.filter fun A => M ≤ (C.filter fun y => y.submodule ≤ A).card
  have hG (A : Submodule K V) (hA : A ∈ G) : finrank K A = 2 :=
    hL A (Finset.mem_filter.mp hA).1
  have hm (A : Submodule K V) (hA : A ∈ G) : M ≤ (C.filter fun y => y.submodule ≤ A).card :=
    (Finset.mem_filter.mp hA).2
  have hμ : 2*((ProjectiveIncidence.Q (Nat.card K) (2-1):ℝ)/ProjectiveIncidence.Q (Nat.card K) 2)*
      (C.filter fun y => y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)).card ≤ M := by
    simpa only [C,cell_filter_own_flat] using hmean
  have hh := rich_hyperplanes_inside_subspace (by omega : 1 ≤ (2:ℕ))
    (P (chosen F hF (fun i => flatPoints (P i)) X j)) (hP _ (chosen_mem F hF _ X j))
    G hG C M hm hμ
  have he : G.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cellRichLines F hF P X L j M := by
    ext A
    simp only [G,cellRichLines,Finset.mem_filter,C]
    tauto
  simpa only [he,C,cell_filter_own_flat,show (2:ℕ)-1=1 from rfl,pow_one] using hh

theorem weighted_cell_rich_lines (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (J M : ℕ)
    (hM : 0 < M) (hJ : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card) :
    (∑ j ∈ Finset.range J, (j:ℝ)*(cellRichLines F hF P X L j M).card)*(M:ℝ)^2 ≤
      12*(X.card:ℝ)^2 := by
  let q : ℝ := Nat.card K
  let N : ℝ := ProjectiveIncidence.Q (Nat.card K) 2
  let p : ℝ := (ProjectiveIncidence.Q (Nat.card K) 1:ℝ)/N
  let s (j : ℕ) : ℝ := (cell F hF (fun i => flatPoints (P i)) X j).card
  let m (j : ℕ) : ℝ := (cellRichLines F hF P X L j M).card
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (show 1 ≤ Nat.card K from (Finite.one_lt_card (α := K)).le)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 2
  have hpq : p*q ≤ 1 := by
    dsimp [p,q,N]
    rw [div_mul_eq_mul_div]
    apply (div_le_one (by exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 2)).mpr
    have he := ProjectiveIncidence.Q_recurrence (q := Nat.card K) (d := 2) (by omega)
    push_cast [he]
    nlinarith
  have hNq : N ≤ 3*q^2 := by
    have he : N = 1+q+q^2 := by
      simp [N,q,ProjectiveIncidence.Q,Finset.sum_range_succ]
    rw [he]
    nlinarith
  have hbudget : ∑ j ∈ Finset.range J, s j ≤ X.card := by
    have hh := sum_card_add_remaining F hF (fun i => flatPoints (P i)) X J
    have hn : ∑ j ∈ Finset.range J, (cell F hF (fun i => flatPoints (P i)) X j).card ≤ X.card := by omega
    dsimp [s]
    exact_mod_cast hn
  apply GreedyWeightedCount.weighted_rich_count J s m q M X.card p N
  · intro j; exact Nat.cast_nonneg _
  · intro i j hij
    dsimp [s]
    exact_mod_cast cell_card_antitone F hF (fun i => flatPoints (P i)) X hij
  · intro j _
    exact ⟨Nat.cast_nonneg _, by dsimp [m,N]; exact_mod_cast card_cellRichLines_le F hF P X hP L hL j M⟩
  · exact hq.trans' zero_le_one
  · exact_mod_cast hM
  · dsimp [p]; positivity
  · exact hN.le
  · exact hpq
  · exact hNq
  · exact hbudget
  · exact hJ
  · intro j _ hj
    exact cellRichLines_variance F hF P X hP L hL j M hj

lemma earliest_line_cell_rich (j M : ℕ) (hj : j ≤ M)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (hrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card) :
    M ≤ ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A).card := by
  have hcap := earliest_line_outside_cell_cap F hF P X j A hA hAj hearlier
  have hsub : X.filter (fun y => y.submodule ≤ A) ⊆
      ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) ∪
      ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) := by
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff] at *
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem captured_center_line_count (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (J M : ℕ)
    (hM : 0 < M) (hJM : J ≤ M) (hJq : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card) :
    (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(M:ℝ)^2 ≤
      12*(X.card:ℝ)^2 := by
  have hrow (A : Submodule K V) (hA : A ∈ L) :
      ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) ≤
        ∑ j ∈ Finset.range J, if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0 := by
    by_cases he : (capturedLineCenters F hF P X J (2*M) A).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxc := (Finset.mem_filter.mp hx).2
      have hcaprich : 2*M ≤ ((X \ remaining F hF (fun i => flatPoints (P i)) X J).filter
          fun y => y.submodule ≤ A).card :=
        hxc.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hfullrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card :=
        hcaprich.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hcont := rich_line_has_containing_flat F hF P X J (2*M) (by omega) A (hL A hA) hcaprich
      let j := Nat.find hcont
      have hj : j < J := (Nat.find_spec hcont).1
      have hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := (Nat.find_spec hcont).2
      have hearlier (i : ℕ) (hi : i < j) : ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
        intro hiA
        exact Nat.find_min hcont hi ⟨hi.trans hj,hiA⟩
      have hmem : A ∈ cellRichLines F hF P X L j M :=
        Finset.mem_filter.mpr ⟨hA,hAj,earliest_line_cell_rich F hF P X j M
          (hj.le.trans hJM) A (hL A hA) hAj hearlier hfullrich⟩
      have hsub : capturedLineCenters F hF P X J (2*M) A ⊆
          (flatPoints A).filter (fun z => j <
            ((X \ ownCell F hF (fun i => flatPoints (P i)) X J z).filter fun y => y.submodule ≤ A).card) := by
        intro z hz
        obtain ⟨hzA,hzr⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_filter.mpr ⟨hzA, ?_⟩
        have hc := hzr.trans (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.sdiff_subset_sdiff_left _ Finset.sdiff_subset)))
        omega
      have hc := (Finset.card_le_card hsub).trans
        (surviving_line_centers_cap F hF P X J j hj A (hL A hA) hAj hearlier)
      have hsingle : (j:ℝ) ≤ ∑ k ∈ Finset.range J,
          if A ∈ cellRichLines F hF P X L k M then (k:ℝ) else 0 := by
        have hh := Finset.single_le_sum (s := Finset.range J)
          (f := fun k => if A ∈ cellRichLines F hF P X L k M then (k:ℝ) else 0)
          (fun k _ => by positivity) (Finset.mem_range.mpr hj)
        simpa only [ite_eq_left hmem] using hh
      exact (by exact_mod_cast hc : ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) ≤ (j:ℝ)).trans hsingle
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.cast_zero]
      exact Finset.sum_nonneg (fun j _ => by positivity)
  have hsum := Finset.sum_le_sum hrow
  have hcount (j : ℕ) :
      (∑ A ∈ L, if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0) =
        (j:ℝ)*(cellRichLines F hF P X L j M).card := by
    have hsub : cellRichLines F hF P X L j M ⊆ L := Finset.filter_subset _ _
    have hh := Finset.sum_subset hsub (f := fun A => if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0)
      (fun _ _ hn => ite_eq_right hn)
    rw [← hh]
    simp [mul_comm]
  rw [Finset.sum_comm] at hsum
  simp_rw [hcount] at hsum
  exact (mul_le_mul_of_nonneg_right hsum (sq_nonneg _)).trans
    (weighted_cell_rich_lines F hF P X hP L hL J M hM hJq)

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_RichCenters
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

lemma richCenters_mono (S T : Finset (ℙ K V))
    (O U : ℙ K V → Finset (ℙ K V)) (δ a : ℝ) (hδ : 0 ≤ δ)
    (hS : S ⊆ T) (hO : ∀ x, U x ⊆ O x) (A : Submodule K V) :
    richCenters S O δ a A ⊆ richCenters T U δ a A := by
  intro x hx
  obtain ⟨hxA,hx⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxA,hx.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hδ
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.sdiff_subset_sdiff hS (Finset.union_subset_union_left (hO x))))

lemma exists_scale {δ a : ℝ} (hδ : 0 < δ) (ha : 4*δ ≤ a) :
    ∃ M : ℕ, 0 < M ∧ 2*δ*M ≤ a ∧ a ≤ 4*δ*M := by
  have hx : 2 ≤ a/(2*δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hp : 1 ≤ ⌊a/(2*δ)⌋₊ := Nat.le_floor (by linarith)
  refine ⟨⌊a/(2*δ)⌋₊,by omega,?_,?_⟩
  · have hf := Nat.floor_le (by linarith : 0 ≤ a/(2*δ))
    have hh := (le_div_iff₀ (by positivity)).mp hf
    nlinarith
  · have hf := Nat.lt_floor_add_one (a/(2*δ))
    have hn : (1:ℝ) ≤ ⌊a/(2*δ)⌋₊ := by exact_mod_cast hp
    have hh : a/(2*δ) ≤ 2*⌊a/(2*δ)⌋₊ := by linarith
    have := (div_le_iff₀ (by positivity)).mp hh
    nlinarith

variable {I : Type*} [LinearOrder I]

theorem captured_rich_centers (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X : Finset (ℙ K V))
    (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2)
    (J M : ℕ) (hM : 0 < M) (hJM : J ≤ M)
    (hJq : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card)
    (O : ℙ K V → Finset (ℙ K V))
    (hO : ∀ x, ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O x)
    (δ a : ℝ) (hδ : 0 < δ) (ha : 2*δ*M ≤ a) (ha' : a ≤ 4*δ*M) :
    (∑ A ∈ L, ((richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A).card:ℝ))*a^2 ≤
      192*δ^2*(X.card:ℝ)^2 := by
  have ha0 : 0 ≤ a := (by positivity : 0 ≤ 2*δ*M).trans ha
  have hsub (A : Submodule K V) : richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A ⊆
      capturedLineCenters F hF P X J (2*M) A := by
    intro x hx
    obtain ⟨hxA,hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxA,?_⟩
    have hs : (X \ remaining F hF (fun i => flatPoints (P i)) X J) \ (O x ∪ {x}) ⊆
        (X \ remaining F hF (fun i => flatPoints (P i)) X J) \
          ownCell F hF (fun i => flatPoints (P i)) X J x :=
      Finset.sdiff_subset_sdiff_right _ ((hO x).trans Finset.subset_union_left)
    have hc : ((((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        (O x ∪ {x})).filter fun y => y.submodule ≤ A).card:ℝ) ≤
        (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter
          fun y => y.submodule ≤ A).card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hs)
    have hh := ha.trans (hx.trans (mul_le_mul_of_nonneg_left hc hδ.le))
    have hm : ((2*M:ℕ):ℝ) ≤ (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter
          fun y => y.submodule ≤ A).card := by
      push_cast
      nlinarith
    exact_mod_cast hm
  have hsum : (∑ A ∈ L, ((richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A).card:ℝ)) ≤
      ∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) := by
    apply Finset.sum_le_sum
    intro A _
    exact_mod_cast Finset.card_le_card (hsub A)
  have hc := captured_center_line_count F hF P X hP L hL J M hM hJM hJq
  have ha2 := pow_le_pow_left₀ ha0 ha' 2
  calc
    _ ≤ (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*a^2 :=
      mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ ≤ (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(4*δ*M)^2 :=
      mul_le_mul_of_nonneg_left ha2 (Finset.sum_nonneg fun _ _ => by positivity)
    _ = 16*δ^2*((∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(M:ℝ)^2) := by ring
    _ ≤ 16*δ^2*(12*(X.card:ℝ)^2) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end SharpRamseyFive.GlobalRadial

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

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Outside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (x : ℙ K V) [Fintype (RadialLine x)]

lemma mass_inFlat (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    PoissonScore.mass (radialWeight x X δ) (RadialLine.inFlat W) =
      (δ:ℝ) * (X.filter fun y => y.val.submodule ≤ W).card := by
  unfold PoissonScore.mass radialWeight
  simp only [NNReal.coe_mul, NNReal.coe_natCast, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [RadialLine.sum_trainingOnLine X W hx]

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

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

lemma badCenters_mass_le (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (D : ℝ) :
    ((badCenters S O δ a L Q D).card:ℝ)*D ≤
      ∑ A ∈ L, ((richCenters S O δ a A).card:ℝ) := by
  let E := badCenters S O δ a L Q D
  calc
    _ = ∑ _x ∈ E, D := by simp only [Finset.sum_const,nsmul_eq_mul]; rfl
    _ ≤ ∑ x ∈ E, ((localLines S O δ a L x).card:ℝ) :=
      Finset.sum_le_sum fun _ hx => (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x ∈ Q, ((localLines S O δ a L x).card:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := by exact_mod_cast sum_localLines_le S O δ a L Q

lemma exception_fraction (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (q n χ C : ℝ) (hq : 0<q) (hn : 0<n) (ha : 0<a)
    (hglobal : (∑ A ∈ L, ((richCenters S O δ a A).card:ℝ))*a^2 ≤ C*q^2) :
    ((badCenters S O δ a L Q (q^4/n^2*Real.exp χ/a^100)).card:ℝ) ≤
      n*(C*(n/q^2)*Real.exp (-χ)*a^98) := by
  let e : ℝ := (badCenters S O δ a L Q (q^4/n^2*Real.exp χ/a^100)).card
  have hh := (mul_le_mul_of_nonneg_right
    (badCenters_mass_le S O δ a L Q (q^4/n^2*Real.exp χ/a^100)) (sq_nonneg a)).trans hglobal
  have heq : (q^4/n^2*Real.exp χ/a^100)*a^2 = q^4/n^2*Real.exp χ/a^98 := by
    field_simp
  have hm : e*(q^4/n^2*Real.exp χ/a^98) ≤ C*q^2 := by
    change e*(q^4/n^2*Real.exp χ/a^100)*a^2 ≤ _ at hh
    rwa [mul_assoc,heq] at hh
  have hpos : 0<q^4/n^2*Real.exp χ/a^98 := by positivity
  have hdiv := (le_div_iff₀ hpos).mpr hm
  have hnorm : C*q^2/(q^4/n^2*Real.exp χ/a^98) =
      n*(C*(n/q^2)*Real.exp (-χ)*a^98) := by
    rw [Real.exp_neg]
    field_simp
  exact hdiv.trans_eq hnorm

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma localLines_mass (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (x : ℙ K V) [Fintype (RadialLine x)] :
    ((localLines S O δ a Lines x).card:ℝ)*a≤(δ:ℝ)*S.card := by
  let E := localLines S O δ a Lines x
  let X := outsideAt x S (O x)
  let f (l : E) : RadialLine x := ⟨l.val,hLines _ (Finset.mem_filter.mp l.property).1,
    (mem_flatPoints _ _).mp (Finset.mem_filter.mp (Finset.mem_filter.mp l.property).2).1⟩
  have hi : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun r : RadialLine x => r.val) h)
  have ha (l : E) : a≤(radialWeight x X δ (f l):ℝ) := by
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp l.property).2).2
    change a≤(δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule≤l.val).card:ℝ)
    rwa [outsideAt_filter_card]
  have hsum : (∑l : RadialLine x,(radialWeight x X δ l:ℝ))=(δ:ℝ)*X.card := by
    have hh := mass_inFlat x X δ ⊤ le_top
    simpa [PoissonScore.mass,RadialLine.inFlat] using hh
  calc
    _ = ∑_l : E,a := by simp [E]
    _ ≤ ∑l : E,(radialWeight x X δ (f l):ℝ) := Finset.sum_le_sum fun l _ => ha l
    _ = ∑l ∈ Finset.univ.image f,(radialWeight x X δ l:ℝ) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hi h
    _ ≤ ∑l : RadialLine x,(radialWeight x X δ l:ℝ) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => NNReal.coe_nonneg _)
    _ = (δ:ℝ)*X.card := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast outsideAt_card_le x S (O x)) δ.coe_nonneg

lemma no_radial_exception_of_mass (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) {a D : ℝ} (ha : 0<a) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (Q : Finset (ℙ K V))
    [∀x : ℙ K V,Fintype (RadialLine x)] (hD : (δ:ℝ)*S.card<D*a) :
    badCenters S O δ a Lines Q D=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := (Finset.mem_filter.mp hx).2
  have hh := (mul_le_mul_of_nonneg_right hx' ha.le).trans (localLines_mass S O δ a Lines hLines x)
  exact (not_lt_of_ge hh) hD

lemma radial_exception_scale (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) {a D : ℝ} (hD : 0<D) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (Q : Finset (ℙ K V))
    (hne : (badCenters S O δ a Lines Q D).Nonempty) :
    a≤(δ:ℝ)*((Nat.card K:ℝ)+1) := by
  obtain ⟨x,hx⟩ := hne
  have hx' := (Finset.mem_filter.mp hx).2
  have hE : (localLines S O δ a Lines x).Nonempty := Finset.card_pos.mp (by
    have ht : (0:ℝ)<(localLines S O δ a Lines x).card := hD.trans_le hx'
    exact_mod_cast ht)
  obtain ⟨l,hl⟩ := hE
  obtain ⟨hll,hlx⟩ := Finset.mem_filter.mp hl
  obtain ⟨hxl,ha⟩ := Finset.mem_filter.mp hlx
  have hc : ((S\(O x∪{x})).filter fun y => y.submodule≤l).card≤Nat.card K+1 := by
    exact RichPlaneGeometry.card_filter_finrank_le_two _ _ (le_of_eq (hLines l hll))
  exact ha.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) δ.coe_nonneg)

lemma radial_exception_uniform (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) {a q n χ C : ℝ} (hq : 0<q) (hn : 0<n) (ha : 0<a) (ha1 : a≤1)
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (hC : 0≤C) (hscale : n*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*q^2)
    (hglobal : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2≤C*q^2) :
    ((badCenters S O δ a Lines Q (q^4/n^2*Real.exp χ/a^100)).card:ℝ)≤
      n*(8*C*Real.exp (-χ)) := by
  by_cases he : (badCenters S O δ a Lines Q (q^4/n^2*Real.exp χ/a^100)).Nonempty
  · have hcap := radial_exception_scale S O δ (by positivity) Lines hLines Q he
    have hna : n*a≤8*q^2 := (mul_le_mul_of_nonneg_left hcap hn.le).trans hscale
    have hpow : a^98≤a := by
      calc
        _ = a*a^97 := by ring
        _ ≤ a*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha.le ha1) ha.le
        _ = a := mul_one a
    have hratio : (n/q^2)*a^98≤8 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
      exact (mul_le_mul_of_nonneg_left hpow hn.le).trans hna
    have hh := exception_fraction S O δ a Lines Q q n χ C hq hn ha hglobal
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hn.le
    calc
      C*(n/q^2)*Real.exp (-χ)*a^98 = C*((n/q^2)*a^98)*Real.exp (-χ) := by ring
      _ ≤ C*8*Real.exp (-χ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) (Real.exp_nonneg _)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end SharpRamseyFive.GlobalRadial
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma biUnion_card_real_le {ι A : Type*} [DecidableEq A] (I : Finset ι) (E : ι→Finset A)
    {e : ℝ} (hE : ∀i∈I,((E i).card:ℝ)≤e) :
    ((I.biUnion E).card:ℝ)≤I.card*e := by
  calc
    _ ≤ ∑i∈I,((E i).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : (I.biUnion E).card≤_)
    _ ≤ ∑_i∈I,e := Finset.sum_le_sum hE
    _ = _ := by simp

lemma strengthDyads_card (m : ℕ) (δ : ℝ≥0) :
    (strengthDyads m δ).card≤Nat.clog 2 m+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem radialExceptions_card [∀x : ℙ K V,Fintype (RadialLine x)]
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (q n χ C : ℝ) (hq : 0<q) (hn : 0<n) (hC : 0≤C)
    (hscale : n*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*q^2)
    (hcount : ∀i∈strengthDyads S.card δ,let a:=((δ:ℝ)*2^i)/2;
      (δ:ℝ)*S.card<(q^4/n^2*Real.exp χ/a^100)*a ∨
      (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2≤C*q^2) :
    ((radialExceptions S O δ Lines Q q n χ).card:ℝ)≤
      n*(8*C*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  have he : 0≤n*(8*C*Real.exp (-χ)) := by positivity
  have hh := biUnion_card_real_le (strengthDyads S.card δ)
    (fun i => badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
      (q^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100)) (e:=n*(8*C*Real.exp (-χ))) (by
    intro i hi
    have ha : 0<((δ:ℝ)*2^i)/2 := by positivity
    have ha1 : ((δ:ℝ)*2^i)/2≤1 := by linarith only [(Finset.mem_filter.mp hi).2]
    rcases hcount i hi with hmass|hglobal
    · rw [no_radial_exception_of_mass S O δ ha Lines hLines Q hmass]
      simpa only [Finset.card_empty,Nat.cast_zero] using he
    · exact radial_exception_uniform S O δ hq hn ha ha1 Lines hLines Q hC hscale hglobal)
  apply hh.trans
  have hc : ((strengthDyads S.card δ).card:ℝ)≤(Nat.clog 2 S.card:ℝ)+1 := by
    exact_mod_cast strengthDyads_card S.card δ
  calc
    _ ≤ ((Nat.clog 2 S.card:ℝ)+1)*(n*(8*C*Real.exp (-χ))) :=
      mul_le_mul_of_nonneg_right hc he
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreScalars
open scoped Topology
open Filter

lemma radial_mass_of_scalar {q n a χ mass : ℝ} (hq : 0<q) (hn : 0<n)
    (ha : 0<a) (hmass : mass≤q) (hratio : n^2*a^99<q^3*Real.exp χ) :
    mass<(q^4/n^2*Real.exp χ/a^100)*a := by
  have hden : 0<n^2*a^99 := by positivity
  have heq : (q^4/n^2*Real.exp χ/a^100)*a=q^4*Real.exp χ/(n^2*a^99) := by
    field_simp
  rw [heq]
  apply hmass.trans_lt
  apply (lt_div_iff₀ hden).mpr
  have hh := mul_lt_mul_of_pos_left hratio hq
  convert hh using 1 <;> first | rfl | ring

lemma radial_small_strength {q n a g χ : ℝ} (hq : 0<q) (hn : 0<n)
    (hsq : n^2=q^3*Real.exp (2*g)) (hg : 0≤g) (hχ : 0<χ)
    (ha : 0≤a) (hcut : a≤Real.exp (-g/20)) :
    n^2*a^99<q^3*Real.exp χ := by
  have hp := pow_le_pow_left₀ ha hcut 99
  have hexp : Real.exp (2*g)*(Real.exp (-g/20))^99≤1 := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    norm_num
    linarith only [hg]
  have hsmall : n^2*a^99≤q^3 := by
    calc
      n^2*a^99 ≤ n^2*(Real.exp (-g/20))^99 :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg hn.le _)
      _ = q^3*(Real.exp (2*g)*(Real.exp (-g/20))^99) := by rw [hsq,mul_assoc]
      _ ≤ q^3*1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = q^3 := mul_one _
  exact hsmall.trans_lt ((lt_mul_iff_one_lt_right (pow_pos hq 3)).mpr (Real.one_lt_exp_iff.mpr hχ))

lemma radial_low_density {q n a g χ : ℝ} (hq : 0<q) (hn : 0<n)
    (hsq : n^2=q^3*Real.exp (2*g)) (hχ : 2*g<χ)
    (ha : 0≤a) (ha1 : a≤1) : n^2*a^99<q^3*Real.exp χ := by
  calc
    _ ≤ n^2*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha ha1) (pow_nonneg hn.le _)
    _ = q^3*Real.exp (2*g) := by rw [mul_one,hsq]
    _ < _ := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hχ) (pow_pos hq 3)

end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀x : ℙ K V,Fintype (RadialLine x)]

theorem captured_radial_exception_bound {I : Type} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (Flat : I→Submodule K V)
    (X S : Finset (ℙ K V)) (hFlat : ∀i∈F,finrank K (Flat i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
    (δ : ℝ≥0) (hδ : 0<δ) (n g χ : ℝ) (hn : 0<n) (hX : (X.card:ℝ)≤n)
    (hsq : n^2=(Nat.card K:ℝ)^3*Real.exp (2*g)) (hg : 0≤g) (hχ : 0<χ)
    (hmass : (δ:ℝ)*S.card≤Nat.card K) (hscale : n*(δ:ℝ)≤4*Nat.card K)
    (hcut : 8*(δ:ℝ)*(j+1)≤Real.exp (-g/20))
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) :
    ((radialExceptions S O δ Lines Q (Nat.card K) n χ).card:ℝ)≤
      n*(24576*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hscale' : n*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*(Nat.card K:ℝ)^2 := by
    calc
      _ = (n*(δ:ℝ))*((Nat.card K:ℝ)+1) := by ring
      _ ≤ (4*Nat.card K)*(2*Nat.card K) := mul_le_mul hscale (by linarith only [hq1])
        (by positivity) (by positivity)
      _ = _ := by ring
  have hbound := radialExceptions_card S O δ hδ Lines hLines Q (Nat.card K) n χ 3072 hq hn (by norm_num) hscale'
  norm_num only [show (8:ℝ)*3072=24576 by norm_num] at hbound
  apply hbound
  intro i hi
  let a : ℝ := ((δ:ℝ)*2^i)/2
  have ha : 0<a := by dsimp [a];positivity
  by_cases hsmall : a≤Real.exp (-g/20)
  · exact Or.inl (ScoreScalars.radial_mass_of_scalar hq hn ha hmass
      (ScoreScalars.radial_small_strength hq hn hsq hg hχ ha.le hsmall))
  · right
    have hacut : 8*(δ:ℝ)*(j+1)≤a := hcut.trans (le_of_not_ge hsmall)
    have hδ' : 0<(δ:ℝ) := hδ
    have ha4 : 4*(δ:ℝ)≤a := by nlinarith only [hacut,hδ',(Nat.cast_nonneg j : (0:ℝ)≤j)]
    obtain ⟨M,hM,hlo,hhi⟩ := exists_scale hδ' ha4
    have hjM : j≤M := by
      have hh : (j:ℝ)≤M := by nlinarith only [hacut,hhi,hδ']
      exact_mod_cast hh
    have hm := captured_rich_centers F hF Flat X hFlat Lines hLines j M hM hjM hj O hO δ a hδ' hlo hhi
    have hs : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))≤
        ∑l∈Lines,((richCenters (X\remaining F hF (fun i => flatPoints (Flat i)) X j) O δ a l).card:ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S _ O O δ a δ.coe_nonneg hS
        (fun _ => Finset.Subset.refl _) l))
    apply ((mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm).trans
    have hscaleX : (δ:ℝ)*X.card≤4*Nat.card K :=
      (mul_le_mul_of_nonneg_left hX δ.coe_nonneg).trans (by simpa only [mul_comm n] using hscale)
    have hsq' := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(δ:ℝ)*X.card) hscaleX 2
    nlinarith only [hsq']

end
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I : Type} [Field K] [Finite K] [Fintype I]
  [∀x : ℙ K (I→K),Fintype (RadialLine x)]

theorem residual_radial_exception_bound {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g n' χ : ℝ) (hσq : Real.exp σ=q) (hσ : 1000≤σ)
    (hg : 100000000≤g) (hghi : g≤2*σ) (hn' : Real.exp (3*σ/2+g)/4≤n')
    (X S : Finset (ℙ K (I→K))) (hS : S⊆X) (hSn : (S.card:ℝ)≤n')
    (hX : (X.card:ℝ)≤Real.exp (3*σ/2+g))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K))) (δ : ℝ≥0) (hδ : (δ:ℝ)=(q:ℝ)/n')
    (hχ : 0<χ)
    (hcap : ∀U : Submodule K (I→K),finrank K U=3 →
      ((X.filter fun y => y.submodule≤U).card:ℝ)≤
        (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (Lines : Finset (Submodule K (I→K))) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) :
    ((radialExceptions S O δ Lines Q q (Real.exp (3*σ/2+g)) χ).card:ℝ)≤
      Real.exp (3*σ/2+g)*(2664192*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast (by omega : 1≤q)
  have hn0 : 0<n' := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hn'
  have hδ0 : 0<δ := by rw [←NNReal.coe_pos,hδ];positivity
  have hmass : (δ:ℝ)*S.card≤q := by
    rw [hδ]
    calc
      _ ≤ ((q:ℝ)/n')*n' := mul_le_mul_of_nonneg_left hSn (by positivity)
      _ = _ := div_mul_cancel₀ _ (ne_of_gt hn0)
  have hscale : Real.exp (3*σ/2+g)*(δ:ℝ)≤4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hn',hq0]
  have hscale' : Real.exp (3*σ/2+g)*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*(q:ℝ)^2 := by
    rw [hcard]
    calc
      _ = (Real.exp (3*σ/2+g)*(δ:ℝ))*((q:ℝ)+1) := by ring
      _ ≤ (4*q)*(2*q) := mul_le_mul hscale (by linarith only [hq1]) (by positivity) (by positivity)
      _ = _ := by ring
  have hsq : (Real.exp (3*σ/2+g))^2=(q:ℝ)^3*Real.exp (2*g) := by
    rw [←hσq,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    norm_num
    ring
  have hbound := radialExceptions_card S O δ hδ0 Lines hLines Q (q:ℝ) (Real.exp (3*σ/2+g)) χ
    333024 hq0 (Real.exp_pos _) (by norm_num) hscale'
  norm_num only [show (8:ℝ)*333024=2664192 by norm_num] at hbound
  apply hbound
  intro i hi
  let a : ℝ := ((δ:ℝ)*2^i)/2
  have ha : 0<a := by dsimp [a];positivity
  by_cases hsmall : a≤Real.exp (-g/20)
  · exact Or.inl (ScoreScalars.radial_mass_of_scalar hq0 (Real.exp_pos _) ha hmass
      (ScoreScalars.radial_small_strength hq0 (Real.exp_pos _) hsq (by linarith only [hg]) hχ ha.le hsmall))
  · right
    have ha2 : a≤2 := by dsimp [a];linarith only [(Finset.mem_filter.mp hi).2]
    have hm := residual_rich_centers hq hcard hI σ g n' a hσq hσ hg hghi hn'
      (le_of_not_ge hsmall) ha2 X hX Lines hLines O hcap
    have hs : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))≤
        ∑l∈Lines,((richCenters X O ((q:ℝ)/n') a l).card:ℝ) := by
      rw [←hδ]
      apply Finset.sum_le_sum
      intro l hl
      exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S X O O δ a δ.coe_nonneg hS
        (fun _ => Finset.Subset.refl _) l))
    exact (mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm

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

lemma sdiff_union_clip (S O : Finset A) (x : A) : S\((S∩O)∪{x})=S\(O∪{x}) := by
  ext y
  simp only [Finset.mem_sdiff,Finset.mem_inter,Finset.mem_union]
  tauto

end SharpRamseyFive.TrainingCells

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial TrainingCells
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma richCenters_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (A : Submodule K V) :
    richCenters S (fun x => S∩O x) δ a A=richCenters S O δ a A := by
  simp only [richCenters,sdiff_union_clip]

lemma localLines_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (x : ℙ K V) :
    localLines S (fun x => S∩O x) δ a Lines x=localLines S O δ a Lines x := by
  simp only [localLines,richCenters_clip]

lemma badCenters_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (D : ℝ) :
    badCenters S (fun x => S∩O x) δ a Lines Q D=badCenters S O δ a Lines Q D := by
  simp only [badCenters,localLines_clip]

lemma radialExceptions_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (q n χ : ℝ) :
    radialExceptions S (fun x => S∩O x) δ Lines Q q n χ=radialExceptions S O δ Lines Q q n χ := by
  simp only [radialExceptions,badCenters_clip]

lemma badCenters_threshold_mono (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) {D E : ℝ} (hDE : D≤E) :
    badCenters S O δ a Lines Q E⊆badCenters S O δ a Lines Q D := by
  intro x hx
  obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,hDE.trans he⟩

lemma radialExceptions_normalization (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (q χ m n : ℝ) (hm : 0 < m) (hmn : m ≤ n) :
    radialExceptions S O δ Lines Q q m χ⊆radialExceptions S O δ Lines Q q n χ := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨i,hi,badCenters_threshold_mono S O δ _ Lines Q ?_ hx⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm) ((sq_le_sq₀ hm.le (hm.le.trans hmn)).mpr hmn)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Peeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀x : ℙ K V,Fintype (RadialLine x)]

lemma radialExceptions_low_density (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0<δ) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (Q : Finset (ℙ K V))
    (q n g χ : ℝ) (hq : 0<q) (hn : 0<n) (hsq : n^2=q^3*Real.exp (2*g))
    (hχ : 2*g<χ) (hmass : (δ:ℝ)*S.card≤q) :
    radialExceptions S O δ Lines Q q n χ=∅ := by
  unfold radialExceptions
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  have ha : 0<((δ:ℝ)*2^i)/2 := by positivity
  have ha1 : ((δ:ℝ)*2^i)/2≤1 := by linarith only [(Finset.mem_filter.mp hi).2]
  have he := no_radial_exception_of_mass S O δ ha Lines hLines Q
    (ScoreScalars.radial_mass_of_scalar hq hn ha hmass
      (ScoreScalars.radial_low_density hq hn hsq hχ ha.le ha1))
  simp only [he,Finset.notMem_empty] at hx

end

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I J : Type} [Field K] [Finite K] [Fintype I] [LinearOrder J]
  [∀x : ℙ K (I→K),Fintype (RadialLine x)]

theorem literal_plane_radial_exceptions {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g b χ : ℝ) (hσq : Real.exp σ=q) (hσ : 1000≤σ)
    (hb : 100000000≤b) (hχb : 2*b<χ) (hghi : g≤2*σ)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
    (hFlat : ∀j∈F,finrank K (Flat j)=3)
    (hcover : ∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U)
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ)≤Real.exp (3*σ/2+g))
    (t : ℝ) (ht : t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (ht0 : 0<t)
    (S : Finset (ℙ K (I→K)))
    (hS : S=peelSet (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0))
    (hquarter : Real.exp (3*σ/2+g)/4≤S.card)
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (hO : ∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
      (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x)
    (δ : ℝ≥0) (hδ : (δ:ℝ)=(q:ℝ)/S.card)
    (Lines : Finset (Submodule K (I→K))) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) :
    ((radialExceptions S (fun x => S∩O x) δ Lines Q q (Real.exp (3*σ/2+g)) χ).card:ℝ)≤
      Real.exp (3*σ/2+g)*(2664192*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  rw [radialExceptions_clip]
  have hq0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hδ0 : 0<δ := by rw [←NNReal.coe_pos,hδ];positivity
  have hsub : S⊆X := hS▸peel_subset (b<g) F hF (fun j => flatPoints (Flat j)) X _ _
  have hSn : (S.card:ℝ)≤Real.exp (3*σ/2+g) := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hX
  have hmass : (δ:ℝ)*S.card=(q:ℝ) := by rw [hδ];exact div_mul_cancel₀ _ (ne_of_gt hn0)
  have hscale : Real.exp (3*σ/2+g)*(δ:ℝ)≤4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hquarter,hq0]
  have hsq : (Real.exp (3*σ/2+g))^2=(q:ℝ)^3*Real.exp (2*g) := by
    rw [←hσq,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1;norm_num;ring
  by_cases hen : b<g
  · have hg : 100000000≤g := hb.trans hen.le
    have htE : t=Real.exp (σ+17*g/15) := ht.trans
      (ScoreScalars.plane_threshold_exp rfl rfl)
    have htq : (q:ℝ)≤t := by rw [htE,←hσq];apply Real.exp_le_exp.mpr;linarith only [hg]
    rcases peel_residual_real (b<g) hen F hF (fun j => flatPoints (Flat j)) X t ht0 with hcap|⟨hJ,hres⟩
    · have hc : S⊆X\remaining F hF (fun j => flatPoints (Flat j)) X
          (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) := by
        rw [hS,hcap]
      have hjt := peel_length_real (b<g) F hF (fun j => flatPoints (Flat j)) X t ht0
      have hjq : (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0):ℝ)*(Nat.card K:ℝ)≤X.card := by
        rw [hcard]
        exact (mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg _)).trans hjt
      have hcut := ScoreScalars.plane_list_cutoff (n:=Real.exp (3*σ/2+g)) (q:=(q:ℝ))
        rfl hσq.symm htE (by linarith only [hg]) hghi δ.coe_nonneg (Nat.cast_nonneg _)
        (hjt.trans hX) hscale
      have hbound := captured_radial_exception_bound F hF Flat X S hFlat _ hc hjq O hO δ hδ0
        (Real.exp (3*σ/2+g)) g χ (Real.exp_pos _) hX (by simpa only [hcard] using hsq)
        (by linarith only [hg]) (by linarith only [hχb,hb]) (by simpa only [hcard] using hmass.le)
        (by simpa only [hcard] using hscale) hcut Lines hLines Q
      rw [hcard] at hbound
      apply hbound.trans
      gcongr
      norm_num
    · apply residual_radial_exception_bound hq hcard hI σ g S.card χ hσq hσ hg hghi hquarter S S
        (Finset.Subset.refl _) (le_refl _) hSn O δ hδ (by linarith only [hχb,hb]) _ Lines hLines Q
      intro U hU
      obtain ⟨j,hj,hjU⟩ := hcover U hU
      have hh := hres j hj
      rw [←hS,ht] at hh
      have he : (S.filter fun y => y.submodule≤U)=S∩flatPoints (Flat j) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hjU]
      rw [he]
      exact hh.le
  · rw [radialExceptions_low_density S O δ hδ0 Lines hLines Q q (Real.exp (3*σ/2+g)) g χ
      hq0 (Real.exp_pos _) hsq (by linarith only [hχb,le_of_not_gt hen]) hmass.le]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

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
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma eventually_exception_decay {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (C : ℝ) (hC : 0<C) :
    ∀ᶠ σ : ℝ in atTop,∀ D R : ℝ,Range η σ D R →
      C*σ*Real.exp (-P η σ D R/20000)≤Real.exp (-L η σ D/1000) := by
  have habs := eventually_power_absorption hη hη' C 1 (1/40000) hC (by norm_num) (by norm_num)
  have hlarge := (tendsto_rpow_atTop (beta_pos hη)).eventually (eventually_ge_atTop (40:ℝ))
  filter_upwards [eventually_ge_atTop (1:ℝ),habs,hlarge] with σ hσ habs hlarge
  intro D R hr
  have hb := finite_bounds hη hη' hσ hr
  have hL : 0<L η σ D := by dsimp [L];exact mul_pos hb.1 (Real.rpow_pos_of_pos (by linarith only [hσ]) _)
  have hR : 40≤R := hlarge.trans hr.rlo
  have hLP : 40*L η σ D≤P η σ D R := by dsimp [P];nlinarith only [hL,hR]
  have hc : C*σ≤Real.exp (P η σ D R/40000) := by
    simpa only [Real.rpow_one,one_mul,one_div,mul_comm (40000⁻¹:ℝ),div_eq_mul_inv] using habs D R hr
  calc
    _ ≤ Real.exp (P η σ D R/40000)*Real.exp (-P η σ D R/20000) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (-P η σ D R/40000) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hLP])

theorem eventually_exception_payment_wide {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (A B M : ℝ) (hA : 0≤A) (hB : 0≤B) (hM : 0<M) :
    ∀ᶠ σ : ℝ in atTop,∀ (D R g χ : ℝ) (m : ℕ),Range η σ D R →
      P η σ D R/10000≤g → P η σ D R/200≤χ → (m:ℝ)≤Real.exp (3*σ) →
      ((Nat.clog 2 m:ℝ)+1)*(A*Real.exp (-(4/5:ℝ)*g)+B*Real.exp (-χ))≤
        Real.exp (-L η σ D/1000)/M := by
  have hC : 0<8*M*(1+A+B) := by positivity
  have he := eventually_exception_decay hη hη' (8*M*(1+A+B)) hC
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with σ hσ he
  intro D R g χ m hr hg hχ hm
  have hb := finite_bounds hη hη' hσ hr
  have hL : 0<L η σ D := by dsimp [L];exact mul_pos hb.1 (Real.rpow_pos_of_pos (by linarith only [hσ]) _)
  have hP : 0<P η σ D R := mul_pos hL hb.2.1
  have h1 : Real.exp (-(4/5:ℝ)*g)≤Real.exp (-P η σ D R/20000) :=
    Real.exp_le_exp.mpr (by linarith only [hg,hP])
  have h2 : Real.exp (-χ)≤Real.exp (-P η σ D R/20000) :=
    Real.exp_le_exp.mpr (by linarith only [hχ,hP])
  have hsum : A*Real.exp (-(4/5:ℝ)*g)+B*Real.exp (-χ)≤
      (1+A+B)*Real.exp (-P η σ D R/20000) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_left h2 hB)
    nlinarith only [hh,Real.exp_pos (-P η σ D R/20000)]
  apply (le_div_iff₀ hM).mpr
  calc
    _ ≤ (8*σ)*((1+A+B)*Real.exp (-P η σ D R/20000))*M :=
      mul_le_mul_of_nonneg_right (mul_le_mul (dyad_count_le hσ hm) hsum (by positivity) (by linarith only [hσ])) hM.le
    _ = (8*M*(1+A+B))*σ*Real.exp (-P η σ D R/20000) := by ring
    _ ≤ _ := he D R hr

end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreScalars

lemma strong_exception_payment {q n E a P : ℝ} (_hq : 0≤q) (hn : 0<n) (hE : 0≤E)
    (ha : Real.exp (-P)≤a) (hnq : q^2≤4*n*Real.exp (4*P))
    (hcount : E*a^2≤333024*q^2) (hbig : (1332096:ℝ)≤Real.exp P) :
    E≤n*Real.exp (7*P) := by
  have ha0 : 0≤a := (Real.exp_pos _).le.trans ha
  have hsq : Real.exp (-2*P)≤a^2 := by
    calc
      Real.exp (-2*P)=(Real.exp (-P))^2 := by rw [←Real.exp_nat_mul];congr 1;ring
      _≤a^2 := pow_le_pow_left₀ (Real.exp_nonneg (-P)) ha 2
  have hh : E*Real.exp (-2*P)≤333024*q^2 :=
    (mul_le_mul_of_nonneg_left hsq hE).trans hcount
  have hcancel : (E*Real.exp (-2*P))*Real.exp (2*P)=E := by
    rw [mul_assoc,←Real.exp_add];simp
  calc
    E=(E*Real.exp (-2*P))*Real.exp (2*P) := hcancel.symm
    _≤(333024*q^2)*Real.exp (2*P) := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
    _≤(333024*(4*n*Real.exp (4*P)))*Real.exp (2*P) := by gcongr
    _=1332096*n*Real.exp (6*P) := by
      rw [show (333024*(4*n*Real.exp (4*P)))*Real.exp (2*P)=1332096*n*(Real.exp (4*P)*Real.exp (2*P)) by ring,
        ←Real.exp_add];congr 2;ring
    _≤Real.exp P*n*Real.exp (6*P) := by gcongr
    _=n*Real.exp (7*P) := by rw [mul_assoc,mul_left_comm (Real.exp P),←Real.exp_add];congr 2;ring
end SharpRamseyFive.ScoreScalars

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneStrongExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀x : ℙ K V,Fintype (RadialLine x)]

omit [∀x : ℙ K V,Fintype (RadialLine x)] in
lemma captured_global_rich {I : Type} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (Flat : I→Submodule K V)
    (X S : Finset (ℙ K V)) (hFlat : ∀i∈F,finrank K (Flat i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ) ≤ X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
    (δ : ℝ≥0) (hδ : 0<δ) (a : ℝ) (hacut : 8*(δ:ℝ)*(j+1) ≤ a)
    (hmass : (δ:ℝ)*X.card ≤ 4*Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2) :
    (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2 ≤ 3072*(Nat.card K:ℝ)^2 := by
  have hδ' : 0<(δ:ℝ) := hδ
  have ha4 : 4*(δ:ℝ) ≤ a := by nlinarith only [hacut,hδ',(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  obtain ⟨M,hM,hlo,hhi⟩ := exists_scale hδ' ha4
  have hjM : j ≤ M := by
    have hh : (j:ℝ) ≤ M := by nlinarith only [hacut,hhi,hδ']
    exact_mod_cast hh
  have hm := captured_rich_centers F hF Flat X hFlat Lines hLines j M hM hjM hj O hO δ a hδ' hlo hhi
  have hs : (∑l∈Lines,((richCenters S O δ a l).card:ℝ)) ≤
      ∑l∈Lines,((richCenters (X\remaining F hF (fun i => flatPoints (Flat i)) X j) O δ a l).card:ℝ) := by
    apply Finset.sum_le_sum
    intro l hl
    exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S _ O O δ a δ.coe_nonneg hS
      (fun _ => Finset.Subset.refl _) l))
  apply ((mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm).trans
  nlinarith only [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (δ:ℝ)*X.card) hmass 2]

end

section

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I J : Type} [Field K] [Finite K] [Fintype I] [LinearOrder J]
  [∀x : ℙ K (I→K),Fintype (RadialLine x)]

omit [∀x : ℙ K (I→K),Fintype (RadialLine x)] in
theorem literal_plane_global_rich {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g b a : ℝ) (hσq : Real.exp σ=q) (hσ : 1000 ≤ σ)
    (hb : 100000000 ≤ b) (hen : b<g) (hghi : g ≤ 2*σ)
    (ha : Real.exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
    (hFlat : ∀j∈F,finrank K (Flat j)=3)
    (hcover : ∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U)
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ) ≤ Real.exp (3*σ/2+g))
    (t : ℝ) (ht : t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (ht0 : 0<t) (S : Finset (ℙ K (I→K)))
    (hS : S=peelSet (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0))
    (hquarter : Real.exp (3*σ/2+g)/4 ≤ S.card)
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (hO : ∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
      (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x)
    (δ : ℝ≥0) (hδ : (δ:ℝ)=(q:ℝ)/S.card)
    (Lines : Finset (Submodule K (I→K))) (hLines : ∀l∈Lines,finrank K l=2) :
    (∑l∈Lines,((richCenters S (fun x => S∩O x) δ a l).card:ℝ))*a^2 ≤ 333024*(q:ℝ)^2 := by
  simp only [richCenters_clip]
  have hq0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hδ0 : 0<δ := by rw [←NNReal.coe_pos,hδ];positivity
  have hsub : S⊆X := hS▸peel_subset (b<g) F hF (fun j => flatPoints (Flat j)) X _ _
  have hSn : (S.card:ℝ) ≤ Real.exp (3*σ/2+g) := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hX
  have hscale : Real.exp (3*σ/2+g)*(δ:ℝ) ≤ 4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hquarter,hq0]
  have hg : 100000000 ≤ g := hb.trans hen.le
  have htE : t=Real.exp (σ+17*g/15) := ht.trans (ScoreScalars.plane_threshold_exp rfl rfl)
  have htq : (q:ℝ) ≤ t := by rw [htE,←hσq];apply Real.exp_le_exp.mpr;linarith only [hg]
  rcases peel_residual_real (b<g) hen F hF (fun j => flatPoints (Flat j)) X t ht0 with hcap|⟨hJ,hres⟩
  · have hc : S⊆X\remaining F hF (fun j => flatPoints (Flat j)) X
        (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) := by
      rw [hS,hcap]
    have hjt := peel_length_real (b<g) F hF (fun j => flatPoints (Flat j)) X t ht0
    have hjq : (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0):ℝ)*(Nat.card K:ℝ) ≤ X.card := by
      rw [hcard];exact (mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg _)).trans hjt
    have hcut := ScoreScalars.plane_list_cutoff (n:=Real.exp (3*σ/2+g)) (q:=(q:ℝ))
      rfl hσq.symm htE (by linarith only [hg]) hghi δ.coe_nonneg (Nat.cast_nonneg _)
      (hjt.trans hX) hscale
    have hmass : (δ:ℝ)*X.card ≤ 4*Nat.card K := by
      rw [hcard];exact (mul_le_mul_of_nonneg_left hX δ.coe_nonneg).trans (by simpa only [mul_comm] using hscale)
    have hh := captured_global_rich F hF Flat X S hFlat _ hc hjq O hO δ hδ0 a (hcut.trans ha) hmass Lines hLines
    rw [hcard] at hh
    nlinarith only [hh,sq_nonneg (q:ℝ)]
  · rw [hδ]
    apply residual_rich_centers hq hcard hI σ g S.card a hσq hσ hg hghi hquarter ha ha2 S hSn Lines hLines O
    intro U hU
    obtain ⟨j,hj,hjU⟩ := hcover U hU
    have hh := hres j hj
    rw [←hS,ht] at hh
    have he : (S.filter fun y => y.submodule ≤ U)=S∩flatPoints (Flat j) := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hjU]
    rw [he]
    exact hh.le

omit [∀x : ℙ K (I→K),Fintype (RadialLine x)] in
lemma strong_exceptions_of_global (S : Finset (ℙ K (I→K)))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K))) (δ a : ℝ)
    (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))) {C : ℝ}
    (hglobal : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2 ≤ C) :
    ((badCenters S O δ a Lines Q 1).card:ℝ)*a^2 ≤ C := by
  have hh := badCenters_mass_le S O δ a Lines Q 1
  rw [mul_one] at hh
  exact (mul_le_mul_of_nonneg_right hh (sq_nonneg a)).trans hglobal

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_literal_plane_exceptions_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
      (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
      2<q → Nat.card K=q → Real.exp σ=q → (Fintype.card I=4 ∨ Fintype.card I=5) →
      g≤2*σ → (∀j∈F,finrank K (Flat j)=3) →
      (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
      (X.card:ℝ)≤Real.exp (3*σ/2+g) →
      t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5) →
      S=peelSet (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
      Real.exp (3*σ/2+g)/4≤S.card → (S.card:ℝ)≤Real.exp (3*σ) →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
      (∀l∈Lines,finrank K l=2) →
      let O' := fun x => S∩O x
      ((radialExceptions S O' (pointStrength S) Lines Q q S.card (P η σ D R/200)).card:ℝ)≤
        (S.card:ℝ)*Real.exp (-L η σ D/1000)/2 ∧
      ((ambientStrongExceptions σ (P η σ D R) S O' Lines Q).card:ℝ)≤
        (S.card:ℝ)*Real.exp (7*P η σ D R) := by
  have he := eventually_exception_payment_wide hη hη' 0 2664192 8 (by norm_num) (by norm_num) (by norm_num)
  have ha := eventually_plane_ambient_margins hη hη'
  filter_upwards [eventually_ge_atTop (1000:ℝ),he,ha] with σ hσ he ha
  intro D R hr q K I J _ _ _ _ _ _ g F hF Flat X S t ht0 O Lines Q hq hcard hσq hI
    hghi hFlat hcover hX ht hS hquarter hcardS hO hLines
  dsimp only
  let P := ParameterHierarchy.P η σ D R
  have ha := ha D R hr
  have hP : 0<P := by dsimp [P];linarith only [ha.1]
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hSn : (S.card:ℝ)≤Real.exp (3*σ/2+g) :=
    (Nat.cast_le.mpr (Finset.card_le_card (hS▸peel_subset (P/10000<g) F hF (fun j => flatPoints (Flat j)) X _ _))).trans hX
  have hδ : (pointStrength (K:=K) S:ℝ)=(q:ℝ)/S.card := by simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast,hcard]
  constructor
  · have hcount := literal_plane_radial_exceptions hq hcard hI σ g (P/10000) (P/200) hσq hσ
      ha.1 (by linarith only [hP]) hghi F hF Flat hFlat hcover X hX t ht ht0 S hS hquarter O hO
      (pointStrength S) hδ Lines hLines Q
    have hsub := radialExceptions_normalization S (fun x => S∩O x) (pointStrength S)
      Lines Q q (P/200) S.card (Real.exp (3*σ/2+g)) hn0 hSn
    have hpay := he D R (P/10000) (P/200) S.card hr (le_refl _) (le_refl _) hcardS
    simp only [zero_mul,zero_add] at hpay
    have hcount' := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcount
    calc
      _≤Real.exp (3*σ/2+g)*(2664192*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-P/200)) := by
        simpa only [neg_div] using hcount'
      _=Real.exp (3*σ/2+g)*(((Nat.clog 2 S.card:ℝ)+1)*(2664192*Real.exp (-P/200))) := by ring
      _≤Real.exp (3*σ/2+g)*(Real.exp (-L η σ D/1000)/8) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        simpa only [neg_div] using hpay
      _≤_ := by nlinarith only [mul_le_mul_of_nonneg_right hquarter (Real.exp_nonneg (-L η σ D/1000))]
  · by_cases hsmall : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P)
    · dsimp only [ambientStrongExceptions]
      rw [ite_eq_left hsmall,Finset.card_empty,Nat.cast_zero]
      positivity
    · rw [ambientStrongExceptions,ite_eq_right hsmall]
      let a : ℝ := 1/(100*(momentOrder σ P:ℝ))
      have hlow : (q:ℝ)^2*Real.exp (-4*P)≤S.card := by rw [←hcard];exact (le_of_not_ge hsmall)
      have hglo : σ/2-4*P≤g := by
        have hh := hlow.trans hSn
        rw [←hσq,←Real.exp_nat_mul,←Real.exp_add] at hh
        have hh := Real.exp_le_exp.mp hh
        norm_num at hh
        linarith only [hh]
      have hen : P/10000<g := ha.2.1.trans_le hglo
      have hg20 : 20*P≤g := ha.2.2.1.trans hglo
      have hacut : Real.exp (-g/20)≤a :=
        (Real.exp_le_exp.mpr (by linarith only [hg20])).trans ha.2.2.2.1
      have hc := literal_plane_global_rich hq hcard hI σ g (P/10000) a hσq hσ ha.1 hen hghi hacut ha.2.2.2.2.1
        F hF Flat hFlat hcover X hX t ht ht0 S hS hquarter O hO (pointStrength S) hδ Lines hLines
      have hc := strong_exceptions_of_global S (fun x => S∩O x) (pointStrength S) a Lines Q hc
      have hnq : (q:ℝ)^2≤4*(S.card:ℝ)*Real.exp (4*P) := by
        have hh := mul_le_mul_of_nonneg_right hlow (Real.exp_nonneg (4*P))
        have hcan : ((q:ℝ)^2*Real.exp (-4*P))*Real.exp (4*P)=(q:ℝ)^2 := by
          rw [mul_assoc,←Real.exp_add];simp
        rw [hcan] at hh
        nlinarith only [hh,mul_nonneg hn0.le (Real.exp_nonneg (4*P))]
      exact ScoreScalars.strong_exception_payment (Nat.cast_nonneg q) hn0 (Nat.cast_nonneg _)
        ha.2.2.2.1 hnq hc ha.2.2.2.2.2
end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions_oai
