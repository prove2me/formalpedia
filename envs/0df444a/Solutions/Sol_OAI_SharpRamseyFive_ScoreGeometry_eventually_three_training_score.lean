-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:42:01.250996+00:00
-- url     : https://prove2.me/submissions/9243638b-fa6f-4db9-b698-f38e8ad814e9

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_cell_score_from_integrals
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_three_score_integrals

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

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma cell_subset (k : ℕ) : cell F hF shape X k ⊆ remaining F hF shape X k :=
  Finset.inter_subset_left

lemma cell_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (cell F hF shape X i) (cell F hF shape X j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hx : x ∈ remaining F hF shape X (i+1) :=
    remaining_antitone F hF shape X hij (cell_subset F hF shape X j hxj)
  have hxnot := (Finset.mem_sdiff.mp hx).2
  exact hxnot (Finset.mem_inter.mp hxi).2

lemma retained_subset (threshold : ℕ) (hthreshold : 0 < threshold) :
    retained F hF shape X threshold hthreshold ⊆ X := by
  unfold retained
  split
  · exact Finset.sdiff_subset
  · exact remaining_subset F hF shape X _

lemma retained_half (threshold : ℕ) (hthreshold : 0 < threshold) :
    X.card ≤ 2*(retained F hF shape X threshold hthreshold).card := by
  have hsub := Finset.card_le_card (remaining_subset F hF shape X
    (stopIndex F hF shape X threshold hthreshold))
  unfold retained
  split
  · rename_i h
    rw [Finset.card_sdiff_of_subset (remaining_subset F hF shape X _)]
    exact h
  · rename_i h
    omega

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

lemma cell_earliest (j : ℕ) (x : V) :
    x ∈ cell F hF shape X j ↔
      x ∈ X ∧ x ∈ shape (chosen F hF shape X j) ∧ ∀ i < j, x ∉ shape (chosen F hF shape X i) := by
  unfold cell
  rw [Finset.mem_inter, remaining_eq_sdiff_union]
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, not_exists, not_and]
  tauto

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

end SharpRamseyFive.ParameterHierarchy

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

lemma peel_half (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    X.card≤2*(peelSet e F hF shape X k hk).card := by
  unfold peelSet
  split_ifs
  · exact retained_half F hF shape X k hk
  · omega

lemma clippedPart_subset (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (i : Option (Fin J)) :
    clippedPart S F hF shape X J i⊆S := by
  cases i
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left

lemma clippedPart_disjoint (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) :
    Pairwise (fun i j => Disjoint (clippedPart S F hF shape X J i) (clippedPart S F hF shape X J j)) := by
  intro i j hij
  cases i with
  | none => simp [clippedPart]
  | some i =>
    cases j with
    | none => simp [clippedPart]
    | some j =>
      have hneq : i≠j := by simpa only [ne_eq,Option.some.injEq] using hij
      have hv : i.val≠j.val := fun hh => hneq (Fin.ext hh)
      rcases lt_or_gt_of_ne hv with h|h
      · exact (cell_disjoint_of_lt F hF shape X h).mono Finset.inter_subset_right Finset.inter_subset_right
      · exact (cell_disjoint_of_lt F hF shape X h).symm.mono Finset.inter_subset_right Finset.inter_subset_right

lemma clippedPart_query (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) :
    clippedPart S F hF shape X J (queryPart F hF shape X J x)=S∩ownCell F hF shape X J x := by
  unfold queryPart ownCell
  split_ifs with h
  · rfl
  · simp [clippedPart]

end SharpRamseyFive.GreedyTraining

namespace SharpRamseyFive.TrainingCells
open scoped BigOperators Classical
variable {A H P : Type*} [DecidableEq A] [Fintype H] [Fintype P]

lemma sum_card_le (S : Finset A) {J : Type*} [Fintype J] (C : J→Finset A)
    (hsub : ∀j,C j⊆S) (hdis : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (∑j,(C j).card)≤S.card := by
  have hpair : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint C :=
    fun i _ j _ hij => hdis hij
  rw [←Finset.card_biUnion hpair]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr fun j _ => hsub j)

lemma small_union (S : Finset A) (C D : Finset A) (hS : S.Nonempty)
    (hC : (C.card:ℝ)≤(S.card:ℝ)/25) (hD : (D.card:ℝ)≤(S.card:ℝ)/25) :
    ((C∪D).card:ℝ)/(S.card:ℝ)≤2/25 := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hS.card_pos)).mpr
  have hc : ((C∪D).card:ℝ)≤(C.card:ℝ)+D.card := by exact_mod_cast Finset.card_union_le C D
  linarith only [hc,hC,hD]

end SharpRamseyFive.TrainingCells

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable [FiniteDimensional K V]

lemma incident_eval (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident b (projectiveEquiv (Module.evalEquiv K V) a) ↔ Incident a b := by
  change Incident b (Projectivization.map (Module.evalEquiv K V).toLinearMap (Module.evalEquiv K V).injective a) ↔ _
  conv_lhs => rw [←a.mk_rep,Projectivization.map_mk,incident_mk_right]
  rw [incident_iff]
  rfl

variable [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

omit [Finite K] [Fintype (ℙ K V)] in
lemma weightOnPencil_eq (w : ℙ K (Module.Dual K V) → ℝ) (a : ℙ K V) :
    weightOnPencil w a = weightOnHyperplane w (projectiveEquiv (Module.evalEquiv K V) a) := by
  unfold weightOnPencil weightOnHyperplane
  apply Finset.sum_congr rfl
  intro b _
  simp only [incidenceEntry,incident_eval]

theorem pencil_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (w : ℙ K (Module.Dual K V) → ℝ) :
    ∑ a, (weightOnPencil w a -
      ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b))^2 ≤
      (Nat.card K:ℝ)^(d-1)*∑ b,w b^2 := by
  let : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
  let := Fintype.ofFinite (ℙ K (Module.Dual K (Module.Dual K V)))
  have hd' : finrank K (Module.Dual K V) = d+1 := by simpa only [Subspace.dual_finrank_eq] using hdim
  have h := incidence_variance hd' hd w
  rw [←(projectiveEquiv (Module.evalEquiv K V)).sum_comp] at h
  simpa only [←weightOnPencil_eq] using h

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_LargeValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PencilRegularity
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

lemma large_value_count {I : Type*} [Fintype I] (f : I → ℝ) (μ h : ℝ)
    (hh : 0 ≤ h) (hμ : μ ≤ h/2) :
    ((Finset.univ.filter fun i => h ≤ f i).card:ℝ) * h^2 ≤
      4*∑ i,(f i-μ)^2 := by
  let E := Finset.univ.filter fun i => h ≤ f i
  have hb (i : I) (hi : i ∈ E) : h^2 ≤ 4*(f i-μ)^2 := by
    have hf := (Finset.mem_filter.mp hi).2
    have hs : h/2 ≤ f i-μ := by linarith
    nlinarith [sq_nonneg (f i-μ-h/2)]
  have hs := Finset.sum_le_sum (s:=E) hb
  simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
    (fun i _ _ => sq_nonneg _)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem clipped_pencil_count {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (w : ℙ K (Module.Dual K V) → ℝ) (hw0 : ∀ b,0 ≤ w b) (hw1 : ∀ b,w b ≤ 1)
    (h : ℝ) (hh : 0 ≤ h)
    (hmean : ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b) ≤ h/2) :
    ((Finset.univ.filter fun a => h ≤ weightOnPencil w a).card:ℝ)*h^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(∑ b,w b) := by
  have hc := large_value_count (weightOnPencil w) _ h hh hmean
  have hv := pencil_variance hdim hd w
  have hn : (∑ b,w b^2) ≤ ∑ b,w b := Finset.sum_le_sum fun b _ => by
    nlinarith [mul_nonneg (hw0 b) (sub_nonneg.mpr (hw1 b))]
  calc
    _ ≤ 4*∑ a,(weightOnPencil w a -
        ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b))^2 := hc
    _ ≤ 4*((Nat.card K:ℝ)^(d-1)*∑ b,w b^2) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ ≤ 4*((Nat.card K:ℝ)^(d-1)*∑ b,w b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (by positivity)) (by norm_num)
    _ = _ := by ring

theorem family_irregular_count {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    {J : Type*} [Fintype J] (w : J → ℙ K (Module.Dual K V) → ℝ)
    (hw0 : ∀ j b,0 ≤ w j b) (hw1 : ∀ j b,w j b ≤ 1) (h : ℝ) (hh : 0 ≤ h)
    (hmean : ∀ j, ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w j b) ≤ h/2) :
    ((Finset.univ.filter fun a => ∃ j,h ≤ weightOnPencil (w j) a).card:ℝ)*h^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(∑ j,∑ b,w j b) := by
  let E : J → Finset (ℙ K V) := fun j => Finset.univ.filter fun a => h ≤ weightOnPencil (w j) a
  have heq : (Finset.univ.filter fun a => ∃ j,h ≤ weightOnPencil (w j) a) =
      Finset.univ.biUnion E := by ext a; simp [E]
  rw [heq]
  have hc : ((Finset.univ.biUnion E).card:ℝ) ≤ ∑ j,((E j).card:ℝ) := by
    exact_mod_cast Finset.card_biUnion_le (s:=Finset.univ) (t:=E)
  calc
    _ ≤ (∑ j,((E j).card:ℝ))*h^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg h)
    _ = ∑ j,((E j).card:ℝ)*h^2 := Finset.sum_mul ..
    _ ≤ ∑ j,4*(Nat.card K:ℝ)^(d-1)*(∑ b,w j b) := Finset.sum_le_sum fun j _ =>
      clipped_pencil_count hdim hd (w j) (hw0 j) (hw1 j) h hh (hmean j)
    _ = _ := (Finset.mul_sum ..).symm

end SharpRamseyFive.PencilRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_CellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.CellVariance
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

lemma sum_shift_square {I : Type*} [Fintype I] (f : I → ℝ) (a b : ℝ) :
    (∑ i,(f i-b)^2) ≤ 2*(∑ i,(f i-a)^2)+2*Fintype.card I*(a-b)^2 := by
  calc
    _ ≤ ∑ i,(2*(f i-a)^2+2*(a-b)^2) := Finset.sum_le_sum fun i _ => by
      nlinarith [sq_nonneg ((f i-a)-(a-b))]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Module.Dual K V))] in
lemma weight_indicator (C : Finset (ℙ K V)) (δ : ℝ) (b : ℙ K (Module.Dual K V)) :
    weightOnHyperplane (fun a => if a ∈ C then δ else 0) b = cellMass C δ b := by
  simp only [weightOnHyperplane,mul_ite,mul_zero,Finset.sum_ite_mem,Finset.univ_inter]
  rw [← Finset.sum_mul]
  have he : (∑ a ∈ C,incidenceEntry a b) = ((C.filter fun a => Incident a b).card:ℝ) := by
    exact Finset.sum_boole _ _
  rw [he,cellMass,mul_comm]

theorem cell_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (C : Finset (ℙ K V)) (δ : ℝ) :
    ∑ b,(cellMass C δ b - δ*C.card/(Nat.card K:ℝ))^2 ≤
      4*δ^2*(Nat.card K:ℝ)^(d-1)*C.card := by
  let q : ℝ := Nat.card K
  let N : ℝ := Q (Nat.card K) d
  let c : ℝ := C.card
  let p : ℝ := (Q (Nat.card K) (d-1):ℝ)/N
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Q_pos (Nat.card K) d
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcN : c ≤ N := by
    dsimp [c,N]
    exact_mod_cast (C.card_le_univ.trans_eq (card_points hdim))
  have hp : p-1/q = -(1/(q*N)) := by
    dsimp [p]
    have hr : N = q*(Q (Nat.card K) (d-1):ℝ)+1 := by
      dsimp [N,q]
      exact_mod_cast Q_recurrence (q:=Nat.card K) hd
    field_simp
    nlinarith
  let w : ℙ K V → ℝ := fun a => if a ∈ C then δ else 0
  have hsum : (∑ a,w a) = δ*c := by simp [w,c,Finset.sum_ite_mem,mul_comm]
  have hsq : (∑ a,w a^2) = δ^2*c := by simp [w,c,Finset.sum_ite_mem,mul_comm]
  have hv := incidence_variance hdim hd w
  rw [hsum,hsq] at hv
  simp_rw [show ∀ b,weightOnHyperplane w b = cellMass C δ b from fun b => weight_indicator C δ b] at hv
  change (∑ b,(cellMass C δ b-p*(δ*c))^2) ≤ q^(d-1)*(δ^2*c) at hv
  have he : p*(δ*c)-δ*c/q = -(δ*c/(q*N)) := by
    calc
      _ = (p-1/q)*(δ*c) := by ring
      _ = _ := by rw [hp]; ring
  have hcor : N*(p*(δ*c)-δ*c/q)^2 ≤ δ^2*c := by
    rw [he]
    have heq : N*(-(δ*c/(q*N)))^2 = δ^2*c^2/(q^2*N) := by
      have hq0 : q ≠ 0 := by linarith
      field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < q^2*N)).mpr
    have hq2 : 1 ≤ q^2 := by nlinarith
    have hbound : c ≤ q^2*N := hcN.trans (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hbound (mul_nonneg (sq_nonneg δ) hc)
    nlinarith
  have hpow : 1 ≤ q^(d-1) := one_le_pow₀ hq
  have hs := sum_shift_square (cellMass C δ) (p*(δ*c)) (δ*c/q)
  rw [card_hyperplanes hdim] at hs
  change (∑ b,(cellMass C δ b-δ*c/q)^2) ≤ 2*(∑ b,(cellMass C δ b-p*(δ*c))^2)+
    2*N*(p*(δ*c)-δ*c/q)^2 at hs
  change (∑ b,(cellMass C δ b-δ*c/q)^2) ≤ 4*δ^2*q^(d-1)*c
  have hh := mul_le_mul_of_nonneg_right hpow (mul_nonneg (sq_nonneg δ) hc)
  nlinarith

end SharpRamseyFive.CellVariance

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_Scale
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

omit [Field K] [Finite K] in
lemma scale_nonneg (d : ℕ) (n : ℝ) (hn : 0≤n) : 0≤ scale (K:=K) d n := by
  unfold scale
  positivity

lemma cell_variance_scale {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (C : Finset (ℙ K V)) {n : ℝ} (hn : 0<n) :
    (∑ H,(cellMass C ((Nat.card K:ℝ)/n) H-(C.card:ℝ)/n)^2)≤
      4*(Nat.card K:ℝ)*scale (K:=K) d n*(C.card/n) := by
  have hq : (Nat.card K:ℝ)≠0 := by exact_mod_cast (Nat.card_pos (α:=K)).ne'
  have hv := cell_variance hdim hd C ((Nat.card K:ℝ)/n)
  have he (a : ℝ) : a^(d-1)*a=a^d := by rw [←pow_succ]; congr 1; omega
  have hc : ((Nat.card K:ℝ)/n)*C.card/(Nat.card K:ℝ)=(C.card:ℝ)/n := by field_simp
  rw [hc] at hv
  convert hv using 1
  all_goals try with_reducible_and_instances rfl
  unfold scale
  rw [←he (Nat.card K:ℝ)]
  ring

lemma total_deviation_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    (∑ j : Option J,∑ H,(deviation S C j H)^2)≤
      16*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hsum : (∑ j : Option J,((familyCell S C j).card:ℝ)/(S.card:ℝ))≤4 := by
    rw [Fintype.sum_option]
    simp only [familyCell,div_self hn.ne',←Finset.sum_div]
    have hC' : (∑ j,((C j).card:ℝ))≤3*(S.card:ℝ) := by exact_mod_cast hC
    have hh := (div_le_iff₀ hn).mpr hC'
    linarith
  calc
    _ ≤ ∑ j : Option J,4*(Nat.card K:ℝ)*scale (K:=K) d S.card*
        ((familyCell S C j).card/(S.card:ℝ)) :=
      Finset.sum_le_sum fun j _ => cell_variance_scale hdim hd _ hn
    _ = 4*(Nat.card K:ℝ)*scale (K:=K) d S.card*
        (∑ j : Option J,((familyCell S C j).card:ℝ)/(S.card:ℝ)) :=
      (Finset.mul_sum ..).symm
    _ ≤ 4*(Nat.card K:ℝ)*scale (K:=K) d S.card*4 :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) (scale_nonneg _ _ hn.le))
    _ = _ := by ring

lemma exceptional_card_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    ((exceptional S C).card:ℝ)≤40000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  have hsq (H : ℙ K (Dual K V)) (hH : H∈exceptional S C) :
      (1:ℝ)≤2500*∑ j : Option J,(deviation S C j H)^2 := by
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hH).2
    have ht : (1/50:ℝ)≤threshold j := by cases j <;> norm_num [threshold]
    have h := ht.trans hj.le
    have he := sq_abs (deviation S C j H)
    have ha := abs_nonneg (deviation S C j H)
    have hu : (deviation S C j H)^2≤∑ k : Option J,(deviation S C k H)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (deviation S C k H)) (Finset.mem_univ j)
    nlinarith
  have hn : 0≤ scale (K:=K) d S.card := scale_nonneg _ _ (Nat.cast_nonneg _)
  calc
    _ = ∑ H∈exceptional S C,(1:ℝ) := by simp
    _ ≤ ∑ H∈exceptional S C,2500*∑ j : Option J,(deviation S C j H)^2 :=
      Finset.sum_le_sum hsq
    _ = 2500*∑ H∈exceptional S C,∑ j : Option J,(deviation S C j H)^2 :=
      (Finset.mul_sum ..).symm
    _ ≤ 2500*∑ H,∑ j : Option J,(deviation S C j H)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by norm_num)
    _ = 2500*∑ j : Option J,∑ H,(deviation S C j H)^2 := by rw [Finset.sum_comm]
    _ ≤ 2500*(16*(Nat.card K:ℝ)*scale (K:=K) d S.card) :=
      mul_le_mul_of_nonneg_left (total_deviation_bound hdim hd S C hS hC) (by norm_num)
    _ = _ := by ring

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClippedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance PencilRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma clippedWeight_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (j : Option (Option J)) (H : ℙ K (Dual K V)) :
    0 ≤ clippedWeight S C j H ∧ clippedWeight S C j H≤1 := by
  cases j with
  | none => simp only [clippedWeight]; split <;> norm_num
  | some j => exact ⟨le_min (by norm_num) (sq_nonneg _),min_le_left _ _⟩

lemma clippedWeight_sum_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    (∑ j : Option (Option J),∑ H,clippedWeight S C j H)≤
      50000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  rw [Fintype.sum_option]
  have hi : (∑ H,clippedWeight S C none H)=((exceptional S C).card:ℝ) := by
    simp [clippedWeight]
  rw [hi]
  have hc : (∑ j : Option J,∑ H,clippedWeight S C (some j) H)≤
      ∑ j : Option J,∑ H,(deviation S C j H)^2 :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun H _ => min_le_right _ _
  have he := exceptional_card_bound hdim hd S C hS hC
  have hv := total_deviation_bound hdim hd S C hS hC
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) (Nat.cast_nonneg _)
  nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.card K) : (0:ℝ)≤Nat.card K) hB]

lemma mean_ratio_le {d : ℕ} (hd : 1≤d) :
    ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)≤1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  have he : (Q (Nat.card K) d:ℝ)=(Nat.card K:ℝ)*Q (Nat.card K) (d-1)+1 :=
    by exact_mod_cast Q_recurrence (q:=Nat.card K) hd
  nlinarith

theorem irregular_card_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card)
    {ξ : ℝ} (hξ : 100000≤Real.exp ξ) :
    ((irregular (d:=d) S C ξ).card:ℝ)≤200000*(S.card:ℝ)*Real.exp (-2*ξ) := by
  let B : ℝ := scale (K:=K) d S.card
  let w := clippedWeight S C
  have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hB : 0<B := by dsimp [B,scale]; positivity
  have hw : ∀ j H,0≤w j H := fun j H => (clippedWeight_bounds S C j H).1
  have htotal := clippedWeight_sum_bound hdim hd S C hS hC
  have hmean (j : Option (Option J)) :
      ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ H,w j H) ≤ B*Real.exp ξ/2 := by
    have hs : (∑ H,w j H)≤∑ i : Option (Option J),∑ H,w i H :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun H _ => hw i H) (Finset.mem_univ j)
    have hc : ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)≥0 := by positivity
    calc
      _ ≤ (1/(Nat.card K:ℝ))*(∑ H,w j H) :=
        mul_le_mul_of_nonneg_right (mean_ratio_le (K:=K) hd) (Finset.sum_nonneg fun H _ => hw j H)
      _ ≤ (1/(Nat.card K:ℝ))*(50000*(Nat.card K:ℝ)*B) :=
        mul_le_mul_of_nonneg_left (hs.trans htotal) (by positivity)
      _ = 50000*B := by field_simp
      _ ≤ _ := by nlinarith
  have hr := family_irregular_count hdim hd w hw
    (fun j H => (clippedWeight_bounds S C j H).2) (B*Real.exp ξ) (by positivity) hmean
  have hcard : ((irregular (d:=d) S C ξ).card:ℝ)≤
      ((Finset.univ.filter fun x : ℙ K V => ∃ j : Option (Option J),
        B*Real.exp ξ≤weightOnPencil (w j) x).card:ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj.le⟩
  have hp : (Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ)=(Nat.card K:ℝ)^d := by
    rw [←pow_succ]; congr 1; omega
  have he : (Nat.card K:ℝ)^d=B*S.card := by dsimp [B,scale]; field_simp
  have hb : ((irregular (d:=d) S C ξ).card:ℝ)*(B*Real.exp ξ)^2≤
      200000*(S.card:ℝ)*B^2 := by
    calc
      _ ≤ 4*(Nat.card K:ℝ)^(d-1)*(∑ j,∑ H,w j H) :=
        (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)).trans hr
      _ ≤ 4*(Nat.card K:ℝ)^(d-1)*(50000*(Nat.card K:ℝ)*B) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by rw [show 4*(Nat.card K:ℝ)^(d-1)*(50000*(Nat.card K:ℝ)*B)=
        200000*((Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ))*B by ring,hp,he]; ring
  have hb' : ((irregular (d:=d) S C ξ).card:ℝ)*(Real.exp ξ)^2≤200000*(S.card:ℝ) := by
    rw [mul_pow] at hb
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hB)).mp
    nlinarith only [hb]
  have hb'' := (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos ξ))).mpr hb'
  have heq : 200000*(S.card:ℝ)*Real.exp (-2*ξ)=
      200000*(S.card:ℝ)/(Real.exp ξ)^2 := by
    rw [←Real.exp_nat_mul,show -2*ξ=-(2*ξ) by ring,Real.exp_neg]
    norm_num
    ring
  rw [heq]
  exact hb''

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_UniformTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

theorem eventually_score_slack {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb A k c : ℝ) (hCb : 0≤Cb) (hk : 1≤k) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R b τ : ℝ,Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      b+k*P η σ D R*τ+A ≤ c*L η σ D := by
  have hk0 : 0<k := by linarith
  have he := eventually_hierarchy hη hη' Cb (c/(2*k)) (2*max A 0/c) hCb (by positivity)
  filter_upwards [he] with σ he
  intro D R b τ hr hb hbhi hτ
  have hs := he D R b τ hr hbhi hτ
  have hA : A ≤ c*L η σ D/2 := by
    have hh := (div_le_iff₀ hc).mp hs.1
    linarith [le_max_left A 0]
  have hB : b+k*P η σ D R*τ≤k*(b+P η σ D R*τ) := by nlinarith only [hb,hk]
  have hh := mul_le_mul_of_nonneg_left hs.2.2.2.2.1 hk0.le
  have hx : k*(c/(2*k)*L η σ D)=c*L η σ D/2 := by field_simp
  rw [hx] at hh
  linarith only [hA,hB,hh]

theorem eventually_R_le_L {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R : ℝ,Range η σ D R → R ≤ c*L η σ D := by
  have hb : 0<8*beta η := mul_pos (by norm_num) (beta_pos hη)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (4/c))] with σ hσ hlarge
  intro D R hr
  have hs : 0<σ := by linarith
  obtain ⟨hD,hR,hpow,hL,hLhi,hP,hPhi⟩ := finite_bounds hη hη' hσ hr
  have hR' : R≤4*σ^beta η := hr.rhi.trans (by linarith)
  have h4 : 4 ≤ c*σ^(8*beta η) := by
    have hh := (div_le_iff₀ hc).mp hlarge
    nlinarith only [hh]
  calc
    R ≤ 4*σ^beta η := hR'
    _ ≤ (c*σ^(8*beta η))*σ^beta η := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = c*σ^(9*beta η) := by rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
    _ ≤ c*L η σ D := mul_le_mul_of_nonneg_left hL hc.le

theorem eventually_score_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ),Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      let ℓ := L η σ D
      let Q := P η σ D R
      let κ := b+8*Q*τ+Real.log 16
      1000000≤ℓ ∧ 100000≤Q ∧ (R:ℝ)≤Q/100000 ∧ 100*ℓ≤Q ∧
      (R:ℝ)*Real.log ℓ≤Q/100 ∧ κ+Real.log 10≤Q/20 ∧
      κ+Real.log 100≤(91/100:ℝ)*ℓ ∧
      (R:ℝ)*Real.exp (-(23/25:ℝ)*ℓ)≤1/10 := by
  have hs := eventually_score_slack hη hη' Cb (Real.log 16+Real.log 100+Real.log 10) 8
    (1/100) hCb (by norm_num) (by norm_num)
  have hh := eventually_hierarchy hη hη' Cb (1/100) 1000000 hCb (by norm_num)
  have hr := eventually_R_le_L hη hη' (c:=1) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hs,hh,hr] with σ hσ hs hh hr
  intro D b τ R hRange hb hbhi hτ
  dsimp only
  have hs := hs D R b τ hRange hb hbhi hτ
  have hh := hh D R b τ hRange hbhi hτ
  have hr : (R:ℝ)≤L η σ D := by simpa using hr D R hRange
  let ℓ := L η σ D
  let Q := P η σ D R
  have hL : 1000000≤ℓ := hh.1
  have hL0 : 0≤ℓ := by linarith only [hL]
  have hR1 : 1≤(R:ℝ) := (finite_bounds hη hη' hσ hRange).2.2.1.trans hRange.rlo
  have hP : ℓ≤Q := by dsimp [Q,P];nlinarith only [hR1,hL0]
  have hRsmall : (R:ℝ)≤Q/100000 := by dsimp [Q,P];nlinarith only [hL,(Nat.cast_nonneg R : (0:ℝ)≤R)]
  have hLP : 100*ℓ≤Q := by nlinarith only [hh.2.2.2.2.2]
  have hlog10 : 0≤Real.log 10 := Real.log_nonneg (by norm_num)
  have hlog100 : 0≤Real.log 100 := Real.log_nonneg (by norm_num)
  have hκP : b+8*Q*τ+Real.log 16+Real.log 10≤Q/20 := by
    change b+8*Q*τ+(Real.log 16+Real.log 100+Real.log 10)≤(1/100:ℝ)*ℓ at hs
    linarith only [hs,hlog100,hP,hL0]
  have hκL : b+8*Q*τ+Real.log 16+Real.log 100≤(91/100:ℝ)*ℓ := by
    linarith only [hs,hlog10,hL0]
  refine ⟨hL,by linarith only [hL,hP],hRsmall,hLP,?_,hκP,hκL,?_⟩
  · simpa only [div_eq_mul_inv,mul_comm (100⁻¹:ℝ),one_mul] using hh.2.2.2.1
  · have he : ℓ≤Real.exp (ℓ/2) := by
      have he := Real.add_one_le_exp (ℓ/4)
      have hp : 0≤ℓ/4+1 := by positivity
      have hh := mul_self_le_mul_self hp he
      rw [←Real.exp_add] at hh
      have hex : ℓ/4+ℓ/4=ℓ/2 := by ring
      rw [hex] at hh
      nlinarith only [hh,sq_nonneg (ℓ/4-1)]
    have he2 : Real.exp (-(21/50:ℝ)*ℓ)≤1/10 := by
      have hx : (10:ℝ)≤Real.exp ((21/50:ℝ)*ℓ) := by
        linarith [Real.add_one_le_exp ((21/50:ℝ)*ℓ)]
      rw [show -(21/50:ℝ)*ℓ=-((21/50:ℝ)*ℓ) by ring,Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10) hx
    calc
      _ ≤ Real.exp (ℓ/2)*Real.exp (-(23/25:ℝ)*ℓ) :=
        mul_le_mul_of_nonneg_right (hr.trans he) (Real.exp_nonneg _)
      _ = Real.exp (-(21/50:ℝ)*ℓ) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := he2

end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_CellScoreProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma exp_sub_le_scaled {a b C : ℝ} (hC : 0<C) (h : a+Real.log C≤b) :
    C*Real.exp (-b)≤Real.exp (-a) := by
  rw [←Real.exp_log hC,←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [h])

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_DimensionTwoProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter
open scoped Topology

theorem eventually_procedure_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ),Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      let Q := P η σ D R
      let κ := b+8*Q*τ+Real.log 16
      104≤Q ∧ κ+8*Q*τ+Real.log 3200000000≤Q/2000 ∧
      8*Q*τ+Real.log 1600≤L η σ D/1000 ∧
      8*Q*τ+Real.log 16≤Q ∧ κ≤Q := by
  have he := eventually_score_slack hη hη' Cb (Real.log 16+Real.log 3200000000)
    16 (1/2000) hCb (by norm_num) (by norm_num)
  have hs := eventually_score_slack hη hη' Cb (Real.log 1600)
    8 (1/1000) hCb (by norm_num) (by norm_num)
  have hu := eventually_score_slack hη hη' Cb (Real.log 16)
    8 1 hCb (by norm_num) (by norm_num)
  have hm := eventually_score_margins hη hη' Cb hCb
  filter_upwards [he,hs,hu,hm] with σ he hs hu hm
  intro D b τ R hr hb hbhi hτ
  have he := he D R b τ hr hb hbhi hτ
  have hs := hs D R b τ hr hb hbhi hτ
  have hu := hu D R b τ hr hb hbhi hτ
  have hm := hm D b τ R hr hb hbhi hτ
  have hL : 0≤L η σ D := by linarith only [hm.1]
  have hLP : L η σ D≤P η σ D R := by linarith only [hm.2.2.2.1,hL]
  dsimp only
  refine ⟨by linarith only [hm.2.1],?_,?_,?_,?_⟩
  all_goals linarith only [he,hs,hu,hLP,hb]

end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePublicTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.MeasurePublicTable
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {α : Type*}

lemma firstIndex_none_iff (E : Set α) {N : ℕ} (t : Fin N→α) :
    firstIndex E t=none ↔ ∀i,t i∉E := by
  unfold firstIndex
  split_ifs with h
  · simp only [false_iff]
    simpa only [Finset.nonempty_def,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using h
  · simp only [true_iff]
    simpa only [Finset.not_nonempty_iff_eq_empty,Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies] using h

lemma firstIndex_some_mem (E : Set α) {N : ℕ} (t : Fin N→α) {i : Fin N}
    (hi : firstIndex E t=some i) : t i∈E := by
  unfold firstIndex at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    have hm := Finset.min'_mem (Finset.univ.filter (fun i=>t i∈E)) h
    rw [he] at hm
    exact (Finset.mem_filter.mp hm).2

lemma firstIndex_minimal (E : Set α) {N : ℕ} (t : Fin N→α) {i : Fin N}
    (hi : firstIndex E t=some i) : ∀ j, j < i → t j∉E := by
  unfold firstIndex at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    intro j hj hE
    have hh := Finset.min'_le (Finset.univ.filter (fun i=>t i∈E)) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hE⟩)
    rw [he] at hh
    exact (not_le_of_gt hj) hh

end SharpRamseyFive.MeasurePublicTable

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_PublicTraining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining

section
open MeasurePublicTable
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

lemma firstIndex_greedyList (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) (x : A) :
    firstIndex {B | x∈B} (greedyList F hF shape X J)=queryPart F hF shape X J x := by
  cases he : firstIndex {B | x∈B} (greedyList F hF shape X J) with
  | none =>
    have hh := (firstIndex_none_iff _ _).mp he
    unfold queryPart
    have hn : ¬firstAt F hF shape X J x<J := by
      intro h
      exact hh ⟨_,h⟩ (firstAt_mem F hF shape X J x h)
    rw [dite_eq_right hn]
  | some i =>
    have hm := firstIndex_some_mem _ _ he
    have hmin := firstIndex_minimal _ _ he
    have hf : firstAt F hF shape X J x=i.val := by
      apply firstAt_eq F hF shape X J i.val x i.prop hm
      intro j hj
      exact hmin ⟨j,hj.trans i.prop⟩ hj
    unfold queryPart
    simp only [hf,dite_eq_left i.prop]

lemma region_cell (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) (i : Fin J) :
    X∩publicRegion (greedyList F hF shape X J) i=cell F hF shape X i := by
  ext x
  rw [cell_earliest]
  rw [Finset.mem_inter]
  change (x∈X ∧ x∈(shape (chosen F hF shape X i)).filter (fun x => ∀ j : Fin J, j < i → x∉shape (chosen F hF shape X j))) ↔ _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hx,hm,he⟩
    refine ⟨hx,hm,fun j hj=>he ⟨j,hj.trans i.prop⟩ hj⟩
  · rintro ⟨hx,hm,he⟩
    exact ⟨hx,hm,fun j hj=>he j.val hj⟩

lemma clipped_publicOwn (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (hSX : S⊆X) (J : ℕ) (x : A) :
    S∩publicOwn (greedyList F hF shape X J) x=
      clippedPart S F hF shape X J (queryPart F hF shape X J x) := by
  unfold publicOwn
  rw [firstIndex_greedyList]
  cases he : queryPart F hF shape X J x with
  | none => simp [clippedPart]
  | some i =>
    change S∩publicRegion (greedyList F hF shape X J) i=S∩cell F hF shape X i
    rw [←region_cell F hF shape X J i,←Finset.inter_assoc,Finset.inter_eq_left.mpr hSX]

lemma ownCell_subset_publicOwn (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) :
    ownCell F hF shape X J x⊆publicOwn (greedyList F hF shape X J) x := by
  have hh := clipped_publicOwn X F hF shape X (Finset.Subset.refl _) J x
  rw [clippedPart_query] at hh
  have hc : ownCell F hF shape X J x⊆X := by
    unfold ownCell
    split_ifs
    · exact (cell_subset F hF shape X _).trans (remaining_subset F hF shape X _)
    · exact Finset.empty_subset _
  rw [Finset.inter_eq_right.mpr hc] at hh
  exact hh▸Finset.inter_subset_right

end

open TrainingCells
open scoped Classical BigOperators

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionThreeProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_score_procedure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ {A : Type} [Fintype A] (g : ℝ) (F : Finset J) (hF : F.Nonempty)
      (Flat : J→Submodule K (I→K)) (X U S : Finset (ℙ K (I→K)))
      (t₀ : ℝ) (ht₀ : 0<t₀) (rawOwn : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (C : A→Finset (ℙ K (I→K))) (ia ib ic : ℙ K (I→K)→A) (T : Finset (ℙ K (Dual K (I→K)))),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → g≤2*σ → S⊆X → S⊆U →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b₀)≤(X.card:ℝ)*T.card →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (X.card:ℝ)≤Real.exp (3*σ/2+g) →
      t₀=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5) →
      S=peelSet (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀) →
      Real.exp (3*σ/2+g)/4≤S.card → (S.card:ℝ)≤10*Real.exp (2*σ) →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀)) x⊆rawOwn x) →
      (∀x,S∩rawOwn x=C (ia x)∪C (ib x)) →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (Nat.card K:ℝ)*P η σ D R≤S.card →
      (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
    Real.exp (-8*P η σ D R*τ)/4≤
    (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
      {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*P η σ D R) ∧
        (W.card:ℝ)≤(S.card:ℝ)*Real.exp (10*P η σ D R) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ)} := by
  have hi := eventually_three_score_integrals hη hη' Cb hCb
  have hp := eventually_procedure_margins hη hη' Cb hCb
  have hm := eventually_score_margins hη hη' Cb hCb
  have ht := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/10))
  have hl := eventually_hierarchy hη hη' Cb 1 10000000000 hCb (by norm_num)
  filter_upwards [eventually_ge_atTop (10:ℝ),hi,hp,hm,ht,hl] with σ hσ hi hp hm ht hl
  rw [←neg_mul] at ht
  intro D b₀ τ R L₀ q K I J _ _ _ _ _ _ _ _ A _ g F hF Flat X U S t₀ ht₀ rawOwn C ia ib ic T
    hq hcard hσq hI hr hL hb₀ hbhi hτ hτhi hg hSX hSU hdens hprod hFlat hcover hX htc hpeel hquarter hn hraw hOwn hC hCS hCc hnP hdiv hf
  have hdim : finrank K (I→K)=3+1 := by rw [Module.finrank_pi, hI]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) hquarter))
  have hret : X.card≤4*S.card := by exact_mod_cast (show (X.card:ℝ)≤4*S.card by linarith only [hX,hquarter])
  have hP : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hi := hi D b₀ τ R L₀ q K I J g F hF Flat X U S t₀ ht₀ rawOwn C ia ib ic
    hq hcard hσq hI hr hL hb₀ hbhi hτhi hg hFlat hcover hX htc hpeel hquarter hn hraw hOwn hC hCS hCc hdiv hf
  have hp := hp D b₀ τ R hr hb₀ hbhi hτhi
  have hm := hm D b₀ τ R hr hb₀ hbhi hτhi
  have hlarge : 10000000000≤(L₀:ℝ) := by rw [hL];exact (hl D R b₀ τ hr hbhi hτhi).1
  have hq10 : (10:ℝ)≤Nat.card K := by rw [hcard,←hσq];linarith only [Real.add_one_le_exp σ,hσ]
  have hτ8 : 8*τ≤4/5 := by linarith only [hτhi,ht]
  have hbcount := irregular_card_bound (d:=3) hdim (by norm_num) S C hS hC
    (ξ:=(L₀:ℝ)/100) (by linarith only [Real.add_one_le_exp ((L₀:ℝ)/100),hlarge])
  have hpay := ScoreScalars.exp_sub_le_scaled (a:=0) (b:=2*((L₀:ℝ)/100))
    (C:=20000000) (by norm_num) (by
      linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤20000000),hlarge])
  simp only [neg_zero,Real.exp_zero] at hpay
  rw [show -(2*((L₀:ℝ)/100))=(-2)*((L₀:ℝ)/100) by ring] at hpay
  have hbad : ((irregular (d:=3) S C ((L₀:ℝ)/100)).card:ℝ)≤(S.card:ℝ)/100 := by
    apply hbcount.trans
    nlinarith only [mul_le_mul_of_nonneg_right hpay (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)]
  have hh := cell_score_from_integrals (d:=3) hdim (by norm_num) hq10 X U S hSX hSU hS hret C hC ia ib hf T L₀ R b₀ τ 8
    hτ hτ8 hdens hprod (by rw [hP];exact hp.1) (by norm_num) (by rwa [hP]) hbad
    (by rw [hP];dsimp only at hp;linarith only [hp.2.1])
    (by rw [hP,hL];exact hp.2.2.1)
    (by rw [hP];exact hp.2.2.2.1)
    (by rw [hP];exact hp.2.2.2.2)
    (by rw [hP,hL];exact hm.2.2.2.2.2.2.1)
    (by rw [hL];exact hm.2.2.2.2.2.2.2)
    (by simpa only [hP] using hi.1)
    (by simpa only [hP] using hi.2)
  simpa only [hP,show (8:ℝ)+2=10 by norm_num] using hh

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionTwoPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma density_three_quarters {d : ℕ} (hd : 1 ≤ d) (hq : 3 ≤ Nat.card K) :
    3 / (4 * (Nat.card K : ℝ)) ≤
      (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d := by
  have hm : 0 < Q (Nat.card K) (d-1) := Q_pos _ _
  have hn : 0 < Q (Nat.card K) d := Q_pos _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [Q_recurrence hd]
  push_cast
  have hq' : (3 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hm' : (1 : ℝ) ≤ Q (Nat.card K) (d-1) := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hm' (by positivity : (0:ℝ) ≤ Nat.card K)
  nlinarith

theorem sparse_half_rectangle_size {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d) (hq3 : 3 ≤ Nat.card K)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V)))
    (hsparse : (incidences A B : ℝ) ≤ (A.card : ℝ) * B.card / (2 * Nat.card K)) :
    (A.card : ℝ) * B.card ≤ 16 * (Nat.card K : ℝ) ^ (d+1) := by
  classical
  let q : ℝ := Nat.card K
  let v : ℝ := (A.card : ℝ) * B.card
  let p : ℝ := (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 3 / (4*q) ≤ p := density_three_quarters hd hq3
  have hpv := mul_le_mul_of_nonneg_right hp hv
  have hlow : v / (4*q) ≤ p*v - incidences A B := by
    change (incidences A B : ℝ) ≤ v / (2*q) at hsparse
    have he : (3 / (4*q)) * v = 3 * (v / (4*q)) := by field_simp
    have he2 : v / (2*q) = 2 * (v / (4*q)) := by field_simp; ring
    rw [he] at hpv
    rw [he2] at hsparse
    linarith
  have hm : |(incidences A B : ℝ) - p*v| ≤ Real.sqrt (q^(d-1)*v) := by
    simpa only [p, q, v, mul_assoc] using incidence_mixing hdim hd A B
  have habs : |(incidences A B : ℝ) - p*v| = p*v - incidences A B := by
    rw [abs_of_nonpos (show (incidences A B : ℝ) - p*v ≤ 0 by
      have hnonneg : 0 ≤ v / (4*q) := by positivity
      linarith)]
    ring
  rw [habs] at hm
  have hs : v / (4*q) ≤ Real.sqrt (q^(d-1)*v) := hlow.trans hm
  have hs2 := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  have he : (v / (4*q))^2 * (16*q^2) = v^2 := by field_simp; ring
  have hm2 := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ 16*q^2 by positivity)
  rw [he] at hm2
  have hexp : q^(d-1)*v*(16*q^2) = (16*q^(d+1))*v := by
    have hd' : d-1 + 2 = d+1 := by omega
    rw [← hd', pow_add]
    ring
  rw [hexp, pow_two] at hm2
  by_cases hv0 : v = 0
  · change v ≤ _
    rw [hv0]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hv (Ne.symm hv0))).mp hm2

end SharpRamseyFive.ProjectiveIncidence

end

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_training_score_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (3*σ/2+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    let a := queryPart F hF (fun j=>flatPoints (Flat j)) X m
    (∀i,(C i).card≤(S.card:ℝ)/25) →
    S⊆X ∧ X.card≤2*S.card ∧
    Real.exp (-8*P η σ D R*τ)/4≤
      (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
        (trueScoreSuccess U S (fun x=>C (a x))
          (fun x=>Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (a x)) ∅)))
          (exceptional S C) R (2*(Nat.card K:ℝ)*P η σ D R)
          ((S.card:ℝ)*Real.exp (10*P η σ D R)) ((9/10:ℝ)*S.card)) := by
  have hh := eventually_three_score_procedure hη hη' Cb hCb
  have htau := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hp := (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<10) (beta_pos hη))).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hh,htau,hp,eventually_ge_atTop (10:ℝ)] with σ hh htau hp hσ
  rw [←neg_mul] at htau
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ F hF Flat X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover
  dsimp only
  let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
  let a := queryPart F hF (fun j=>flatPoints (Flat j)) X m
  change (∀i,(C i).card≤(S.card:ℝ)/25) → _
  intro hsmall
  have hSX : S⊆X := peel_subset _ _ _ _ _ _ _
  have hret : X.card≤2*S.card := peel_half _ _ _ _ _ _ _
  have hret' : (X.card:ℝ)≤2*S.card := by exact_mod_cast hret
  have hSn : 0<(S.card:ℝ) := by nlinarith only [hret',hX,Real.exp_pos (3*σ/2+g)]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn)
  have hP : 4≤P η σ D R := hp.trans (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hq : 2<q := by exact_mod_cast (show (2:ℝ)<q by rw [←hσq];linarith only [Real.add_one_le_exp σ,hσ])
  have hqp : (0:ℝ)<Nat.card K := by rw [hcard,←hσq];exact Real.exp_pos _
  have hdim : finrank K (I→K)=3+1 := by rw [Module.finrank_pi,hI]
  have hm := sparse_half_rectangle_size (d:=3) hdim (by norm_num) (by omega : 3≤Nat.card K) X T (by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(Nat.card K:ℝ))).mpr
    have := mul_le_mul_of_nonneg_right (hτhi.trans htau.le) (by positivity : (0:ℝ)≤(X.card:ℝ)*T.card)
    nlinarith only [hdens,this])
  have hxx : (X.card:ℝ)^2≤16*Real.exp (4*σ) := by
    have hxt : (X.card:ℝ)≤T.card := by exact_mod_cast hXT
    have he : (Real.exp σ)^4=Real.exp (4*σ) := by rw [←Real.exp_nat_mul];norm_num
    rw [hcard,←hσq,he] at hm
    nlinarith
  have hnhi : (X.card:ℝ)≤10*Real.exp (2*σ) := by
    have he : (Real.exp (2*σ))^2=Real.exp (4*σ) := by rw [←Real.exp_nat_mul];congr 1;ring
    have hepos := Real.exp_pos (2*σ)
    nlinarith [sq_nonneg ((X.card:ℝ)-10*Real.exp (2*σ))]
  have hg : g≤2*σ := by
    have he : 3*σ/2+g≤2*σ+Real.log 10 := Real.exp_le_exp.mp (by
      rw [Real.exp_add (2*σ),Real.exp_log (by norm_num : (0:ℝ)<10)]
      nlinarith only [hnhi,hX])
    have hl := Real.log_le_self (by norm_num : (0:ℝ)≤10)
    linarith only [he,hl,hσ]
  have hsum := TrainingCells.sum_card_le S C
    (clippedPart_subset S F hF (fun j=>flatPoints (Flat j)) X m)
    (clippedPart_disjoint S F hF (fun j=>flatPoints (Flat j)) X m)
  have hqP : (Nat.card K:ℝ)*P η σ D R≤S.card := by nlinarith only [hn,hret',hqp,hP]
  have hdiv : (Nat.card K:ℝ)/S.card≤1/100 := by
    apply (div_le_iff₀ hSn).mpr
    nlinarith only [hn,hret',mul_le_mul_of_nonneg_left hP hqp.le]
  have hc := hh D b τ R L₀ q K I J g F hF Flat X U S t ht
    (publicOwn (greedyList F hF (fun j=>flatPoints (Flat j)) X m)) C a (fun _=>none) (fun _=>none) T
    hq hcard hσq hI hr hL hb hbhi hτ hτhi hg hSX (hSX.trans hXU) hdens hprod
    hFlat hcover hX.le rfl rfl (by nlinarith only [hret',hX])
    ((show (S.card:ℝ)≤X.card by exact_mod_cast Finset.card_le_card hSX).trans hnhi)
    (ownCell_subset_publicOwn F hF (fun j=>flatPoints (Flat j)) X m)
    (by intro x;simpa only [C,clippedPart,Finset.union_empty] using clipped_publicOwn S F hF (fun j=>flatPoints (Flat j)) X hSX m x)
    (by omega) (clippedPart_subset S F hF (fun j=>flatPoints (Flat j)) X m)
    (by intro x;simp [C,clippedPart]) hqP hdiv
    (by intro x;exact TrainingCells.small_union S (C (a x)) (C none) hS (hsmall _) (hsmall _))
  refine ⟨hSX,hret,?_⟩
  simpa only [trueScoreSuccess,C,clippedPart,Finset.union_empty,mul_assoc] using hc

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score_oai
