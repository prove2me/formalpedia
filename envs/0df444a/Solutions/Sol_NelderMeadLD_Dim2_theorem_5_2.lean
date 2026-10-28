-- Prove2me | solution 1 for NelderMeadLD.Dim2.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T12:19:01.513832+00:00
-- url     : https://prove2.me/submissions/edcd1d26-7969-48aa-8a92-bde97e4c6b33

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
import Theorems.Thm_NelderMeadLD_Dim2_lemma_3_1
import Theorems.Thm_NelderMeadLD_Dim2_lemma_3_3
import Theorems.Thm_NelderMeadLD_Dim2_lemma_3_5
import Theorems.Thm_NelderMeadLD_Dim2_theorem_5_1

set_option autoImplicit false

open Filter Topology

namespace NM2Diam

open NelderMeadLD.Dim2
open NelderMeadLD.Conv1D (Move ParamsOK)

/-- Sum of all pairwise distances of a triangle (twice its perimeter). -/
noncomputable def P (x : Fin 3 → E 2) : ℝ := ∑ i, ∑ j, ‖x i - x j‖

lemma P_cont : Continuous P := by
  unfold P; fun_prop

lemma P_eq (x : Fin 3 → E 2) :
    P x = 2 * (‖x 0 - x 1‖ + ‖x 0 - x 2‖ + ‖x 1 - x 2‖) := by
  simp only [P, Fin.sum_univ_three, sub_self, norm_zero]
  rw [norm_sub_rev (x 1) (x 0), norm_sub_rev (x 2) (x 0), norm_sub_rev (x 2) (x 1)]
  ring

lemma diam_le_P (x : Fin 3 → E 2) : diam x ≤ P x := by
  unfold diam
  apply Finset.sup'_le
  rintro ⟨i, j⟩ _
  calc ‖x i - x j‖ ≤ ∑ j', ‖x i - x j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖x i - x j'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ P x := Finset.single_le_sum (f := fun i' => ∑ j', ‖x i' - x j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

lemma diam_nonneg (x : Fin 3 → E 2) : 0 ≤ diam x := by
  unfold diam
  exact le_trans (norm_nonneg (x 0 - x 0))
    (Finset.le_sup' (fun ij : Fin 3 × Fin 3 => ‖x ij.1 - x ij.2‖) (Finset.mem_univ (0, 0)))

lemma centroid_eq (x : Fin 3 → E 2) : centroid x = (1 / 2 : ℝ) • (x 0 + x 1) := by
  simp only [centroid, Fin.sum_univ_two]
  norm_num

lemma trial_one (x : Fin 3 → E 2) : trial x 1 = x 0 + x 1 - x 2 := by
  rw [trial, centroid_eq]
  show (1 + 1 : ℝ) • ((1 / 2 : ℝ) • (x 0 + x 1)) - (1 : ℝ) • x 2 = x 0 + x 1 - x 2
  (module)
lemma insertPos_le (f : E 2 → ℝ) (x : Fin 3 → E 2) (v : E 2) : insertPos f x v ≤ 2 := by
  unfold insertPos
  calc _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_filter_le _ _
    _ = 2 := by simp

lemma iv_cases (f : E 2 → ℝ) (x : Fin 3 → E 2) (v : E 2) :
    insertVertex f x v = ![v, x 0, x 1] ∨ insertVertex f x v = ![x 0, v, x 1] ∨
      insertVertex f x v = ![x 0, x 1, v] := by
  have h := insertPos_le f x v
  obtain h0 | h1 | h2 : insertPos f x v = 0 ∨ insertPos f x v = 1 ∨ insertPos f x v = 2 := by
    omega
  · left; funext i; fin_cases i <;> simp [insertVertex, h0]
  · right; left; funext i; fin_cases i <;> simp [insertVertex, h1]
  · right; right; funext i; fin_cases i <;> simp [insertVertex, h2]

lemma iv_mem (f : E 2 → ℝ) (x : Fin 3 → E 2) (v : E 2) (i : Fin 3) :
    insertVertex f x v i = v ∨ ∃ j, insertVertex f x v i = x j := by
  rcases iv_cases f x v with h | h | h <;> rw [h] <;> fin_cases i <;> simp

lemma iv_has (f : E 2 → ℝ) (x : Fin 3 → E 2) (v : E 2) : ∃ i, insertVertex f x v i = v := by
  rcases iv_cases f x v with h | h | h <;> rw [h]
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

lemma P_reflect (f : E 2 → ℝ) (x : Fin 3 → E 2) :
    P (insertVertex f x (x 0 + x 1 - x 2)) = P x := by
  have e1 : x 0 + x 1 - x 2 - x 0 = x 1 - x 2 := by abel
  have e2 : x 0 + x 1 - x 2 - x 1 = x 0 - x 2 := by abel
  have e3 : x 0 - (x 0 + x 1 - x 2) = -(x 1 - x 2) := by abel
  have e4 : x 1 - (x 0 + x 1 - x 2) = -(x 0 - x 2) := by abel
  rcases iv_cases f x (x 0 + x 1 - x 2) with h | h | h <;> rw [h, P_eq, P_eq] <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, e1, e2, e3, e4, norm_neg] <;> ring

lemma move_expand_spec (f : E 2 → ℝ) (x : Fin 3 → E 2) (h : move f 1 2 (1 / 2) x = Move.expand) :
    f (trial x (1 * 2)) < f (trial x 1) ∧ f (trial x 1) < f (x 0) := by
  simp only [move] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  all_goals first | exact absurd h (by decide) | exact ⟨by assumption, by assumption⟩

lemma move_outside_spec (f : E 2 → ℝ) (x : Fin 3 → E 2)
    (h : move f 1 2 (1 / 2) x = Move.outside) :
    f (trial x (1 * (1 / 2))) ≤ f (trial x 1) ∧ f (trial x 1) < f (x (Fin.last 2)) := by
  simp only [move] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  all_goals first | exact absurd h (by decide) | exact ⟨by assumption, by assumption⟩

section geo

variable (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f) (T : Fin 3 → E 2) (L : ℝ)
  (hT : ∀ i, f (T i) = L) (hP : 0 < P T)
include hf hT hP

lemma m_ne_c : centroid T ≠ T (Fin.last 2) := by
  intro h
  rw [centroid_eq] at h
  by_cases h01 : T 0 = T 1
  · have h2 : T (Fin.last 2) = T 0 := by
      rw [← h, ← h01]; module
    have : P T = 0 := by
      rw [P_eq, ← h01]
      have : T 2 = T 0 := h2
      rw [this]; simp
    linarith
  · have hs := hf.2 (Set.mem_univ (T 0)) (Set.mem_univ (T 1)) h01 (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have e : (1 / 2 : ℝ) • T 0 + (1 / 2 : ℝ) • T 1 = T (Fin.last 2) := by
      rw [← h]; module
    rw [e, hT, hT, hT] at hs
    simp only [smul_eq_mul] at hs
    linarith

lemma geo_expand (h2 : L ≤ f (trial T (1 * 2))) (h21 : f (trial T (1 * 2)) ≤ f (trial T 1))
    (h1 : f (trial T 1) ≤ L) : False := by
  have hm := m_ne_c f hf T L hT hP
  have e : trial T 1 = (1 / 3 : ℝ) • T (Fin.last 2) + (2 / 3 : ℝ) • trial T (1 * 2) := by
    simp only [trial]; module
  have key : trial T (1 * 2) - T (Fin.last 2) = (3 : ℝ) • (centroid T - T (Fin.last 2)) := by
    simp only [trial]; module
  have hne : T (Fin.last 2) ≠ trial T (1 * 2) := by
    intro h
    rw [← h, sub_self] at key
    rcases smul_eq_zero.mp key.symm with h3 | h3
    · norm_num at h3
    · exact hm (sub_eq_zero.mp h3)
  have hs := hf.2 (Set.mem_univ _) (Set.mem_univ _) hne (by norm_num : (0 : ℝ) < 1 / 3)
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num)
  rw [← e, hT] at hs
  simp only [smul_eq_mul] at hs
  generalize f (trial T (1 * 2)) = a at h2 h21 hs
  generalize f (trial T 1) = b at h21 h1 hs
  linarith

lemma geo_outside (h2 : L ≤ f (trial T (1 * (1 / 2))))
    (h21 : f (trial T (1 * (1 / 2))) ≤ f (trial T 1)) (h1 : f (trial T 1) ≤ L) : False := by
  have hm := m_ne_c f hf T L hT hP
  have e : trial T (1 * (1 / 2)) = (1 / 4 : ℝ) • T (Fin.last 2) + (3 / 4 : ℝ) • trial T 1 := by
    simp only [trial]; module
  have key : trial T 1 - T (Fin.last 2) = (2 : ℝ) • (centroid T - T (Fin.last 2)) := by
    simp only [trial]; module
  have hne : T (Fin.last 2) ≠ trial T 1 := by
    intro h
    rw [← h, sub_self] at key
    rcases smul_eq_zero.mp key.symm with h3 | h3
    · norm_num at h3
    · exact hm (sub_eq_zero.mp h3)
  have hs := hf.2 (Set.mem_univ _) (Set.mem_univ _) hne (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  rw [← e, hT] at hs
  simp only [smul_eq_mul] at hs
  linarith

lemma geo_inside (h2 : L ≤ f (trial T (-(1 / 2)))) : False := by
  have hm := m_ne_c f hf T L hT hP
  have e : trial T (-(1 / 2)) = (1 / 2 : ℝ) • centroid T + (1 / 2 : ℝ) • T (Fin.last 2) := by
    simp only [trial]; module
  have hmL : f (centroid T) ≤ L := by
    have hc := hf.convexOn.2 (Set.mem_univ (T 0)) (Set.mem_univ (T 1))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have e' : (1 / 2 : ℝ) • T 0 + (1 / 2 : ℝ) • T 1 = centroid T := by
      rw [centroid_eq]; module
    rw [e', hT, hT] at hc
    simp only [smul_eq_mul] at hc
    linarith
  have hs := hf.2 (Set.mem_univ _) (Set.mem_univ _) hm (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [← e, hT] at hs
  simp only [smul_eq_mul] at hs
  linarith

end geo

lemma linInd_of_nd (x : Fin 3 → E 2) (hnd : Nondegenerate x) :
    LinearIndependent ℝ ![x 0 - x 2, x 1 - x 2] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hD : (edgeMatrix x).det ≠ 0 := hnd
  rw [Matrix.det_fin_two] at hD
  simp only [edgeMatrix, Matrix.of_apply] at hD
  have c0 := congrArg (fun v : E 2 => v 0) hst
  have c1 := congrArg (fun v : E 2 => v 1) hst
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.zero_apply] at c0 c1
  have hl : Fin.last 2 = (2 : Fin 3) := rfl
  have hc0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  have hc1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
  rw [hl, hc0, hc1] at hD
  set D := (x 0 0 - x 2 0) * (x 1 1 - x 2 1) - (x 1 0 - x 2 0) * (x 0 1 - x 2 1) with hDdef
  have hs : s * D = 0 := by rw [hDdef]; linear_combination (x 1 1 - x 2 1) * c0 - (x 1 0 - x 2 0) * c1
  have ht : t * D = 0 := by rw [hDdef]; linear_combination (x 0 0 - x 2 0) * c1 - (x 0 1 - x 2 1) * c0
  exact ⟨(mul_eq_zero.mp hs).resolve_right hD, (mul_eq_zero.mp ht).resolve_right hD⟩

theorem main (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 2 (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0)) :
    Tendsto (fun k => diam (Δ k)) atTop (𝓝 0) := by
  have hpar : ParamsOK 1 2 (1 / 2) σ :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, hσ0, hσ1⟩
  have hcont : Continuous f := continuousOn_univ.mp (hf.convexOn.continuousOn isOpen_univ)
  have hbdd : BddBelow (Set.range f) := by
    have hK : IsCompact {x | f x ≤ f 0} :=
      Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const) (hlev (f 0))
    obtain ⟨y, -, hy⟩ := hK.exists_isMinOn ⟨0, (by simp : (0 : E 2) ∈ {x | f x ≤ f 0})⟩ hcont.continuousOn
    refine ⟨f y, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : f x ≤ f 0
    · exact hy hx
    · have := hy (by simp : (0 : E 2) ∈ {x | f x ≤ f 0})
      simp only [Set.mem_setOf_eq] at this
      linarith [not_le.mp hx]
  have hns := NelderMeadLD.Dim2.lemma_3_5 (n := 2) f 1 2 (1 / 2) σ hpar Δ hrun hnd hf
  have hndk := (NelderMeadLD.Dim2.lemma_3_1 (n := 2) f 1 2 (1 / 2) σ hpar Δ hrun hnd).1
  have h33 := (NelderMeadLD.Dim2.lemma_3_3 (n := 2) f 1 2 (1 / 2) σ hpar Δ hrun hnd hbdd).2.1
  obtain ⟨L, hL⟩ := NelderMeadLD.Dim2.theorem_5_1 f hf hlev 2 σ hpar Δ hrun hnd
  have hstep : ∀ k, Δ (k + 1) = insertVertex f (Δ k)
      (trial (Δ k) (tau 1 2 (1 / 2) (move f 1 2 (1 / 2) (Δ k)))) :=
    fun k => (hrun.2 k).2 (hns k)
  have hanti : ∀ i, Antitone (fun k => f (Δ k i)) :=
    fun i => antitone_nat_of_succ_le (fun k => (h33 k (hns k)).1 i)
  have hge : ∀ k i, L ≤ f (Δ k i) := fun k i => (hanti i).le_of_tendsto (hL i) k
  have hv : ∀ k, L ≤ f (trial (Δ k) (tau 1 2 (1 / 2) (move f 1 2 (1 / 2) (Δ k)))) := by
    intro k
    obtain ⟨i, hi⟩ := iv_has f (Δ k) (trial (Δ k) (tau 1 2 (1 / 2) (move f 1 2 (1 / 2) (Δ k))))
    rw [← hi, ← hstep k]
    exact hge (k + 1) i
  -- boundedness
  set M := |f (Δ 0 0)| + |f (Δ 0 1)| + |f (Δ 0 2)| with hM
  have hKM : ∀ k i, f (Δ k i) ≤ M := by
    intro k i
    have h := (hanti i) (Nat.zero_le k)
    simp only at h
    have a0 := abs_nonneg (f (Δ 0 0))
    have a1 := abs_nonneg (f (Δ 0 1))
    have a2 := abs_nonneg (f (Δ 0 2))
    fin_cases i
    · have := le_abs_self (f (Δ 0 0)); simp only [Fin.zero_eta] at h ⊢; linarith
    · have := le_abs_self (f (Δ 0 1)); simp only [Fin.mk_one] at h ⊢; linarith
    · have := le_abs_self (f (Δ 0 2)); simp only [Fin.reduceFinMk] at h ⊢; linarith
  obtain ⟨R, hR⟩ := (hlev M).subset_closedBall (0 : E 2)
  have hR0 : 0 ≤ R := by
    have := hR (show Δ 0 0 ∈ {x | f x ≤ M} from hKM 0 0)
    exact le_trans (norm_nonneg _) (by simpa using this)
  have hvert : ∀ k i, ‖Δ k i‖ ≤ R := fun k i => by
    simpa using hR (show Δ k i ∈ {x | f x ≤ M} from hKM k i)
  have hball : ∀ k, Δ k ∈ Metric.closedBall (0 : Fin 3 → E 2) R := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0]
    exact hvert k
  have hsub : ∀ p : ℕ → Prop, (∃ᶠ k in atTop, p k) → ∃ T : Fin 3 → E 2, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ (∀ j, p (φ j)) ∧ Tendsto (fun j => Δ (φ j)) atTop (𝓝 T) := by
    intro p hp
    obtain ⟨φ, hφm, hφp⟩ := extraction_of_frequently_atTop hp
    obtain ⟨T, -, ψ, hψ, hT⟩ := tendsto_subseq_of_bounded
      (Metric.isBounded_closedBall (x := (0 : Fin 3 → E 2)) (r := R)) (x := Δ ∘ φ)
      (fun j => hball (φ j))
    exact ⟨T, φ ∘ ψ, hφm.comp hψ, fun j => hφp _, hT⟩
  have hTval : ∀ (T : Fin 3 → E 2) (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (fun j => Δ (φ j)) atTop (𝓝 T) → ∀ i, f (T i) = L := by
    intro T φ hφ hT i
    exact tendsto_nhds_unique ((hcont.tendsto (T i)).comp ((tendsto_pi_nhds.mp hT) i))
      ((hL i).comp hφ.tendsto_atTop)
  have htc : ∀ τ : ℝ, Continuous (fun x : Fin 3 → E 2 => f (trial x τ)) := by
    intro τ
    unfold trial centroid
    fun_prop
  have hlim : ∀ (T : Fin 3 → E 2) (φ : ℕ → ℕ), Tendsto (fun j => Δ (φ j)) atTop (𝓝 T) →
      ∀ τ : ℝ, Tendsto (fun j => f (trial (Δ (φ j)) τ)) atTop (𝓝 (f (trial T τ))) :=
    fun T φ hT τ => ((htc τ).tendsto T).comp hT
  have hPlim : ∀ (T : Fin 3 → E 2) (φ : ℕ → ℕ), Tendsto (fun j => Δ (φ j)) atTop (𝓝 T) →
      Tendsto (fun j => P (Δ (φ j))) atTop (𝓝 (P T)) :=
    fun T φ hT => (P_cont.tendsto T).comp hT
  have hvlim : ∀ (T : Fin 3 → E 2) (φ : ℕ → ℕ), Tendsto (fun j => Δ (φ j)) atTop (𝓝 T) →
      ∀ i, Tendsto (fun j => f (Δ (φ j) i)) atTop (𝓝 (f (T i))) :=
    fun T φ hT i => (hcont.tendsto (T i)).comp ((tendsto_pi_nhds.mp hT) i)
  -- main claim: the pairwise-distance sum tends to zero
  have hPto : Tendsto (fun k => P (Δ k)) atTop (𝓝 0) := by
    by_contra hne
    rw [Metric.tendsto_atTop] at hne
    push Not at hne
    obtain ⟨ε, hε, hfr⟩ := hne
    have hfreq : ∃ᶠ k in atTop, ε ≤ P (Δ k) := by
      rw [frequently_atTop]
      intro N
      obtain ⟨k, hk, hk'⟩ := hfr N
      refine ⟨k, hk, ?_⟩
      rw [Real.dist_eq, sub_zero] at hk'
      exact le_trans hk' (le_of_eq (abs_of_nonneg (by
        rw [P_eq]; positivity)))
    have hE : ∀ᶠ k in atTop, ¬ (ε ≤ P (Δ k) ∧ move f 1 2 (1 / 2) (Δ k) = Move.expand) := by
      rw [← not_frequently]
      intro hp
      obtain ⟨T, φ, hφ, hpφ, hT⟩ := hsub _ hp
      have hTi := hTval T φ hφ hT
      have hPT : ε ≤ P T := ge_of_tendsto' (hPlim T φ hT) (fun j => (hpφ j).1)
      apply geo_expand f hf T L hTi (by linarith)
      · refine ge_of_tendsto' (hlim T φ hT _) (fun j => ?_)
        have := hv (φ j); rw [(hpφ j).2] at this; exact this
      · exact le_of_tendsto_of_tendsto' (hlim T φ hT _) (hlim T φ hT _)
          (fun j => (move_expand_spec f _ (hpφ j).2).1.le)
      · rw [← hTi 0]
        exact le_of_tendsto_of_tendsto' (hlim T φ hT _) (hvlim T φ hT 0)
          (fun j => (move_expand_spec f _ (hpφ j).2).2.le)
    have hO : ∀ᶠ k in atTop, ¬ (ε ≤ P (Δ k) ∧ move f 1 2 (1 / 2) (Δ k) = Move.outside) := by
      rw [← not_frequently]
      intro hp
      obtain ⟨T, φ, hφ, hpφ, hT⟩ := hsub _ hp
      have hTi := hTval T φ hφ hT
      have hPT : ε ≤ P T := ge_of_tendsto' (hPlim T φ hT) (fun j => (hpφ j).1)
      apply geo_outside f hf T L hTi (by linarith)
      · refine ge_of_tendsto' (hlim T φ hT _) (fun j => ?_)
        have := hv (φ j); rw [(hpφ j).2] at this; exact this
      · exact le_of_tendsto_of_tendsto' (hlim T φ hT _) (hlim T φ hT _)
          (fun j => (move_outside_spec f _ (hpφ j).2).1)
      · rw [← hTi (Fin.last 2)]
        exact le_of_tendsto_of_tendsto' (hlim T φ hT _) (hvlim T φ hT _)
          (fun j => (move_outside_spec f _ (hpφ j).2).2.le)
    have hI : ∀ᶠ k in atTop, ¬ (ε ≤ P (Δ k) ∧ move f 1 2 (1 / 2) (Δ k) = Move.inside) := by
      rw [← not_frequently]
      intro hp
      obtain ⟨T, φ, hφ, hpφ, hT⟩ := hsub _ hp
      have hTi := hTval T φ hφ hT
      have hPT : ε ≤ P T := ge_of_tendsto' (hPlim T φ hT) (fun j => (hpφ j).1)
      apply geo_inside f hf T L hTi (by linarith)
      refine ge_of_tendsto' (hlim T φ hT _) (fun j => ?_)
      have := hv (φ j); rw [(hpφ j).2] at this; exact this
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hE.and hO).and hI)
    obtain ⟨k0, hk0N, hk0⟩ := frequently_atTop.mp hfreq N
    have hmv : ∀ k ≥ N, ε ≤ P (Δ k) → move f 1 2 (1 / 2) (Δ k) = Move.reflect := by
      intro k hk hPk
      obtain ⟨⟨hE', hO'⟩, hI'⟩ := hN k hk
      cases hm : move f 1 2 (1 / 2) (Δ k) with
      | reflect => rfl
      | expand => exact absurd ⟨hPk, hm⟩ hE'
      | outside => exact absurd ⟨hPk, hm⟩ hO'
      | inside => exact absurd ⟨hPk, hm⟩ hI'
      | shrink => exact absurd hm (hns k)
    have hPstep : ∀ k, move f 1 2 (1 / 2) (Δ k) = Move.reflect → P (Δ (k + 1)) = P (Δ k) := by
      intro k hm
      rw [hstep k, hm]
      show P (insertVertex f (Δ k) (trial (Δ k) 1)) = P (Δ k)
      rw [trial_one]
      exact P_reflect f (Δ k)
    -- from k0 on every step is a reflection
    have hrefl : ∀ j, ε ≤ P (Δ (k0 + j)) ∧ move f 1 2 (1 / 2) (Δ (k0 + j)) = Move.reflect := by
      intro j
      induction j with
      | zero =>
        have h0 : ε ≤ P (Δ (k0 + 0)) := by simpa using hk0
        exact ⟨h0, hmv _ (by omega) h0⟩
      | succ j ih =>
        have h1 : ε ≤ P (Δ (k0 + (j + 1))) := by
          rw [show k0 + (j + 1) = (k0 + j) + 1 by omega, hPstep _ ih.2]
          exact ih.1
        exact ⟨h1, hmv _ (by omega) h1⟩
    -- the vertices stay in a translated lattice
    have hli := linInd_of_nd (Δ k0) (hndk k0)
    let bas : Module.Basis (Fin 2) ℝ (E 2) :=
      basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hb0 : bas 0 = Δ k0 0 - Δ k0 2 := by simp [bas]
    have hb1 : bas 1 = Δ k0 1 - Δ k0 2 := by simp [bas]
    have hmemΛ : ∀ j i, Δ (k0 + j) i - Δ k0 2 ∈ Submodule.span ℤ (Set.range bas) := by
      intro j
      induction j with
      | zero =>
        intro i
        fin_cases i
        · rw [show k0 + 0 = k0 from rfl]
          exact Submodule.subset_span ⟨0, hb0⟩
        · rw [show k0 + 0 = k0 from rfl]
          exact Submodule.subset_span ⟨1, hb1⟩
        · simp
      | succ j ih =>
        intro i
        rw [show k0 + (j + 1) = (k0 + j) + 1 by omega, hstep, (hrefl j).2]
        show insertVertex f (Δ (k0 + j)) (trial (Δ (k0 + j)) 1) i - Δ k0 2 ∈ _
        rw [trial_one]
        rcases iv_mem f (Δ (k0 + j)) (Δ (k0 + j) 0 + Δ (k0 + j) 1 - Δ (k0 + j) 2) i with h | ⟨j', h⟩
        · rw [h]
          have e : Δ (k0 + j) 0 + Δ (k0 + j) 1 - Δ (k0 + j) 2 - Δ k0 2 =
              (Δ (k0 + j) 0 - Δ k0 2) + (Δ (k0 + j) 1 - Δ k0 2) - (Δ (k0 + j) 2 - Δ k0 2) := by
            abel
          rw [e]
          exact Submodule.sub_mem _ (Submodule.add_mem _ (ih 0) (ih 1)) (ih 2)
        · rw [h]; exact ih j'
    have hF := ZSpan.setFinite_inter bas
      (Metric.isBounded_closedBall (x := (0 : E 2)) (r := R + ‖Δ k0 2‖))
    have hG := hF.image (fun z => z + Δ k0 2)
    have hin : ∀ j i, Δ (k0 + j) i ∈ (fun z => z + Δ k0 2) ''
        (Metric.closedBall (0 : E 2) (R + ‖Δ k0 2‖) ∩ (Submodule.span ℤ (Set.range bas) : Set (E 2))) := by
      intro j i
      refine ⟨Δ (k0 + j) i - Δ k0 2, ⟨?_, hmemΛ j i⟩, sub_add_cancel _ _⟩
      rw [mem_closedBall_zero_iff]
      exact le_trans (norm_sub_le _ _) (by linarith [hvert (k0 + j) i])
    have hpi := Set.Finite.pi (ι := Fin 3) (t := fun _ => (fun z => z + Δ k0 2) ''
        (Metric.closedBall (0 : E 2) (R + ‖Δ k0 2‖) ∩ (Submodule.span ℤ (Set.range bas) : Set (E 2))))
      (fun _ => hG)
    have hSanti : StrictAnti (fun j => ∑ i, f (Δ (k0 + j) i)) := by
      apply strictAnti_nat_of_succ_lt
      intro j
      have h := h33 (k0 + j) (hns _)
      rw [show k0 + (j + 1) = k0 + j + 1 by omega]
      obtain ⟨i0, hi0⟩ := h.2
      exact Finset.sum_lt_sum (fun i _ => h.1 i) ⟨i0, Finset.mem_univ _, hi0⟩
    have hinj : Function.Injective (fun j => Δ (k0 + j)) := by
      intro a b hab
      apply hSanti.injective
      simp only at hab ⊢
      rw [hab]
    exact Set.infinite_range_of_injective hinj
      (hpi.subset (by rintro _ ⟨j, rfl⟩; exact Set.mem_univ_pi.mpr (fun i => hin j i)))
  exact squeeze_zero (fun k => diam_nonneg (Δ k)) (fun k => diam_le_P (Δ k)) hPto

end NM2Diam

open Filter Topology NelderMeadLD.Dim2 in
theorem solution (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 2 (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0)) :
    Tendsto (fun k => diam (Δ k)) atTop (𝓝 0) := by
  exact NM2Diam.main f hf hlev σ hσ0 hσ1 Δ hrun hnd
