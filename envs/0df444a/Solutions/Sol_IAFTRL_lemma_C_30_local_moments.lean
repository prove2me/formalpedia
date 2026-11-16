-- Prove2me | solution 1 for IAFTRL.lemma_C_30_local_moments
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:41:46.415702+00:00
-- url     : https://prove2.me/submissions/559ae36d-14ac-49e0-8095-a48eaab30aaa

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_Zd
import Definitions.Def_IAFTRL_refArm
import Definitions.Def_IAFTRL_Run_cumEst
import Definitions.Def_IAFTRL_Run_thetaHat
import Theorems.Thm_IAFTRL_lemma_C_34_interface
import Theorems.Thm_IAFTRL_lemma_C_37_scalar_moments

open Matrix IAFTRL MeasureTheory

namespace C30

variable {d K : ℕ}

lemma abs_dot_le (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (j : Fin K) :
    |arms j ⬝ᵥ θ| ≤ actionNorm arms θ :=
  le_ciSup (f := fun j => |arms j ⬝ᵥ θ|) (Set.finite_range _).bddAbove j

/-- `|(a − b)^⊤ z| ≤ 2‖z‖_𝒜` -/
lemma abs_diff_le (arms : Fin K → Fin d → ℝ) (z : Fin d → ℝ) (a b : Fin K) :
    |(arms a - arms b) ⬝ᵥ z| ≤ 2 * actionNorm arms z := by
  rw [sub_dotProduct]
  have h1 := abs_dot_le arms z a
  have h2 := abs_dot_le arms z b
  have := abs_sub (arms a ⬝ᵥ z) (arms b ⬝ᵥ z)
  linarith

lemma actionNorm_nonneg (arms : Fin K → Fin d → ℝ) (z : Fin d → ℝ) (j : Fin K) :
    0 ≤ actionNorm arms z := le_trans (abs_nonneg _) (abs_dot_le arms z j)

/-- `‖z − θ‖_𝒜 ≤ ‖z‖_𝒜 + ‖θ‖_𝒜` -/
lemma actionNorm_sub_le (arms : Fin K → Fin d → ℝ) (z θ : Fin d → ℝ) (j : Fin K) :
    actionNorm arms (z - θ) ≤ actionNorm arms z + actionNorm arms θ := by
  have : Nonempty (Fin K) := ⟨j⟩
  unfold actionNorm
  apply ciSup_le
  intro i
  rw [dotProduct_sub]
  have h1 := abs_dot_le arms z i
  have h2 := abs_dot_le arms θ i
  unfold actionNorm at h1 h2
  have := abs_sub (arms i ⬝ᵥ z) (arms i ⬝ᵥ θ)
  linarith

/-- the reference action minimizes the cumulative estimate -/
lemma refArm_min (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (j : Fin K) :
    ∃ j₀, refArm arms S = arms j₀ ∧ ∀ i, arms j₀ ⬝ᵥ S ≤ arms i ⬝ᵥ S := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (fun i => arms i ⬝ᵥ S)
    ⟨j, Finset.mem_univ _⟩
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty :=
    ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hm i (Finset.mem_univ _)⟩⟩
  refine ⟨_, ?_, (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2⟩
  unfold refArm
  rw [dif_pos hne]

/-- (C.224): the program's reference gap is `Z_{t,a} = X_{t,a} − min_b X_{t,b}` -/
lemma Zd_eq (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar b : Fin K) :
    Zd arms S b = (arms b - arms jstar) ⬝ᵥ S - ⨅ c, (arms c - arms jstar) ⬝ᵥ S := by
  have : Nonempty (Fin K) := ⟨jstar⟩
  obtain ⟨j₀, hr, hj₀⟩ := refArm_min arms S jstar
  have hinf : ⨅ c, (arms c - arms jstar) ⬝ᵥ S = (arms j₀ - arms jstar) ⬝ᵥ S := by
    apply le_antisymm (ciInf_le (Set.finite_range _).bddBelow j₀)
    apply le_ciInf
    intro c
    rw [sub_dotProduct, sub_dotProduct]
    linarith [hj₀ c]
  unfold Zd
  rw [hr, hinf, sub_dotProduct, sub_dotProduct]
  ring

end C30

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∃ (G : ℕ → Set Ω) (p : ℕ) (Ψ : ℕ → ℝ), (∀ t, MeasurableSet (G t)) ∧
            8 ≤ p ∧ (K : ℝ) ≤ 2 ^ p ∧
            (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar →
              4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) ∧
            cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
              c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
                M ∧
            (∀ t < T, ∀ a, a ≠ jstar →
              Integrable ((G t).indicator fun ω => ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
                ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) P ∧
              ∫ ω, (G t).indicator (fun ω => ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
                ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) ω ∂P ≤ 8 ^ p) ∧
            (∀ t < T, ∀ a, a ≠ jstar →
              Integrable ((G t).indicator fun ω => ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
                ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) P ∧
              ∫ ω, (G t).indicator (fun ω => ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
                ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) ω ∂P ≤ (8 * Ψ t) ^ p) ∧
            (∀ t < T, 1 ≤ Ψ t ∧ Ψ t ≤ M) ∧
            ∑ t ∈ Finset.range T, (Ψ t - 1) / (t + 1) ≤ M := by
  classical
  obtain ⟨c₁, hc₁, hB⟩ := lemma_C_37_scalar_moments
  refine ⟨c₁, hc₁, ?_⟩
  intro d K hd arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap
  have hΔ2 : ∀ a, (arms a - arms jstar) ⬝ᵥ θ ≤ 2 := fun a => by
    have := C30.abs_diff_le arms θ a jstar
    have := le_abs_self ((arms a - arms jstar) ⬝ᵥ θ)
    linarith
  obtain ⟨M, hM⟩ := hB hd jstar (fun a => (arms a - arms jstar) ⬝ᵥ θ) Δ₀ hΔ₀ hΔ₀1
    (by simp) hgap hΔ2
  refine ⟨M, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  have hI := lemma_C_34_interface hd arms hA jstar P T R hR
  have hX0 : ∀ a ω, (arms a - arms jstar) ⬝ᵥ R.cumEst arms 0 ω = 0 := by
    intro a ω; simp [Run.cumEst]
  have hXs : ∀ t a ω, (arms a - arms jstar) ⬝ᵥ R.cumEst arms (t + 1) ω =
      (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω +
        (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω := by
    intro t a ω
    simp only [Run.cumEst, Finset.sum_range_succ, dotProduct_add]
  have hfilt : ∀ t < T, R.G t ≤ ‹MeasurableSpace Ω› ∧ R.G t ≤ R.G (t + 1) := fun t ht =>
    ⟨(hR t ht).1.2.2.2.1, (hR t ht).1.2.2.2.2.2.2.1⟩
  have hDj : ∀ t ω, (arms jstar - arms jstar) ⬝ᵥ R.thetaHat arms t ω = 0 := by
    intro t ω; simp
  have hDm : ∀ t < T, ∀ a,
      Measurable[R.G (t + 1)] (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ∧
        Measurable (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) :=
    fun t ht a => (hI t ht a).1
  have hκm : ∀ t < T, Measurable[R.G t] (fun ω => actionNorm arms (R.θs t ω - θ)) ∧
      ∀ a, Measurable[R.G t] (fun ω => (arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ)) := by
    intro t ht
    have hθm : Measurable[R.G t] (R.θs t) := (hR t ht).1.2.2.2.2.2.1
    refine ⟨?_, fun a => ?_⟩
    · unfold actionNorm
      exact Measurable.iSup fun j =>
        ((continuous_const.dotProduct (continuous_id.sub continuous_const)).abs.measurable).comp
          hθm
    · exact ((continuous_const.dotProduct (continuous_id.sub continuous_const)).measurable).comp
        hθm
  have hκb : ∀ t < T, ∀ ω, 0 ≤ actionNorm arms (R.θs t ω - θ) ∧
      actionNorm arms (R.θs t ω - θ) ≤ 2 ∧
      ∀ a, |(arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ)| ≤ 2 * actionNorm arms (R.θs t ω - θ) ∧
        |(arms a - arms jstar) ⬝ᵥ θ + (arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ)| ≤ 2 := by
    intro t ht ω
    have hθt : actionNorm arms (R.θs t ω) ≤ 1 := (hR t ht).2.2.2.2 ω
    refine ⟨C30.actionNorm_nonneg arms _ jstar, ?_, fun a => ⟨C30.abs_diff_le arms _ a jstar, ?_⟩⟩
    · have := C30.actionNorm_sub_le arms (R.θs t ω) θ jstar
      linarith
    · have e : (arms a - arms jstar) ⬝ᵥ θ + (arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ) =
          (arms a - arms jstar) ⬝ᵥ R.θs t ω := by rw [dotProduct_sub]; ring
      rw [e]
      have := C30.abs_diff_le arms (R.θs t ω) a jstar
      linarith
  have hmean : ∀ t < T, ∀ a,
      P[fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω | R.G t] =ᵐ[P]
        fun ω => (arms a - arms jstar) ⬝ᵥ θ + (arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ) := by
    intro t ht a
    refine (hI t ht a).2.1.trans (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [dotProduct_sub]; ring
  have hZ : ∀ t (ω : Ω) b, Zd arms (R.cumEst arms t ω) b =
      (arms b - arms jstar) ⬝ᵥ R.cumEst arms t ω -
        ⨅ c, (arms c - arms jstar) ⬝ᵥ R.cumEst arms t ω :=
    fun t ω b => C30.Zd_eq arms (R.cumEst arms t ω) jstar b
  have hmag : ∀ t < T, ∀ a ω, |(arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω| ≤
      2 * beta d K (t + 1) + (((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω -
        ⨅ b, (arms b - arms jstar) ⬝ᵥ R.cumEst arms t ω) +
        ((arms jstar - arms jstar) ⬝ᵥ R.cumEst arms t ω -
          ⨅ b, (arms b - arms jstar) ⬝ᵥ R.cumEst arms t ω)) / Bc K := by
    intro t ht a ω
    have h := (hI t ht a).2.2.1 ω
    rw [hZ t ω a, hZ t ω jstar] at h
    exact h
  have hsec : ∀ t < T, ∀ a,
      P[fun ω => ((arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ^ 2 | R.G t] ≤ᵐ[P]
        fun ω => 4 * beta d K (t + 1) + 2 * (((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω -
          ⨅ b, (arms b - arms jstar) ⬝ᵥ R.cumEst arms t ω) ^ 2 +
          ((arms jstar - arms jstar) ⬝ᵥ R.cumEst arms t ω -
            ⨅ b, (arms b - arms jstar) ⬝ᵥ R.cumEst arms t ω) ^ 2) / (Bc K * ((t : ℝ) + 1)) := by
    intro t ht a
    refine (hI t ht a).2.2.2.trans (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [hZ t ω a, hZ t ω jstar]
  exact hM P R.G T C (fun t a ω => (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)
    (fun t a ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω)
    (fun t a ω => (arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ))
    (fun t ω => actionNorm arms (R.θs t ω - θ)) hT hC hfilt hX0 hXs hDj hDm hκm hκb hcor.2
    hmean hmag hsec
