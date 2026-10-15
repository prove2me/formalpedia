-- Prove2me | solution 1 for HunterPDE.Sobolev.sobolev_endpoint_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T21:18:06.964423+00:00
-- url     : https://prove2.me/submissions/96bb643d-79f5-441d-8be2-b08de64f8aed

import Theorems.Thm_HunterPDE_Sobolev_gagliardo_nirenberg_sobolev
import Theorems.Thm_HunterPDE_Sobolev_smooth_compact_dense
import Theorems.Thm_HunterPDE_Sobolev_memW_of_isTestFunction
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_zero_ae_eq
import Theorems.Thm_HunterPDE_Sobolev_gradient_eLpNorm_le_sobolevNorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory HunterPDE.Sobolev Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (hpn : p < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW 1 (ENNReal.ofReal p) Set.univ f →
        MemLp f (ENNReal.ofReal (sobolevConjugate n p)) volume ∧
          eLpNorm f (ENNReal.ofReal (sobolevConjugate n p)) volume ≤
            (C : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hn : 2 ≤ n := by
    have h : 1 < (n : ℝ) := lt_of_le_of_lt hp hpn
    have : 1 < n := by exact_mod_cast h
    omega
  let C : NNReal := Real.toNNReal (p * ((n : ℝ) - 1) / (2 * ((n : ℝ) - p))) * n
  refine ⟨C, ?_⟩
  intro f hf
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (sobolevConjugate n p)
  let N := fun u : EuclideanSpace ℝ (Fin n) → ℝ => sobolevNorm 1 P Set.univ u
  have chosen {u v : EuclideanSpace ℝ (Fin n) → ℝ} {α : Fin n → ℕ}
      (hv : HasWeakDeriv Set.univ α u v) :
      HasWeakDeriv Set.univ α u (weakDeriv Set.univ α u) := by
    unfold weakDeriv
    rw [dif_pos (show ∃ v, HasWeakDeriv Set.univ α u v from ⟨v, hv⟩)]
    exact Exists.choose_spec _
  have coord (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ)
      (hα : α ∈ multiIndices n 1) :
      eLpNorm (weakDeriv Set.univ α u) P volume ≤ N u := by
    dsimp [N, P]
    rw [sobolevNorm, if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
    have hs := Finset.single_le_sum (s := multiIndices n 1)
      (f := fun β => eLpNorm (weakDeriv Set.univ β u) (ENNReal.ofReal p)
        (volume.restrict Set.univ) ^ p) (fun _ _ => bot_le) hα
    have hr := ENNReal.rpow_le_rpow hs (by positivity : 0 ≤ 1 / p)
    simpa only [Measure.restrict_univ, ← ENNReal.rpow_mul,
      mul_one_div_cancel hp0.ne', ENNReal.rpow_one] using hr
  have zmem : (fun _ : Fin n => 0) ∈ multiIndices n 1 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨fun _ => (0 : Fin 2), Finset.mem_univ _, rfl⟩, by simp⟩
  have memp (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemW 1 P Set.univ u) :
      MemLp u P volume := by
    obtain ⟨g, hg, hgp⟩ := hu.2 (fun _ => 0) (by simp)
    have hgf : g =ᵐ[volume] u := by
      simpa only [Measure.restrict_univ] using hg.zero_ae_eq isOpen_univ
    exact (show MemLp g P volume by simpa only [Measure.restrict_univ] using hgp).ae_eq hgf
  have zerobound (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemW 1 P Set.univ u) :
      eLpNorm u P volume ≤ N u := by
    obtain ⟨g, hg, _⟩ := hu.2 (fun _ => 0) (by simp)
    have heq : weakDeriv Set.univ (fun _ => 0) u =ᵐ[volume] u := by
      simpa only [Measure.restrict_univ] using (chosen hg).zero_ae_eq isOpen_univ
    simpa only [eLpNorm_congr_ae heq] using coord u (fun _ => 0) zmem
  have subW (u v : EuclideanSpace ℝ (Fin n) → ℝ)
      (hu : MemW 1 P Set.univ u) (hv : MemW 1 P Set.univ v) :
      MemW 1 P Set.univ (u - v) := by
    refine ⟨hu.1.sub hv.1, ?_⟩
    intro α hα
    obtain ⟨a, ha, hap⟩ := hu.2 α hα
    obtain ⟨b, hb, hbp⟩ := hv.2 α hα
    exact ⟨a - b, ha.sub hb, hap.sub hbp⟩
  have finite : N f < ⊤ := by
    dsimp [N, P]
    rw [sobolevNorm, if_neg ENNReal.ofReal_ne_top]
    apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
    apply ne_of_lt
    apply ENNReal.sum_lt_top.mpr
    intro α hα
    obtain ⟨g, hg, hgp⟩ := hf.2 α (Finset.mem_filter.mp hα).2
    rw [eLpNorm_congr_ae ((chosen hg).ae_eq isOpen_univ hg)]
    exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hgp.eLpNorm_lt_top.ne
  have normbound (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemW 1 P Set.univ u) :
      N u ≤ N f + N (f - u) := by
    have hc (α : Fin n → ℕ) (hα : α ∈ multiIndices n 1) :
        eLpNorm (weakDeriv Set.univ α u) P (volume.restrict Set.univ) ≤
          eLpNorm (weakDeriv Set.univ α f) P (volume.restrict Set.univ) +
          eLpNorm (weakDeriv Set.univ α (f - u)) P (volume.restrict Set.univ) := by
      obtain ⟨a, ha, hap⟩ := hf.2 α (Finset.mem_filter.mp hα).2
      obtain ⟨b, hb, hbp⟩ := hu.2 α (Finset.mem_filter.mp hα).2
      rw [eLpNorm_congr_ae ((chosen ha).ae_eq isOpen_univ ha),
        eLpNorm_congr_ae ((chosen hb).ae_eq isOpen_univ hb),
        eLpNorm_congr_ae ((chosen (ha.sub hb)).ae_eq isOpen_univ (ha.sub hb))]
      have heq : b = a - (a - b) := by ext x; simp
      calc
        eLpNorm b P (volume.restrict Set.univ) = eLpNorm (a - (a - b)) P (volume.restrict Set.univ) := congrArg (fun w => eLpNorm w P (volume.restrict Set.univ)) heq
        _ ≤ _ := eLpNorm_sub_le hap.aestronglyMeasurable (hap.sub hbp).aestronglyMeasurable hpE
    dsimp [N]
    simp only [sobolevNorm, if_neg (show P ≠ ⊤ from ENNReal.ofReal_ne_top)]
    calc
      _ ≤ (∑ α ∈ multiIndices n 1,
        (eLpNorm (weakDeriv Set.univ α f) P (volume.restrict Set.univ) +
        eLpNorm (weakDeriv Set.univ α (f - u)) P (volume.restrict Set.univ)) ^ P.toReal) ^ (1 / P.toReal) := by
          apply ENNReal.rpow_le_rpow
          · exact Finset.sum_le_sum fun α hα => ENNReal.rpow_le_rpow (hc α hα) ENNReal.toReal_nonneg
          · positivity
      _ ≤ _ := ENNReal.Lp_add_le (multiIndices n 1) _ _ (by simpa [P, ENNReal.toReal_ofReal hp0.le] using hp)
  let ε : ℕ → ENNReal := fun m => ENNReal.ofReal (1 / ((m : ℝ) + 1))
  have εpos (m : ℕ) : 0 < ε m := ENNReal.ofReal_pos.mpr (by positivity)
  have εlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose φ hφ hclose using fun m => smooth_compact_dense (n := n) (k := 1)
    (by rfl) hpE ENNReal.ofReal_ne_top f hf (ε m) (εpos m)
  have hφW (m : ℕ) : MemW 1 P Set.univ (φ m) := memW_of_isTestFunction hpE (φ m) (hφ m)
  have hmeas (m : ℕ) : AEStronglyMeasurable (φ m) volume := (hφ m).1.continuous.aestronglyMeasurable
  have hlp : Tendsto (fun m => eLpNorm (φ m - f) P volume) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds εlim
    · intro m; exact bot_le
    · intro m
      change eLpNorm (φ m - f) P volume ≤ ε m
      rw [eLpNorm_sub_comm]
      exact (zerobound (f - φ m) (subW f (φ m) hf (hφW m))).trans (hclose m).le
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (show P ≠ 0 from (ENNReal.ofReal_pos.mpr hp0).ne') hmeas (memp f hf).1 hlp
  have hsmooth (m : ℕ) : eLpNorm (φ m) Q volume ≤ (C : ENNReal) * N (φ m) := by
    have hg := gagliardo_nirenberg_sobolev hn hp hpn (φ m) (hφ m).1 (hφ m).2.1
    have hb := gradient_eLpNorm_le_sobolevNorm hp (φ m) (hφ m)
    have hm := mul_le_mul' (le_refl (ENNReal.ofReal
      (p * ((n : ℝ) - 1) / (2 * ((n : ℝ) - p))))) hb
    exact hg.trans (by simpa [C, N, P, Q, mul_assoc, ENNReal.ofReal] using hm)
  have hδ (m : ℕ) : eLpNorm f Q volume ≤ (C : ENNReal) * (N f + ε m) := by
    apply eLpNorm_le_of_tendstoInMeasure (h_tendsto := hmeasure) (hf := hmeas)
    have hev : ∀ᶠ j in atTop, ε j < ε m := εlim.eventually (eventually_lt_nhds (εpos m))
    filter_upwards [hev] with j hj
    have he : N (f - φ j) ≤ ε m := le_trans (hclose j).le hj.le
    have hb : N (φ j) ≤ N f + ε m :=
      le_trans (normbound (φ j) (hφW j)) (add_le_add le_rfl he)
    exact le_trans (hsmooth j) (mul_le_mul' (le_refl (C : ENNReal)) hb)
  have hbound : eLpNorm f Q volume ≤ (C : ENNReal) * N f := by
    have ht : Tendsto (fun m => (C : ENNReal) * (N f + ε m)) atTop
        (𝓝 ((C : ENNReal) * N f)) := by
      have hsum : Tendsto (fun m => N f + ε m) atTop (𝓝 (N f)) := by
        simpa only [add_zero] using tendsto_const_nhds.add εlim
      exact ENNReal.Tendsto.const_mul hsum (Or.inr ENNReal.coe_ne_top)
    exact ge_of_tendsto ht (Eventually.of_forall hδ)
  exact ⟨⟨(memp f hf).1, hbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top finite)⟩, hbound⟩
