-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:58:02.220018+00:00
-- url     : https://prove2.me/submissions/bbc1be5b-5042-4272-b395-ff4589163583

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ModeSampling.lean:L76-L128
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_finiteAverage_zero
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_linear_average_error
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_sampled_support_zero
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_tsum_eq_sum_fin

-- ---- from OAI.Analysis.Littlewood.SamplingEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma phase_zero (x : ℝ) : phase 0 0 x=1 := by simp [phase]

lemma unphased_average {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A : ℝ} (hA : 0≤A)
    (hsupp : tsupport g⊆Set.Icc (-A) A) :
    Tendsto (fun N : ℕ ↦ (1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)))
      atTop (𝓝 (∫ x : ℝ, g x)) := by
  obtain ⟨C,hC,h⟩ := linear_average_error hg hgs hA hsupp 0 {0} (by
    intro l hl
    exact_mod_cast (show l≠0 by simpa only [Finset.mem_singleton] using hl))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : 1≤(N : ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N : ℝ) := by positivity
  have hh := h N hN0
  simp only [neg_zero,phase_zero,mul_one,Finset.sum_singleton,Int.cast_zero,
    sub_zero,mul_zero] at hh
  exact hh.trans (div_le_div_of_nonneg_left hC hN0 (by nlinarith))

lemma finiteAverage_eq {g : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {N : ℕ} (hN : 0<N) (β b : ℝ) :
    finiteAverage g N β b=(1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k) := by
  rw [tsum_eq_sum_fin _ (fun k hk ↦ by rw [sampled_support_zero hg hN hk,zero_mul])]
  rfl

lemma finiteAverage_diagonal {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hsupp : tsupport g⊆Set.Ioo (0:ℝ) 1) :
    Tendsto (fun N : ℕ ↦ finiteAverage g N 0 0) atTop (𝓝 (∫ x : ℝ, g x)) := by
  have hs : tsupport g⊆Set.Icc (-1:ℝ) 1 := fun x hx ↦
    ⟨by linarith [(hsupp hx).1],(hsupp hx).2.le⟩
  apply (unphased_average hg hgs (by norm_num : (0:ℝ)≤1) hs).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [finiteAverage_eq hsupp (by omega)]
  simp only [zero_div,neg_zero,phase_zero,mul_one]

lemma phase_mul (t u s v x : ℝ) : phase t u x*phase s v x=phase (t+s) (u+v) x := by
  rw [phase,phase,phase,← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_conj (t u x : ℝ) : conj (phase t u x)=phase (-t) (-u) x := by
  rw [phase,phase,← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring

lemma phase_mul_conj (t u s v x : ℝ) :
    phase t u x*conj (phase s v x)=phase (t-s) (u-v) x := by
  rw [phase_conj,phase_mul]
  rfl

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- from OAI.Analysis.Littlewood.ModeSampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uP

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma realPhase_mul_conj (x y : ℝ) :
    realPhase x*conj (realPhase y)=realPhase (x-y) := by
  rw [realPhase,realPhase,realPhase,← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_sub]
  ring

lemma realPhase_zero : realPhase 0=1 := by simp [realPhase]

lemma norm_sq_modeSum {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (N : ℕ) :
    (((∑ k : Fin N, ‖modeSum g c lam b d N k‖^2)/(N : ℝ) : ℝ) : ℂ)=
      ∑ i, ∑ j, (c i*conj (c j))*realPhase (2*Real.pi*N*(d i-d j))*
        finiteAverage (fun x ↦ g i x*conj (g j x)) N (lam i-lam j) (b i-b j) := by
  classical
  simp only [Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_pow]
  have he (z : ℂ) : (‖z‖ : ℂ)^2=z*conj z := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  simp_rw [he]
  simp only [modeSum,map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin N))]
  simp only [Finset.sum_div,finiteAverage,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_mul,Complex.ofReal_natCast]
  have hp := phase_mul_conj (lam i/N) (-b i) (lam j/N) (-b j) (k : ℝ)
  rw [← sub_div,show -b i - -b j= -(b i-b j) by ring] at hp
  have hd := realPhase_mul_conj (2*Real.pi*N*d i) (2*Real.pi*N*d j)
  rw [show 2*Real.pi*N*d i-2*Real.pi*N*d j=2*Real.pi*N*(d i-d j) by ring] at hd
  calc
    _ = (c i*conj (c j))*(realPhase (2*Real.pi*N*d i)*conj (realPhase (2*Real.pi*N*d j)))*
      (g i ((k : ℝ)/N)*conj (g j ((k : ℝ)/N)))*
      (phase (lam i/N) (-b i) k*conj (phase (lam j/N) (-b j) k))/(N : ℂ) := by ring
    _ = _ := by rw [hd,hp]; ring

lemma amplitude_pair_compact {g h : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x ↦ g x*conj (h x)) := hg.mul_right

lemma amplitude_pair_smooth {g h : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (fun x ↦ g x*conj (h x)) :=
  hg.mul (Complex.conjCLE.contDiff.comp hh)

lemma amplitude_pair_support {g h : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1) :
    tsupport (fun x ↦ g x*conj (h x))⊆Set.Ioo (0:ℝ) 1 :=
  tsupport_mul_subset_left.trans hg

lemma diagonal_integral (g : ℝ → ℂ) :
    (∫ x : ℝ, g x*conj (g x))=((∫ x : ℝ, ‖g x‖^2 : ℝ) : ℂ) := by
  simp_rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  exact integral_ofReal

/-- Fixed-data mean square sampling, including the equal-curvature case.
Separated blocks may be handled by the zero-product alternative. -/
theorem mode_energy {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (hgc : ∀ i, HasCompactSupport (g i))
    (hgs : ∀ i, ContDiff ℝ ∞ (g i)) (hgi : ∀ i, tsupport (g i)⊆Set.Ioo (0:ℝ) 1)
    (hgb : ∀ i x, ‖g i x‖≤1)
    (hfreq : ∀ i j, i≠j → (lam i≠lam j ∨ ∀ l : ℤ, (l : ℝ)≠b i-b j) ∨
      ∀ x, g i x*conj (g j x)=0) :
    Tendsto (fun N : ℕ ↦ (∑ k : Fin N, ‖modeSum g c lam b d N k‖^2)/(N : ℝ))
      atTop (𝓝 (∑ i, ‖c i‖^2*(∫ x : ℝ, ‖g i x‖^2))) := by
  classical
  let V (i j : P) (N : ℕ) : ℂ := (c i*conj (c j))*realPhase (2*Real.pi*N*(d i-d j))*
    finiteAverage (fun x ↦ g i x*conj (g j x)) N (lam i-lam j) (b i-b j)
  have hV (i j : P) : Tendsto (V i j) atTop
      (𝓝 (if i=j then ((‖c i‖^2*(∫ x : ℝ, ‖g i x‖^2) : ℝ) : ℂ) else 0)) := by
    by_cases hij : i=j
    · subst j
      simp only [V,sub_self,mul_zero,realPhase_zero,mul_one]
      have h := (finiteAverage_diagonal (amplitude_pair_compact (hgc i))
        (amplitude_pair_smooth (hgs i) (hgs i)) (amplitude_pair_support (hgi i))).const_mul (c i*conj (c i))
      rw [diagonal_integral] at h
      simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,
        Complex.ofReal_mul,ite_true] using h
    · rw [ite_eq_right hij]
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      have ht : Tendsto (fun N : ℕ ↦ ‖finiteAverage (fun x ↦ g i x*conj (g j x)) N
          (lam i-lam j) (b i-b j)‖) atTop (𝓝 0) := by
        rcases hfreq i j hij with hf | hz
        · apply finiteAverage_zero (amplitude_pair_compact (hgc i))
            (amplitude_pair_smooth (hgs i) (hgs j)) (amplitude_pair_support (hgi i))
            (by norm_num : (0:ℝ)≤1) ?_ (hf.imp (sub_ne_zero.mpr) id)
          intro x
          rw [norm_mul,norm_conj]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hgb i x)).trans (hgb j x)
        · simp only [finiteAverage,hz,zero_mul,Finset.sum_const_zero,mul_zero,norm_zero]
          exact tendsto_const_nhds
      have he (N : ℕ) : ‖V i j N‖=‖c i*conj (c j)‖*
          ‖finiteAverage (fun x ↦ g i x*conj (g j x)) N (lam i-lam j) (b i-b j)‖ := by
        simp only [V,norm_mul,norm_realPhase,mul_one]
      simp_rw [he]
      simpa only [mul_zero] using ht.const_mul ‖c i*conj (c j)‖
  have ht := tendsto_finsetSum Finset.univ (fun i _ ↦
    tendsto_finsetSum Finset.univ (fun j _ ↦ hV i j))
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true] at ht
  have ht' := continuous_re.tendsto _ |>.comp ht
  simp only [Complex.re_sum,Complex.ofReal_re] at ht'
  apply ht'.congr'
  filter_upwards [] with N
  have he := norm_sq_modeSum g c lam b d N
  dsimp [V] at *
  rw [← he]
  simp only [Complex.ofReal_re]

end
end AsymptoticallyMinimalLittlewood.Sampling

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail


theorem solution.{uP} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_energy.{uP} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_energy.{uP}
