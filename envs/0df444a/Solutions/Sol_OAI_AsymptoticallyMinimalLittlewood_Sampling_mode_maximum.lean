-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_maximum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:59:51.380227+00:00
-- url     : https://prove2.me/submissions/de706519-7311-40f9-bdd8-00e80791b2c2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ModeSampling.lean:L176-L249
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_maximum. The node keeps its source
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
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_sampled_support_zero
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_tsum_eq_sum_fin
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_uniform_poisson_chirp

-- ---- from OAI.Analysis.Littlewood.SamplingTail ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

lemma stationaryWave_norm (g : ℝ → ℂ) (N β b : ℝ) (l : ℤ) :
    ‖stationaryWave g N β b l‖=‖g (((l : ℝ)-b)/β)‖/Real.sqrt |β| := by
  rw [stationaryWave,norm_mul,norm_div,norm_realPhase,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- from OAI.Analysis.Littlewood.ModeSampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uP

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

end
end AsymptoticallyMinimalLittlewood.Sampling

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma norm_sum_sparse {P : Type uP} (s : Finset P) (f : P → ℂ) {K : ℝ}
    (hK : 0≤K) (hb : ∀ i∈s, ‖f i‖≤K)
    (hs : ∀ i∈s, ∀ j∈s, f i≠0 → f j≠0 → i=j) : ‖∑ i∈s, f i‖≤K := by
  classical
  by_cases h : ∃ i∈s, f i≠0
  · obtain ⟨i,hi,hfi⟩ := h
    rw [Finset.sum_eq_single i]
    · exact hb i hi
    · intro j hj hji
      by_contra hjf
      exact hji (hs j hj i hi hjf hfi)
    · exact fun hn ↦ (hn hi).elim
  · have hz : ∀ i∈s, f i=0 := by simpa using h
    simpa only [Finset.sum_eq_zero hz,norm_zero] using hK

lemma phase_modulate (lam b t x : ℝ) :
    phase lam (-b) x*realPhase (2*Real.pi*t*x)=phase lam (-(b+t)) x := by
  simp only [phase,realPhase,← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma mode_modulate {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (N : ℕ) (t : ℝ) :
    ∑ k : Fin N, modeSum g c lam b d N k*realPhase (2*Real.pi*t*k)=
    ∑ i, (c i*realPhase (2*Real.pi*N*d i))*
      ∑ k : Fin N, g i ((k : ℝ)/N)*phase (lam i/N) (-(b i+t)) k := by
  simp only [modeSum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (c i*realPhase (2*Real.pi*N*d i))*(g i ((k : ℝ)/N)*
      (phase (lam i/N) (-b i) k*realPhase (2*Real.pi*t*k))) := by ring
    _ = _ := by rw [phase_modulate]

/-- The fixed-data uniform circle estimate; the sparse-stationary hypothesis
will be discharged by the signed interval packing. -/
theorem mode_maximum {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (hgc : ∀ i, HasCompactSupport (g i))
    (hgs : ∀ i, ContDiff ℝ ∞ (g i)) (hgi : ∀ i, tsupport (g i)⊆Set.Ioo (0:ℝ) 1)
    (hgb : ∀ i x, ‖g i x‖≤1) (hlam : ∀ i, lam i≠0)
    {K : ℝ} (hK : 0≤K) (hc : ∀ i, ‖c i‖/Real.sqrt |lam i|≤K)
    (hsparse : ∀ t : ℝ, ∀ i j : P, ∀ l m : ℤ,
      g i (((l : ℝ)-(b i+t))/lam i)≠0 → g j (((m : ℝ)-(b j+t))/lam j)≠0 →
      i=j ∧ l=m) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → ∀ t∈Set.Icc (0:ℝ) 1,
      ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N,
        modeSum g c lam b d N k*realPhase (2*Real.pi*t*k)‖≤K+C/N := by
  classical
  have hh (i : P) := uniform_poisson_chirp (hgc i) (hgs i)
    (A := 1) (B := |b i|+1) (by norm_num) (by positivity)
    (fun x hx ↦ by have := hgi i hx; constructor <;> linarith [this.1,this.2]) (hlam i)
  choose J C hC hest using hh
  let D := ∑ i, ‖c i‖*C i
  have hD : 0≤D := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (norm_nonneg _) (hC i))
  refine ⟨D,hD,?_⟩
  intro N hN t ht
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hN0 : 0<N := by omega
  have hb (i : P) : |b i+t|≤|b i|+1 :=
    (abs_add_le _ _).trans (add_le_add_right (show |t|≤1 by rw [abs_of_nonneg ht.1]; exact ht.2) _)
  let W (i : P) (l : ℤ) := (c i*realPhase (2*Real.pi*N*d i))*stationaryWave (g i) N (lam i) (b i+t) l
  let S : Finset (P × ℤ) := Finset.univ.sigma J |>.map
    ⟨fun p ↦ (p.1,p.2),by intro x y h; exact Sigma.ext (congrArg Prod.fst h) (heq_of_eq (congrArg Prod.snd h))⟩
  have hlead : ‖∑ i, ∑ l∈J i, W i l‖≤K := by
    have he : (∑ i, ∑ l∈J i, W i l)=∑ p∈S, W p.1 p.2 := by
      simp only [S,Finset.sum_map,Finset.sum_sigma]
      rfl
    rw [he]
    apply norm_sum_sparse S (fun p ↦ W p.1 p.2) hK
    · intro p _
      simp only [W,norm_mul,norm_realPhase,mul_one,stationaryWave_norm]
      calc
        _ ≤ ‖c p.1‖*(1/Real.sqrt |lam p.1|) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hgb _ _) (Real.sqrt_nonneg _)) (norm_nonneg _)
        _ ≤ K := by simpa only [mul_one_div] using hc p.1
    · intro p _ q _ hp hq
      have hgp : g p.1 (((p.2 : ℝ)-(b p.1+t))/lam p.1)≠0 := by
        intro hz; apply hp; simp [W,stationaryWave,hz]
      have hgq : g q.1 (((q.2 : ℝ)-(b q.1+t))/lam q.1)≠0 := by
        intro hz; apply hq; simp [W,stationaryWave,hz]
      exact Prod.ext (hsparse t _ _ _ _ hgp hgq).1 (hsparse t _ _ _ _ hgp hgq).2
  let A (i : P) := (1/(Real.sqrt N : ℂ))*∑ k : Fin N,
    g i ((k : ℝ)/N)*phase (lam i/N) (-(b i+t)) k
  have hA (i : P) : ‖A i-∑ l∈J i, stationaryWave (g i) N (lam i) (b i+t) l‖≤C i/N := by
    have h := (hest i (N : ℝ) (b i+t) hNr (hb i)).2
    rw [tsum_eq_sum_fin _ (fun k hk ↦ by rw [sampled_support_zero (hgi i) hN0 hk,zero_mul])] at h
    simpa only [Int.cast_natCast] using h
  have herr : ‖(∑ i, (c i*realPhase (2*Real.pi*N*d i))*A i)-
      ∑ i, ∑ l∈J i, W i l‖≤D/N := by
    simp only [W,← Finset.mul_sum,← Finset.sum_sub_distrib,← mul_sub]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i, ‖c i‖*(C i/N) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_mul,norm_realPhase,mul_one] using
          mul_le_mul_of_nonneg_left (hA i) (norm_nonneg (c i))
      _ = D/N := by simp only [D,Finset.sum_div,mul_div_assoc]
  have he : (1/(Real.sqrt N : ℂ))*∑ k : Fin N,
      modeSum g c lam b d N k*realPhase (2*Real.pi*t*k)=
      ∑ i, (c i*realPhase (2*Real.pi*N*d i))*A i := by
    rw [mode_modulate,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [A]
    ring
  rw [he]
  exact (norm_le_norm_sub_add _ _).trans ((add_le_add herr hlead).trans_eq (add_comm _ _))

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail


theorem solution.{uP} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_maximum.{uP} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_maximum.{uP}
