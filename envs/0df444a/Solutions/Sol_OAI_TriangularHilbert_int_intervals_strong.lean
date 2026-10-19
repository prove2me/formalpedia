-- Prove2me | solution 1 for OAI.TriangularHilbert.int_intervals_strong
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:32:46.462117+00:00
-- url     : https://prove2.me/submissions/16aed564-590b-469d-a43b-0b623fb86172

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/IntStrong.lean:L28-L79
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.int_intervals_strong. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Theorems.Thm_OAI_TriangularHilbert_int_intervals_weak

-- ---- from OAI.Analysis.TriangularHilbert.IntWeak ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma card_intInterval (n : ℤ) (r : ℕ) : (intInterval n r).card = 2*r+1 := by
  rw [intInterval,Int.card_Icc]
  have he : n+(r:ℤ)+1-(n-r) = ((2*r+1 : ℕ):ℤ) := by push_cast; ring
  rw [he,Int.toNat_natCast]

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.StrongLayer ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma squareLayer_integrable (a : ℝ) : Integrable (squareLayer a) := by
  have h : IntegrableOn (fun t : ℝ => t^2) (Set.Icc 0 (Real.sqrt a)) volume :=
    (continuous_id.pow 2).integrableOn_Icc
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (h.mono_set Set.Ioo_subset_Icc_self)

lemma oneLayer_integrable (a : ℝ) : Integrable (oneLayer a) := by
  have h : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioo 0 (Real.sqrt a)) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  exact (integrable_indicator_iff measurableSet_Ioo).mpr h

lemma integral_squareLayer {a : ℝ} (ha : 0 ≤ a) :
    (∫ t, squareLayer a t) = a * Real.sqrt a / 3 := by
  simp only [squareLayer]
  rw [integral_indicator measurableSet_Ioo]
  rw [← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (Real.sqrt_nonneg a)]
  rw [integral_pow]
  have he : (Real.sqrt a)^3 = a*Real.sqrt a := by
    rw [pow_succ,Real.sq_sqrt ha]
  norm_num [he]

lemma integral_oneLayer (a : ℝ) : (∫ t, oneLayer a t) = Real.sqrt a := by
  simp only [oneLayer]
  rw [integral_indicator measurableSet_Ioo,← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (Real.sqrt_nonneg a),intervalIntegral.integral_const]
  simp

lemma layer_iff {a t : ℝ} (ht : 0 < t) :
    t ∈ Set.Ioo 0 (Real.sqrt a) ↔ t^2 < a := by
  exact and_iff_right ht |>.trans (Real.lt_sqrt (by positivity))

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.IntStrong ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma truncated_average_lower (D : Finset ℤ) (f : ℤ → ℝ) (r : ℤ → ℕ) (n : ℤ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hav : ρ*(2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    (ρ/2)*(2*(r n:ℝ)+1) ≤
      ∑ m ∈ D ∩ intInterval n (r n), if ρ < 2*f m then f m else 0 := by
  classical
  have he (m : ℤ) : f m ≤ (if ρ < 2*f m then f m else 0) + ρ/2 := by
    split_ifs <;> linarith
  have hsum := Finset.sum_le_sum (fun m (_ : m ∈ D ∩ intInterval n (r n)) => he m)
  have hc : ((D ∩ intInterval n (r n)).card:ℝ) ≤ 2*(r n:ℝ)+1 := by
    have ht := Finset.card_le_card (Finset.inter_subset_right : D ∩ intInterval n (r n) ⊆ intInterval n (r n))
    rw [card_intInterval] at ht
    exact_mod_cast ht
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
  have hp := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ ρ/2)
  linarith

lemma int_intervals_strong (D s : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ m ∈ D, 0 ≤ f m) (hg : ∀ n ∈ s, 0 ≤ g n) (r : ℤ → ℕ)
    (hav : ∀ n ∈ s, g n*(2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    (∑ n ∈ s, g n*Real.sqrt (g n)) ≤
      18*Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
  classical
  have layer_bound (t : ℝ) : (∑ n ∈ s, 3*squareLayer (g n) t) ≤
      18 * ∑ m ∈ D, f m * oneLayer (2*f m) t := by
    by_cases ht : 0 < t
    · let u := s.filter (fun n => t^2 < g n)
      let f' := fun m => if t^2 < 2*f m then f m else 0
      have hw := int_intervals_weak D u f'
        (fun m hm => by unfold f'; split_ifs; exact hf m hm; exact le_rfl) r (by positivity : 0 ≤ t^2/2)
        (fun n hn => truncated_average_lower D f r n (sq_nonneg t)
          ((mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hn).2.le (by positivity)).trans
            (hav n (Finset.mem_filter.mp hn).1)))
      have hl : (∑ n ∈ s, 3*squareLayer (g n) t) = 3*t^2*(u.card:ℝ) := by
        simp only [squareLayer,Set.indicator_apply,layer_iff ht,mul_ite,mul_zero]
        rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const]
        simp only [u,nsmul_eq_mul]
        ring
      have hr : (∑ m ∈ D, f m*oneLayer (2*f m) t) = ∑ m ∈ D, f' m := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [oneLayer,Set.indicator_apply,layer_iff ht,f']
        split_ifs <;> simp
      rw [hl,hr]
      linarith
    · have he (a : ℝ) : squareLayer a t = 0 ∧ oneLayer a t = 0 := by
        simp [squareLayer,oneLayer,Set.indicator_of_notMem,ht]
      simp only [(he _).1,(he _).2,mul_zero,Finset.sum_const_zero,le_refl]
  have hL : Integrable (fun t => ∑ n ∈ s, 3*squareLayer (g n) t) :=
    integrable_finsetSum _ (fun n _ => (squareLayer_integrable (g n)).const_mul 3)
  have hR : Integrable (fun t => 18*∑ m ∈ D, f m*oneLayer (2*f m) t) :=
    (integrable_finsetSum _ (fun m _ => (oneLayer_integrable (2*f m)).const_mul (f m))).const_mul 18
  have hi := integral_mono hL hR layer_bound
  rw [integral_finsetSum _ (fun n _ => (squareLayer_integrable (g n)).const_mul 3),
    integral_const_mul,integral_finsetSum _ (fun m _ => (oneLayer_integrable (2*f m)).const_mul (f m))] at hi
  have hl : (∑ n ∈ s, ∫ t, 3*squareLayer (g n) t) = ∑ n ∈ s, g n*Real.sqrt (g n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul,integral_squareLayer (hg n hn)]
    ring
  have hr : (∑ m ∈ D, ∫ t, f m*oneLayer (2*f m) t) =
      Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_const_mul,integral_oneLayer,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hl,hr] at hi
  simpa only [mul_assoc] using hi
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.int_intervals_strong := @_root_.OAI.TriangularHilbert.int_intervals_strong
