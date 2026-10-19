-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.selectedSum_le_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:52:41.523111+00:00
-- url     : https://prove2.me/submissions/e3cf4ad5-f7d0-48f8-b125-873d9bd338c4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SelectedScale.lean:L105-L130
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.selectedSum_le_cubic. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Theorems.Thm_OAI_TriangularHilbert_Heat_heatPlane_integrable
import Theorems.Thm_OAI_TriangularHilbert_Heat_integral_oddWindow_triple
import Theorems.Thm_OAI_TriangularHilbert_Heat_masked_cost_integral_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_oddWindow_triple_integrable
import Theorems.Thm_OAI_TriangularHilbert_Heat_planeTime_intervalIntegrable
import Theorems.Thm_OAI_TriangularHilbert_Heat_windowTrace_eq
import Theorems.Thm_OAI_TriangularHilbert_Heat_windowTrace_le

-- ---- from OAI.Analysis.TriangularHilbert.HeatCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma heatCost_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ)
    (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :
    0 ≤ heatCost A h u p σ v w := by
  unfold heatCost hessianCost rootCost
  apply mul_nonneg (by norm_num)
  by_cases hb : BddAbove (Set.range (variation (CFC.sqrt (localGram A h u p σ v w))
      (localFirst A h u p σ v w)))
  · apply le_csSup hb
    exact ⟨0, by simp [variation, penalty]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneDissipation ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma strictRate_pos (i w : Three) : 0 < strictRate i w := by
  unfold strictRate; split_ifs <;> norm_num

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SortedWindows ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma sortedTimes_monotone (S : Finset ℝ) (hS : S.Nonempty) : Monotone (sortedTimes S hS) := by
  intro k l hkl
  apply (S.orderEmbOfFin rfl).monotone
  exact min_le_min_right _ hkl

lemma sortedTimes_zero (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS 0 = S.min' hS := by
  exact Finset.orderEmbOfFin_zero rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_last (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS (S.card-1) = S.max' hS := by
  simp only [sortedTimes,min_self]
  exact Finset.orderEmbOfFin_last rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_no_between (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e : ℝ}
    (he : e ∈ S) : ¬ (sortedTimes S hS k < e ∧ e < sortedTimes S hS (k+1)) := by
  have he' : e ∈ Set.range (S.orderEmbOfFin rfl) := by simpa using he
  obtain ⟨j,rfl⟩ := he'
  intro ⟨h1,h2⟩
  have h1' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h1
  have h2' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h2
  change min k (S.card-1) < j.val at h1'
  change j.val < min (k+1) (S.card-1) at h2'
  omega

lemma sortedTimes_le_iff (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e s : ℝ}
    (he : e ∈ S) (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    e ≤ s ↔ e ≤ sortedTimes S hS k := by
  constructor
  · intro hes
    by_contra h
    exact sortedTimes_no_between S hS k he ⟨lt_of_not_ge h,hes.trans_lt hs.2⟩
  · exact fun h => h.trans hs.1

lemma sortedTimes_mask_const (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {a b s : ℝ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) (A : ℂ) :
    windowMask a b s A = windowMask a b (sortedTimes S hS k) A := by
  have h1 := sortedTimes_le_iff S hS k ha hs
  have h2 := not_congr (sortedTimes_le_iff S hS k hb hs)
  simp only [not_le] at h2
  simp only [windowMask,h1,h2]

lemma intervalIntegrable_of_Ico_eq {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (he : ∀ s ∈ Set.Ico a b, f s=g s) :
    IntervalIntegrable f volume a b := by
  apply hg.congr_ae
  rw [Set.uIoc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Ioc).2
  filter_upwards [volume.ae_ne b] with s hsb hs
  exact (he s ⟨hs.1.le,lt_of_le_of_ne hs.2 hsb⟩).symm

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MaskedActual ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma maskedArray_const (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    (k : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    maskedArray A a b s = maskedArray A a b (sortedTimes S hS k) := by
  unfold maskedArray
  congr 1
  funext i j
  exact sortedTimes_mask_const S hS k (ha i j) (hb i j) hs _

lemma planeSumCost_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (r : Three) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => ∑ v, planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b := by
  have hi : IntervalIntegrable (∑ v : Three, fun s => planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b :=
    IntervalIntegrable.sum Finset.univ (fun v _ => (planeTime_intervalIntegrable A hh u d (strictRate r) (strictRate_pos r) ha hab).2 v v)
  convert hi using 1
  ext s
  simp

lemma maskedCost_interval_piece (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (ht0 : 0 < sortedTimes S hS 0) (r : Three) (k : ℕ) :
    IntervalIntegrable (maskedCost A a b h u r) volume (sortedTimes S hS k) (sortedTimes S hS (k+1)) := by
  have ht := sortedTimes_monotone S hS
  apply intervalIntegrable_of_Ico_eq (ht (Nat.le_succ k))
    (planeSumCost_intervalIntegrable (maskedArray A a b (sortedTimes S hS k)) hh u 0 r
      (ht0.trans_le (ht (Nat.zero_le k))) (ht (Nat.le_succ k)))
  intro s hs
  unfold maskedCost
  rw [maskedArray_const A a b S hS ha hb k hs]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SignedCenter ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma signedCenter_eq_integral (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) : signedCenter A h u s = ∫ z : ℝ×ℝ, windowTrace A h u (chart 2 0 z) s := by
  have hi (i j k : ι) : Integrable (fun z : ℝ×ℝ => (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*
      ((oddWindow s (u i-z.1)*oddWindow s (u j-z.2)*oddWindow s (u k+z.1+z.2):ℝ):ℂ)) :=
    (oddWindow_triple_integrable hs (u i) (u j) (u k)).ofReal.const_mul _
  have he (z : ℝ×ℝ) : windowTrace A h u (chart 2 0 z) s =
      ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*
        ((oddWindow s (u i-z.1)*oddWindow s (u j-z.2)*oddWindow s (u k+z.1+z.2):ℝ):ℂ) := by
    rw [windowTrace_eq A hh hs]
    congr 1
    ext i
    congr 1
    ext j
    congr 1
    ext k
    rw [show chart 2 0 z 0 = z.1 by rfl,show chart 2 0 z 1 = z.2 by rfl,
      show chart 2 0 z 2 = 0-z.1-z.2 by rfl,show u k-(0-z.1-z.2) = u k+z.1+z.2 by ring]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k)))]
  unfold signedCenter
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul,integral_complex_ofReal,integral_oddWindow_triple hs]

lemma signedCenter_norm_le (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) : ‖signedCenter A h u s‖ ≤ (440/3)*s*∑ v,
      planeIntegral (fun p => heatCost A h u p (fun z => strictRate v z*s) v v) 0 := by
  have hi (v : Three) := (heatPlane_integrable A hh u 0 (fun z => mul_pos (strictRate_pos v z) hs)).cost 2 v v
  rw [signedCenter_eq_integral A hh hs]
  have hb := norm_integral_le_of_norm_le
    ((integrable_finsetSum _ (fun v _ => hi v)).const_mul ((440/3)*s))
    (Filter.Eventually.of_forall (fun z => windowTrace_le A hh hs u (chart 2 0 z)))
  apply hb.trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun v _ => hi v)]
  rfl

lemma continuousOn_signedKernel (t : ℝ) : ContinuousOn (fun s => signedKernel s t) (Set.Ioi 0) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have hs' : 0 < s := hs
  unfold signedKernel density
  fun_prop (disch := positivity)

lemma signedKernel_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    IntervalIntegrable (fun s => signedKernel s t / s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact ((continuousOn_signedKernel t).div continuousOn_id (fun s hs => ne_of_gt hs)).mono
    (fun s hs => ha.trans_le hs.1)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.IntervalMask ----
namespace OAI

universe uE uι

section
namespace TriangularHilbert
open MeasureTheory
noncomputable section

lemma intervalIntegrable_indicator {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {L U a b : ℝ} (hf : IntervalIntegrable f volume L U) :
    IntervalIntegrable ((Set.Ico a b).indicator f) volume L U :=
  ⟨hf.1.indicator measurableSet_Ico,hf.2.indicator measurableSet_Ico⟩

lemma intervalIntegral_indicator_Ico {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {L U a b : ℝ} (hLa : L ≤ a) (hab : a ≤ b) (hbU : b ≤ U) :
    (∫ s in L..U, (Set.Ico a b).indicator f s) = ∫ s in a..b, f s := by
  rw [intervalIntegral.integral_of_le (hLa.trans (hab.trans hbU)),
    ← integral_Icc_eq_integral_Ioc,integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico]
  rw [Set.inter_eq_left.mpr (show Set.Ico a b ⊆ Set.Icc L U from fun s hs =>
    ⟨hLa.trans hs.1,hs.2.le.trans hbU⟩),integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

lemma intervalIntegrable_finsetSum {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ι → ℝ → E} (S : Finset ι) {a b : ℝ}
    (hf : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun s => ∑ i ∈ S, f i s) volume a b := by
  have hh := IntervalIntegrable.sum S hf
  convert! hh using 1
  ext s
  simp
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SelectedScale ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma maskedSigned_eq (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) (s : ℝ) :
    maskedSigned A h u a b s = ∑ i, ∑ j, ∑ k,
      (Set.Ico (a i j) (b i j)).indicator
        (fun s => (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*((signedKernel s (u i+u j+u k)/s:ℝ):ℂ)) s := by
  simp only [maskedSigned,signedCenter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change (h^3:ℝ)*(windowMask (a i j) (b i j) s (A 0 i j)*A 1 j k*A 2 k i)*
    (signedKernel s (u i+u j+u k):ℂ)/(s:ℂ) = _
  by_cases hs : s ∈ Set.Ico (a i j) (b i j)
  · rw [Set.indicator_of_mem hs]
    simp only [Set.mem_Ico] at hs
    simp only [windowMask,ite_eq_left hs]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hs]
    simp only [Set.mem_Ico] at hs
    simp only [windowMask,ite_eq_right hs]
    simp

omit [DecidableEq ι] in
lemma selectedSum_eq_integral (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (ha : ∀ i j, L ≤ a i j) (hab : ∀ i j, a i j ≤ b i j)
    (hb : ∀ i j, b i j ≤ U) : selectedSum A h u a b = ∫ s in L..U, maskedSigned A h u a b s := by
  have hc (i j k : ι) : IntervalIntegrable (fun s => ((signedKernel s (u i+u j+u k)/s:ℝ):ℂ)) volume L U :=
    ⟨(signedKernel_intervalIntegrable hL hLU (u i+u j+u k)).1.ofReal,
     (signedKernel_intervalIntegrable hL hLU (u i+u j+u k)).2.ofReal⟩
  have hi (i j k : ι) := intervalIntegrable_indicator
    ((hc i j k).const_mul ((h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i))) (a := a i j) (b := b i j)
  simp_rw [maskedSigned_eq]
  rw [intervalIntegral.integral_finsetSum (fun i _ => intervalIntegrable_finsetSum _ (fun j _ => intervalIntegrable_finsetSum _ (fun k _ => hi i j k)))]
  unfold selectedSum
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => intervalIntegrable_finsetSum _ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_finsetSum (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral_indicator_Ico (ha i j) (hab i j) (hb i j),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  rfl

lemma maskedSigned_norm_le (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (a b : Matrix ι ι ℝ) :
    ‖maskedSigned A h u a b s‖ ≤ (440/3)*∑ r, maskedCost A a b h u r s := by
  have hn (r w : Three) : 0 ≤ planeIntegral (fun p => heatCost (maskedArray A a b s) h u p
      (fun z => strictRate r z*s) w w) 0 := integral_nonneg (fun _ => heatCost_nonneg _ _ _ _ _ _ _)
  have hb : (∑ v, planeIntegral (fun p => heatCost (maskedArray A a b s) h u p
      (fun z => strictRate v z*s) v v) 0) ≤ ∑ r, maskedCost A a b h u r s := by
    apply Finset.sum_le_sum
    intro v _
    exact Finset.single_le_sum (fun w _ => hn v w) (Finset.mem_univ v)
  unfold maskedSigned
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hs.le]
  apply (div_le_div_of_nonneg_right (signedCenter_norm_le _ hh hs u) hs.le).trans
  rw [mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ hs.ne']
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma maskedCost_intervalIntegrable (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (hL : 0 < S.min' hS) (r : Three) :
    IntervalIntegrable (maskedCost A a b h u r) volume (S.min' hS) (S.max' hS) := by
  have ht0 : 0 < sortedTimes S hS 0 := by simpa only [sortedTimes_zero] using hL
  have hi := IntervalIntegrable.trans_iterate (n := S.card-1)
    (fun k _ => maskedCost_interval_piece A a b S hS ha hb hh u ht0 r k)
  simpa only [sortedTimes_zero,sortedTimes_last] using hi

lemma selectedSum_le_cubic (D : Finset ℤ) (A : Three → Matrix D D ℂ) (a b : Matrix D D ℝ)
    (hab : ∀ i j, a i j ≤ b i j) (S : Finset ℝ) (hS : S.Nonempty)
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (hl : ∀ s ∈ S, h^2 ≤ s) :
    ‖selectedSum A h (fun m => h*(m:ℤ)) a b‖ ≤ selectedConstant*arrayCubic A h := by
  have hL : 0 < S.min' hS := (sq_pos_of_pos hh).trans_le (hl _ (Finset.min'_mem S hS))
  have hLU : S.min' hS ≤ S.max' hS := Finset.min'_le S _ (Finset.max'_mem S hS)
  have hi r := maskedCost_intervalIntegrable A a b S hS ha hb hh (fun m => h*(m:ℤ)) hL r
  rw [selectedSum_eq_integral A _ _ a b hL hLU
    (fun i j => Finset.min'_le _ _ (ha i j)) hab (fun i j => Finset.le_max' _ _ (hb i j))]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hLU
    (Filter.Eventually.of_forall (fun s hs => maskedSigned_norm_le A hh (hL.trans hs.1) _ a b))
    ((intervalIntegrable_finsetSum _ (fun r _ => hi r)).const_mul (440/3:ℝ))
  apply hbound.trans
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (fun r _ => hi r)]
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset Three)) =>
    masked_cost_integral_le D A a b hab S hS ha hb hh hl r)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Three,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  have hc : (∑ r, ∫ s in S.min' hS..S.max' hS, maskedCost A a b h (fun m => h*(m:ℤ)) r s) ≤
      (3*(maskedConstant*arrayCubic A h))/strictConstant :=
    (le_div_iff₀ strictConstant_pos).mpr (by nlinarith only [hs])
  unfold selectedConstant
  calc
    _ ≤ (440/3)*((3*(maskedConstant*arrayCubic A h))/strictConstant) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.selectedSum_le_cubic := @_root_.OAI.TriangularHilbert.Heat.selectedSum_le_cubic
