-- Prove2me | solution 1 for OAI.BackwardIntertwiners.forward_backward_scalar_transitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:17:25.960448+00:00
-- url     : https://prove2.me/submissions/628db965-ff77-4d5a-8a6b-b656bfa1ad11

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ErgodicTransitivity.lean:L207-L243
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.forward_backward_scalar_transitive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity
import Theorems.Thm_OAI_BackwardIntertwiners_SupportSeparation_strict_order
import Theorems.Thm_OAI_BackwardIntertwiners_bilateralWeight_quadratic
import Theorems.Thm_OAI_BackwardIntertwiners_bilateralWeight_ratio
import Theorems.Thm_OAI_BackwardIntertwiners_quadratic_support_separation

-- ---- from OAI.Analysis.BackwardIntertwiners.FiberTails ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma weighted_shift_pow {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    {T : Fiber →L[ℂ] Fiber}
    (hT : ∀ v j, T v j = (w j / w (j-1) : ℂ) * v (j-1))
    (n : ℕ) (v : Fiber) (j : ℤ) :
    (T^n) v j = (w j / w (j-(n:ℤ)) : ℂ) * v (j-(n:ℤ)) := by
  have hwC (k : ℤ) : (w k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw k))
  induction n generalizing j with
  | zero => simp [hwC]
  | succ n ih =>
    rw [pow_succ']
    change T ((T^n) v) j = _
    rw [hT, ih]
    have hi : j-1-(n:ℤ) = j-((n+1:ℕ):ℤ) := by omega
    rw [hi]
    field_simp [hwC]

end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.HaarBase ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

lemma ae_goodBase : ∀ᵐ x ∂baseMeasure, x ∈ goodBase :=
  (Set.countable_range (fun n : ℤ => (show Base from (n : PadicInt 2)))).ae_notMem baseMeasure
end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.BackwardWeights ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

lemma explicitWeight_ratio (x : Base) (j : ℤ) :
    explicitWeight x (j+1) / explicitWeight x j = explicitBeta x j :=
  bilateralWeight_ratio _ _ _

lemma backwardCoeff_pos {x : Base} (hx : x ∈ goodBase) (j : ℤ) : 0 < backwardCoeff x j := by
  rw [backwardCoeff, ite_eq_left hx]
  exact div_pos (rawBackward_pos x j) (lt_of_lt_of_le (by norm_num) (backwardBound_ge_one hx))
lemma backwardCoeff_ae_pos : ∀ᵐ x ∂baseMeasure, ∀ j : ℤ, 0 < backwardCoeff x j :=
  ae_goodBase.mono fun _ hx => backwardCoeff_pos hx

end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.GlobalOperators ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

section Fields
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma fieldOperator_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldOperator A C hC hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldVector_ae A C hA hm f

lemma scalarMultiplier_ae (g : Lp ℂ ∞ μ) (f : Lp Fiber 2 μ) :
    scalarMultiplier g f =ᵐ[μ] fun x => g x • f x := Lp.coeFn_lpSMul g f
end Fields

lemma forwardOperator_ae (f : GlobalHilbert) :
    forwardOperator f =ᵐ[baseMeasure] fun x => forwardFiber x (f x) :=
  fieldOperator_ae _ _ _ _ _ f
lemma backwardOperator_ae_inverse (f : GlobalHilbert) :
    backwardOperator f =ᵐ[baseMeasure] fun x => backwardFiber (inverseOdometer x) (f (inverseOdometer x)) := by
  have h₁ := Lp.coeFn_compMeasurePreserving (backwardFieldOperator f) inverseOdometer_preserving
  have h₂ := (fieldOperator_ae backwardFiber 1 (by norm_num) backwardFiber_norm_le
    backwardFiber_aestronglyMeasurable f).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae
  exact h₁.trans h₂

lemma forwardOperator_power_ae (n : ℕ) (f : GlobalHilbert) :
    (forwardOperator^n) f =ᵐ[baseMeasure] fun x => (forwardFiber x ^ n) (f x) := by
  induction n with
  | zero => filter_upwards [] with x; rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [forwardOperator_ae ((forwardOperator^n) f), ih] with x h₁ h₂
    simp only [h₁,h₂,pow_succ',mul_apply_eq_comp]
end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.ErgodicTransitivity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

lemma ergodic_late_intersection {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {θ : X → X} (hθ : Ergodic θ μ)
    {A B : Set X} (_ : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : μ A ≠ 0) (hB0 : μ B ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ μ (A ∩ (θ^[n]) ⁻¹' B) ≠ 0 := by
  let U : Set X := ⋃ n : ℕ, (θ^[n+N]) ⁻¹' B
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion fun n =>
    hB.preimage (hθ.measurable.iterate (n+N))
  have hsub : θ ⁻¹' U ⊆ U := by
    intro x hx
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨n+1, ?_⟩
    change θ^[n+1+N] x ∈ B
    have hi : n+1+N = (n+N)+1 := by omega
    rw [hi,Function.iterate_succ_apply]
    exact hn
  have hU0 : μ U ≠ 0 := by
    intro h
    have hs : (θ^[N]) ⁻¹' B ⊆ U := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
    have he := (hθ.toMeasurePreserving.iterate N).measure_preimage hB.nullMeasurableSet
    exact hB0 (le_antisymm (by rw [← he]; exact (measure_mono hs).trans (by rw [h])) bot_le)
  have hUfull : U =ᵐ[μ] Set.univ := by
    obtain he | he := hθ.ae_empty_or_univ_of_preimage_ae_le hUmeas.nullMeasurableSet
      (Filter.Eventually.of_forall hsub)
    · exact False.elim (hU0 (by rw [measure_congr he,measure_empty]))
    · exact he
  by_contra! hn
  have hzero : μ (A ∩ U) = 0 := by
    rw [show A ∩ U = ⋃ n : ℕ, A ∩ (θ^[n+N]) ⁻¹' B from Set.inter_iUnion _ _]
    exact measure_iUnion_null fun n => hn (n+N) (by omega)
  have he : (A ∩ U : Set X) =ᵐ[μ] A := by
    filter_upwards [hUfull] with x hx
    apply propext
    change (x ∈ A ∧ x ∈ U) ↔ x ∈ A
    have hxU : x ∈ U := (eq_iff_iff.mp hx).mpr (Set.mem_univ x)
    simp [hxU]
  exact hA0 ((measure_congr he).symm.trans hzero)

section Localization
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [finiteMeasure : IsFiniteMeasure μ]

omit finiteMeasure in
lemma measurable_global_coordinate [IsFiniteMeasure μ] (f : Lp Fiber 2 μ) (j : ℤ) : Measurable (fun x => f x j) :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable f)).measurable

omit finiteMeasure in
lemma exists_coordinate_support_nonnull [IsFiniteMeasure μ] {f : Lp Fiber 2 μ} (hf : f ≠ 0) :
    ∃ j : ℤ, μ {x | f x j ≠ 0} ≠ 0 := by
  by_contra! h
  apply hf
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have ha : ∀ j : ℤ, ∀ᵐ x ∂μ, f x j = 0 := fun j => by
    exact ae_iff.mpr (h j)
  filter_upwards [ae_all_iff.mpr ha] with x hx
  ext j
  exact hx j

lemma scalar_invariant_pointwise_orthogonal {L : Submodule ℂ (Lp Fiber 2 μ)}
    (hL : ∀ g : Lp ℂ ∞ μ, ∀ f ∈ L, scalarMultiplier g f ∈ L)
    {f z : Lp Fiber 2 μ} (hf : f ∈ L) (hz : z ∈ L.orthogonal) :
    ∀ᵐ x ∂μ, inner ℂ (z x) (f x) = 0 := by
  apply (L2.integrable_inner z f).ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s hs _
  let g : Lp ℂ ∞ μ := indicatorConstLp ∞ hs (measure_ne_top μ s) (1:ℂ)
  have hg : g =ᵐ[μ] s.indicator (fun _ => (1:ℂ)) := indicatorConstLp_coeFn
  rw [← integral_indicator hs]
  calc
    _ = ∫ x, inner ℂ (z x) (scalarMultiplier g f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [scalarMultiplier_ae g f, hg] with x hx hgx
      rw [hx,hgx]
      by_cases hxs : x ∈ s
      · simp [Set.indicator_of_mem hxs]
      · simp [Set.indicator_of_notMem hxs]
    _ = inner ℂ z (scalarMultiplier g f) := (L2.inner_def _ _).symm
    _ = 0 := Submodule.inner_left_of_mem_orthogonal (hL g f hf) hz
end Localization

lemma fiber_cyclic_orthogonal_order {w : ℤ → ℝ} (hw : QuadraticWeights w)
    {T : Fiber →L[ℂ] Fiber}
    (hT : ∀ v j, T v j = (w j / w (j-1) : ℂ) * v (j-1))
    {v z : Fiber} (horth : ∀ r : ℕ, inner ℂ z ((T^r) v) = 0)
    {i j : ℤ} (hzi : z i ≠ 0) (hvj : v j ≠ 0) : i < j := by
  let b := fun k : ℤ => star (z k) * (w k:ℂ)
  let c := fun k : ℤ => v k / (w k:ℂ)
  have hwC (k : ℤ) : (w k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw.positive k))
  have hbi : b i ≠ 0 := mul_ne_zero (by simpa using hzi) (hwC i)
  have hcj : c j ≠ 0 := div_ne_zero hvj (hwC j)
  have hb (k : ℤ) : ‖b k‖ ≤ (‖z‖+1)*w k := by
    dsimp [b]
    rw [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hw.positive k).le]
    apply mul_le_mul_of_nonneg_right _ (hw.positive k).le
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) z k).trans (by linarith)
  have hc (k : ℤ) : ‖c k‖*w k ≤ ‖v‖+1 := by
    dsimp [c]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw.positive k).le,
      div_mul_cancel₀ _ (ne_of_gt (hw.positive k))]
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) v k).trans (by linarith)
  have hcor (r : ℕ) : (∑' k : ℤ, b k*c (k-r)) = 0 := by
    calc (∑' k : ℤ, b k*c (k-r)) = inner ℂ z ((T^r) v) := by
          rw [lp.inner_eq_tsum]
          apply tsum_congr
          intro k
          rw [RCLike.inner_apply, weighted_shift_pow hw.positive hT]
          dsimp [b, c]
          simp only [← Complex.star_def]
          ring
      _ = 0 := horth r
  exact (quadratic_support_separation w hw).strict_order ⟨i,hbi⟩ ⟨j,hcj⟩
    (by positivity : 0 < ‖z‖+1) (by positivity : 0 < ‖v‖+1) hb hc hcor hbi hcj

lemma explicitWeight_quadratic (x : Base) : QuadraticWeights (explicitWeight x) :=
  bilateralWeight_quadratic (plusResidue_bounds x) (minusResidue_bounds x)

lemma forwardFiber_weight_coordinates (x : Base) (v : Fiber) (j : ℤ) :
    forwardFiber x v j = (explicitWeight x j / explicitWeight x (j-1) : ℂ) * v (j-1) := by
  rw [forwardFiber_apply, ← explicitWeight_ratio x (j-1)]
  simp only [sub_add_cancel, Complex.ofReal_div]

lemma inverseOdometer_ergodic : Ergodic inverseOdometer baseMeasure :=
  Ergodic.symm (e := odometerMeasurableEquiv) odometer_ergodic

lemma backwardOperator_power_nonzero (n : ℕ) (f : GlobalHilbert) (j : ℤ) :
    ∀ᵐ x ∂baseMeasure, f (inverseOdometer^[n] x) j ≠ 0 →
      ((backwardOperator^n) f) x (j-n) ≠ 0 := by
  induction n with
  | zero => filter_upwards [] with x; simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [backwardOperator_ae_inverse ((backwardOperator^n) f),
      inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae.eventually ih,
      inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae.eventually backwardCoeff_ae_pos]
      with x hx hi hp
    intro hn
    rw [hx, backwardFiber_apply]
    have he : j - (n+1:ℕ) + 1 = j - n := by omega
    rw [he]
    apply mul_ne_zero
    · exact_mod_cast (ne_of_gt (hp (j-n)))
    · apply hi
      simpa only [Function.iterate_succ_apply] using hn

lemma global_invariant_pow {T : GlobalHilbert →L[ℂ] GlobalHilbert}
    {L : Submodule ℂ GlobalHilbert} (hi : OperatorInvariant L T)
    {v : GlobalHilbert} (hv : v ∈ L) (n : ℕ) : (T^n) v ∈ L := by
  induction n with
  | zero => simpa using hv
  | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hi _ ih

lemma invariant_pointwise_order {L : Submodule ℂ GlobalHilbert}
    (hS : OperatorInvariant L forwardOperator)
    (hM : ∀ g : Lp ℂ ∞ baseMeasure, OperatorInvariant L (scalarMultiplier g))
    {f z : GlobalHilbert} (hf : f ∈ L) (hz : z ∈ L.orthogonal) :
    ∀ᵐ x ∂baseMeasure, ∀ i j : ℤ, z x i ≠ 0 → f x j ≠ 0 → i < j := by
  have horth (r : ℕ) : ∀ᵐ x ∂baseMeasure, inner ℂ (z x) (((forwardOperator^r) f) x) = 0 :=
    scalar_invariant_pointwise_orthogonal hM (global_invariant_pow hS hf r) hz
  filter_upwards [ae_all_iff.mpr horth,
    ae_all_iff.mpr (fun r => forwardOperator_power_ae r f)] with x hx hxpow
  intro i j hzi hfj
  apply fiber_cyclic_orthogonal_order (explicitWeight_quadratic x) (forwardFiber_weight_coordinates x) ?_ hzi hfj
  intro r
  rw [← hxpow r]
  exact hx r

lemma forward_backward_scalar_transitive (L : Submodule ℂ GlobalHilbert)
    (hclosed : IsClosed (L : Set GlobalHilbert))
    (hS : OperatorInvariant L forwardOperator)
    (hV : OperatorInvariant L backwardOperator)
    (hM : ∀ g : Lp ℂ ∞ baseMeasure, OperatorInvariant L (scalarMultiplier g)) :
    L = ⊥ ∨ L = ⊤ := by
  by_contra! hproper
  have hOO : L.orthogonal.orthogonal = L := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, hclosed.submodule_topologicalClosure_eq]
  have hnotOrth : L.orthogonal ≠ ⊥ := by
    intro hh
    rw [hh, Submodule.bot_orthogonal_eq_top] at hOO
    exact hproper.2 hOO.symm
  obtain ⟨f,hf,hf0⟩ := (Submodule.ne_bot_iff L).mp hproper.1
  obtain ⟨z,hz,hz0⟩ := (Submodule.ne_bot_iff L.orthogonal).mp hnotOrth
  obtain ⟨j,hA0⟩ := exists_coordinate_support_nonnull hf0
  obtain ⟨i,hB0⟩ := exists_coordinate_support_nonnull hz0
  let A : Set Base := {x | f x j ≠ 0}
  let B : Set Base := {x | z x i ≠ 0}
  have hA : MeasurableSet A := (measurableSet_eq_fun (measurable_global_coordinate f j) measurable_const).compl
  have hB : MeasurableSet B := (measurableSet_eq_fun (measurable_global_coordinate z i) measurable_const).compl
  obtain ⟨n,hn,hinter⟩ := ergodic_late_intersection inverseOdometer_ergodic hB hA hB0 hA0 (j-i).toNat
  have horder := invariant_pointwise_order hS hM (global_invariant_pow hV hf n) hz
  have hnull : ∀ᵐ x ∂baseMeasure, x ∉ B ∩ (inverseOdometer^[n]) ⁻¹' A := by
    filter_upwards [horder, backwardOperator_power_nonzero n f j] with x hx hp
    intro hmem
    have hzi : z x i ≠ 0 := hmem.1
    have hfj : f (inverseOdometer^[n] x) j ≠ 0 := hmem.2
    have hh := hx i (j-n) hzi (hp hfj)
    have hnat : (j-i) ≤ ((j-i).toNat : ℤ) := by omega
    have hnn : ((j-i).toNat : ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    omega
  apply hinter
  convert ae_iff.mp hnull using 1
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, not_not]

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
open Topology MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.forward_backward_scalar_transitive := @_root_.OAI.BackwardIntertwiners.forward_backward_scalar_transitive
