-- Prove2me | solution 1 for OAI.PlaneFiveColor.Spectral.radial_positive_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:17:16.372743+00:00
-- url     : https://prove2.me/submissions/ac75f276-0129-4e78-b65f-9f72cadabdae

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_PlaneFiveColor_Spectral_massReal_difference

section
-- module Solutions.OAIQ5_T4.Compat
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Amenability
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

open scoped RealInnerProductSpace BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable
variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

variable {G}
namespace Mean
variable (M : Mean G)

lemma exists_lt {f : G →ᵇ ℝ} {ε : ℝ} (h : M.map f < ε) : ∃ g, f g < ε := by
  by_contra hn
  push Not at hn
  have := M.mono (BoundedContinuousFunction.const G ε) f hn
  rw [M.map_const] at this
  exact (not_lt_of_ge this) h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma vector_shift (V : G →ᵇ H) (g : G) : M.vector (shift G g V) = M.vector V := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, M.vector_pair]
  exact M.invariant g (pairing V v)

lemma vector_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]
    (L : H →L[ℝ] J) (V : G →ᵇ H) :
    M.vector (L.compLeftContinuousBounded G V) = L (M.vector V) := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, ← L.adjoint_inner_right, M.vector_pair]
  congr 1; ext x
  exact (L.adjoint_inner_right (V x) v).symm

lemma jensen (V : G →ᵇ H) : ‖M.vector V‖^2 ≤ M.map (squareNorm V) := by
  let c := M.vector V
  have he : squareNorm (V - BoundedContinuousFunction.const G c) =
      squareNorm V - (2 : ℝ) • pairing V c + BoundedContinuousFunction.const G (‖c‖^2) := by
    ext x
    simp only [squareNorm_apply, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply, pairing_apply, smul_eq_mul]
    rw [norm_sub_sq_real]
  have hp := M.positive (squareNorm (V - BoundedContinuousFunction.const G c)) (fun x => by
    rw [squareNorm_apply]; positivity)
  rw [he, map_add, map_sub, map_smul, M.map_const, ← M.vector_pair] at hp
  change 0 ≤ M.map (squareNorm V) - 2 * inner ℝ c c + ‖c‖^2 at hp
  rw [real_inner_self_eq_norm_sq] at hp
  dsimp [c] at hp
  linarith
end Mean
end EuclideanFiveColor.Amenable

namespace EuclideanFiveColor.Amenable.Mean

section
open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
lemma cross_comm (V W : G →ᵇ H) : cross V W = cross W V := by
  ext x; exact real_inner_comm _ _

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
lemma squareNorm_add (V W : G →ᵇ H) :
    squareNorm (V+W) = squareNorm V + squareNorm W + (2 : ℝ) • cross V W := by
  ext x
  simp only [squareNorm_apply, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, cross_apply, smul_eq_mul]
  rw [norm_add_sq_real]; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma squareNorm_shift (V : G →ᵇ H) (g : G) :
    M.map (squareNorm (shift G g V)) = M.map (squareNorm V) :=
  M.invariant g (squareNorm V)

omit [CompleteSpace H] in
lemma correlation_add (V W Z : G →ᵇ H) :
    M.correlation V (W+Z) = M.correlation V W + M.correlation V Z := by
  ext g
  simp only [correlation_apply, BoundedContinuousFunction.add_apply]
  rw [← map_add]
  congr 1; ext x
  simp only [cross_apply, BoundedContinuousFunction.add_apply, inner_add_right]

omit [CompleteSpace H] in
lemma correlation_zero (V : G →ᵇ H) : M.correlation V 0 = 0 := by
  ext g
  change M.map (cross (shift G g V) (0 : G →ᵇ H)) = 0
  have he : cross (shift G g V) (0 : G →ᵇ H) = 0 := by ext; simp
  rw [he, map_zero]

omit [CompleteSpace H] in
lemma correlation_shift (V W : G →ᵇ H) (g : G) :
    M.correlation V (shift G g W) = shift G (-g) (M.correlation V W) := by
  ext h
  change M.map (cross (shift G h V) (shift G g W)) =
    M.map (cross (shift G (h+-g) V) W)
  rw [← M.invariant (-g) (cross (shift G h V) (shift G g W))]
  congr 1; ext x
  simp only [shift_apply, cross_apply]
  congr 2 <;> abel

/-- Invariant-mean van der Corput: positivity and finite translates suffice.
There is no exchange of iterated means. -/
theorem vector_eq_zero_of_correlation_nonpos (V : G →ᵇ H)
    (hc : M.map (M.correlation V V) ≤ 0) : M.vector V = 0 := by
  classical
  let C : ℝ := M.map (squareNorm V) + 2
  have hC : 0 < C := by
    have := M.positive (squareNorm V) (fun x => by rw [squareNorm_apply]; positivity)
    dsimp [C]; linarith
  have hW (n : ℕ) : ∃ W : G →ᵇ H, M.vector W = (n : ℝ) • M.vector V ∧
      M.map (M.correlation V W) ≤ 0 ∧ M.map (squareNorm W) ≤ (n : ℝ)*C := by
    induction n with
    | zero =>
      refine ⟨0, ?_, ?_, ?_⟩
      · have he : M.vector (0 : G →ᵇ H) = 0 := by
          apply ext_inner_right ℝ; intro v
          rw [M.vector_pair, inner_zero_left]
          have he : pairing (0 : G →ᵇ H) v = 0 := by ext; simp
          rw [he, map_zero]
        simpa using he
      · simp [M.correlation_zero]
      · have he : squareNorm (0 : G →ᵇ H) = 0 := by ext; simp
        simp [he]
    | succ n ih =>
      obtain ⟨W, hv, hwc, hwe⟩ := ih
      obtain ⟨g, hg⟩ := M.exists_lt (lt_of_le_of_lt hwc zero_lt_one)
      refine ⟨W+shift G g V, ?_, ?_, ?_⟩
      · rw [M.vector_add, M.vector_shift, hv]
        simp [Nat.cast_add, add_smul]
      · rw [M.correlation_add, map_add, M.correlation_shift, M.invariant]
        linarith
      · rw [squareNorm_add, map_add, map_add, map_smul, M.squareNorm_shift,
          cross_comm W _, ← M.correlation_apply V W g]
        have hn : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by simp
        rw [hn]
        dsimp [C] at *
        change M.map (squareNorm W) + M.map (squareNorm V) + 2 * M.correlation V W g ≤
          ((n : ℝ)+1) * (M.map (squareNorm V) + 2)
        change M.correlation V W g < 1 at hg
        nlinarith
  have hn (n : ℕ) (hp : 0 < n) : (n : ℝ) * ‖M.vector V‖^2 ≤ C := by
    obtain ⟨W, hw, _, he⟩ := hW n
    have hj := (M.jensen W).trans he
    rw [hw, norm_smul, Real.norm_natCast] at hj
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hp
    apply (mul_le_mul_iff_right₀ hnr).mp
    nlinarith
  by_contra hv
  have hnorm : 0 < ‖M.vector V‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  obtain ⟨n, hn'⟩ := exists_nat_gt (max 0 (C / ‖M.vector V‖^2))
  have hn0 : 0 < n := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn')
  have hratio := lt_of_le_of_lt (le_max_right _ _) hn'
  have hbad := (div_lt_iff₀ hnorm).mp hratio
  have hgood := hn n hn0
  linarith

end

open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma vector_orbit_invariant (U : G → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ g h v, U (g+h) v = U g (U h v)) (v : H) (g : G) :
    U g (M.vector (orbit U v)) = M.vector (orbit U v) := by
  change (U g).toLinearIsometry.toContinuousLinearMap (M.vector (orbit U v)) = _
  rw [← M.vector_map (U g).toLinearIsometry.toContinuousLinearMap]
  have he : (U g).toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded G (orbit U v) =
      shift G g (orbit U v) := by
    ext h
    change U g (U h v) = U (h+g) v
    rw [add_comm h g, hU]
  rw [he, M.vector_shift]

lemma vector_orbit_pair_fixed (U : G → H ≃ₗᵢ[ℝ] H) (v w : H)
    (hw : ∀ g, U g w = w) : inner ℝ (M.vector (orbit U v)) w = inner ℝ v w := by
  rw [M.vector_pair]
  have he : pairing (orbit U v) w = BoundedContinuousFunction.const G (inner ℝ v w) := by
    ext g
    change inner ℝ (U g v) w = inner ℝ v w
    calc
      inner ℝ (U g v) w = inner ℝ (U g v) (U g w) := by rw [hw g]
      _ = inner ℝ v w := (U g).inner_map_map v w
  rw [he, M.map_const]

/-- The mean ergodic projection criterion, valid for every positive invariant
mean and without an assumption that the group has a distinguished generator. -/
theorem vector_orbit_eq_zero (U : G → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ g h v, U (g+h) v = U g (U h v)) (v : H)
    (hv : ∀ w, (∀ g, U g w = w) → inner ℝ v w = 0) :
    M.vector (orbit U v) = 0 := by
  have hf := M.vector_orbit_invariant U hU v
  have hi := M.vector_orbit_pair_fixed U v (M.vector (orbit U v)) hf
  rw [hv _ hf] at hi
  exact inner_self_eq_zero.mp hi

end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.Amenable.Koopman
open MeasureTheory Filter
section Action
variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [VAddInvariantMeasure G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma action_add (g h : G) (f : Lp E 2 μ) :
    action μ (g+h) f = action μ g (action μ h f) := linear_add μ g h f

lemma coe_action (g : G) (f : Lp E 2 μ) :
    action μ g f =ᵐ[μ] (fun x => f (g +ᵥ x)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_vadd g μ)

end Action

variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace.CountablySeparated E]

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma ae_eq_const_of_fixed (f : Lp E 2 μ)
    (hf : ∀ g : G, action μ g f = f) : ∃ c : E, f =ᵐ[μ] fun _ => c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro A hA
  have := ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := G)
    ((Lp.stronglyMeasurable f).measurable hA) (fun g => by
      have ha := coe_action μ g f
      rw [hf g] at ha
      exact ha.symm.mono (fun x hx =>
        propext (show f (g +ᵥ x) ∈ A ↔ f x ∈ A by change f (g +ᵥ x) = f x at hx; rw [hx])))
  exact eventuallyConst_set.mp this

lemma inner_fixed_zero (v : Lp E 2 μ)
    (hv : ∫ x, v x ∂μ = 0) (w : Lp E 2 μ) (hw : ∀ g : G, action μ g w = w) :
    inner ℝ v w = 0 := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_fixed (G := G) μ w hw
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ (v x) (w x) ∂μ) = ∫ x, inner ℝ c (v x) ∂μ :=
      integral_congr_ae (hc.mono (fun x hx => by dsimp only at hx ⊢; rw [hx, real_inner_comm]))
    _ = inner ℝ c (∫ x, v x ∂μ) := integral_inner ((Lp.memLp v).integrable (by norm_num)) c
    _ = 0 := by rw [hv, inner_zero_right]

end EuclideanFiveColor.Amenable.Koopman

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeCenters
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

open MeasureTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.KernelSupport

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_map_base (ν : Measure Y) [SFinite ν] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (R : Y ≃ᵐ Y) :
    (ν.map R) ⊗ₘ (κ.comap R.symm R.symm.measurable) =
      (ν ⊗ₘ κ).map (Prod.map R id) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply (R.measurable.prodMap measurable_id) hs,
    Measure.compProd_apply ((R.measurable.prodMap measurable_id) hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) R.measurable]
  apply lintegral_congr
  intro y
  simp only [Kernel.comap_apply, R.symm_apply_apply]
  rfl

lemma condDistrib_comp_equiv [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (R : Y ≃ᵐ Y) :
    condDistrib f (R ∘ p) μ =ᵐ[μ.map (R ∘ p)]
      (condDistrib f p μ).comap R.symm R.symm.measurable := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (R.measurable.comp hp) hf
  rw [← Measure.map_map R.measurable hp, compProd_map_base,
    compProd_map_condDistrib hf.aemeasurable,
    Measure.map_map (R.measurable.prodMap measurable_id) (hp.prodMk hf)]
  rfl

/-- Changing both coordinates of a conditional law by invertible measurable
maps commutes with conditional sampling. -/
lemma condDistrib_equivariant [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (S : X ≃ᵐ X) (R : Y ≃ᵐ Y) (T : Z → Z) (hT : Measurable T)
    (hS : MeasurePreserving S μ μ)
    (hRp : p ∘ S =ᵐ[μ] R ∘ p) (hTf : f ∘ S =ᵐ[μ] T ∘ f) :
    ∀ᵐ y ∂μ.map p, condDistrib f p μ (R y) = (condDistrib f p μ y).map T := by
  have hR : (μ.map p).map R = μ.map p := by
    rw [Measure.map_map R.measurable hp, ← Measure.map_congr hRp,
      ← Measure.map_map hp S.measurable, hS.map_eq]
  have hRS : μ.map (p ∘ S) = μ.map p := by
    rw [← Measure.map_map hp S.measurable, hS.map_eq]
  have hm := condDistrib_map (X := p) (Y := f) (ν := μ) (f := S)
    (hp.aemeasurable) (hf.aemeasurable) S.measurable.aemeasurable
  simp only [hS.map_eq, hRS] at hm
  rw [condDistrib_congr hTf hRp] at hm
  have hc := condDistrib_comp_equiv μ (T ∘ f) p (hT.comp hf) hp R
  have hh : μ.map (R ∘ p) = μ.map p := by
    rw [← Measure.map_map R.measurable hp, hR]
  rw [hh] at hc
  have he := condDistrib_comp (μ := μ) (mβ := inferInstance) p hf.aemeasurable hT
  have hcomp : ∀ᵐ y ∂μ.map p,
      condDistrib f p μ y = (condDistrib f p μ (R.symm y)).map T := by
    have he' : ∀ᵐ y ∂μ.map p,
        condDistrib (T ∘ f) p μ (R.symm y) =
          (condDistrib f p μ (R.symm y)).map T := by
      have hRinv : MeasurePreserving R.symm (μ.map p) (μ.map p) := by
        refine ⟨R.symm.measurable, ?_⟩
        calc
          (μ.map p).map R.symm = ((μ.map p).map R).map R.symm := by rw [hR]
          _ = μ.map p := R.map_symm_map
      exact hRinv.quasiMeasurePreserving.ae <| he.mono fun y hy => by
        simpa only [Kernel.map_apply _ hT] using hy
    filter_upwards [hm, hc, he'] with y h₁ h₂ h₃
    simpa only [Kernel.comap_apply] using h₁.trans (h₂.trans h₃)
  have hRpres : MeasurePreserving R (μ.map p) (μ.map p) := ⟨R.measurable, hR⟩
  have hfinal := hRpres.quasiMeasurePreserving.ae hcomp
  filter_upwards [hfinal] with y hy
  simpa only [R.symm_apply_apply] using hy

end EuclideanFiveColor.KernelSupport

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalSelection
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators

open MeasureTheory

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.ConditionalFiber
variable {X W G V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma comp_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) :
    (condDistrib id p μ) ∘ₘ μ.map p = μ := by
  simpa using condDistrib_comp_map hp.aemeasurable (measurable_id.aemeasurable (μ := μ))

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_fiber_of_ae (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, P x := by
  exact Measure.ae_ae_of_ae_comp (by rwa [comp_identity_fiber μ p hp])

lemma map_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : AEMeasurable p μ) (b : X → G) (hb : Measurable b) :
    ∀ᵐ w ∂μ.map p, (condDistrib id p μ w).map b = condDistrib b p μ w := by
  filter_upwards [condDistrib_comp p
    (measurable_id.aemeasurable (μ := μ)) hb] with w hw
  simpa [Kernel.map_apply _ hb] using hw.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_in_own_fiber [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsFiniteMeasure μ] (p : X → W) (hp : Measurable p) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, p x = w := by
  filter_upwards [map_identity_fiber μ p hp.aemeasurable p hp,
    condDistrib_self p] with w hw hs
  have he : (condDistrib id p μ w).map p = Measure.dirac w := by
    rw [hw, hs]; rfl
  apply ae_of_ae_map (p := fun z : W => z = w) hp.aemeasurable
  rw [he]
  simp

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integral_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∫ w, (∫ x, f x ∂condDistrib id p μ w) ∂μ.map p = ∫ x, f x ∂μ := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply,
    comp_identity_fiber μ p hp] using he.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integrable_fiber_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    Integrable (fun w => ∫ x, f x ∂condDistrib id p μ w) (μ.map p) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  exact hi.integral_comp

end EuclideanFiveColor.ConditionalFiber

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_ConditionalSpectrum
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

lemma eval_add (a b : E) (d : D) : eval (a+b) d = eval a d * eval b d :=
  map_mul d (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

end

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalLimits
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/
namespace EuclideanFiveColor.LimitDensity
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Y : Type*} [mY : MeasurableSpace Y]

lemma clip_bound {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : |clip C t| ≤ C := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
lemma clip_eq {C t : ℝ} (ht : |t| ≤ C) : clip C t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  simp only [clip, min_eq_right hu, max_eq_right hl]
lemma continuous_clip (C : ℝ) : Continuous (clip C) := by
  unfold clip
  fun_prop

/-- A bounded vector measurable for a generated join is an L² limit of
uniformly bounded functions measurable at finite stages. -/
theorem bounded_vector_approximation
    (ν : Measure Y) [IsProbabilityMeasure ν] (ℱ : Filtration ℕ mY)
    (m : ℕ) (H : Y → Fin m → ℂ) (hH : Measurable[⨆ n, ℱ n] H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖H y‖ ≤ C) :
    ∃ Hn : ℕ → Y → Fin m → ℂ,
      (∀ n, Measurable[ℱ n] (Hn n)) ∧
      (∀ n y, ‖Hn n y‖ ≤ 2*C) ∧
      (∀ n, Integrable (fun y => dist (H y) (Hn n y)^2) ν) ∧
      Tendsto (fun n => ∫ y, dist (H y) (Hn n y)^2 ∂ν) atTop (𝓝 0) := by
  classical
  have hle : (⨆ n, ℱ n) ≤ mY := iSup_le fun n => ℱ.le n
  have hHm : Measurable H := hH.mono hle le_rfl
  let R : Fin m → Y → ℝ := fun j y => (H y j).re
  let I : Fin m → Y → ℝ := fun j y => (H y j).im
  have hR (j : Fin m) : Measurable[⨆ n, ℱ n] (R j) := by
    let : MeasurableSpace Y := ⨆ n, ℱ n
    exact Complex.measurable_re.comp ((measurable_pi_iff.mp hH) j)
  have hI (j : Fin m) : Measurable[⨆ n, ℱ n] (I j) := by
    let : MeasurableSpace Y := ⨆ n, ℱ n
    exact Complex.measurable_im.comp ((measurable_pi_iff.mp hH) j)
  have hRB (j : Fin m) (y : Y) : |R j y| ≤ C :=
    (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (H y) j).trans (hbound y))
  have hIB (j : Fin m) (y : Y) : |I j y| ≤ C :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (H y) j).trans (hbound y))
  have hRi (j : Fin m) : Integrable (R j) ν :=
    Integrable.of_bound ((hR j).mono hle le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hRB j y)
  have hIi (j : Fin m) : Integrable (I j) ν :=
    Integrable.of_bound ((hI j).mono hle le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hIB j y)
  let Hn : ℕ → Y → Fin m → ℂ := fun n y j =>
    (clip C ((ν[R j | ℱ n]) y) : ℂ) + Complex.I * (clip C ((ν[I j | ℱ n]) y) : ℂ)
  have hHn (n : ℕ) : Measurable[ℱ n] (Hn n) := by
    let : MeasurableSpace Y := ℱ n
    apply Measurable.of_eval
    intro j
    exact ((Complex.measurable_ofReal.comp ((continuous_clip C).measurable.comp
      stronglyMeasurable_condExp.measurable))).add
      (measurable_const.mul (Complex.measurable_ofReal.comp ((continuous_clip C).measurable.comp
        stronglyMeasurable_condExp.measurable)))
  have hBn (n : ℕ) (y : Y) : ‖Hn n y‖ ≤ 2*C := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    calc
      ‖Hn n y j‖ ≤ ‖(clip C ((ν[R j | ℱ n]) y) : ℂ)‖ +
          ‖Complex.I * (clip C ((ν[I j | ℱ n]) y) : ℂ)‖ := norm_add_le _ _
      _ = |clip C ((ν[R j | ℱ n]) y)| + |clip C ((ν[I j | ℱ n]) y)| := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2*C := by linarith [clip_bound hC ((ν[R j | ℱ n]) y), clip_bound hC ((ν[I j | ℱ n]) y)]
  have hconv : ∀ᵐ y ∂ν, Tendsto (fun n => Hn n y) atTop (𝓝 (H y)) := by
    have hr (j : Fin m) := (hRi j).tendsto_ae_condExp (hR j).stronglyMeasurable
    have hi (j : Fin m) := (hIi j).tendsto_ae_condExp (hI j).stronglyMeasurable
    filter_upwards [ae_all_iff.mpr hr, ae_all_iff.mpr hi] with y hyr hyi
    apply tendsto_pi_nhds.mpr
    intro j
    have hr' := (continuous_clip C).continuousAt.tendsto.comp (hyr j)
    have hi' := (continuous_clip C).continuousAt.tendsto.comp (hyi j)
    rw [clip_eq (hRB j y)] at hr'
    rw [clip_eq (hIB j y)] at hi'
    have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr').add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi').const_mul Complex.I)
    convert ht using 1
    · rfl
    · simp only [R, I, Complex.re_add_im, mul_comm Complex.I]
  have hdist (n : ℕ) (y : Y) : dist (H y) (Hn n y)^2 ≤ (3*C)^2 := by
    have hd : dist (H y) (Hn n y) ≤ 3*C :=
      (dist_le_norm_add_norm _ _).trans (by linarith [hbound y, hBn n y])
    exact pow_le_pow_left₀ dist_nonneg hd 2
  have hint (n : ℕ) : Integrable (fun y => dist (H y) (Hn n y)^2) ν :=
    Integrable.of_bound ((hHm.dist ((hHn n).mono (ℱ.le n) le_rfl)).pow_const 2).aestronglyMeasurable
      ((3*C)^2) (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs, abs_sq] using hdist n y)
  refine ⟨Hn, hHn, hBn, hint, ?_⟩
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (f := fun _ : Y => (0 : ℝ)) (fun _ : Y => (3*C)^2)
    (fun n => (hint n).aestronglyMeasurable) (integrable_const _) (fun n =>
      Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n y)
    (hconv.mono fun y hy => by
      have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H y) atTop (𝓝 (H y))).dist hy).pow 2
      simpa only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht)

/-- At a generated limit factor, one earlier factor carries a bounded
finite-vector approximant, with a pointwise bounded measurable representative. -/
theorem generated_factor_approximation
    {Z : ℕ → Type*} [∀ n, MeasurableSpace (Z n)]
    (ν : Measure Y) [IsProbabilityMeasure ν] (p : ∀ n, Y → Z n)
    (hp : ∀ n, Measurable (p n))
    (hmono : Monotone (fun n => (inferInstance : MeasurableSpace (Z n)).comap (p n)))
    (hgen : (⨆ n, (inferInstance : MeasurableSpace (Z n)).comap (p n)) = mY)
    (m : ℕ) (H : Y → Fin m → ℂ) (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖H y‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ H₀ : Z n → Fin m → ℂ, Measurable H₀ ∧ (∀ z, ‖H₀ z‖ ≤ 2*C) ∧
      Integrable (fun y => dist (H y) (H₀ (p n y))^2) ν ∧
      (∫ y, dist (H y) (H₀ (p n y))^2 ∂ν) < ε^2 := by
  classical
  let ℱ : Filtration ℕ mY := ⟨fun n => (inferInstance : MeasurableSpace (Z n)).comap (p n),
    hmono, fun n => (hp n).comap_le⟩
  have hHg : Measurable[⨆ n, ℱ n] H := by
    change Measurable[⨆ n, (inferInstance : MeasurableSpace (Z n)).comap (p n)] H
    rwa [hgen]
  obtain ⟨Hn, hHn, hBn, hint, hlim⟩ := bounded_vector_approximation ν ℱ m H hHg C hC hbound
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))).exists
  obtain ⟨H', hH', heq⟩ := (hHn n).exists_eq_measurable_comp
  let H₀ : Z n → Fin m → ℂ := fun z => if ‖H' z‖ ≤ 2*C then H' z else 0
  have hH₀ : Measurable H₀ := hH'.piecewise (measurableSet_le hH'.norm measurable_const) measurable_const
  have hB₀ (z : Z n) : ‖H₀ z‖ ≤ 2*C := by
    by_cases hz : ‖H' z‖ ≤ 2*C
    · simpa only [H₀, ite_eq_left hz] using hz
    · simp only [H₀, ite_eq_right hz, norm_zero]; positivity
  have heq₀ (y : Y) : H₀ (p n y) = Hn n y := by
    have hy := congrFun heq y
    simp only [Function.comp_apply] at hy
    have hb : ‖H' (p n y)‖ ≤ 2*C := hy ▸ hBn n y
    simpa only [H₀, ite_eq_left hb] using hy.symm
  refine ⟨n, H₀, hH₀, hB₀, ?_, ?_⟩
  · simpa only [heq₀] using hint n
  · simpa only [heq₀] using hn

end EuclideanFiveColor.LimitDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Kernels
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.RelativeProduct.law_probability_add _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded integral kernels yield finite-module orbit approximation.
This implements the compact-tower construction without spectral projections:
approximate the invariant kernel by finite rectangles first. -/
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma norm_integral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  let a := ∫ x, ‖f x‖ ∂μ
  have ha : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hvar : 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - a^2 := by
    have h : (0 : ℝ) ≤ ∫ x, (‖f x‖-a)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (‖f x‖-a))
    have he : (fun x => (‖f x‖-a)^2) = fun x => ‖f x‖^2 - (2*a)*‖f x‖ + a^2 := by
      funext x; ring
    rw [he, integral_add (f := fun x => ‖f x‖^2 - (2*a)*‖f x‖) (g := fun _ => a^2) (hf₂.sub (hf.norm.const_mul (2*a))) (integrable_const (a^2)),
      integral_sub (f := fun x => ‖f x‖^2) (g := fun x => (2*a)*‖f x‖) hf₂ (hf.norm.const_mul (2*a)), integral_const_mul] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    change 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - (2*a)*a + a^2 at h
    nlinarith
  have hn : ‖∫ x, f x ∂μ‖ ≤ a := norm_integral_le_integral_norm f
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]

end EuclideanFiveColor.KernelCompact

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/

namespace EuclideanFiveColor.RectangleDensity
open MeasureTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]

lemma measurable_pairCode (n : ℕ) : Measurable (pairCode (X := X) (Y := Y) n) :=
  ((measurable_code n).comp measurable_fst).prodMk ((measurable_code n).comp measurable_snd)

lemma pairCode_mono : Monotone (fun n =>
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) := by
  intro n m hnm
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun z : Code m × Code m => (fun i : Fin n => z.1 (Fin.castLE hnm i), fun i : Fin n => z.2 (Fin.castLE hnm i)))
    (measurable_of_countable _)
  rfl

lemma pairCode_generates : (⨆ n,
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  classical
  apply le_antisymm (iSup_le fun n => (measurable_pairCode n).comap_le)
  let m := ⨆ n, (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)
  have hp (n : ℕ) : Measurable[m] (pairCode (X := X) (Y := Y) n) :=
    (comap_measurable _).mono (by exact le_iSup (fun n =>
      (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) n) le_rfl
  have hx : @Measurable (X × Y) X m _ Prod.fst := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence X]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).1 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_fst.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [pairCode, code]
  have hy : @Measurable (X × Y) Y m _ Prod.snd := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence Y]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).2 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_snd.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [pairCode, code]
  have hi := (hx.prodMk hy).comap_le
  have hfun : (fun z : X × Y => (z.1, z.2)) = id := rfl
  rw [hfun] at hi
  simpa only [MeasurableSpace.comap_id] using hi

/-- Bounded finite rectangle approximation for any probability coupling, not
only a product measure. The common sup bound is twice the original bound. -/
theorem bounded_rectangles (ν : Measure (X × Y)) [IsProbabilityMeasure ν]
    (L : X × Y → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Code n × Code n → ℂ),
      (∀ z, ‖a z‖ ≤ 2*C) ∧
      Integrable (fun z => ‖L z - a (pairCode n z)‖^2) ν ∧
      (∫ z, ‖L z - a (pairCode n z)‖^2 ∂ν) < ε^2 := by
  let H : X × Y → Fin 1 → ℂ := fun z _ => L z
  have hH : Measurable H := Measurable.of_eval fun _ => hL
  have hHB (z : X × Y) : ‖H z‖ ≤ C := by
    rw [pi_norm_le_iff_of_nonneg hC]; intro i; exact hLC z
  obtain ⟨n, H₀, _, hB, hi, he⟩ := LimitDensity.generated_factor_approximation ν
    (fun n => pairCode (X := X) (Y := Y) n) measurable_pairCode
    pairCode_mono pairCode_generates 1 H hH C hC hHB ε hε
  have hd (z : X × Y) : dist (H z) (H₀ (pairCode n z)) = ‖L z - H₀ (pairCode n z) 0‖ := by
    rw [dist_eq_norm]
    have heq : H z - H₀ (pairCode n z) = fun _ : Fin 1 => L z - H₀ (pairCode n z) 0 := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    rw [heq, pi_norm_const]
  refine ⟨n, fun z => H₀ z 0, fun z => (norm_le_pi_norm (H₀ z) 0).trans (hB z), ?_, ?_⟩
  · simpa only [hd] using hi
  · simpa only [hd] using he

end EuclideanFiveColor.RectangleDensity

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

lemma law_eq_mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) :
    law μ q hq = ((condDistrib id q μ).prod (condDistrib id q μ)) ∘ₘ μ.map q := by
  let κ := condDistrib id q μ
  ext s hs
  rw [law, Measure.compProd_apply hs, Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  have he := ConditionalFiber.comp_identity_fiber μ q hq
  change κ ∘ₘ μ.map q = μ at he
  have hm : Measurable (fun x => (κ (q x)) (Prod.mk x ⁻¹' s)) :=
    Kernel.measurable_kernel_prodMk_left (κ := κ.comap q hq) hs
  change (∫⁻ x, κ (q x) (Prod.mk x ⁻¹' s) ∂μ) = _
  conv_lhs => rw [← he]
  rw [Measure.lintegral_bind (Kernel.measurable κ).aemeasurable hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  rw [Kernel.prod_apply, Measure.prod_apply hs]
  exact lintegral_congr_ae (hy.mono fun x hx => by change κ (q x) _ = _; rw [hx])

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_BoundedFunctions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.familyRealModule _root_.OAI.EuclideanFiveColor.BoundedMeasurable.instCoeFunFamilyForallFunc _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable (X : Type*) [MeasurableSpace X]

variable {X}

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma lp_congr (p : ℝ≥0∞) {f g : Func X} (h : f =ᵐ[μ] g) : lp μ p f = lp μ p g :=
  MemLp.toLp_congr _ _ h

lemma l2_eq_iff (f g : Func X) : l2 μ f = l2 μ g ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact (l2_ae μ f).symm.trans (h ▸ l2_ae μ g)
  · exact lp_congr μ 2

lemma integral_l2 (f : Func X) : ∫ x, l2 μ f x ∂μ = ∫ x, f x ∂μ :=
  integral_congr_ae (l2_ae μ f)

lemma inner_l2 (f g : Func X) :
    inner ℝ (l2 μ f) (l2 μ g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2_ae μ f, l2_ae μ g] with x hx hy
  rw [hx, hy]

lemma l2_norm_mul_le (f g : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖l2 μ (f*g)‖ ≤ C * ‖l2 μ g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [l2_ae μ (f*g), l2_ae μ g] with x hx hy
  rw [hx, hy, mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)

end
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma integrable_norm_sq (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) :
    Integrable (fun x => ‖f x‖^2) μ :=
  Integrable.of_bound ((measurable f).norm.pow_const 2).aestronglyMeasurable ((bound f : ℝ)^2)
    (.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_sq] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_bound f x) 2)))

lemma norm_l2_sq (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) :
    ‖l2 μ f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_l2]
  simp only [real_inner_self_eq_norm_sq]

lemma expect_conj (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) :
    expect κ (bmConj f) = bmConj (expect κ f) := by
  ext y; exact integral_conj

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_integral (f : Func X) : ∫ y, conditional μ q f y ∂μ.map q = ∫ x, f x ∂μ :=
  ConditionalFiber.integral_fiber μ q hq f (integrable μ f)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_integral (f : Func X) : ∫ x, project μ q hq f x ∂μ = ∫ x, f x ∂μ := by
  rw [← conditional_integral μ q hq f]
  exact (integral_map hq.aemeasurable (measurable (conditional μ q f)).aestronglyMeasurable).symm

lemma conditional_pullout (f : Func X) (b : Func Y) :
    conditional μ q (f * comp b q hq) =ᵐ[μ.map q] (conditional μ q f * b) := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  change (∫ x, f x * b (q x) ∂condDistrib id q μ y) =
    (∫ x, f x ∂condDistrib id q μ y) * b y
  rw [← integral_mul_const]
  exact integral_congr_ae (hy.mono (fun x hx => by dsimp; rw [hx]))

lemma conditional_lift (b : Func Y) :
    conditional μ q (comp b q hq) =ᵐ[μ.map q] b := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  change (∫ x, b (q x) ∂condDistrib id q μ y) = b y
  rw [integral_congr_ae (hy.mono (fun x hx => congrArg b hx))]
  simp

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_congr {f g : Func X} (h : f =ᵐ[μ] g) :
    conditional μ q f =ᵐ[μ.map q] conditional μ q g :=
  (ConditionalFiber.ae_fiber_of_ae μ q hq h).mono (fun _ hy => integral_congr_ae hy)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_norm_l2_le (f : Func X) :
    ‖l2 (μ.map q) (conditional μ q f)‖ ≤ ‖l2 μ f‖ := by
  have hs : ‖l2 (μ.map q) (conditional μ q f)‖^2 ≤ ‖l2 μ f‖^2 := by
    rw [norm_l2_sq, norm_l2_sq, ← ConditionalFiber.integral_fiber μ q hq
      (fun x => ‖f x‖^2) (integrable_norm_sq μ f)]
    apply integral_mono
    · exact integrable_norm_sq _ _
    · exact ConditionalFiber.integrable_fiber_integral μ q hq _ (integrable_norm_sq μ f)
    · intro y
      exact KernelCompact.norm_integral_sq _ f (integrable _ f) (integrable_norm_sq _ f)
  nlinarith [norm_nonneg (l2 (μ.map q) (conditional μ q f)), norm_nonneg (l2 μ f)]

end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeProducts
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [AddGroup K] [AddAction K X] [AddAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstVAdd K X] [MeasurableConstVAdd K Y]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_covariance_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) (k : K) :
    ∀ᵐ y ∂μ.map q, condDistrib id q μ (k +ᵥ y) =
      (condDistrib id q μ y).map (fun x => k +ᵥ x) :=
  KernelSupport.condDistrib_equivariant μ id q measurable_id hq
    (MeasurableEquiv.vadd k) (MeasurableEquiv.vadd k) (fun x => k +ᵥ x)
    (measurable_const_vadd k) (hpres k) (hqcov k) (Filter.Eventually.of_forall fun _ => rfl)

lemma law_preserving_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) (k : K) :
    MeasurePreserving (fun z : X × X => (k +ᵥ z.1,k +ᵥ z.2)) (law μ q hq) (law μ q hq) := by
  let κ := condDistrib id q μ
  let ν := μ.map q
  have hS := measurable_const_vadd (M := K) (α := X) k
  have hR := measurable_const_vadd (M := K) (α := Y) k
  have hν : ν.map (fun y => k +ᵥ y) = ν := by
    dsimp [ν]
    rw [Measure.map_map hR hq]
    calc
      _ = μ.map (q ∘ (fun x => k +ᵥ x)) := Measure.map_congr (Filter.EventuallyEq.symm (hqcov k))
      _ = _ := by rw [← Measure.map_map hq hS, (hpres k).map_eq]
  have hc := conditional_covariance_add μ q hq hpres hqcov k
  refine ⟨hS.prodMap hS, ?_⟩
  change (law μ q hq).map (Prod.map (fun x => k +ᵥ x) (fun x => k +ᵥ x)) = _
  rw [law_eq_mixture, Measure.map_comp _ _ (hS.prodMap hS), ← Kernel.map_prod_map _ _ hS hS]
  change ((κ.map (fun x => k +ᵥ x)).prod (κ.map (fun x => k +ᵥ x))) ∘ₘ ν = _
  calc
    _ = ((κ.prod κ).comap (fun y => k +ᵥ y) hR) ∘ₘ ν := by
      apply Measure.comp_congr
      filter_upwards [hc] with y hy
      simp only [Kernel.prod_apply, Kernel.map_apply _ hS, Kernel.comap_apply]
      rw [hy]
    _ = (κ.prod κ) ∘ₘ ν.map (fun y => k +ᵥ y) := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        lintegral_map ((κ.prod κ).measurable_coe hs) hR]
      rfl
    _ = (κ.prod κ) ∘ₘ ν := by rw [hν]

lemma law_invariant_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) :
    VAddInvariantMeasure K (X × X) (law μ q hq) := by
  constructor
  intro k s hs
  exact (law_preserving_add μ q hq hpres hqcov k).measure_preimage hs.nullMeasurableSet

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

lemma norm_project_l2 (f : Func X) :
    ‖l2 μ (project μ q hq f)‖ = ‖l2 (μ.map q) (conditional μ q f)‖ := by
  have : ‖l2 μ (project μ q hq f)‖^2 = ‖l2 (μ.map q) (conditional μ q f)‖^2 := by
    rw [norm_l2_sq, norm_l2_sq]
    exact (integral_map hq.aemeasurable
      ((measurable (conditional μ q f)).norm.pow_const 2).aestronglyMeasurable).symm
  nlinarith [norm_nonneg (l2 μ (project μ q hq f)),
    norm_nonneg (l2 (μ.map q) (conditional μ q f))]

end
section
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

lemma act_add (g h : G) (f : Func X) : act (g+h) f = act g (act h f) := by
  ext x
  simp only [act_apply, ← add_vadd, add_comm g h]
lemma act_mul (g : G) (f h : Func X) : act g (f*h) = act g f * act g h := rfl
lemma act_conj (g : G) (f : Func X) : act g (bmConj f) = bmConj (act g f) := rfl
lemma act_sub (g : G) (f h : Func X) : act g (f-h) = act g f - act g h := rfl

variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma l2_act (g : G) (f : Func X) :
    l2 μ (act g f) = Amenable.Koopman.action μ g (l2 μ f) := by
  apply Lp.ext
  exact (l2_ae μ (act g f)).trans ((MeasureTheory.measurePreserving_vadd g μ).quasiMeasurePreserving.ae_eq_comp
    (l2_ae μ f)).symm |>.trans (Amenable.Koopman.coe_action μ g (l2 μ f)).symm

end
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_sub (f g : Func X) : project μ q hq (f-g) = project μ q hq f - project μ q hq g := by
  ext x
  exact integral_sub (integrable _ f) (integrable _ g)
omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_bound (f : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (x : X) :
    ‖project μ q hq f x‖ ≤ C := expect_bound _ f hf (q x)
lemma project_comp (b : Func Y) : project μ q hq (comp b q hq) =ᵐ[μ] comp b q hq :=
  ae_of_ae_map hq.aemeasurable (conditional_lift μ q hq b)
lemma project_project (f : Func X) : project μ q hq (project μ q hq f) =ᵐ[μ] project μ q hq f :=
  project_comp μ q hq _
lemma center_project_l2 (f : Func X) : l2 μ (project μ q hq (f-project μ q hq f)) = 0 := by
  rw [project_sub, map_sub]
  have : l2 μ (project μ q hq (project μ q hq f)) = l2 μ (project μ q hq f) :=
    (l2_eq_iff μ _ _).mpr (project_project μ q hq f)
  rw [this, sub_self]

lemma project_pullout (f : Func X) (b : Func Y) :
    project μ q hq (f * comp b q hq) =ᵐ[μ] project μ q hq f * comp b q hq :=
  ae_of_ae_map hq.aemeasurable (conditional_pullout μ q hq f b)

lemma integral_mul_lift (f : Func X) (b : Func Y) :
    ∫ x, (f * comp b q hq) x ∂μ = ∫ x, (project μ q hq f * comp b q hq) x ∂μ := by
  rw [← project_integral μ q hq (f * comp b q hq)]
  exact integral_congr_ae (project_pullout μ q hq f b)

variable {G : Type*} [AddCommGroup G] [AddAction G X] [AddAction G Y]
  [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y] [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, ∀ᵐ x ∂μ, q (g +ᵥ x) = g +ᵥ q x)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma conditional_act (g : G) (f : Func X) :
    conditional μ q (act g f) =ᵐ[μ.map q] act g (conditional μ q f) := by
  filter_upwards [RelativeProduct.conditional_covariance_add μ q hq
    (fun k => measurePreserving_vadd k μ) hqcov g] with y hy
  change (∫ x, f (g +ᵥ x) ∂condDistrib id q μ y) = ∫ x, f x ∂condDistrib id q μ (g +ᵥ y)
  rw [hy]
  exact (integral_map (measurable_const_vadd g).aemeasurable (measurable f).aestronglyMeasurable).symm

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ] in
include hqcov in
lemma act_lift (g : G) (b : Func Y) :
    act g (comp b q hq) =ᵐ[μ] comp (act g b) q hq := by
  filter_upwards [hqcov g] with x hx
  simp only [act_apply, comp_apply, hx]

omit [StandardBorelSpace Y] [Nonempty Y] in
include hqcov in
lemma project_act (g : G) (f : Func X) :
    project μ q hq (act g f) =ᵐ[μ] act g (project μ q hq f) := by
  have he : project μ q hq (act g f) =ᵐ[μ] comp (act g (conditional μ q f)) q hq :=
    ae_of_ae_map hq.aemeasurable (conditional_act μ q hq hqcov g f)
  exact he.trans (act_lift μ q hq hqcov g _).symm

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable (G X : Type*) [MeasurableSpace X]
variable {G X}

namespace Family

variable [TopologicalSpace G] [DiscreteTopology G]
variable (μ : Measure X) [IsProbabilityMeasure μ]

variable [AddCommGroup G] (M : Amenable.Mean G)

lemma avg_pair (F : Family G X) (h : Lp ℂ 2 μ) :
    inner ℝ (avg μ M F) h = M.map (Amenable.Mean.pairing (toL2 μ F) h) := M.vector_pair _ _

omit [TopologicalSpace G] [DiscreteTopology G]
variable [AddAction G X] [MeasurableConstVAdd G X]
lemma orbit_sub (φ : G →+ G) (f h : Func X) : orbit φ (f-h) = orbit φ f - orbit φ h := rfl

end Family
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma tensor_mul (f h : Func X) (g k : Func Y) : tensor (f*h) (g*k) = tensor f g * tensor h k := by
  ext z; simp only [tensor_apply, mul_apply]; ring

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

lemma integral_law (f : Func (X×X)) :
    ∫ z, f z ∂(RelativeProduct.law μ q hq) =
      ∫ y, (∫ z, f z ∂(condDistrib id q μ y).prod (condDistrib id q μ y)) ∂μ.map q := by
  have hi := integrable (RelativeProduct.law μ q hq) f
  rw [RelativeProduct.law_eq_mixture, Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa only [Kernel.const_apply, Kernel.prod_apply, ← Measure.comp_eq_comp_const_apply,
    ← RelativeProduct.law_eq_mixture μ q hq] using he

lemma integral_tensor (f g : Func X) :
    ∫ z, tensor f g z ∂(RelativeProduct.law μ q hq) =
      ∫ y, conditional μ q f y * conditional μ q g y ∂μ.map q := by
  rw [integral_law]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => integral_prod_mul f g)

lemma integral_tensor_self (f : Func X) :
    ∫ z, tensor f (bmConj f) z ∂(RelativeProduct.law μ q hq) =
      (‖l2 (μ.map q) (conditional μ q f)‖^2 : ℝ) := by
  rw [integral_tensor, norm_l2_sq]
  simp only [conditional, expect_conj, conj_apply]
  change (∫ y, conditional μ q f y * star (conditional μ q f y) ∂μ.map q) = _
  calc
    _ = ∫ y, ((‖conditional μ q f y‖^2 : ℝ) : ℂ) ∂μ.map q := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => (Complex.mul_conj _).trans
        (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq _))
    _ = _ := integral_complex_ofReal

lemma inner_tensor (v w : Func X) :
    inner ℝ (l2 (RelativeProduct.law μ q hq) (tensor w (bmConj w)))
      (l2 (RelativeProduct.law μ q hq) (tensor (bmConj v) v)) =
      ‖l2 (μ.map q) (conditional μ q (v*w))‖^2 := by
  rw [real_inner_comm, inner_l2]
  have he : (fun z : X×X => inner ℝ (tensor (bmConj v) v z) (tensor w (bmConj w) z)) =
      (fun z => (tensor (v*w) (bmConj (v*w)) z).re) := by
    funext z
    simp only [Complex.inner, tensor_apply, conj_apply, mul_apply, starRingEnd_apply, star_mul', star_star]
    congr 1
    ring
  rw [he]
  change (∫ z, RCLike.re (tensor (v*w) (bmConj (v*w)) z) ∂(RelativeProduct.law μ q hq)) = _
  rw [integral_re (integrable _ (tensor (v*w) (bmConj (v*w)))), integral_tensor_self]
  rfl

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable.Koopman
variable {G X E : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace.CountablySeparated E]

lemma vector_orbit_hom_zero (M : Mean G) (φ : G →+ G) (hs : Function.Surjective φ)
    (v : Lp E 2 μ) (hv : ∫ x, v x ∂μ = 0) :
    M.vector (Mean.orbit (fun g => action (E := E) μ (φ g)) v) = 0 := by
  apply M.vector_orbit_eq_zero _ (fun g h v => by rw [map_add, action_add]) v
  intro w hw
  apply inner_fixed_zero (G := G) (E := E) μ v hv w
  intro g
  obtain ⟨h, rfl⟩ := hs g
  exact hw h
end EuclideanFiveColor.Amenable.Koopman
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X] [Nonempty X] in
lemma tensor_act (g : G) (v w : Func X) :
    tensor (act g v) (act g w) = act g (tensor v w) := rfl

variable [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]

include hq in
lemma pair_mean_sq_zero (M : Amenable.Mean G) (φ : G →+ G) (hs : Function.Surjective φ)
    (v w : Func X) (hw : l2 (μ.map q) (conditional μ q w) = 0) :
    M.map (Amenable.Mean.squareNorm (pairSequence μ q hq φ v w)) = 0 := by
  let ρ := RelativeProduct.law μ q hq
  let t := tensor w (bmConj w)
  have iw : ∫ z, l2 ρ t z ∂ρ = 0 := by
    rw [integral_l2, integral_tensor_self, hw]
    simp
  let U := fun g : G => Amenable.Koopman.action (E := ℂ) ρ (φ g)
  have hv := Amenable.Koopman.vector_orbit_hom_zero ρ M φ hs (l2 ρ t) iw
  let a := l2 ρ (tensor (bmConj v) v)
  have he : Amenable.Mean.squareNorm (pairSequence μ q hq φ v w) =
      Amenable.Mean.pairing (Amenable.Mean.orbit U (l2 ρ t)) a := by
    ext g
    rw [Amenable.Mean.squareNorm_apply]
    change ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖^2 =
      inner ℝ (Amenable.Koopman.action ρ (φ g) (l2 ρ t)) a
    dsimp only [t, a]
    rw [← l2_act, ← tensor_act, act_conj]
    exact (inner_tensor μ q hq v (act (φ g) w)).symm
  rw [he, ← M.vector_pair]
  change inner ℝ (M.vector (Amenable.Mean.orbit U (l2 ρ t))) a = 0
  rw [hv, inner_zero_left]

end EuclideanFiveColor.BoundedMeasurable

namespace EuclideanFiveColor.AlgebraReplacement

section
variable {ι R A H : Type*} [DecidableEq ι] [Semiring R] [CommRing A]
  [Module R A] [AddCommMonoid H] [Module R H]

lemma mixed_prod (s t : Finset ι) (ht : t ⊆ s) (f g : ι → A) :
    (∏ i ∈ t, f i) * (∏ i ∈ s\t, g i) = ∏ i ∈ s, if i∈t then f i else g i := by
  have he : s.filter (fun i => i ∈ t) = t := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨ht h,h⟩⟩
  have hn : s.filter (fun i => ¬ i∈t) = s\t := by ext i; simp
  rw [Finset.prod_ite, he, hn]

end
variable {ι A H : Type*} [DecidableEq ι] [CommRing A] [AddCommMonoid H]
lemma add_prod_replace (L : A →+ H) (s : Finset ι) (f g : ι → A)
    (h : ∀ t ∈ s.powerset, t ≠ ∅ →
      L ((∏ i ∈ t, (f i - g i)) * ∏ i ∈ s\t, g i) = 0) :
    L (∏ i ∈ s, f i) = L (∏ i ∈ s, g i) := by
  have he := Finset.prod_add (fun i => f i - g i) g s
  simp only [sub_add_cancel] at he
  rw [he, map_sum]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro t ht hn
    exact h t ht hn
  · simp
end EuclideanFiveColor.AlgebraReplacement

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Separability
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.Amenable.Mean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : EuclideanFiveColor.Amenable.Mean G)
lemma vector_real (f : G →ᵇ ℝ) : M.vector f = M.map f := by
  have h := M.vector_pair f 1
  have he : pairing f 1 = f := by ext g; simp [pairing_apply]
  simpa only [Real.inner_apply, mul_one, he] using h

lemma norm_mean_zero_of_square {H : Type*} [NormedAddCommGroup H]
    (V : G →ᵇ H) (h : M.map (squareNorm V) = 0) : M.map (normFn V) = 0 := by
  have he : squareNorm (normFn V) = squareNorm V := by
    ext g
    simp only [squareNorm_apply, normFn_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hj := M.jensen (normFn V)
  rw [M.vector_real, he, h] at hj
  rw [Real.norm_eq_abs, sq_abs] at hj
  have : (M.map (normFn V))^2 = 0 := le_antisymm hj (sq_nonneg _)
  exact sq_eq_zero_iff.mp this
end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]

lemma l2_inner (f h : Func X) : inner ℝ (l2 μ f) (l2 μ h) =
    (∫ x, (bmConj f * h) x ∂μ).re := by
  rw [inner_l2]
  simp only [Complex.inner, starRingEnd_apply, mul_comm (h _)]
  change (∫ x, RCLike.re ((bmConj f * h) x) ∂μ) = _
  exact integral_re (integrable μ (bmConj f * h))

omit [TopologicalSpace G] [DiscreteTopology G] [IsProbabilityMeasure μ] in
lemma integral_act (g : G) (f : Func X) : ∫ x, act g f x ∂μ = ∫ x, f x ∂μ :=
  (measurePreserving_vadd g μ).integral_comp (MeasurableEquiv.vadd g).measurableEmbedding (f : X → ℂ)

lemma l2_mul_norm_le (f h : Func X) {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) :
    ‖l2 μ (f*h)‖ ≤ C * ‖l2 μ f‖ := by
  have hC0 : 0 ≤ C := by
    have : Nonempty X := MeasureTheory.nonempty_of_isProbabilityMeasure μ
    exact (norm_nonneg (h (Classical.choice this))).trans (hC _)
  have hi : ‖l2 μ (f*h)‖^2 ≤ C^2 * ‖l2 μ f‖^2 := by
    rw [norm_l2_sq, norm_l2_sq, ← integral_const_mul]
    apply integral_mono (integrable_norm_sq μ (f*h)) ((integrable_norm_sq μ f).const_mul _)
    intro x
    change ‖f x * h x‖^2 ≤ C^2 * ‖f x‖^2
    rw [norm_mul, mul_pow]
    have hh : ‖h x‖^2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (sq_nonneg ‖f x‖)
  have hn := norm_nonneg (l2 μ (f*h))
  have hm := norm_nonneg (l2 μ f)
  nlinarith [mul_nonneg hC0 hm]

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {ι G X : Type*} [DecidableEq ι] [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

lemma conj_prod (s : Finset ι) (f : ι → Func X) : bmConj (∏ i ∈ s, f i) = ∏ i ∈ s, bmConj (f i) := by
  ext x
  simp
lemma comp_prod {Y : Type*} [MeasurableSpace Y] (s : Finset ι) (f : ι → Func Y)
    (q : X → Y) (hq : Measurable q) : comp (∏ i ∈ s, f i) q hq = ∏ i ∈ s, comp (f i) q hq := by
  ext x
  simp
lemma act_prod (g : G) (s : Finset ι) (f : ι → Func X) :
    act g (∏ i ∈ s, f i) = ∏ i ∈ s, act g (f i) := by ext x; simp

lemma prod_orbit_correlation (s : Finset ι) (φ : ι → G →+ G) (f : ι → Func X) (u h : G) :
    (∏ i ∈ s, act (φ i (u+h)) (f i)) * bmConj (∏ i ∈ s, act (φ i u) (f i)) =
    ∏ i ∈ s, act (φ i u) (act (φ i h) (f i) * bmConj (f i)) := by
  rw [conj_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_add, act_add, act_mul, act_conj]

lemma prod_shift_erase (s : Finset ι) (j : ι) (hj : j∈s)
    (φ : ι → G →+ G) (f : ι → Func X) (u : G) :
    (∏ i ∈ s, act (φ i u) (f i)) =
    act (φ j u) (f j * ∏ i ∈ s.erase j, act ((φ i - φ j) u) (f i)) := by
  rw [act_mul, act_prod]
  rw [← Finset.mul_prod_erase s (fun i => act (φ i u) (f i)) hj]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← act_add]
  congr 1
  simp only [AddMonoidHom.sub_apply]
  abel

variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
omit [DecidableEq ι] in
lemma l2_inner_mul (f h : Func X) : inner ℝ (l2 μ f) (l2 μ (bmConj h)) =
    (∫ x, (f*h) x ∂μ).re := by
  rw [real_inner_comm, l2_inner, conj_conj]
  congr 1
  rw [mul_comm h f]

variable [TopologicalSpace G] [DiscreteTopology G]
lemma correlation_product (M : Amenable.Mean G) (s : Finset ι) (j : ι) (hj : j∈s)
    (φ : ι → G →+ G) (f : ι → Func X) (h : G) :
    M.correlation (Family.toL2 μ (∏ i ∈ s, Family.orbit (φ i) (f i)))
      (Family.toL2 μ (∏ i ∈ s, Family.orbit (φ i) (f i))) h =
    inner ℝ (Family.avg μ M (∏ i ∈ s.erase j,
      Family.orbit (φ i - φ j) (act (φ i h) (f i) * bmConj (f i))))
      (l2 μ (bmConj (act (φ j h) (f j) * bmConj (f j)))) := by
  rw [Family.avg_pair, Amenable.Mean.correlation_apply]
  congr 1
  apply BoundedContinuousFunction.ext
  intro u
  simp only [Amenable.Mean.cross_apply, Amenable.shift_apply, Family.toL2_apply,
    Family.prod_apply, Family.orbit_apply, Amenable.Mean.pairing_apply]
  rw [← conj_conj (∏ i ∈ s, act (φ i u) (f i)), l2_inner_mul]
  rw [prod_orbit_correlation, prod_shift_erase s j hj, integral_act, l2_inner_mul]
  congr 1
  rw [mul_comm]

end

section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] in
lemma norm_l2_conj (f : Func X) : ‖l2 μ (bmConj f)‖ = ‖l2 μ f‖ := by
  have he : ‖l2 μ (bmConj f)‖^2 = ‖l2 μ f‖^2 := by simp only [norm_l2_sq, conj_apply, norm_star]
  nlinarith [norm_nonneg (l2 μ (bmConj f)), norm_nonneg (l2 μ f)]

lemma inner_replace_project (w h : Func X) (b : Func Y) (hw : w =ᵐ[μ] comp b q hq) :
    inner ℝ (l2 μ w) (l2 μ (bmConj h)) =
    inner ℝ (l2 μ w) (l2 μ (bmConj (project μ q hq h))) := by
  rw [l2_inner_mul, l2_inner_mul]
  congr 1
  calc
    (∫ x, (w*h) x ∂μ) = ∫ x, (h*comp b q hq) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      simp only [mul_apply, hx, mul_comm]
    _ = ∫ x, (project μ q hq h * comp b q hq) x ∂μ := integral_mul_lift μ q hq h b
    _ = ∫ x, (w * project μ q hq h) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      simp only [mul_apply, hx, mul_comm]

lemma inner_project_bound (w h : Func X) (b : Func Y) (hw : w =ᵐ[μ] comp b q hq)
    {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    |inner ℝ (l2 μ w) (l2 μ (bmConj h))| ≤ C * ‖l2 μ (project μ q hq h)‖ := by
  rw [inner_replace_project μ q hq w h b hw]
  calc
    |inner ℝ (l2 μ w) (l2 μ (bmConj (project μ q hq h)))| ≤
        ‖l2 μ w‖ * ‖l2 μ (bmConj (project μ q hq h))‖ := abs_real_inner_le_norm _ _
    _ ≤ C * ‖l2 μ (project μ q hq h)‖ := by
      rw [norm_l2_conj]
      exact mul_le_mul_of_nonneg_right (l2_norm_le μ w hC) (norm_nonneg _)

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma avg_project_bound (M : Amenable.Mean G) (W : Family G X) (h : Func X) (b : G → Func Y)
    (hw : ∀ g, W g =ᵐ[μ] comp (b g) q hq) {C : ℝ} (hC : ∀ g x, ‖W g x‖ ≤ C) :
    |inner ℝ (Family.avg μ M W) (l2 μ (bmConj h))| ≤ C * ‖l2 μ (project μ q hq h)‖ := by
  rw [Family.avg_pair, ← M.map_const (C * ‖l2 μ (project μ q hq h)‖)]
  apply M.abs_le
  intro g
  exact inner_project_bound μ q hq (W g) h (b g) (hw g) (hC g)

variable [AddAction G X] [MeasurableConstVAdd G X] [VAddInvariantMeasure G X μ]
  [AddAction G Y] [MeasurableConstVAdd G Y]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable {ι : Type*} [DecidableEq ι]
omit [StandardBorelSpace Y] [Nonempty Y] [TopologicalSpace G] [DiscreteTopology G]
  [VAddInvariantMeasure G X μ] in
include hqcov in
lemma prod_act_project_lift (s : Finset ι) (ψ : ι → G →+ G) (f : ι → Func X) (u : G) :
    (∏ i ∈ s, act (ψ i u) (project μ q hq (f i))) =ᵐ[μ]
    comp (∏ i ∈ s, act (ψ i u) (conditional μ q (f i))) q hq := by
  rw [comp_prod]
  induction s using Finset.induction_on with
  | empty => exact .of_forall (fun _ => by simp)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    filter_upwards [act_lift μ q hq hqcov (ψ i u) (conditional μ q (f i)), ih] with x hx hy
    exact congrArg₂ (·*·) hx hy

end

variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)

omit [VAddInvariantMeasure G X μ] in
lemma pairVanishing_of_ergodic [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]
    (M : Amenable.Mean G) : PairVanishing μ q hq M := by
  intro φ hs v w hw
  apply M.norm_mean_zero_of_square
  apply pair_mean_sq_zero μ q hq M φ hs v w
  apply norm_eq_zero.mp
  rw [← norm_project_l2 μ q hq w, hw, norm_zero]

variable {ι : Type*} [DecidableEq ι]

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Admissible.erase_diff {s : Finset ι} {φ : ι → G →+ G}
    (ha : Admissible s φ) {j : ι} (hj : j∈s) :
    Admissible (s.erase j) (fun i => φ i - φ j) := by
  constructor
  · intro i hi
    exact ha.2 i (Finset.mem_of_mem_erase hi) j hj (Finset.ne_of_mem_erase hi)
  · intro i hi k hk hik
    have he : (φ i - φ j) - (φ k - φ j) = φ i - φ k := by abel
    rw [he]
    exact ha.2 i (Finset.mem_of_mem_erase hi) k (Finset.mem_of_mem_erase hk) hik

variable [AddAction G Y] [MeasurableConstVAdd G Y]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
include hqcov in
/-- Centered multiple vector averages for every invariant mean. The proof only
uses the actual conditional pair criterion, never exchanges iterated means. -/
theorem avg_product_zero_of_pair (M : Amenable.Mean G) (hpair : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (f : ι → Func X) (ha : Admissible s φ)
    (hc : ∃ j∈s, l2 μ (project μ q hq (f j)) = 0) :
    Family.avg μ M (∏ i∈s, Family.orbit (φ i) (f i)) = 0 := by
  have main : ∀ n : ℕ, ∀ (s : Finset ι), s.card ≤ n → ∀ (φ : ι → G →+ G)
      (f : ι → Func X), Admissible s φ →
      (∃ j∈s, l2 μ (project μ q hq (f j)) = 0) →
      Family.avg μ M (∏ i∈s, Family.orbit (φ i) (f i)) = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hn φ f ha hc
      have hs : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
      obtain ⟨j,hj,_⟩ := hc
      simp [hs] at hj
    | succ n ih =>
      intro s hn φ f ha hc
      obtain ⟨j,hj,hfj⟩ := hc
      let e := s.erase j
      let ψ := fun i => φ i - φ j
      have he : e.card ≤ n := by
        have := Finset.card_erase_of_mem hj
        dsimp [e]
        omega
      have had : Admissible e ψ := ha.erase_diff hj
      let F : G → ι → Func X := fun h i => act (φ i h) (f i) * bmConj (f i)
      have replace (h : G) :
          Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (F h i)) =
          Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) := by
        apply EuclideanFiveColor.AlgebraReplacement.add_prod_replace
          (A := Family G X) (H := Lp ℂ 2 μ) (Family.avg μ M).toAddMonoidHom e
          (fun i => Family.orbit (ψ i) (F h i))
          (fun i => Family.orbit (ψ i) (project μ q hq (F h i)))
        intro t ht htn
        have hte := Finset.mem_powerset.mp ht
        rw [EuclideanFiveColor.AlgebraReplacement.mixed_prod e t hte]
        have heq : (∏ i∈e, if i∈t then
            Family.orbit (ψ i) (F h i) - Family.orbit (ψ i) (project μ q hq (F h i))
            else Family.orbit (ψ i) (project μ q hq (F h i))) =
            ∏ i∈e, Family.orbit (ψ i)
              (if i∈t then F h i - project μ q hq (F h i) else project μ q hq (F h i)) := by
          apply Finset.prod_congr rfl
          intro i _
          split_ifs <;> simp only [Family.orbit_sub]
        rw [heq]
        apply ih e he ψ _ had
        obtain ⟨i,hit⟩ := Finset.nonempty_iff_ne_empty.mpr htn
        refine ⟨i,hte hit, ?_⟩
        rw [ite_eq_left hit]
        exact center_project_l2 μ q hq (F h i)
      let C : ℝ := ∏ i∈e, (bound (f i) : ℝ)^2
      have hCb (h u : G) (x : X) :
          ‖(∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) u x‖ ≤ C := by
        simp only [Family.prod_apply, Family.orbit_apply, func_prod_apply]
        rw [norm_prod]
        apply Finset.prod_le_prod (fun index _ => norm_nonneg _)
        intro i _
        apply project_bound μ q hq
        intro z
        dsimp only [F, mul_apply, act_apply, conj_apply]
        rw [norm_mul, norm_star, pow_two]
        exact mul_le_mul (norm_le_bound (f i) _) (norm_le_bound (f i) _) (norm_nonneg _) (bound (f i)).coe_nonneg
      let V := Family.toL2 μ (∏ i∈s, Family.orbit (φ i) (f i))
      let a := Amenable.Mean.normFn (pairSequence μ q hq (φ j) (bmConj (f j)) (f j))
      have hcorr (h : G) : M.correlation V V h ≤ C * a h := by
        dsimp only [V]
        rw [correlation_product μ M s j hj]
        change inner ℝ (Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (F h i)))
          (l2 μ (bmConj (F h j))) ≤ _
        rw [replace]
        have hb := avg_project_bound μ q hq M
          (∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) (F h j)
          (fun u => ∏ i∈e, act (ψ i u) (conditional μ q (F h i)))
          (fun u => by
            filter_upwards [prod_act_project_lift μ q hq hqcov e ψ (F h) u] with x hx
            simpa only [Family.prod_apply, Family.orbit_apply, func_prod_apply, Finset.prod_apply] using hx) (hCb h)
        apply (le_abs_self _).trans (hb.trans_eq ?_)
        congr 1
        rw [norm_project_l2]
        change ‖l2 (μ.map q) (conditional μ q (F h j))‖ =
          ‖l2 (μ.map q) (conditional μ q (bmConj (f j) * act (φ j h) (f j)))‖
        dsimp only [F]
        rw [mul_comm]
      change M.vector V = 0
      apply M.vector_eq_zero_of_correlation_nonpos
      have hm := M.mono (M.correlation V V) (C • a) hcorr
      rw [map_smul, show M.map a = 0 from hpair (φ j) (ha.1 j hj) (bmConj (f j)) (f j) hfj,
        smul_zero] at hm
      exact hm
  exact main s.card s le_rfl φ f ha hc

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable.Family
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (M : Amenable.Mean G)
lemma meanNorm_nonneg (F : Family G X) : 0 ≤ meanNorm μ M F :=
  M.positive _ (fun g => by
    change 0 ≤ ‖l2 μ (F g)‖
    exact norm_nonneg _)
lemma meanNorm_congr {F H : Family G X} (h : ∀ g, F g =ᵐ[μ] H g) :
    meanNorm μ M F = meanNorm μ M H := by
  apply congrArg M.map
  apply BoundedContinuousFunction.ext
  intro g
  exact congrArg norm ((l2_eq_iff μ _ _).mpr (h g))
lemma meanNorm_le {F : Family G X} {C : ℝ} (h : ∀ g, ‖l2 μ (F g)‖ ≤ C) :
    meanNorm μ M F ≤ C := by
  rw [meanNorm, ← M.map_const C]
  exact M.mono _ _ h
@[simp] lemma meanNorm_zero : meanNorm μ M (0 : Family G X) = 0 := by
  apply le_antisymm _ (meanNorm_nonneg μ M 0)
  apply meanNorm_le
  intro g
  change ‖l2 μ (0 : Func X)‖ ≤ 0
  rw [map_zero, norm_zero]
lemma meanNorm_add_le (F H : Family G X) :
    meanNorm μ M (F+H) ≤ meanNorm μ M F + meanNorm μ M H := by
  unfold meanNorm
  rw [← map_add]
  apply M.mono
  intro g
  simpa only [Amenable.Mean.normFn_apply, BoundedContinuousFunction.add_apply,
    toL2_apply, add_apply, map_add] using norm_add_le (l2 μ (F g)) (l2 μ (H g))
lemma meanNorm_mul_le (F H : Family G X) {C : ℝ} (hC : ∀ g x, ‖H g x‖ ≤ C) :
    meanNorm μ M (F*H) ≤ C * meanNorm μ M F := by
  unfold meanNorm
  calc
    _ ≤ M.map (C • Amenable.Mean.normFn (toL2 μ F)) := by
      apply M.mono
      intro g
      exact l2_mul_norm_le μ (F g) (H g) (hC g)
    _ = _ := by rw [map_smul]; rfl
lemma meanNorm_add_zero {F H : Family G X} (hF : meanNorm μ M F = 0) (hH : meanNorm μ M H = 0) :
    meanNorm μ M (F+H) = 0 := by
  have h := meanNorm_add_le μ M F H
  rw [hF, hH, add_zero] at h
  exact le_antisymm h (meanNorm_nonneg μ M _)
lemma meanNorm_mul_zero {F H : Family G X} (hF : meanNorm μ M F = 0) :
    meanNorm μ M (F*H) = 0 := by
  have h := meanNorm_mul_le μ M F H H.norm_le_bound
  rw [hF, mul_zero] at h
  exact le_antisymm h (meanNorm_nonneg μ M _)
lemma meanNorm_sum_zero {ι : Type*} (s : Finset ι) (F : ι → Family G X)
    (hF : ∀ i∈s, meanNorm μ M (F i) = 0) : meanNorm μ M (∑ i∈s, F i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact meanNorm_add_zero μ M (hF i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
lemma meanNorm_eq_zero_of_approx {F : Family G X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ H : Family G X, meanNorm μ M H = 0 ∧
      ∀ g, ‖l2 μ (F g - H g)‖ ≤ ε) : meanNorm μ M F = 0 := by
  apply le_antisymm _ (meanNorm_nonneg μ M F)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨H,hH,hd⟩ := h ε hε
  have hb := meanNorm_add_le μ M (F-H) H
  rw [hH, add_zero] at hb
  have ht : (F-H)+H = F := sub_add_cancel F H
  rw [ht] at hb
  have hd' : meanNorm μ M (F-H) ≤ ε := meanNorm_le μ M hd
  simpa only [zero_add] using hb.trans hd'
end EuclideanFiveColor.BoundedMeasurable.Family

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)
namespace Family
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_add (F H : Family G X) : conditional μ q (F+H) = conditional μ q F + conditional μ q H := by
  ext g y
  exact integral_add (integrable _ (F g)) (integrable _ (H g))
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_sub (F H : Family G X) : conditional μ q (F-H) = conditional μ q F - conditional μ q H := by
  ext g y
  exact integral_sub (integrable _ (F g)) (integrable _ (H g))
end Family
variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_add_left (φ : G →+ G) (v v' w : Func X) :
    covariance μ q φ (v+v') w = covariance μ q φ v w + covariance μ q φ v' w := by
  apply Family.ext
  intro g
  change conditional μ q ((v+v')*act (φ g) w) - conditional μ q (v+v') *
    act (φ g) (conditional μ q w) =
    (conditional μ q (v*act (φ g) w) - conditional μ q v * act (φ g) (conditional μ q w)) +
    (conditional μ q (v'*act (φ g) w) - conditional μ q v' * act (φ g) (conditional μ q w))
  unfold conditional
  rw [add_mul, expect_add, expect_add, add_mul]
  abel

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_add_right (φ : G →+ G) (v w w' : Func X) :
    covariance μ q φ v (w+w') = covariance μ q φ v w + covariance μ q φ v w' := by
  have ha (g : G) (a b : Func X) : act g (a+b) = act g a + act g b := rfl
  have hb (g : G) (a b : Func Y) : act g (a+b) = act g a + act g b := rfl
  apply Family.ext
  intro g
  change conditional μ q (v*act (φ g) (w+w')) - conditional μ q v *
    act (φ g) (conditional μ q (w+w')) =
    (conditional μ q (v*act (φ g) w) - conditional μ q v * act (φ g) (conditional μ q w)) +
    (conditional μ q (v*act (φ g) w') - conditional μ q v * act (φ g) (conditional μ q w'))
  unfold conditional
  rw [ha, mul_add, expect_add, expect_add, hb, mul_add]
  abel
variable [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma conditional_mul_project_act (g : G) (v w : Func X) :
    conditional μ q (v*act g (project μ q hq w)) =ᵐ[μ.map q]
      conditional μ q v * act g (conditional μ q w) := by
  have h := act_lift μ q hq hqcov g (conditional μ q w)
  have hc : v*act g (project μ q hq w) =ᵐ[μ] v*comp (act g (conditional μ q w)) q hq := by
    filter_upwards [h] with x hx
    exact congrArg (fun t => v x*t) hx
  exact (conditional_congr μ q hq hc).trans (conditional_pullout μ q hq v _)

omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma covariance_center (φ : G →+ G) (v w : Func X) (g : G) :
    covariance μ q φ v w g =ᵐ[μ.map q]
      conditional μ q (v*act (φ g) (w-project μ q hq w)) := by
  have he : conditional μ q (v*act (φ g) (w-project μ q hq w)) =
      conditional μ q (v*act (φ g) w) - conditional μ q (v*act (φ g) (project μ q hq w)) := by
    rw [act_sub, mul_sub]
    exact (expectLinear (condDistrib id q μ)).map_sub _ _
  rw [he]
  filter_upwards [conditional_mul_project_act μ q hq hqcov (φ g) v w] with y hy
  simp only [covariance_apply, sub_apply]
  rw [hy]
  rfl

variable [TopologicalSpace G] [DiscreteTopology G]

omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma covariance_mean_zero [IsProbabilityMeasure (μ.map q)] (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (v w : Func X) :
    Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
  rw [Family.meanNorm_congr (μ.map q) M (F := covariance μ q φ v w)
    (H := Family.conditional μ q (Family.const v * Family.orbit φ (w-project μ q hq w)))
    (fun g => by
      simpa only [Family.conditional_apply, Family.mul_apply, Family.const_apply, Family.orbit_apply]
        using covariance_center μ q hq hqcov φ v w g)]
  have he : Family.toL2 (μ.map q) (Family.conditional μ q
      (Family.const v * Family.orbit φ (w-project μ q hq w))) =
      pairSequence μ q hq φ v (w-project μ q hq w) := by
    ext g
    rfl
  unfold Family.meanNorm
  rw [he]
  exact hp φ hs v _ (center_project_l2 μ q hq w)
end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_AlgebraModels
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_sub_left (φ : G →+ G) (v v' w : Func X) :
    covariance μ q φ (v-v') w = covariance μ q φ v w - covariance μ q φ v' w := by
  have h := covariance_add_left μ q φ (v-v') v' w
  rw [sub_add_cancel] at h
  rw [h]
  ext g y
  simp only [Family.sub_apply, Family.add_apply, sub_apply, add_apply]
  ring
omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_sub_right (φ : G →+ G) (v w w' : Func X) :
    covariance μ q φ v (w-w') = covariance μ q φ v w - covariance μ q φ v w' := by
  have h := covariance_add_right μ q φ v (w-w') w'
  rw [sub_add_cancel] at h
  rw [h]
  ext g y
  simp only [Family.sub_apply, Family.add_apply, sub_apply, add_apply]
  ring

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma covariance_norm_left (φ : G →+ G) (v w : Func X) (g : G) :
    ‖l2 (μ.map q) (covariance μ q φ v w g)‖ ≤ (2*(bound w : ℝ))*‖l2 μ v‖ := by
  have hp := conditional_norm_l2_le μ q hq v
  have h1 : ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ ≤ (bound w : ℝ)*‖l2 μ v‖ :=
    (conditional_norm_l2_le μ q hq _).trans (l2_mul_norm_le μ v (act (φ g) w)
      (fun x => norm_le_bound w _))
  have h2 : ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ ≤
      (bound w : ℝ)*‖l2 μ v‖ := by
    have h := l2_norm_mul_le (μ.map q) (act (φ g) (conditional μ q w)) (conditional μ q v)
      (fun y => expect_bound _ w (norm_le_bound w) (φ g +ᵥ y))
    rw [mul_comm (act _ _) _] at h
    exact h.trans (mul_le_mul_of_nonneg_left hp (bound w).coe_nonneg)
  rw [covariance_apply, map_sub]
  calc
    _ ≤ ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ +
        ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

variable [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma covariance_norm_right (φ : G →+ G) (v w : Func X) (g : G) :
    ‖l2 (μ.map q) (covariance μ q φ v w g)‖ ≤ (2*(bound v : ℝ))*‖l2 μ w‖ := by
  have hn : ‖l2 μ (act (φ g) w)‖ = ‖l2 μ w‖ := by
    rw [l2_act]
    exact (Amenable.Koopman.action μ (φ g)).norm_map _
  have h1 : ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ ≤ (bound v : ℝ)*‖l2 μ w‖ := by
    have h := (conditional_norm_l2_le μ q hq (v*act (φ g) w)).trans
      (l2_norm_mul_le μ v _ (norm_le_bound v))
    rwa [hn] at h
  have hp : ‖l2 (μ.map q) (act (φ g) (conditional μ q w))‖ ≤ ‖l2 μ w‖ := by
    have he := (l2_eq_iff (μ.map q) _ _).mpr (conditional_act μ q hq hqcov (φ g) w)
    rw [← he, ← hn]
    exact conditional_norm_l2_le μ q hq _
  have h2 : ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ ≤
      (bound v : ℝ)*‖l2 μ w‖ := by
    exact (l2_norm_mul_le (μ.map q) _ _ (expect_bound _ v (norm_le_bound v))).trans
      (mul_le_mul_of_nonneg_left hp (bound v).coe_nonneg)
  rw [covariance_apply, map_sub]
  calc
    _ ≤ ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ +
        ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]

lemma meanNorm_zero_of_dense (M : Amenable.Mean G) (S : Set (Func X))
    (hd : ∀ f : Func X, ∀ ε : ℝ, 0<ε → ∃ h∈S, ‖l2 μ (f-h)‖ < ε)
    (T : Func X → Family G Y) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ f h : Func X, ∀ g, ‖l2 ν (T f g-T h g)‖ ≤ C*‖l2 μ (f-h)‖)
    (hS : ∀ f∈S, Family.meanNorm ν M (T f) = 0) (f : Func X) :
    Family.meanNorm ν M (T f) = 0 := by
  apply Family.meanNorm_eq_zero_of_approx
  intro ε hε
  have hden : 0 < C+1 := by linarith
  obtain ⟨h,hh,hdist⟩ := hd f (ε/(C+1)) (div_pos hε hden)
  refine ⟨T h, hS h hh, fun g => ?_⟩
  have he : ε/(C+1)*(C+1) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  have hd0 : 0 ≤ ε/(C+1) := (div_pos hε hden).le
  calc
    _ ≤ C * ‖l2 μ (f-h)‖ := hT f h g
    _ ≤ C*(ε/(C+1)) := mul_le_mul_of_nonneg_left hdist.le hC
    _ ≤ ε := by nlinarith

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (q : X → Y) (hq : Measurable q) [IsProbabilityMeasure (μ.map q)]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma covariance_zero_of_dense (M : Amenable.Mean G) (S : Set (Func X))
    (hd : ∀ f : Func X, ∀ ε : ℝ, 0<ε → ∃ h∈S, ‖l2 μ (f-h)‖ < ε)
    (φ : G →+ G)
    (hS : ∀ v∈S, ∀ w∈S, Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0)
    (v w : Func X) : Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
  have hw (v : Func X) (hv : v∈S) (w : Func X) :
      Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
    apply meanNorm_zero_of_dense μ (μ.map q) M S hd (covariance μ q φ v)
      (C := 2*(bound v : ℝ)) (by positivity) _ (hS v hv) w
    intro w w' g
    have he : covariance μ q φ v w g - covariance μ q φ v w' g = covariance μ q φ v (w-w') g :=
      congrArg (fun F : Family G Y => F g) (covariance_sub_right μ q φ v w w').symm
    rw [he]
    exact covariance_norm_right μ q hq hqcov φ v (w-w') g
  apply meanNorm_zero_of_dense μ (μ.map q) M S hd (fun v => covariance μ q φ v w)
    (C := 2*(bound w : ℝ)) (by positivity) _ (fun v hv => hw v hv w) v
  intro v v' g
  have he : covariance μ q φ v w g - covariance μ q φ v' w g = covariance μ q φ (v-v') w g :=
    congrArg (fun F : Family G Y => F g) (covariance_sub_left μ q φ v v' w).symm
  rw [he]
  exact covariance_norm_left μ q hq φ (v-v') w g
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.RelativeProduct
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma graph_mixture (ν : Measure Y) [SFinite ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (hf : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, q x = y) :
    (κ ∘ₘ ν).map (fun x => (q x,x)) = ν ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (show Measurable (fun x => (q x,x)) from hq.prodMk measurable_id) hs,
    Measure.bind_apply (hs.preimage (show Measurable (fun x => (q x,x)) from hq.prodMk measurable_id)) (Kernel.measurable κ).aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr_ae
  filter_upwards [hf] with y hy
  apply measure_congr
  filter_upwards [hy] with x hx
  change ((q x,x) ∈ s) = ((y,x) ∈ s)
  rw [hx]

lemma map_mixture (ν : Measure Y) [SFinite ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (hf : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, q x = y) :
    (κ ∘ₘ ν).map q = ν := by
  have he := congrArg Measure.fst (graph_mixture ν κ q hq hf)
  change ((κ ∘ₘ ν).map (fun x => (q x,id x))).fst = (ν ⊗ₘ κ).fst at he
  simpa only [Measure.fst_map_prodMk measurable_id, Measure.fst_compProd] using he

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

include hq in
lemma square_fiber : ∀ᵐ y ∂μ.map q,
    ∀ᵐ z ∂((condDistrib id q μ).prod (condDistrib id q μ)) y, q z.1 = y := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  rw [Kernel.prod_apply]
  exact (measurePreserving_fst (μ := condDistrib id q μ y)
    (ν := condDistrib id q μ y)).quasiMeasurePreserving.ae hy

lemma law_map_base : (law μ q hq).map (q ∘ Prod.fst) = μ.map q := by
  rw [law_eq_mixture]
  exact map_mixture (μ.map q) _ _ (hq.comp measurable_fst) (square_fiber μ q hq)

lemma conditional_square :
    condDistrib id (q ∘ Prod.fst) (law μ q hq) =ᵐ[μ.map q]
      (condDistrib id q μ).prod (condDistrib id q μ) := by
  have he := graph_mixture (μ.map q) ((condDistrib id q μ).prod (condDistrib id q μ))
    (q ∘ Prod.fst) (hq.comp measurable_fst) (square_fiber μ q hq)
  rw [← law_eq_mixture μ q hq] at he
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hq.comp measurable_fst) measurable_id (he.trans (by rw [law_map_base]))
  rwa [law_map_base] at hc

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
lemma conditional_tensor (v w : Func X) :
    conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor v w) =ᵐ[μ.map q]
      conditional μ q v * conditional μ q w := by
  filter_upwards [RelativeProduct.conditional_square μ q hq] with y hy
  change (∫ z, tensor v w z ∂condDistrib id (q ∘ Prod.fst) (RelativeProduct.law μ q hq) y) = _
  rw [hy, Kernel.prod_apply]
  exact integral_prod_mul v w

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [IsProbabilityMeasure μ] in
include hq hqcov in
lemma factor_preserving (g : G) : MeasurePreserving (fun y : Y => g +ᵥ y) (μ.map q) (μ.map q) := by
  refine ⟨measurable_const_vadd g, ?_⟩
  rw [Measure.map_map (measurable_const_vadd g) hq]
  calc
    _ = μ.map (q ∘ (fun x => g +ᵥ x)) := Measure.map_congr (hqcov g).symm
    _ = _ := by rw [← Measure.map_map hq (measurable_const_vadd g), (measurePreserving_vadd g μ).map_eq]

omit [TopologicalSpace G] [DiscreteTopology G] in
include hqcov in
lemma covariance_tensor (φ : G →+ G) (a₁ a₂ b₁ b₂ : Func X) (g : G) :
    covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ (tensor a₁ a₂) (tensor b₁ b₂) g =ᵐ[μ.map q]
      ((Family.conditional μ q (Family.const a₁ * Family.orbit φ b₁)) *
        (Family.conditional μ q (Family.const a₂ * Family.orbit φ b₂)) -
        (Family.const (conditional μ q a₁) * Family.orbit φ (conditional μ q b₁)) *
        (Family.const (conditional μ q a₂) * Family.orbit φ (conditional μ q b₂)) : Family G Y) g := by
  have ht : tensor a₁ a₂ * act (φ g) (tensor b₁ b₂) = tensor (a₁*act (φ g) b₁) (a₂*act (φ g) b₂) := by
    rw [← tensor_act, tensor_mul]
  have h₁ := conditional_tensor μ q hq a₁ a₂
  have h₂ := (factor_preserving μ q hq hqcov (φ g)).quasiMeasurePreserving.ae
    (conditional_tensor μ q hq b₁ b₂)
  have h₃ := conditional_tensor μ q hq (a₁*act (φ g) b₁) (a₂*act (φ g) b₂)
  filter_upwards [h₁,h₂,h₃] with y hy₁ hy₂ hy₃
  change conditional _ _ (tensor a₁ a₂ * act (φ g) (tensor b₁ b₂)) y -
    conditional _ _ (tensor a₁ a₂) y * conditional _ _ (tensor b₁ b₂) (φ g +ᵥ y) = _
  rw [ht, hy₁, hy₂, hy₃]
  dsimp only [Family.mul_apply, Family.sub_apply, Family.conditional_apply,
    Family.const_apply, Family.orbit_apply, mul_apply, sub_apply, act_apply, Pi.mul_apply]
  ring

variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma covariance_tensor_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (a₁ a₂ b₁ b₂ : Func X) :
    Family.meanNorm (μ.map q) M
      (covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ (tensor a₁ a₂) (tensor b₁ b₂)) = 0 := by
  let A₁ := Family.conditional μ q (Family.const a₁ * Family.orbit φ b₁)
  let A₂ := Family.conditional μ q (Family.const a₂ * Family.orbit φ b₂)
  let B₁ := Family.const (conditional μ q a₁) * Family.orbit φ (conditional μ q b₁)
  let B₂ := Family.const (conditional μ q a₂) * Family.orbit φ (conditional μ q b₂)
  have h₁ : Family.meanNorm (μ.map q) M (A₁-B₁) = 0 := covariance_mean_zero μ q hq hqcov M hp φ hs a₁ b₁
  have h₂ : Family.meanNorm (μ.map q) M (A₂-B₂) = 0 := covariance_mean_zero μ q hq hqcov M hp φ hs a₂ b₂
  rw [Family.meanNorm_congr (μ.map q) M (covariance_tensor μ q hq hqcov φ a₁ a₂ b₁ b₂)]
  change Family.meanNorm (μ.map q) M (A₁*A₂-B₁*B₂) = 0
  have he : A₁*A₂-B₁*B₂ = (A₁-B₁)*A₂ + (A₂-B₂)*B₁ := by ring
  rw [he]
  exact Family.meanNorm_add_zero _ _ (Family.meanNorm_mul_zero _ _ h₁) (Family.meanNorm_mul_zero _ _ h₂)
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma FiniteTensor.zero : FiniteTensor (0 : Func (X×Y)) := by
  have he : BoundedMeasurable.tensor (0 : Func X) (0 : Func Y) = 0 := by ext z; simp
  rw [← he]
  exact .tensor _ _

lemma FiniteTensor.sum {ι : Type*} (s : Finset ι) (f : ι → Func (X×Y))
    (hf : ∀ i∈s, FiniteTensor (f i)) : FiniteTensor (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FiniteTensor.zero (X := X) (Y := Y)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma func_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Func X) (x : X) :
    (∑ i∈s, f i) x = ∑ i∈s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

variable [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]
open RectangleDensity

lemma tensor_code_finite (n : ℕ) (a : Code n × Code n → ℂ) (F : Func (X×Y))
    (he : ∀ z, F z = a (pairCode n z)) : FiniteTensor F := by
  classical
  let T : Code n × Code n → Func (X×Y) := fun c =>
    tensor (a c • codeCell (X := X) n c.1) (codeCell (X := Y) n c.2)
  have hsum : F = ∑ c, T c := by
    ext z
    rw [he, func_sum_apply]
    rw [Finset.sum_eq_single (pairCode n z)]
    · simp [T, tensor_apply, codeCell, pairCode]
    · intro c _ hc
      have hn : code X n z.1 ≠ c.1 ∨ code Y n z.2 ≠ c.2 := by
        contrapose! hc
        exact Prod.ext hc.1.symm hc.2.symm
      rcases hn with hn | hn <;> simp [T, tensor_apply, codeCell, hn]
    · simp
  rw [hsum]
  exact FiniteTensor.sum _ _ (fun _ _ => .tensor _ _)

lemma finiteTensor_dense (ν : Measure (X×Y)) [IsProbabilityMeasure ν]
    (f : Func (X×Y)) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : Func (X×Y), FiniteTensor h ∧ ‖l2 ν (f-h)‖ < ε := by
  obtain ⟨n,a,ha,_,he⟩ := bounded_rectangles ν f (measurable f) (bound f)
    (bound f).coe_nonneg (norm_le_bound f) ε hε
  let h : Func (X×Y) := ⟨fun z => a (pairCode n z),
    (measurable_of_countable a).comp (measurable_pairCode n), 2*bound f,
    fun z => by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using ha (pairCode n z)⟩
  refine ⟨h, tensor_code_finite n a h (fun _ => rfl), ?_⟩
  have hh : ‖l2 ν (f-h)‖^2 < ε^2 := by
    rw [norm_l2_sq]
    exact he
  nlinarith [norm_nonneg (l2 ν (f-h))]
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q) [IsProbabilityMeasure (μ.map q)]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
include hqcov in
lemma pairVanishing_of_covariance (M : Amenable.Mean G)
    (hc : ∀ (φ : G →+ G), Function.Surjective φ → ∀ v w : Func X,
      Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0) : PairVanishing μ q hq M := by
  intro φ hs v w hw
  have he0 : l2 μ (project μ q hq w) = l2 μ 0 := hw.trans (map_zero _).symm
  have hp : project μ q hq w =ᵐ[μ] (0 : Func X) := (l2_eq_iff μ _ _).mp he0
  have he (g : G) : covariance μ q φ v w g =ᵐ[μ.map q] conditional μ q (v*act (φ g) w) := by
    apply (covariance_center μ q hq hqcov φ v w g).trans
    apply conditional_congr μ q hq
    filter_upwards [(measurePreserving_vadd (φ g) μ).quasiMeasurePreserving.ae hp] with x hx
    change v x * (w (φ g +ᵥ x) - project μ q hq w (φ g +ᵥ x)) = v x*w (φ g +ᵥ x)
    change project μ q hq w (φ g +ᵥ x) = 0 at hx
    rw [hx, sub_zero]
  have hmean := hc φ hs v w
  have hnorm : Family.meanNorm (μ.map q) M (covariance μ q φ v w) =
      Family.meanNorm (μ.map q) M (Family.conditional μ q (Family.const v * Family.orbit φ w)) :=
    Family.meanNorm_congr _ _ he
  rw [hnorm] at hmean
  have hseq : Family.toL2 (μ.map q) (Family.conditional μ q (Family.const v * Family.orbit φ w)) =
      pairSequence μ q hq φ v w := by ext g; rfl
  unfold Family.meanNorm at hmean
  rwa [hseq] at hmean
end

variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))

omit [TopologicalSpace G] [DiscreteTopology G] [VAddInvariantMeasure G X μ]
  [StandardBorelSpace Y] [Nonempty Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y] in
include hqcov in
lemma square_equivariant (g : G) :
    (fun z => (q ∘ Prod.fst) (g +ᵥ z)) =ᵐ[RelativeProduct.law μ q hq]
      (fun z => g +ᵥ (q ∘ Prod.fst) z) := by
  have hp : MeasurePreserving Prod.fst (RelativeProduct.law μ q hq) μ :=
    ⟨measurable_fst, Measure.fst_compProd μ ((condDistrib id q μ).comap q hq)⟩
  exact hp.quasiMeasurePreserving.ae (hqcov g)

variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma covariance_finiteTensor_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (v w : Func (X×X))
    (hv : FiniteTensor v) (hw : FiniteTensor w) :
    Family.meanNorm (μ.map q) M
      (covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ v w) = 0 := by
  induction hv with
  | tensor a₁ a₂ =>
    induction hw with
    | tensor b₁ b₂ => exact covariance_tensor_mean_zero μ q hq hqcov M hp φ hs a₁ a₂ b₁ b₂
    | add _ _ ih₁ ih₂ =>
      rw [covariance_add_right]
      exact Family.meanNorm_add_zero _ _ ih₁ ih₂
  | add _ _ ih₁ ih₂ =>
    rw [covariance_add_left]
    exact Family.meanNorm_add_zero _ _ ih₁ ih₂

include hqcov in
lemma square_pairVanishing (M : Amenable.Mean G) (hp : PairVanishing μ q hq M) :
    PairVanishing (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (hq.comp measurable_fst) M := by
  have : VAddInvariantMeasure G (X×X) (RelativeProduct.law μ q hq) :=
    RelativeProduct.law_invariant_add μ q hq (fun g => measurePreserving_vadd g μ) hqcov
  have : IsProbabilityMeasure ((RelativeProduct.law μ q hq).map (q ∘ Prod.fst)) := by
    rw [RelativeProduct.law_map_base μ q hq]
    infer_instance
  apply pairVanishing_of_covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
  intro φ hs v w
  apply covariance_zero_of_dense (RelativeProduct.law μ q hq) (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
    {f | FiniteTensor f} (fun f ε hε => finiteTensor_dense _ f ε hε) φ _ v w
  intro v hv w hw
  simpa only [RelativeProduct.law_map_base μ q hq] using
    covariance_finiteTensor_mean_zero μ q hq hqcov M hp φ hs v w hv hw
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
lemma square_tensor_centered (f : Func X) (hf : l2 μ (project μ q hq f) = 0) :
    l2 (RelativeProduct.law μ q hq)
      (project (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (hq.comp measurable_fst)
        (tensor f (bmConj f))) = 0 := by
  have he : l2 (μ.map q) (conditional μ q f) = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_project_l2 μ q hq, hf, norm_zero]
  have hz : conditional μ q f =ᵐ[μ.map q] (0 : Func Y) := by
    apply (l2_eq_iff _ _ _).mp
    rw [he, map_zero]
  have ht : conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor f (bmConj f))
      =ᵐ[μ.map q] (0 : Func Y) := by
    filter_upwards [conditional_tensor μ q hq f (bmConj f), hz] with y hy hz
    rw [hy]
    change conditional μ q f y * _ = 0
    rw [hz, zero_apply, zero_mul]
  rw [← map_zero (l2 (RelativeProduct.law μ q hq))]
  apply (l2_eq_iff _ _ _).mpr
  have ht' : conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor f (bmConj f)) =ᵐ[(RelativeProduct.law μ q hq).map (q ∘ Prod.fst)] (0 : Func Y) := by
    simpa only [RelativeProduct.law_map_base μ q hq] using ht
  exact (ae_of_ae_map (hq.comp measurable_fst).aemeasurable ht').mono (fun z hz => hz)

variable {ι : Type*} [DecidableEq ι]
omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X]
  [Nonempty X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] in
lemma tensor_prod (s : Finset ι) (f h : ι → Func X) :
    tensor (∏ i∈s, f i) (∏ i∈s, h i) = ∏ i∈s, tensor (f i) (h i) := by
  induction s using Finset.induction_on with
  | empty => ext z; simp [tensor_apply]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, tensor_mul, ih]

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma centered_conditional_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (θ : G →+ G) (f : ι → Func X)
    (ha : Admissible s (fun i => θ + φ i))
    (hc : ∃ j∈s, l2 μ (project μ q hq (f j)) = 0) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i))) = 0 := by
  let ρ := RelativeProduct.law μ q hq
  have : VAddInvariantMeasure G (X×X) ρ :=
    RelativeProduct.law_invariant_add μ q hq (fun g => measurePreserving_vadd g μ) hqcov
  let t : ι → Func (X×X) := fun i => tensor (f i) (bmConj (f i))
  let F : Family G (X×X) := ∏ i∈s, Family.orbit (θ+φ i) (t i)
  have htc : ∃ j∈s, l2 ρ (project ρ (q ∘ Prod.fst) (hq.comp measurable_fst) (t j)) = 0 := by
    obtain ⟨j,hj,hf⟩ := hc
    exact ⟨j,hj,square_tensor_centered μ q hq (f j) hf⟩
  have hv : Family.avg ρ M F = 0 := avg_product_zero_of_pair ρ (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
    (square_pairVanishing μ q hq hqcov M hp) s (fun i => θ+φ i) t ha htc
  unfold Family.meanNorm
  apply M.norm_mean_zero_of_square
  have he : Amenable.Mean.squareNorm (Family.toL2 (μ.map q)
      (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i)))) =
      Amenable.Mean.pairing (Family.toL2 ρ F) (l2 ρ (1 : Func (X×X))) := by
    ext g
    simp only [Amenable.Mean.squareNorm_apply, Amenable.Mean.pairing_apply,
      Family.toL2_apply, Family.conditional_apply, Family.prod_apply, Family.orbit_apply]
    change ‖l2 (μ.map q) (conditional μ q (∏ i∈s, act (φ i g) (f i)))‖^2 =
      inner ℝ (l2 ρ (F g)) (l2 ρ (1 : Func (X×X)))
    have hF : F g = act (θ g) (tensor (∏ i∈s, act (φ i g) (f i))
        (bmConj (∏ i∈s, act (φ i g) (f i)))) := by
      dsimp only [F]
      rw [Family.prod_apply, conj_prod, tensor_prod, act_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← act_conj, tensor_act, ← act_add]
      rfl
    have hc1 : bmConj (1 : Func (X×X)) = 1 := by ext z; simp
    rw [hF, real_inner_comm, l2_inner, hc1, one_mul, integral_act,
      integral_tensor_self μ q hq]
    rfl
  rw [he, ← Family.avg_pair, hv, inner_zero_left]
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.AlgebraReplacement
variable {ι A : Type*} [DecidableEq ι] [CommRing A]
lemma prod_sub_prod (s : Finset ι) (f g : ι → A) :
    (∏ i∈s, f i) - (∏ i∈s, g i) = ∑ t∈s.powerset.erase ∅,
      (∏ i∈t, (f i-g i)) * ∏ i∈s\t, g i := by
  have he := Finset.prod_add (fun i => f i-g i) g s
  simp only [sub_add_cancel] at he
  rw [he]
  have hs := Finset.sum_erase_add s.powerset
    (fun t => (∏ i∈t, (f i-g i)) * ∏ i∈s\t, g i) (Finset.empty_mem_powerset s)
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul] at hs
  exact sub_eq_iff_eq_add.mpr hs.symm
end EuclideanFiveColor.AlgebraReplacement
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)
variable {ι : Type*} [DecidableEq ι]
omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace Y] [Nonempty Y] in
lemma Family.conditional_sum (s : Finset ι) (f : ι → Family G X) :
    Family.conditional μ q (∑ i∈s, f i) = ∑ i∈s, Family.conditional μ q (f i) := by
  induction s using Finset.induction_on with
  | empty => ext g y; simp [Family.conditional, conditional, expect]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Family.conditional_add, ih]

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma conditional_multiple_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (θ : G →+ G) (f : ι → Func X)
    (ha : Admissible s (fun i => θ + φ i)) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i)) -
      ∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) = 0 := by
  let a : ι → Family G X := fun i => Family.orbit (φ i) (f i)
  let b : ι → Family G X := fun i => Family.orbit (φ i) (project μ q hq (f i))
  have hb (g : G) : conditional μ q ((∏ i∈s, b i) g) =ᵐ[μ.map q]
      (∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) g := by
    simp only [Family.prod_apply, Family.orbit_apply]
    apply (conditional_congr μ q hq (f := ∏ i∈s, act (φ i g) (project μ q hq (f i)))
      (g := comp (∏ i∈s, act (φ i g) (conditional μ q (f i))) q hq) ?_).trans
      (conditional_lift μ q hq _)
    filter_upwards [prod_act_project_lift μ q hq hqcov s φ f g] with x hx
    simpa only [func_prod_apply, Finset.prod_apply] using hx
  have hrep : Family.meanNorm (μ.map q) M (Family.conditional μ q
      ((∏ i∈s, a i) - ∏ i∈s, b i)) = 0 := by
    rw [AlgebraReplacement.prod_sub_prod s a b, Family.conditional_sum]
    apply Family.meanNorm_sum_zero
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have htn : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    rw [AlgebraReplacement.mixed_prod s t hts]
    let w : ι → Func X := fun i => if i∈t then f i-project μ q hq (f i) else project μ q hq (f i)
    have he : (∏ i∈s, if i∈t then a i-b i else b i) = ∏ i∈s, Family.orbit (φ i) (w i) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hit : i∈t
      · simp only [hit, ↓reduceIte, w, a, b]
        apply Family.ext
        intro g
        exact (act_sub _ _ _).symm
      · simp only [hit, ↓reduceIte, w, b]
    rw [he]
    apply centered_conditional_mean_zero μ q hq hqcov M hp s φ θ w ha
    obtain ⟨j,hj⟩ := htn
    refine ⟨j,hts hj,?_⟩
    simp only [w, hj, ↓reduceIte]
    exact center_project_l2 μ q hq (f j)
  rw [Family.conditional_sub] at hrep
  rw [Family.meanNorm_congr (μ.map q) M (F := Family.conditional μ q (∏ i∈s, a i) -
      Family.conditional μ q (∏ i∈s, b i)) (H := Family.conditional μ q (∏ i∈s, a i) -
      ∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) (fun g => by
        filter_upwards [hb g] with y hy
        simp only [Family.sub_apply, sub_apply, Family.conditional_apply]
        rw [hy])] at hrep
  exact hrep
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G : Type*} [AddCommGroup G]
lemma scaleHom_add (n m : ℤ) : scaleHom (G := G) (n+m) = scaleHom n + scaleHom m := add_smul _ _ _
lemma scaleHom_sub (n m : ℤ) : scaleHom (G := G) (n-m) = scaleHom n - scaleHom m := sub_smul _ _ _
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι] in
lemma shifted_admissible (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (s : Finset ι) (n : ι → ℤ) (hn : Set.InjOn n s) :
    ∃ m : ℤ, Admissible s (fun i => scaleHom (G := G) m + scaleHom (n i)) := by
  obtain ⟨m,hm⟩ := Infinite.exists_notMem_finset (s.image (fun i => -n i))
  refine ⟨m, ?_, ?_⟩
  · intro i hi
    dsimp only
    rw [← scaleHom_add]
    apply hdiv
    intro hz
    have he : m = -n i := eq_neg_of_add_eq_zero_left hz
    exact hm (Finset.mem_image.mpr ⟨i,hi,he.symm⟩)
  · intro i hi j hj hij
    have he : (scaleHom m + scaleHom (n i)) - (scaleHom m + scaleHom (n j)) =
        scaleHom (G := G) (n i-n j) := by rw [scaleHom_sub]; abel
    rw [he]
    apply hdiv
    exact sub_ne_zero.mpr (fun h => hij (hn hi hj h))
variable {X Y : Type*} [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma conditional_integer_multiple_mean_zero
    (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (n : ι → ℤ) (f : ι → Func X) (hn : Set.InjOn n s) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (scaleHom (n i)) (f i)) -
      ∏ i∈s, Family.orbit (scaleHom (n i)) (conditional μ q (f i))) = 0 := by
  obtain ⟨m,hm⟩ := shifted_admissible hdiv s n hn
  exact conditional_multiple_mean_zero μ q hq hqcov M hp s (fun i => scaleHom (n i)) (scaleHom m) f hm
end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Representations
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.instCountableRot _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
lemma rot_zsmul_surjective (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (EuclideanFiveColor.BoundedMeasurable.scaleHom (G := Rot) n) := by
  intro g
  obtain ⟨k,hk⟩ := K_pow_surjective n.natAbs (Int.natAbs_ne_zero.mpr hn) (rotMul g)
  rcases n with n | n
  · refine ⟨mulRot k, ?_⟩
    change Additive.ofMul (k^n) = g
    exact congrArg mulRot hk
  · refine ⟨mulRot k⁻¹, ?_⟩
    change Additive.ofMul (k⁻¹ ^ (Int.negSucc n)) = g
    have he : k⁻¹ ^ (Int.negSucc n) = k^(n+1) := by simp
    rw [he]
    exact congrArg mulRot hk
end PlaneFiveColor.Spectral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Energy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.Spectral.instCountableRot _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BoundedContinuousFunction
open Filter Topology
namespace EuclideanFiveColor.MovingMean

open PlaneFiveColor.InvariantMean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
attribute [local instance] OAI.EuclideanFiveColor.MovingMean.instDecidableEq_solutions
lemma cube_le_of_support (L : List G) (n : ℕ) (f : G →ᵇ ℝ) (v : G) (c : ℝ)
    (hf : ∀ h ∈ cubeSupport L n, f (v+h) ≤ c) : cube L n f v ≤ c := by
  induction L generalizing v with
  | nil => simpa [cubeSupport, cube] using hf 0 (by simp [cubeSupport])
  | cons g L ih =>
    rw [cube, single_apply]
    have hb : ∑ k ∈ Finset.range (n+1), cube L n f (v+k • g) ≤ (n+1 : ℕ) * c := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (n+1), c := Finset.sum_le_sum fun k hk =>
          ih _ (by
            intro h hh
            have hm : k • g+h ∈ cubeSupport (g::L) n := by
              apply Finset.mem_biUnion.mpr
              exact ⟨k, hk, Finset.mem_image.mpr ⟨h,hh,rfl⟩⟩
            simpa only [add_assoc] using hf _ hm)
        _ = _ := by simp
    calc
      _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * ((n+1 : ℕ) * c) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = c := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- If every invariant mean gives a bounded function a value above c, its
strict c-superlevel set has finitely many translates covering the group. -/
lemma syndetic_of_all_means (f : G →ᵇ ℝ) (c : ℝ)
    (hf : ∀ M : Amenable.Mean G, c < M.map f) :
    ∃ S : Finset G, ∀ v : G, ∃ s ∈ S, c < f (v+s) := by
  classical
  by_contra hn
  push Not at hn
  choose b hb using (fun i : Finset G × ℕ => hn (cubeSupport i.1.toList i.2))
  have hle : meanAt b f ≤ c := by
    apply le_of_tendsto (tendsto_approx b f)
    apply Filter.Eventually.of_forall
    intro i
    exact cube_le_of_support _ _ _ _ _ (hb i)
  exact (not_lt_of_ge hle) (hf (toMean b))
end EuclideanFiveColor.MovingMean
end

section
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]
namespace Family
lemma energy_mean_eq_of_meanNorm_zero (M : Amenable.Mean G) (F H : Family G X)
    (he : meanNorm μ M (F-H) = 0) : M.map (energy μ F) = M.map (energy μ H) := by
  have hb : |M.map (energy μ F - energy μ H)| ≤
      M.map (((bound F : ℝ)+(bound H : ℝ)) • Amenable.Mean.normFn (toL2 μ (F-H))) := by
    apply M.abs_le
    intro g
    simp only [BoundedContinuousFunction.sub_apply, energy_apply,
      BoundedContinuousFunction.smul_apply, Amenable.Mean.normFn_apply, toL2_apply,
      sub_apply, smul_eq_mul]
    rw [map_sub]
    have hn := abs_norm_sub_norm_le (l2 μ (F g)) (l2 μ (H g))
    have hF := l2_norm_le μ (F g) (F.norm_le_bound g)
    have hH := l2_norm_le μ (H g) (H.norm_le_bound g)
    calc
      _ = |‖l2 μ (F g)‖-‖l2 μ (H g)‖| * (‖l2 μ (F g)‖+‖l2 μ (H g)‖) := by
        have heq : ‖l2 μ (F g)‖^2 - ‖l2 μ (H g)‖^2 =
            (‖l2 μ (F g)‖-‖l2 μ (H g)‖) * (‖l2 μ (F g)‖+‖l2 μ (H g)‖) := by ring
        rw [heq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      _ ≤ ‖l2 μ (F g)-l2 μ (H g)‖ * ((bound F : ℝ)+bound H) :=
        mul_le_mul hn (add_le_add hF hH) (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  rw [map_sub, map_smul] at hb
  change |M.map (energy μ F) - M.map (energy μ H)| ≤ _ * meanNorm μ M (F-H) at hb
  rw [he, mul_zero] at hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
lemma avg_const (M : Amenable.Mean G) (f : Func X) :
    avg μ M (const (G := G) f) = l2 μ f := by
  apply ext_inner_right ℝ
  intro v
  rw [avg_pair]
  have he : Amenable.Mean.pairing (toL2 μ (const (G := G) f)) v =
      BoundedContinuousFunction.const G (inner ℝ (l2 μ f) v) := rfl
  rw [he, M.map_const]
end Family

lemma integral_normSquare (f : Func X) : ∫ x, normSquare f x ∂μ = (‖l2 μ f‖^2 : ℝ) := by
  simp only [normSquare_apply, norm_l2_sq, integral_complex_ofReal]
lemma inner_normSquare (f h : Func X) :
    inner ℝ (l2 μ (normSquare f)) (l2 μ (normSquare h)) = ‖l2 μ (f*h)‖^2 := by
  rw [inner_l2, norm_l2_sq]
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [normSquare_apply, Complex.inner, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
      mul_apply, norm_mul]
    ring

variable [AddAction G X] [MeasurableConstVAdd G X] [ErgodicVAdd G X μ]
lemma avg_orbit_const (M : Amenable.Mean G) (φ : G →+ G) (hs : Function.Surjective φ) (f : Func X) :
    Family.avg μ M (Family.orbit φ f) = l2 μ (algebraMap ℂ (Func X) (∫ x, f x ∂μ)) := by
  let c : Func X := algebraMap ℂ (Func X) (∫ x, f x ∂μ)
  have hc : ∫ x, l2 μ (f-c) x ∂μ = 0 := by
    rw [integral_l2]
    change ∫ x, f x-c x ∂μ = 0
    rw [integral_sub (integrable μ f) (integrable μ c)]
    change (∫ x, f x ∂μ) - (∫ _x : X, (∫ x, f x ∂μ) ∂μ) = 0
    simp
  have hv := Amenable.Koopman.vector_orbit_hom_zero μ M φ hs (l2 μ (f-c)) hc
  have he : Family.avg μ M (Family.orbit φ (f-c)) =
      M.vector (Amenable.Mean.orbit (fun g => Amenable.Koopman.action μ (φ g)) (l2 μ (f-c))) := by
    congr 1
  rw [← he] at hv
  have ho : Family.orbit φ (f-c) = Family.orbit φ f - Family.const c := by
    ext g x
    rfl
  rw [ho, (Family.avg μ M).map_sub, Family.avg_const] at hv
  exact sub_eq_zero.mp hv

lemma pair_energy_mean (M : Amenable.Mean G) (φ : G →+ G) (hs : Function.Surjective φ) (f h : Func X) :
    M.map (Family.energy μ (Family.const f * Family.orbit φ h)) = ‖l2 μ f‖^2 * ‖l2 μ h‖^2 := by
  have he : Family.energy μ (Family.const f * Family.orbit φ h) =
      Amenable.Mean.pairing (Family.toL2 μ (Family.orbit φ (normSquare h))) (l2 μ (normSquare f)) := by
    ext g
    rw [Family.energy_apply, Amenable.Mean.pairing_apply, Family.toL2_apply]
    change ‖l2 μ (f*act (φ g) h)‖^2 = inner ℝ (l2 μ (act (φ g) (normSquare h))) (l2 μ (normSquare f))
    rw [real_inner_comm]
    exact (inner_normSquare μ f (act (φ g) h)).symm
  rw [he, ← Family.avg_pair, avg_orbit_const μ M φ hs]
  rw [integral_normSquare]
  rw [inner_l2]
  calc
    _ = ∫ x, ‖l2 μ h‖^2 * ‖f x‖^2 ∂μ := by
      apply integral_congr_ae
      exact .of_forall fun x => by
        change inner ℝ ((‖l2 μ h‖^2 : ℝ) : ℂ) (normSquare f x) = _
        rw [normSquare_apply]
        simp only [Complex.inner, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
    _ = _ := by rw [integral_const_mul, ← norm_l2_sq]; ring
end

variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma energy_two_orbits (φ θ : G →+ G) (f h : Func X) :
    Family.energy μ (Family.orbit φ f * Family.orbit θ h) =
      Family.energy μ (Family.const f * Family.orbit (θ-φ) h) := by
  ext g
  rw [Family.energy_apply, Family.energy_apply]
  have he : act (φ g) f * act (θ g) h = act (φ g) (f * act ((θ-φ) g) h) := by
    ext x
    simp only [mul_apply, act_apply, AddMonoidHom.sub_apply, ← add_vadd]
    congr 2
    abel_nf
  change ‖l2 μ (act (φ g) f * act (θ g) h)‖^2 = _
  rw [he, l2_act]
  simp
omit [VAddInvariantMeasure G X μ]
variable [ErgodicVAdd G X μ]
lemma two_orbit_energy_mean (M : Amenable.Mean G) (φ θ : G →+ G)
    (hs : Function.Surjective (θ-φ)) (f h : Func X) :
    M.map (Family.energy μ (Family.orbit φ f * Family.orbit θ h)) = ‖l2 μ f‖^2 * ‖l2 μ h‖^2 := by
  rw [energy_two_orbits]
  exact pair_energy_mean μ M (θ-φ) hs f h
end EuclideanFiveColor.BoundedMeasurable
end

section
open MeasureTheory Filter
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  (q : X → Y) (hq : Measurable q)
  (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [IsProbabilityMeasure μ] in
include hq hqcov in
lemma factor_ergodic : ErgodicVAdd G Y (μ.map q) := by
  have hp (g : G) : MeasurePreserving (fun y : Y => g +ᵥ y) (μ.map q) (μ.map q) := by
    refine ⟨measurable_const_vadd _, ?_⟩
    rw [Measure.map_map (measurable_const_vadd _) hq]
    calc
      _ = μ.map (q ∘ (fun x => g +ᵥ x)) := Measure.map_congr (hqcov g).symm
      _ = _ := by rw [← Measure.map_map hq (measurable_const_vadd _), (measurePreserving_vadd g μ).map_eq]
  have : VAddInvariantMeasure G Y (μ.map q) := ⟨fun g s hs => (hp g).measure_preimage hs.nullMeasurableSet⟩
  constructor
  intro s hs hinv
  have hc : EventuallyConst (q ⁻¹' s) (ae μ) := by
    apply ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := G) (hs.preimage hq)
    intro g
    filter_upwards [ae_of_ae_map hq.aemeasurable (hinv g), hqcov g] with x hx he
    change (q (g +ᵥ x) ∈ s) = (q x ∈ s)
    rw [he]
    exact hx
  rw [eventuallyConst_set] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl ((ae_map_iff hq.aemeasurable hs).mpr hc)
  · exact Or.inr ((ae_map_iff hq.aemeasurable hs.compl).mpr hc)
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  (q : X → Y) (hq : Measurable q)
  (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
variable [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]
include hq hqcov in
lemma conditional_integer_pair_energy
    (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (M : Amenable.Mean G) {n m : ℤ} (hnm : n ≠ m) (f h : Func X) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q
      (Family.orbit (scaleHom n) f * Family.orbit (scaleHom m) h))) =
      ‖l2 (μ.map q) (conditional μ q f)‖^2 * ‖l2 (μ.map q) (conditional μ q h)‖^2 := by
  have : ErgodicVAdd G Y (μ.map q) := factor_ergodic μ q hq hqcov
  have hp := pairVanishing_of_ergodic μ q hq M
  have hn : Set.InjOn (![n,m]) (Finset.univ : Finset (Fin 2)) := by
    intro i _ j _ he
    fin_cases i <;> fin_cases j <;> simp_all
  have he := conditional_integer_multiple_mean_zero μ q hq hqcov hdiv M hp
    Finset.univ ![n,m] ![f,h] hn
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  rw [Family.energy_mean_eq_of_meanNorm_zero (μ.map q) M _ _ he]
  apply two_orbit_energy_mean
  rw [← scaleHom_sub]
  exact hdiv _ (sub_ne_zero.mpr hnm.symm)
end EuclideanFiveColor.BoundedMeasurable
end

open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

lemma char_add (z w : E) : char (z+w) = char z * char w := by
  ext d
  exact congrArg (fun a : Circle => (a : ℂ)) (eval_add z w d)
lemma char_act (g : Rot) (z : E) : act g (char z) = char (kCoeff (rotMul g)*z) := rfl

variable {Y : Type*} [MeasurableSpace Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] (q : D → Y)
variable (hq : Measurable q)
include hq in
lemma projectedMass_zero : projectedMass μ q 0 = 1 := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  have he : conditional μ q (char 0) = 1 := by
    ext y
    change (∫ d, char 0 d ∂condDistrib id q μ y) = 1
    simp
  unfold projectedMass
  rw [he, norm_l2_sq]
  simp

variable [MulAction K Y] [MeasurableConstSMul K Y] [SMulInvariantMeasure K D μ]
variable (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
include hq hqcov in
lemma projectedMass_rotation (u : K) (z : E) :
    projectedMass μ q (kCoeff u*z) = projectedMass μ q z := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  unfold projectedMass
  rw [← norm_project_l2 μ q hq, ← norm_project_l2 μ q hq]
  have hchar : char (kCoeff u*z) = act (mulRot u) (char z) := rfl
  rw [hchar]
  have he := (l2_eq_iff μ _ _).mpr (project_act μ q hq (fun g : Rot => hqcov (rotMul g)) (mulRot u) (char z))
  rw [he, l2_act]
  simp
include hq hqcov in
lemma projectedMass_radial {z w : E} (hn : ‖(z : ℂ)‖ = ‖(w : ℂ)‖) :
    projectedMass μ q z = projectedMass μ q w := by
  by_cases hw : w = 0
  · have hz : z = 0 := by
      apply Subtype.ext
      apply norm_eq_zero.mp
      simpa [hw] using hn
    rw [hz, hw]
  have hwc : (w : ℂ) ≠ 0 := fun h => hw (Subtype.ext h)
  let c : Circle := ⟨(z : ℂ)/(w : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hwc)])⟩
  let u : K := ⟨c, mem_algebraicClosure_iff.mp (div_mem z.property w.property)⟩
  have he : kCoeff u * w = z := by
    apply Subtype.ext
    exact div_mul_cancel₀ _ hwc
  rw [← he]
  exact projectedMass_rotation μ q hq hqcov u w
end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_NumberFields
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma minpoly_reverse_eval_ne_zero (b : L) (hb : IsAlgebraic ℚ b) (t : ℚ)
    (ht : 1-b*algebraMap ℚ L t ≠ 0) : (minpoly ℚ b).reverse.eval t ≠ 0 := by
  intro hz
  by_cases ht0 : t = 0
  · subst t
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, (minpoly.monic hb.isIntegral).leadingCoeff] at hz
    exact one_ne_zero hz
  let : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht0)
  have hp : (minpoly ℚ b).IsRoot t⁻¹ := by
    have he := (eval₂_reverse_eq_zero_iff (RingHom.id ℚ) t⁻¹ (minpoly ℚ b))
    simp only [invOf_eq_inv, inv_inv, eval₂_id] at he
    exact he.mp hz
  have he := minpoly.root hb.isIntegral hp
  apply ht
  rw [← he, ← map_mul, inv_mul_cancel₀ ht0, map_one, sub_self]

/-- A scalar-rational common denominator for an algebraic linear reciprocal. -/
lemma reciprocal_denominator (b : L) (hb : IsAlgebraic ℚ b) :
    ∃ (P : ℚ[X]) (R : L[X]), P.coeff 0 = 1 ∧
      (1-C b*X)*R = P.map (algebraMap ℚ L) ∧
      ∀ t : ℚ, 1-b*algebraMap ℚ L t ≠ 0 → P.eval t ≠ 0 := by
  by_cases hb0 : b = 0
  · subst b
    exact ⟨1,1,by simp,by simp,by simp⟩
  let p := minpoly ℚ b
  have hm : p.Monic := minpoly.monic hb.isIntegral
  let : Invertible b := invertibleOfNonzero hb0
  have hz : (p.reverse.map (algebraMap ℚ L)).IsRoot b⁻¹ := by
    rw [IsRoot, eval_map]
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℚ L) b p).mpr (minpoly.aeval ℚ b)
    simpa only [invOf_eq_inv] using h
  obtain ⟨R,hR⟩ := (dvd_iff_isRoot.mpr hz)
  refine ⟨p.reverse,C (-b⁻¹)*R,?_,?_,minpoly_reverse_eval_ne_zero b hb⟩
  · rw [coeff_zero_reverse, hm.leadingCoeff]
  · calc
      _ = (X-C b⁻¹)*R := by
        have he : (1-C b*X)*C (-b⁻¹) = X-C b⁻¹ := by
          have hc : C b*C b⁻¹ = (1 : L[X]) := by rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
          rw [map_neg]
          calc
            _ = (C b*C b⁻¹)*X-C b⁻¹ := by ring
            _ = _ := by rw [hc, one_mul]
        rw [← mul_assoc, he]
      _ = _ := hR.symm

lemma polyLinear_add (ℓ : L →ₗ[ℚ] ℚ) (p q : L[X]) :
    polyLinear ℓ (p+q) = polyLinear ℓ p + polyLinear ℓ q := by
  ext n
  simp only [coeff_polyLinear, coeff_add, map_add]
lemma polyLinear_monomial (ℓ : L →ₗ[ℚ] ℚ) (n : ℕ) (a : L) :
    polyLinear ℓ (monomial n a) = monomial n (ℓ a) := by
  ext k
  simp only [coeff_polyLinear, coeff_monomial]
  split_ifs <;> simp
lemma eval_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (t : ℚ) :
    (polyLinear ℓ p).eval t = ℓ (p.eval (algebraMap ℚ L t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [polyLinear_add, eval_add, hp, hq, map_add]
  | monomial n a =>
    rw [polyLinear_monomial, eval_monomial, eval_monomial]
    have he : a*(algebraMap ℚ L t)^n = (t^n) • a := by
      rw [Algebra.smul_def, map_pow, mul_comm]
    rw [he, map_smul]
    exact mul_comm _ _

lemma polyLinear_eq_zero_iff (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) :
    polyLinear ℓ p = 0 ↔ ∀ t : ℚ, ℓ (p.eval (algebraMap ℚ L t)) = 0 := by
  simp_rw [← eval_polyLinear]
  exact ⟨fun he _ => by rw [he, eval_zero], fun h => Polynomial.funext fun t => by simpa using h t⟩

/-- The first three formal coefficients of the Cayley curve force annihilation
of 1, b and b². No analytic continuity is used. -/
lemma cayley_annihilation (b : L) (hb : IsAlgebraic ℚ b) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, 1-b*(algebraMap ℚ L t) ≠ 0)
    (h : ∀ t : ℚ, ℓ ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) = 0) :
    ℓ 1 = 0 ∧ ℓ b = 0 ∧ ℓ (b^2) = 0 := by
  obtain ⟨P,R,hP,hR,_hPreg⟩ := reciprocal_denominator b hb
  have hR' : R-(C b*R)*X = P.map (algebraMap ℚ L) := by
    convert hR using 1
    all_goals try with_reducible_and_instances rfl
    ring
  let T := R+(C b*R)*X
  have hT : polyLinear ℓ T = 0 := by
    apply (polyLinear_eq_zero_iff ℓ T).mpr
    intro t
    have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
    have he : T.eval (algebraMap ℚ L t) =
        (P.eval t) • ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) := by
      dsimp only [T]
      simp only [eval_add, eval_mul, eval_C, eval_X, Algebra.smul_def]
      rw [← hRt]
      rw [← mul_div_assoc, eq_div_iff (hd t)]
      ring
    rw [he, map_smul, h t, smul_zero]
  have h0 : R.coeff 0 = 1 := by
    have he := congrArg (fun p : L[X] => p.coeff 0) hR'
    simpa only [coeff_sub, coeff_mul_X_zero, sub_zero, coeff_map, hP, map_one] using he
  have h1 : R.coeff 1-b = algebraMap ℚ L (P.coeff 1) := by
    have he := congrArg (fun p : L[X] => p.coeff 1) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, h0, mul_one, coeff_map] using he
  have h2 : R.coeff 2-b*R.coeff 1 = algebraMap ℚ L (P.coeff 2) := by
    have he := congrArg (fun p : L[X] => p.coeff 2) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, coeff_map] using he
  have ht0 : ℓ 1 = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 0) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X_zero, add_zero, h0, coeff_zero] using he
  have ht1 : ℓ (R.coeff 1) + ℓ b = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 1) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul, h0, mul_one,
      map_add, coeff_zero] using he
  have ht2 : ℓ (R.coeff 2) + ℓ (b*R.coeff 1) = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul,
      map_add, coeff_zero] using he
  have hlQ (c : ℚ) : ℓ (algebraMap ℚ L c) = 0 := by
    have he : algebraMap ℚ L c = c • (1:L) := by rw [Algebra.smul_def, mul_one]
    rw [he, map_smul, ht0, smul_zero]
  have hh1 := congrArg ℓ h1
  rw [map_sub, hlQ] at hh1
  have hb0 : ℓ b = 0 := by linarith
  have hh2 := congrArg ℓ h2
  rw [map_sub, hlQ] at hh2
  have hbR : ℓ (b*R.coeff 1) = 0 := by linarith
  have hR1 : R.coeff 1 = algebraMap ℚ L (P.coeff 1)+b := sub_eq_iff_eq_add.mp h1
  rw [hR1, mul_add, map_add] at hbR
  have he : b*algebraMap ℚ L (P.coeff 1) = (P.coeff 1) • b := by
    rw [Algebra.smul_def, mul_comm]
  rw [he, map_smul, hb0, smul_zero, zero_add, ← sq] at hbR
  exact ⟨ht0,hb0,hbR⟩

end EuclideanFiveColor.AlgebraicCayley

end

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma linearFraction_polynomials (a b c d : L) (hc : c ≠ 0)
    (hb : IsAlgebraic ℚ (-d/c)) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, c+d*algebraMap ℚ L t ≠ 0) :
    ∃ P Q : ℚ[X], ∀ t : ℚ, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t * ℓ ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
  obtain ⟨Q,R,hQ,hR,hQreg⟩ := reciprocal_denominator (-d/c) hb
  clear hQ
  have hdn (t : ℚ) : 1-(-d/c)*algebraMap ℚ L t ≠ 0 := by
    intro hh
    apply hd t
    have he : c+d*algebraMap ℚ L t = c*(1-(-d/c)*algebraMap ℚ L t) := by
      field_simp
      ring
    rw [he, hh, mul_zero]
  let U : L[X] := (C (a/c)+C (b/c)*X)*R
  refine ⟨polyLinear ℓ U,Q,fun t => ⟨hQreg t (hdn t),?_⟩⟩
  rw [eval_polyLinear]
  have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
  simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
  have he : U.eval (algebraMap ℚ L t) =
      (Q.eval t) • ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
    dsimp only [U]
    simp only [eval_mul, eval_add, eval_C, eval_X, Algebra.smul_def]
    rw [← hRt, ← mul_div_assoc, eq_div_iff (hd t)]
    field_simp
    ring
  rw [he, map_smul, smul_eq_mul]

/-- Finite simultaneous avoidance for rational functions with no rational poles. -/
lemma rational_functions_avoid {ι : Type*} (s : Finset ι) (f : ι → ℚ → ℚ)
    (hpoly : ∀ i ∈ s, ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧ P.eval t = Q.eval t*f i t)
    (hn : ∀ i ∈ s, ∃ t, f i t ≠ 0) :
    ∃ t, ∀ i ∈ s, f i t ≠ 0 := by
  classical
  choose P Q hQ using fun i : s => hpoly i i.property
  have hP (i : s) : P i ≠ 0 := by
    obtain ⟨t,ht⟩ := hn i i.property
    intro he
    have hh := (hQ i t).2
    rw [he, eval_zero] at hh
    exact mul_ne_zero (hQ i t).1 ht hh.symm
  have hz : (∏ i : s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => hP _)
  obtain ⟨t,ht⟩ : ∃ t : ℚ, (∏ i : s, P i).eval t ≠ 0 := by
    by_contra! hn
    exact hz (Polynomial.funext fun t => by simpa using hn t)
  refine ⟨t,fun i hi hh => ?_⟩
  have hpt : (P ⟨i,hi⟩).eval t ≠ 0 := by
    rw [eval_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht _ (Finset.mem_univ _)
  apply hpt
  rw [(hQ ⟨i,hi⟩ t).2, hh, mul_zero]

/-- An affine-line rational curve escaping each hyperplane also escapes their finite union. -/
lemma finite_hyperplanes_avoid {T : Type*} [Nonempty T]
    (f : T → L) (line : T → T → ℚ → T)
    (hzero : ∀ a b, line a b 0 = a) (hone : ∀ a b, line a b 1 = b)
    (hline : ∀ a b (ℓ : L →ₗ[ℚ] ℚ), ∃ P Q : ℚ[X], ∀ t,
      Q.eval t ≠ 0 ∧ P.eval t = Q.eval t * ℓ (f (line a b t)))
    (s : Finset (L →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ∃ t, ℓ (f t) ≠ 0) :
    ∃ t, ∀ ℓ ∈ s, ℓ (f t) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary T, by simp⟩
  | @insert ℓ s hℓ ih =>
    obtain ⟨a,ha⟩ := ih (fun ψ hψ => hs ψ (Finset.mem_insert_of_mem hψ))
    obtain ⟨b,hb⟩ := hs ℓ (Finset.mem_insert_self _ _)
    obtain ⟨t,ht⟩ := rational_functions_avoid (insert ℓ s)
      (fun ψ t => ψ (f (line a b t))) (fun ψ _ => hline a b ψ) (by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact ⟨1,by simpa only [hone] using hb⟩
        · exact ⟨0,by simpa only [hzero] using ha ψ hψ⟩)
    exact ⟨line a b t,ht⟩
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley
variable (N : IntermediateField ℚ ℂ)
variable (hi : Complex.I ∈ N)
lemma iN_sq : iN N hi ^2 = -1 := by ext; exact Complex.I_sq
lemma cayley_den_ne (a : realSlice N) : 1-iN N hi*asN N a ≠ 0 := by
  intro h
  have hh := congrArg (fun z : N => (z : ℂ).re) h
  simp [iN, asN] at hh

lemma cayley_real_norm (a : realSlice N) : ‖((realCayley N hi a : N) : ℂ)‖ = 1 := by
  change ‖(1+Complex.I*(a:ℝ))/(1-Complex.I*(a:ℝ))‖ = 1
  have hn : ‖(1+Complex.I*(a:ℝ))‖ = ‖(1-Complex.I*(a:ℝ))‖ := by
    have he : conj (1+Complex.I*(a:ℝ)) = 1-Complex.I*(a:ℝ) := by simp; ring
    rw [← he, Complex.norm_conj]
  rw [norm_div, hn, div_self]
  apply norm_ne_zero_iff.mpr
  intro hz
  have he := congrArg Complex.re hz
  simp at he

variable [FiniteDimensional ℚ N]
lemma cayley_functional_escape
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (ℓ : N →ₗ[ℚ] ℚ) (hℓ : ℓ ≠ 0) :
    ∃ a : realSlice N, ℓ (realCayley N hi a) ≠ 0 := by
  by_contra! hh
  have hx (a : realSlice N) : ℓ 1 = 0 ∧ ℓ (iN N hi*asN N a) = 0 ∧
      ℓ ((asN N a)^2) = 0 := by
    have he (t : ℚ) : asN N (a*algebraMap ℚ (realSlice N) t) =
        asN N a*algebraMap ℚ N t := by simp
    have hd (t : ℚ) : 1-(iN N hi*asN N a)*algebraMap ℚ N t ≠ 0 := by
      simpa only [he, mul_assoc] using cayley_den_ne N hi (a*algebraMap ℚ (realSlice N) t)
    have ha (t : ℚ) : ℓ ((1+(iN N hi*asN N a)*algebraMap ℚ N t)/
        (1-(iN N hi*asN N a)*algebraMap ℚ N t)) = 0 := by
      simpa only [realCayley, he, mul_assoc] using hh (a*algebraMap ℚ (realSlice N) t)
    obtain ⟨h1,hia,hsa⟩ := cayley_annihilation (iN N hi*asN N a)
      (Algebra.IsAlgebraic.isAlgebraic _) ℓ hd ha
    rw [mul_pow, iN_sq, neg_one_mul, map_neg, neg_eq_zero] at hsa
    exact ⟨h1,hia,hsa⟩
  have hreal (a : realSlice N) : ℓ (asN N a) = 0 := by
    have h1 := (hx (a+1)).2.2
    have h2 := (hx (a-1)).2.2
    have he : (asN N (a+1))^2-(asN N (a-1))^2 = (4:ℚ) • asN N a := by
      simp only [map_add, map_one, map_sub, Algebra.smul_def, map_ofNat]
      ring
    have hh := congrArg ℓ he
    rw [map_sub, h1,h2,sub_self,map_smul,smul_eq_mul] at hh
    linarith
  apply hℓ
  ext z
  let a : realSlice N := ⟨(z:ℂ).re,hre z⟩
  let b : realSlice N := ⟨(z:ℂ).im,him z⟩
  have he : z = asN N a+iN N hi*asN N b := by
    apply Subtype.ext
    change (z:ℂ) = (z:ℂ).re+Complex.I*(z:ℂ).im
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  rw [he,map_add,hreal,(hx b).2.1,add_zero]
  rfl

lemma cayley_line_polynomials (a b : realSlice N) (ℓ : N →ₗ[ℚ] ℚ) :
    ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t*ℓ (realCayley N hi (realLine N a b t)) := by
  let A := 1+iN N hi*asN N a
  let B := iN N hi*(asN N b-asN N a)
  let C := 1-iN N hi*asN N a
  let D := -iN N hi*(asN N b-asN N a)
  have he (t : ℚ) : asN N (realLine N a b t) =
      asN N a+algebraMap ℚ N t*(asN N b-asN N a) := by simp [realLine]
  have hd (t : ℚ) : C+D*algebraMap ℚ N t = 1-iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [C,D]; ring
  have hn (t : ℚ) : A+B*algebraMap ℚ N t = 1+iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [A,B]; ring
  obtain ⟨P,Q,hPQ⟩ := linearFraction_polynomials A B C D (cayley_den_ne N hi a)
    (Algebra.IsAlgebraic.isAlgebraic _) ℓ (fun t => by rw [hd]; exact cayley_den_ne N hi _)
  refine ⟨P,Q,fun t => ?_⟩
  simpa only [hn,hd,realCayley] using hPQ t

lemma cayley_finite_avoid
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (s : Finset (N →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ℓ ≠ 0) :
    ∃ a : realSlice N, ∀ ℓ ∈ s, ℓ (realCayley N hi a) ≠ 0 :=
  finite_hyperplanes_avoid (realCayley N hi) (realLine N)
    (realLine_zero N) (realLine_one N) (cayley_line_polynomials N hi) s
    (fun ℓ hℓ => cayley_functional_escape N hi hre him ℓ (hs ℓ hℓ))
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

omit [FiniteDimensional ℚ V] in
/-- Finite general-position sets from avoidance of finitely many proper subspaces. -/
lemma exists_general (A : Set V) (hd : 2 ≤ finrank ℚ V)
    (ha : ∀ P : Finset (Submodule ℚ V), (∀ p ∈ P, p < ⊤) →
      ∃ x ∈ A, ∀ p ∈ P, x ∉ p) (n : ℕ) :
    ∃ s : Finset V, s.card = n ∧ (s : Set V) ⊆ A ∧ General s := by
  classical
  induction n with
  | zero =>
    refine ⟨∅,rfl,by simp,?_⟩
    intro t ht _
    have : t = ∅ := Finset.subset_empty.mp ht
    simp [this, linearIndepOn_empty]
  | succ n ih =>
    obtain ⟨s,hs,hA,hg⟩ := ih
    let B := s.powerset.filter (fun t => t.card < finrank ℚ V)
    let P := B.image (fun t : Finset V => Submodule.span ℚ (t : Set V))
    have hP : ∀ p ∈ P, p < ⊤ := by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      have hc : t.card < finrank ℚ V := (Finset.mem_filter.mp ht).2
      apply Submodule.lt_top_of_finrank_lt_finrank
      exact (finrank_span_finset_le_card t).trans_lt hc
    obtain ⟨x,hx,havoid⟩ := ha P hP
    have havo (t : Finset V) (ht : t ⊆ s) (hc : t.card < finrank ℚ V) :
        x ∉ Submodule.span ℚ (t : Set V) := by
      apply havoid _
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ht,hc⟩,rfl⟩
    have hxs : x ∉ s := by
      intro hh
      exact havo {x} (Finset.singleton_subset_iff.mpr hh) (by simpa only [Finset.card_singleton] using (show 1 < finrank ℚ V by omega))
        (Submodule.subset_span (by simp))
    refine ⟨insert x s,by simp [hxs,hs],?_,?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hA hy
    · intro t ht hc
      by_cases hxt : x ∈ t
      · have hts : t.erase x ⊆ s := by
          intro y hy
          obtain ⟨hyx,hyt⟩ := Finset.mem_erase.mp hy
          exact (Finset.mem_insert.mp (ht hyt)).resolve_left hyx
        have hct : (t.erase x).card < finrank ℚ V := by
          rw [Finset.card_erase_of_mem hxt]
          have hp := Finset.card_pos.mpr ⟨x,hxt⟩
          omega
        have hli := hg (t.erase x) hts hct.le
        have hn := havo (t.erase x) hts hct
        have hh := (linearIndepOn_id_insert (K := ℚ) (by simp : x ∉ (t.erase x : Set V))).mpr ⟨hli,hn⟩
        simpa only [← Finset.coe_insert, Finset.insert_erase hxt] using hh
      · exact hg t (by
          intro y hy
          exact (Finset.mem_insert.mp (ht hy)).resolve_left (fun he => hxt (he ▸ hy))) hc

lemma General.spans {s t : Finset V} (hs : General s) (ht : t ⊆ s)
    (hc : t.card = finrank ℚ V) : Submodule.span ℚ (t : Set V) = ⊤ := by
  have hli := hs t ht hc.le
  have hr : finrank ℚ (Submodule.span ℚ (t : Set V)) = finrank ℚ V :=
    (finrank_span_finset_eq_card hli).trans hc
  exact Submodule.eq_top_of_finrank_eq hr

end EuclideanFiveColor.GeneralPosition
end

noncomputable section
open Module
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley

lemma generatedField_I (s : Finset ℂ) : Complex.I ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp [generatingSet]
lemma generatedField_real (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.re : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩))
lemma generatedField_imag (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.im : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
lemma generatedField_contains (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) : z ∈ generatedField s := by
  rw [← Complex.re_add_im z]
  exact (generatedField s).add_mem (generatedField_real s z hz)
    ((generatedField s).mul_mem (generatedField_imag s z hz) (generatedField_I s))
lemma generatedField_conj (s : Finset ℂ) {z : ℂ} (hz : z ∈ generatedField s) :
    conj z ∈ generatedField s := by
  induction hz using IntermediateField.adjoin_induction ℚ with
  | mem z hz =>
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have : z = Complex.I := Finset.mem_singleton.mp hz
        rw [this,Complex.conj_I]
        exact (generatedField s).neg_mem (generatedField_I s)
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa using generatedField_real s w hw
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      simpa using generatedField_imag s w hw
  | algebraMap r => simp
  | add x y hx hy ihx ihy => simpa using (generatedField s).add_mem ihx ihy
  | inv x hx ihx => simpa using (generatedField s).inv_mem ihx
  | mul x y hx hy ihx ihy => simpa using (generatedField s).mul_mem ihx ihy
lemma generatedField_re_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).re : ℂ) ∈ generatedField s := by
  rw [Complex.re_eq_add_conj]
  exact (generatedField s).div_mem ((generatedField s).add_mem z.property
    (generatedField_conj s z.property)) (by norm_cast; exact (generatedField s).natCast_mem 2)
lemma generatedField_im_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).im : ℂ) ∈ generatedField s := by
  rw [Complex.im_eq_sub_conj]
  exact (generatedField s).div_mem ((generatedField s).sub_mem z.property
    (generatedField_conj s z.property)) ((generatedField s).mul_mem
      (by norm_cast; exact (generatedField s).natCast_mem 2) (generatedField_I s))

lemma generatedField_finite (s : Finset ℂ) (hs : ∀ z ∈ s, IsAlgebraic ℚ z) :
    FiniteDimensional ℚ (generatedField s) := by
  have hiAlg : IsAlgebraic ℚ Complex.I := IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]; exact isAlgebraic_one.neg)
  apply IntermediateField.finiteDimensional_adjoin
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_union.mp hz with hz | hz
    · have : z = Complex.I := Finset.mem_singleton.mp hz
      rw [this]
      exact hiAlg.isIntegral
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      rw [Complex.re_eq_add_conj, div_eq_mul_inv]
      exact ((hs w hw).add (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
        (hs w hw))).mul (isAlgebraic_natCast 2).inv |>.isIntegral
  · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    rw [Complex.im_eq_sub_conj, div_eq_mul_inv]
    exact ((hs w hw).sub (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
      (hs w hw))).mul ((isAlgebraic_natCast 2).mul hiAlg).inv |>.isIntegral

lemma finrank_ge_two (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) : 2 ≤ finrank ℚ N := by
  have hp : 0 < finrank ℚ N := finrank_pos
  by_contra! hh
  have he : finrank ℚ N = 1 := by omega
  obtain ⟨q,hq⟩ := (finrank_eq_one_iff_of_nonzero' (1:N) one_ne_zero).mp he (iN N hi)
  have hqc := congrArg (fun z : N => (z:ℂ).im) hq
  simp [iN,Algebra.smul_def] at hqc

lemma cayley_subspaces_avoid (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N)
    (P : Finset (Submodule ℚ N)) (hP : ∀ p ∈ P, p < ⊤) :
    ∃ x : N, ‖(x:ℂ)‖ = 1 ∧ ∀ p ∈ P, x ∉ p := by
  classical
  choose ℓ hn hker using fun p : P => Submodule.exists_le_ker_of_lt_top p.val (hP p p.property)
  let s : Finset (N →ₗ[ℚ] ℚ) := Finset.univ.image ℓ
  have hs : ∀ ψ ∈ s, ψ ≠ 0 := by
    intro ψ hψ
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hψ
    exact hn p
  obtain ⟨a,ha⟩ := cayley_finite_avoid N hi hre him s hs
  refine ⟨realCayley N hi a,cayley_real_norm N hi a,fun p hp hx => ?_⟩
  exact ha (ℓ ⟨p,hp⟩) (Finset.mem_image.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,rfl⟩) (hker ⟨p,hp⟩ hx)

lemma numberField_general_position (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N) (n : ℕ) :
    ∃ s : Finset N, s.card = n ∧ (∀ z ∈ s, ‖(z:ℂ)‖ = 1) ∧ GeneralPosition.General s := by
  obtain ⟨s,hs,hA,hg⟩ := GeneralPosition.exists_general {z : N | ‖(z:ℂ)‖ = 1}
    (finrank_ge_two N hi) (cayley_subspaces_avoid N hi hre him) n
  exact ⟨s,hs,hA,hg⟩
end EuclideanFiveColor.AlgebraicCayley
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Selections
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- A cover evaluated at a large general-position set contains a spanning monochromatic subset. -/
lemma spanning_selection {ι : Type*} (Q : Finset ι) (S : Finset V) (hS : General S)
    (hcard : Q.card*(finrank ℚ V-1) < S.card)
    (A : ι → V → Prop) (hA : ∀ x ∈ S, ∃ i ∈ Q, A i x) :
    ∃ i ∈ Q, ∃ T ⊆ S, T.card = finrank ℚ V ∧
      Submodule.span ℚ (T : Set V) = ⊤ ∧ ∀ x ∈ T, A i x := by
  classical
  choose f hfQ hfA using fun x : S => hA x x.property
  have hs : Fintype.card Q * (finrank ℚ V-1) < Fintype.card S := by simpa using hcard
  let g : S → Q := fun x => ⟨f x,hfQ x⟩
  obtain ⟨i,hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card g hs
  have hi' : finrank ℚ V ≤ (S.filter (fun x => A i x)).card := by
    have hx : (Finset.univ.filter (fun x : S => g x = i)).card ≤
        (S.filter (fun x => A i x)).card := by
      apply Finset.card_le_card_of_injOn (fun x : S => x.val)
      · intro x hx
        have hg : g x = i := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨x.property,by
          have hh := hfA x
          change A (g x).val x.val at hh
          rwa [hg] at hh⟩
      · intro x hx y hy hxy
        exact Subtype.ext hxy
    omega
  obtain ⟨T,hT,hTc⟩ := Finset.exists_subset_card_eq hi'
  have hTS : T ⊆ S := fun x hx => (Finset.mem_filter.mp (hT hx)).1
  exact ⟨i,i.property,T,hTS,hTc,hS.spans hTS hTc, fun x hx => (Finset.mem_filter.mp (hT hx)).2⟩
end EuclideanFiveColor.GeneralPosition
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma common_denominator {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : ι → ℤ, ∀ i, (D:ℚ)*c i = a i := by
  classical
  let D := ∏ i, (c i).den
  let a := fun i => ((∏ j ∈ Finset.univ.erase i, (c j).den : ℕ) : ℤ)*(c i).num
  refine ⟨D,Finset.prod_pos (fun _ _ => Rat.den_pos _),a,fun i => ?_⟩
  have hD : D = (∏ j ∈ Finset.univ.erase i, (c j).den)*(c i).den :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  rw [hD, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
  simp only [a, Int.cast_mul, Int.cast_natCast]

lemma uniform_integral_representations {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : ∀ i, κ i → V) (x y : V)
    (hx : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = x)
    (hy : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = y) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∃ a b : ∀ i, κ i → ℤ, ∀ i : ι,
      (∑ j, a i j • v i j) = D • x ∧
      (∑ j, b i j • v i j) = D • y ∧
      (∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)) ≤ M := by
  classical
  choose c hc using hx
  choose d hd using hy
  let f : (Σ i, κ i) × Bool → ℚ := fun p => if p.2 then c p.1.1 p.1.2 else d p.1.1 p.1.2
  obtain ⟨D,hD,A,hA⟩ := common_denominator f
  let a := fun (i : ι) (j : κ i) => A (⟨i,j⟩,true)
  let b := fun (i : ι) (j : κ i) => A (⟨i,j⟩,false)
  let m := fun i => ∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)
  let M := (∑ i, m i)+1
  refine ⟨D,M,hD,Nat.zero_lt_succ _,a,b,fun i => ⟨?_,?_,?_⟩⟩
  · calc
      (∑ j, a i j • v i j) = ∑ j, ((D:ℚ)*c i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,true)
        simp only [f,ite_true] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, c i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • x := by rw [hc,Nat.cast_smul_eq_nsmul]
  · calc
      (∑ j, b i j • v i j) = ∑ j, ((D:ℚ)*d i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,false)
        simp only [f,Bool.false_eq_true,ite_false] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, d i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • y := by rw [hd,Nat.cast_smul_eq_nsmul]
  · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)).trans (Nat.le_succ _)
end EuclideanFiveColor.Arithmetic
end

noncomputable section
open Module
namespace EuclideanFiveColor.Arithmetic
open AlgebraicCayley GeneralPosition

lemma span_mult_rep (N : IntermediateField ℚ ℂ) (T : Finset N)
    (hT : Submodule.span ℚ (T : Set N) = ⊤) (q : N) (hq : q ≠ 0) (x : N) :
    ∃ c : T → ℚ, ∑ j, c j • (q*j.val) = x := by
  have hs : Set.range (fun j : T => j.val) = (T : Set N) := Subtype.range_coe
  have hx : q⁻¹*x ∈ Submodule.span ℚ (Set.range (fun j : T => j.val)) := by rw [hs,hT]; trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  refine ⟨c,?_⟩
  calc
    (∑ j, c j • (q*j.val)) = q * ∑ j, c j • j.val := by
      simp only [Finset.mul_sum, mul_smul_comm]
    _ = x := by rw [hc,← mul_assoc,mul_inv_cancel₀ hq,one_mul]

/-- Uniform integral spanning selections extracted from the source's syndetic cover. -/
lemma uniform_selection (Q : Finset ℂ)
    (hQn : ∀ q ∈ Q, ‖q‖ = 1) (hQa : ∀ q ∈ Q, IsAlgebraic ℚ q)
    (A : ℂ → Prop)
    (hA : ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v → ∃ q ∈ Q, A (q*v)) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v →
      ∃ n : ℕ, ∃ k : Fin n → ℂ, ∃ a b : Fin n → ℤ,
        (∀ j, ‖k j‖ = 1 ∧ IsAlgebraic ℚ (k j) ∧ A (k j*v)) ∧
        (∑ j, a j • k j) = D • (1:ℂ) ∧
        (∑ j, b j • k j) = D • Complex.I ∧
        (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M := by
  classical
  let N := generatedField Q
  have : FiniteDimensional ℚ N := generatedField_finite Q hQa
  obtain ⟨S,hSc,hSn,hSg⟩ := numberField_general_position N (generatedField_I Q)
    (generatedField_re_closed Q) (generatedField_im_closed Q)
    (Q.card*(finrank ℚ N-1)+1)
  let TS : Finset (Finset N) := S.powerset.filter (fun T => Submodule.span ℚ (T:Set N) = ⊤)
  let I := Q × TS
  let κ : I → Type := fun i => i.2.val
  let qs : Q → N := fun q => ⟨q.val,generatedField_contains Q q.val q.property⟩
  have hqs (q : Q) : qs q ≠ 0 := by
    intro he
    have hec := congrArg (fun z : N => (z:ℂ)) he
    have hn := hQn q q.property
    change q.val = 0 at hec
    simp [hec] at hn
  let k : ∀ i : I, κ i → N := fun i j => qs i.1*j.val
  have hs (i : I) : Submodule.span ℚ (i.2.val:Set N) = ⊤ := (Finset.mem_filter.mp i.2.property).2
  obtain ⟨D,M,hD,hM,a,b,hab⟩ := uniform_integral_representations k (1:N) (iN N (generatedField_I Q))
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
  refine ⟨D,M,hD,hM,fun v hv hva => ?_⟩
  have hAlg (z : N) : IsAlgebraic ℚ (z:ℂ) :=
    IsAlgebraic.algHom N.val (IsAlgebraic.of_finite ℚ z)
  obtain ⟨q,hq,T,hTS,hTc,hTspan,hTA⟩ := spanning_selection Q S hSg (by omega)
    (fun q s => A (q*(s:ℂ)*v)) (by
      intro s hs
      have hn : ‖(s:ℂ)*v‖ = 1 := by rw [norm_mul,hSn s hs,hv,one_mul]
      obtain ⟨q,hq,hqA⟩ := hA ((s:ℂ)*v) hn ((hAlg s).mul hva)
      exact ⟨q,hq,by simpa only [mul_assoc] using hqA⟩)
  have hTmem : T ∈ TS := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTS,hTspan⟩
  let i : I := (⟨q,hq⟩,⟨T,hTmem⟩)
  let e := (Fintype.equivFin (κ i)).symm
  refine ⟨Fintype.card (κ i),fun j => (k i (e j):ℂ),fun j => a i (e j),fun j => b i (e j),?_,?_,?_,?_⟩
  · intro j
    have hj : (e j).val ∈ T := (e j).property
    refine ⟨?_,hAlg (k i (e j)),?_⟩
    · change ‖q*((e j).val:ℂ)‖ = 1
      rw [norm_mul,hQn q hq,hSn _ (hTS hj),one_mul]
    · exact hTA _ hj
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).1
    push_cast at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).2.1
    push_cast at he
    change (∑ j, b i j • (k i j:ℂ)) = D • Complex.I at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · rw [Fintype.sum_equiv e _ (fun j => (a i j).natAbs+(b i j).natAbs) (fun _ => rfl)]
    exact (hab i).2.2
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma real_sum_bound {ι : Type*} [Fintype ι] (a : ι → ℤ) (x : ι → ℝ) (B : ℝ)
    (hx : ∀ i, |x i| ≤ B) :
    |∑ i, (a i : ℝ)*x i| ≤ (∑ i, ((a i).natAbs : ℝ))*B := by
  calc
    _ ≤ ∑ i, |(a i:ℝ)*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((a i).natAbs : ℝ)*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |(a i:ℝ)| = ((a i).natAbs : ℝ) := by simp
      rw [he]
      exact mul_le_mul_of_nonneg_left (hx i) (Nat.cast_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma selection_transverse {ι : Type*} [Fintype ι] (k : ι → ℂ) (a b : ι → ℤ)
    (D M : ℕ) (hD : 0 < D)
    (ha : (∑ i, a i • k i) = D • (1:ℂ))
    (hb : (∑ i, b i • k i) = D • Complex.I)
    (hM : (∑ i, ((a i).natAbs+(b i).natAbs)) ≤ M)
    (v : ℂ) (hv : ‖v‖ = 1) :
    ∃ i, ∀ j, |(k j*v).re| ≤ |(k i*v).re| ∧
      (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
  classical
  have hn : Nonempty ι := by
    by_contra hh
    have : IsEmpty ι := not_nonempty_iff.mp hh
    have he : (D:ℂ) = 0 := by simpa using ha.symm
    have : D = 0 := by exact_mod_cast he
    omega
  have := hn
  obtain ⟨i,_,him⟩ := Finset.exists_max_image Finset.univ (fun j => |(k j*v).re|) Finset.univ_nonempty
  have hm (j : ι) : |(k j*v).re| ≤ |(k i*v).re| := him j (Finset.mem_univ j)
  have h1 : (∑ j, (a j:ℝ)*(k j*v).re) = (D:ℝ)*v.re := by
    have he := congrArg (fun z : ℂ => (z*v).re) ha
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
      mul_one] using he
  have h2 : (∑ j, (b j:ℝ)*(k j*v).re) = -(D:ℝ)*v.im := by
    have he := congrArg (fun z : ℂ => (z*v).re) hb
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im,
      one_mul, zero_sub, mul_neg, neg_mul] using he
  have h1b := real_sum_bound a (fun j => (k j*v).re) _ hm
  have h2b := real_sum_bound b (fun j => (k j*v).re) _ hm
  rw [h1,abs_mul,abs_of_nonneg (Nat.cast_nonneg D)] at h1b
  rw [h2,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg D)] at h2b
  have hcomp : 1 ≤ |v.re|+|v.im| := hv ▸ Complex.norm_le_abs_re_add_abs_im v
  have hMc : (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) ≤ (M:ℝ) := by
    have he : ((∑ j, ((a j).natAbs+(b j).natAbs) : ℕ):ℝ) =
        (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) := by
      simp [Finset.sum_add_distrib]
    rw [← he]
    exact_mod_cast hM
  have hexp := mul_le_mul_of_nonneg_right hMc (abs_nonneg (k i*v).re)
  have hfinal : (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
    nlinarith [mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg D)]
  exact ⟨i,fun j => ⟨hm j,hfinal⟩⟩
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a * m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)

include hc0 hc1 in
omit [Field α] [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_mono {n k : ℕ} {x : α} (h : Good m c n x) (hnk : n ≤ k) : Good m c k x :=
  (pow_le_pow_of_le_one hc0 hc1 hnk).trans h
include hm0 hc0 hc1 in
omit [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_zero (n : ℕ) : Good m c n 0 := by
  unfold Good
  rw [hm0]
  exact pow_le_one₀ hc0 hc1
include hd hc0 in
omit [IsStrictOrderedRing α] in
lemma good_diff {n k : ℕ} {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Good m c n a) (hB : Good m c k b) : Good m c (n+k) |a-b| := by
  unfold Good at *
  rw [pow_add]
  exact (mul_le_mul hA hB (pow_nonneg hc0 k) ((pow_nonneg hc0 n).trans hA)).trans (hd a b ha hb)

variable {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hd hc0 hc1 hp hpG in
lemma add_residues {a b : α} {n k : ℕ} (ha : a ∈ Set.Ico 0 p) (hb : b ∈ Set.Ico 0 p)
    (hA : Good m c n a) (hB : Good m c k b) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (n+k+2) r ∧ ∃ j : ℤ, a+b = r+j•p := by
  obtain ⟨ha0, hap⟩ := ha
  obtain ⟨hb0, hbp⟩ := hb
  have ha : a ∈ Set.Ico 0 p := ⟨ha0,hap⟩
  have hb : b ∈ Set.Ico 0 p := ⟨hb0,hbp⟩
  by_cases hs : a+b < p
  · refine ⟨a+b, ⟨add_nonneg ha.1 hb.1, hs⟩, ?_, 0, by simp⟩
    have hpa : Good m c (1+n) (p-a) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr ha.2.le)] using
        good_diff m hd c hc0 hp.le ha.1 hpG hA
    have hsub : Good m c (1+n+k) ((p-a)-b) := by
      simpa only [abs_of_nonneg (show 0 ≤ (p-a)-b by linarith)] using
        good_diff m hd c hc0 (sub_nonneg.mpr ha.2.le) hb.1 hpa hB
    have hfinal := good_diff m hd c hc0 hp.le (show 0 ≤ (p-a)-b by linarith) hpG hsub
    have he : |p-((p-a)-b)| = a+b := by rw [abs_of_nonneg (by linarith)]; abel
    simpa only [he, show 1+(1+n+k) = n+k+2 by omega] using hfinal
  · refine ⟨a+b-p, ⟨by linarith, by linarith⟩, ?_, 1, by simp⟩
    have hpb : Good m c (1+k) (p-b) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hb.2.le)] using
        good_diff m hd c hc0 hp.le hb.1 hpG hB
    have hfinal := good_diff m hd c hc0 ha.1 (sub_nonneg.mpr hb.2.le) hA hpb
    have he : |a-(p-b)| = a+b-p := by rw [abs_of_nonneg (by linarith)]; abel
    apply good_mono m c hc0 hc1 (n := n+(1+k)) (hnk := by omega)
    simpa only [he] using hfinal

include hm0 hd hc0 hc1 hp hpG in
lemma input_residue {x : α} (hx : |x| ≤ p) (hG : Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c 2 r ∧ ∃ j : ℤ, x = r+j•p := by
  by_cases hx0 : 0 ≤ x
  · have hxp : x ≤ p := by simpa [abs_of_nonneg hx0] using hx
    rcases lt_or_eq_of_le hxp with hlt | rfl
    · exact ⟨x, ⟨hx0,hlt⟩, good_mono m c hc0 hc1 (by simpa [abs_of_nonneg hx0] using hG) (by omega), 0, by simp⟩
    · exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, 1, by simp⟩
  · have hn : 0 < -x := neg_pos.mpr (lt_of_not_ge hx0)
    have hnx : -x ≤ p := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hx
    rcases lt_or_eq_of_le hnx with hlt | heq
    · refine ⟨p+x, ⟨by linarith, by linarith⟩, ?_, -1, by simp⟩
      have hneg : Good m c 1 (-x) := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hG
      have hfinal := good_diff m hd c hc0 hp.le hn.le hpG hneg
      simpa only [show |p- -x| = p+x by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]] using hfinal
    · refine ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, -1, ?_⟩
      simp only [neg_smul, one_smul, zero_add]
      linarith

include hm0 hd hc0 hc1 hp hpG in
lemma list_residue (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (4*l.length) r ∧ ∃ j : ℤ, l.sum = r+j•p := by
  induction l with
  | nil => exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 _, 0, by simp⟩
  | cons x l ih =>
    obtain ⟨a,ha,hA,i,hi⟩ := input_residue m hm0 hd c hc0 hc1 hp hpG (hl x (List.mem_cons_self)).1 (hl x (List.mem_cons_self)).2
    obtain ⟨b,hb,hB,j,hj⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    obtain ⟨r,hr,hR,k,hk⟩ := add_residues m hd c hc0 hc1 hp hpG ha hb hA hB
    refine ⟨r,hr,?_,i+j+k,?_⟩
    · simpa only [List.length_cons, show 2+4*l.length+2 = 4*(l.length+1) by omega] using hR
    · simp only [List.sum_cons, hi, hj, add_zsmul]
      calc
        _ = (a+b)+(i•p+j•p) := by abel
        _ = _ := by rw [hk]; abel

include hm0 hd hc0 hc1 hp hpG in
lemma list_cap (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|)
    (hz : l.sum ∈ Set.Ico 0 p) : Good m c (4*l.length) l.sum := by
  obtain ⟨r,hr,hR,j,hj⟩ := list_residue m hm0 hd c hc0 hc1 hp hpG l hl
  have hzero : j = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hle : j ≤ -1 := by omega
      have hh : j•p ≤ (-1:ℤ)•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hp.le
      simp only [neg_smul, one_smul] at hh
      linarith [hz.1, hr.2]
    · have hge : 1 ≤ j := by omega
      have hh : (1:ℤ)•p ≤ j•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hge) hp.le
      simp only [one_smul] at hh
      linarith [hz.2, hr.1]
  have he : l.sum = r := by simpa only [hzero, zero_smul, add_zero] using hj
  rw [he]
  exact hR
end EuclideanFiveColor.CappedResidues
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

omit [IsStrictOrderedRing α] in
lemma signedList_mem (a : ℤ) (x v : α) (hv : v ∈ signedList a x) : |v| = |x| := by
  cases a <;> simp only [signedList,List.mem_replicate] at hv
  · rw [hv.2]
  · rw [hv.2,abs_neg]

omit [IsStrictOrderedRing α] in
lemma integer_list {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α) :
    ∃ l : List α, l.length = ∑ i ∈ s, (a i).natAbs ∧ l.sum = ∑ i ∈ s, a i • x i ∧
      ∀ v ∈ l, ∃ i ∈ s, |v| = |x i| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[],by simp,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨l,hl,hs,hv⟩ := ih
    refine ⟨signedList (a i) (x i) ++ l,?_,?_,?_⟩
    · simp [hl,hi]
    · simp [hs,hi]
    · intro v hv'
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact ⟨i,Finset.mem_insert_self _ _,signedList_mem _ _ _ hv'⟩
      · obtain ⟨j,hj,he⟩ := hv v hv'
        exact ⟨j,Finset.mem_insert_of_mem hj,he⟩

variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
  {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hm0 hd hc0 hc1 hp hpG in
lemma integer_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : (∑ i ∈ s, a i • x i) ∈ Set.Ico 0 p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) (∑ i ∈ s, a i • x i) := by
  obtain ⟨l,hl,hs,hv⟩ := integer_list s a x
  have he := list_cap m hm0 hd c hc0 hc1 hp hpG l (by
    intro v hvl
    obtain ⟨i,hi,he⟩ := hv v hvl
    rw [he]
    exact hx i hi) (hs.symm ▸ hz)
  rwa [hl,hs] at he
include hm0 hd hc0 hc1 hp hpG in
lemma integer_abs_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : |∑ i ∈ s, a i • x i| < p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) |∑ i ∈ s, a i • x i| := by
  by_cases hn : 0 ≤ ∑ i ∈ s, a i • x i
  · rw [abs_of_nonneg hn] at hz ⊢
    exact integer_cap m hm0 hd c hc0 hc1 hp hpG s a x hx ⟨hn,hz⟩
  · have hs : (∑ i ∈ s, a i • (-x i)) = -∑ i ∈ s, a i • x i := by simp
    have hz' : (∑ i ∈ s, a i • (-x i)) ∈ Set.Ico 0 p := by
      rw [hs]
      have he : |∑ i ∈ s, a i • x i| = -∑ i ∈ s, a i • x i := abs_of_neg (lt_of_not_ge hn)
      exact ⟨by linarith,he ▸ hz⟩
    have he := integer_cap m hm0 hd c hc0 hc1 hp hpG s a (fun i => -x i)
      (fun i hi => by simpa only [abs_neg] using hx i hi) hz'
    simpa only [hs,abs_of_neg (lt_of_not_ge hn)] using he
end EuclideanFiveColor.CappedResidues
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_RadialEnergy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.Spectral.instCountableRot _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

lemma kCoeff_scale_one (g : Rot) : kCoeff (rotMul ((scaleHom (G := Rot) 1) g)) = kCoeff (rotMul g) := by
  change kCoeff (rotMul ((1:ℤ) • g)) = _
  rw [one_zsmul]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

lemma sqrtF_sq (a : F) (ha : 0 ≤ a) : sqrtF a ^ 2 = a := by
  apply Subtype.ext
  exact Real.sq_sqrt ha
lemma norm_ofF (a : F) : ‖((ofF a : E) : ℂ)‖ = |(a : ℝ)| := by
  change ‖((a : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs]

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
include hq hqcov in
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
lemma massReal_abs (a : F) : massReal μ q |a| = massReal μ q a := by
  apply projectedMass_radial μ q hq hqcov
  rw [norm_ofF, norm_ofF]
  change abs (abs (a : ℝ)) = abs (a : ℝ)
  exact abs_abs _
end PlaneFiveColor.Spectral
end

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.Arithmetic

lemma reF_sum {ι : Type*} (s : Finset ι) (z : ι → E) : reF (∑ i ∈ s,z i) = ∑ i ∈ s,reF (z i) := by
  apply Subtype.ext
  simp [reF]
lemma reF_zsmul (a : ℤ) (z : E) : reF (a • z) = a • reF z := by
  apply Subtype.ext
  simp only [reF, zsmul_eq_mul]
  push_cast
  simp
lemma reF_nsmul (a : ℕ) (z : E) : reF (a • z) = a • reF z := by
  apply Subtype.ext
  simp only [reF,nsmul_eq_mul]
  push_cast
  simp

/-- The signed capped-residue conclusion for any integral transverse selection. -/
lemma selected_mass_bound (m : F → ℝ) (hm0 : m 0 = 1)
    (hd : ∀ a b : F, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (r : F) (hr : 0 < r) {n : ℕ} (k : Fin n → E) (a b : Fin n → ℤ)
    (D M : ℕ) (hD : 0 < D) (hM : 0 < M)
    (ha : (∑ j, a j • k j) = D • (1:E))
    (hb : (∑ j, b j • k j) = D • imagUnit)
    (hab : (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M)
    (v : E) (hv : ‖(v:ℂ)‖ = 1) (hsmall : |reF v| < (M:F)⁻¹)
    (hgood : ∀ j, c ≤ m |2*r*reF (k j*v)|) :
    c^(4*M) ≤ m |2*r*D*reF v| := by
  classical
  have hac : (∑ j, a j • (k j:ℂ)) = D • (1:ℂ) := by
    have he := congrArg (fun z : E => (z:ℂ)) ha
    simpa using he
  have hbc : (∑ j, b j • (k j:ℂ)) = D • Complex.I := by
    have he := congrArg (fun z : E => (z:ℂ)) hb
    simpa [imagUnit] using he
  obtain ⟨i,hi⟩ := selection_transverse (fun j => (k j:ℂ)) a b D M hD hac hbc hab (v:ℂ) hv
  have hmax (j : Fin n) : |reF (k j*v)| ≤ |reF (k i*v)| := by
    exact_mod_cast (hi j).1
  have htrans : (D:F) ≤ (M:F)*|reF (k i*v)| := by exact_mod_cast (hi i).2
  have hDp : (0:F) < D := Nat.cast_pos.mpr hD
  have hMp : (0:F) < M := Nat.cast_pos.mpr hM
  have hip : 0 < |reF (k i*v)| := by nlinarith
  let x := fun j => 2*r*reF (k j*v)
  let p := |x i|
  have hx (j : Fin n) : |x j| = 2*r*|reF (k j*v)| := by
    dsimp [x]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2*r)]
  have hp : 0 < p := by dsimp [p]; rw [hx]; positivity
  have hsum : (∑ j, a j • x j) = 2*r*D*reF v := by
    have he := congrArg reF (congrArg (fun z : E => z*v) ha)
    simp only [Finset.sum_mul,reF_sum,smul_mul_assoc,reF_zsmul,one_mul,reF_nsmul] at he
    calc
      (∑ j, a j • x j) = 2*r * ∑ j, a j • reF (k j*v) := by
        simp only [x,Finset.mul_sum,zsmul_eq_mul]; congr 1; ext j; ring_nf
      _ = 2*r*D*reF v := by rw [he,nsmul_eq_mul]; ring
  have hz : |∑ j, a j • x j| < p := by
    rw [hsum,abs_mul,abs_of_pos (by positivity : (0:F) < 2*r*D)]
    dsimp only [p]
    rw [hx]
    have hvM : (M:F)*|reF v| < 1 := by
      have hh := mul_lt_mul_of_pos_left hsmall hMp
      rwa [mul_inv_cancel₀ hMp.ne'] at hh
    have ht : (D:F)*|reF v| < |reF (k i*v)| := by
      have hh := mul_le_mul_of_nonneg_right htrans (abs_nonneg (reF v))
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left ht (by positivity : (0:F) < 2*r)]
  have hcap := CappedResidues.integer_abs_cap m hm0 hd c hc0 hc1 hp
    (by simpa only [CappedResidues.Good,p,pow_one] using hgood i)
    Finset.univ a x (fun j _ => ⟨by dsimp only [p]; rw [hx,hx]; exact mul_le_mul_of_nonneg_left (hmax j) (by positivity),
      by simpa only [CappedResidues.Good,pow_one] using hgood j⟩) hz
  have hlen : ∑ j, (a j).natAbs ≤ M := by
    calc
      _ ≤ ∑ j, ((a j).natAbs+(b j).natAbs) := Finset.sum_le_sum (fun j _ => Nat.le_add_right _ _)
      _ ≤ M := hab
  have hpow : c^(4*M) ≤ c^(4*∑ j,(a j).natAbs) :=
    pow_le_pow_of_le_one hc0 hc1 (Nat.mul_le_mul_left 4 hlen)
  exact hpow.trans (by simpa only [CappedResidues.Good,hsum] using hcap)
end PlaneFiveColor.Spectral
end

noncomputable section
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.Arithmetic

lemma circle_realPart (t : F) (ht : |t| ≤ 1) :
    ∃ v : E, ‖(v:ℂ)‖ = 1 ∧ reF v = t := by
  let y := sqrtF (1-t^2)
  have hy : y^2 = 1-t^2 := sqrtF_sq _ (by have hh := sq_le_sq₀ (abs_nonneg t) zero_le_one |>.mpr ht; nlinarith [sq_abs t])
  let v := ofF t + imagUnit * ofF y
  have hv : (v:ℂ) = (t:ℝ) + Complex.I*(y:ℝ) := rfl
  refine ⟨v,?_,?_⟩
  · have hh : ‖(v:ℂ)‖^2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq,hv]
      simp only [Complex.normSq_apply, Complex.add_re,Complex.add_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        zero_mul,one_mul,mul_zero,sub_zero,add_zero,zero_add]
      have hyc : (y:ℝ)^2 = 1-(t:ℝ)^2 := by exact_mod_cast hy
      nlinarith
    nlinarith [norm_nonneg (v:ℂ)]
  · apply Subtype.ext
    change (v:ℂ).re = (t:ℝ)
    simp [hv]

/-- Arithmetic propagation: one syndetic positive mass level forces uniformly
positive mass at every sufficiently small positive algebraic radius. -/
lemma cover_mass_positive (m : F → ℝ) (hm0 : m 0 = 1)
    (hd : ∀ a b : F, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (r : F) (hr : 0 < r) (Q : Finset E) (hQ : ∀ q ∈ Q, ‖(q:ℂ)‖ = 1)
    (hcover : ∀ v : E, ‖(v:ℂ)‖ = 1 → ∃ q ∈ Q, c ≤ m |2*r*reF (q*v)|) :
    ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ s : F, 0 < s → s < δ → ε ≤ m s := by
  classical
  let A : ℂ → Prop := fun w => ∃ z : E, (z:ℂ) = w ∧ c ≤ m |2*r*reF z|
  have hQN : ∀ q ∈ Q.image (fun z : E => (z:ℂ)), ‖q‖ = 1 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    exact hQ z hz
  have hQA : ∀ q ∈ Q.image (fun z : E => (z:ℂ)), IsAlgebraic ℚ q := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    exact mem_algebraicClosure_iff.mp z.property
  have hA : ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v → ∃ q ∈ Q.image (fun z : E => (z:ℂ)), A (q*v) := by
    intro v hv hva
    let v' : E := ⟨v,mem_algebraicClosure_iff.mpr hva⟩
    obtain ⟨q,hq,hgood⟩ := hcover v' hv
    exact ⟨q,Finset.mem_image.mpr ⟨q,hq,rfl⟩,q*v',rfl,hgood⟩
  obtain ⟨D,M,hD,hM,hsel⟩ := uniform_selection _ hQN hQA A hA
  have hDp : (0:F) < D := Nat.cast_pos.mpr hD
  have hMp : (0:F) < M := Nat.cast_pos.mpr hM
  let δ : F := 2*r*D/(M+1)
  refine ⟨δ,by dsimp [δ]; positivity,c^(4*M),pow_pos hc0 _,pow_le_one₀ hc0.le hc1,?_⟩
  intro s hs hsδ
  let t := s/(2*r*D)
  have ht : 0 < t := div_pos hs (by positivity)
  have htM : t < ((M:F)+1)⁻¹ := by
    dsimp [t,δ] at *
    apply (div_lt_iff₀ (by positivity : (0:F) < 2*r*D)).mpr
    simpa only [div_eq_mul_inv,mul_comm] using hsδ
  have ht1 : |t| ≤ 1 := by
    rw [abs_of_pos ht]
    have hh : ((M:F)+1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
    exact htM.le.trans hh
  obtain ⟨v,hv,hvt⟩ := circle_realPart t ht1
  obtain ⟨n,k,a,b,hkg,ha,hb,hab⟩ := hsel (v:ℂ) hv (mem_algebraicClosure_iff.mp v.property)
  let k' : Fin n → E := fun j => ⟨k j,mem_algebraicClosure_iff.mpr (hkg j).2.1⟩
  have ha' : (∑ j, a j • k' j) = D • (1:E) := by
    apply Subtype.ext
    simpa [k'] using ha
  have hb' : (∑ j, b j • k' j) = D • imagUnit := by
    apply Subtype.ext
    simpa [k',imagUnit] using hb
  have hgood (j : Fin n) : c ≤ m |2*r*reF (k' j*v)| := by
    obtain ⟨z,hz,hg⟩ := (hkg j).2.2
    have he : z = k' j*v := Subtype.ext hz
    rwa [he] at hg
  have hsmall : |reF v| < (M:F)⁻¹ := by
    rw [hvt,abs_of_pos ht]
    exact htM.trans (inv_lt_inv₀ (by positivity : (0:F) < M+1) hMp |>.mpr (by linarith))
  have hh := selected_mass_bound m hm0 hd c hc0.le hc1 r hr k' a b D M hD hM ha' hb' hab v hv hsmall hgood
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  have he : 2*r*(D:F)*reF v = s := by rw [hvt]; dsimp [t]; field_simp
  rw [he,abs_of_pos hs]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
lemma kCoeff_scale_neg_one (g : Rot) :
    ((kCoeff (rotMul (scaleHom (G := Rot) (-1) g)) : E) : ℂ) = conj ((kCoeff (rotMul g) : E) : ℂ) := by
  change ((rotMul ((-1:ℤ) • g)).val : ℂ) = _
  rw [neg_one_zsmul]
  exact Circle.coe_inv_eq_conj _
lemma char_symmetric (r : F) (g : Rot) :
    (Family.orbit (scaleHom (G := Rot) 1) (char (ofF r)) *
      Family.orbit (scaleHom (G := Rot) (-1)) (char (ofF r))) g =
      char (ofF (2*r*reF (kCoeff (rotMul g)))) := by
  simp only [Family.mul_apply, Family.orbit_apply, char_act, kCoeff_scale_one, ← char_add]
  congr 1
  apply Subtype.ext
  change ((kCoeff (rotMul g) : E) : ℂ)*(r : ℝ) +
    ((kCoeff (rotMul (scaleHom (G := Rot) (-1) g)) : E) : ℂ)*(r : ℝ) =
    ((2*r*reF (kCoeff (rotMul g)) : F) : ℝ)
  rw [kCoeff_scale_neg_one]
  push_cast
  change _ = 2*(r : ℝ)*(((kCoeff (rotMul g) : E) : ℂ).re : ℂ)
  apply Complex.ext <;> simp
  ring

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
include hq hqcov in
lemma radiusFamily_mean (r : F) (M : Amenable.Mean Rot) :
    M.map (radiusFamily μ q hq r) = massReal μ q r ^2 := by
  haveI : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map hq.aemeasurable
  have he : radiusFamily μ q hq r = Family.energy (μ.map q) (Family.conditional μ q
      (Family.orbit (scaleHom (G := Rot) 1) (char (ofF r)) *
        Family.orbit (scaleHom (G := Rot) (-1)) (char (ofF r)))) := by
    ext g
    simp only [radiusFamily_apply, Family.energy_apply, Family.conditional_apply, char_symmetric]
    rfl
  rw [he, conditional_integer_pair_energy μ q hq (fun g : Rot => hqcov (rotMul g))
    rot_zsmul_surjective M (by decide : (1:ℤ) ≠ -1)]
  exact (pow_two _).symm
include hq hqcov in
lemma radius_syndetic (r : F) (c : ℝ) (hc : c < massReal μ q r ^2) :
    ∃ S : Finset Rot, ∀ v : Rot, ∃ s ∈ S,
      c < massReal μ q (2*r*reF (kCoeff (rotMul (v+s)))) := by
  apply MovingMean.syndetic_of_all_means (radiusFamily μ q hq r) c
  intro M
  rwa [radiusFamily_mean μ q hq hqcov r M]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

include hq hqcov in
lemma radial_positive_near_zero_oai (r : F) (hr : 0 < r) (hm : massReal μ q r ≠ 0) :
    ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ s : F, 0 < s → s < δ → ε ≤ massReal μ q s := by
  classical
  let c := massReal μ q r ^2/2
  have hp : 0 < massReal μ q r := lt_of_le_of_ne (projectedMass_nonneg μ q _) (Ne.symm hm)
  have hc : 0 < c := div_pos (sq_pos_of_pos hp) (by norm_num)
  have hc1 : c ≤ 1 := by
    have h := projectedMass_le_one μ q hq (ofF r)
    change massReal μ q r ≤ 1 at h
    dsimp [c]; nlinarith
  obtain ⟨S,hS⟩ := radius_syndetic μ q hq hqcov r c (by dsimp [c]; nlinarith)
  let Q := S.image (fun s => kCoeff (rotMul s))
  apply cover_mass_positive (massReal μ q) (projectedMass_zero μ q hq)
    (massReal_difference μ q hq hqcov) c hc hc1 r hr Q
  · intro z hz
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    exact Circle.norm_coe _
  · intro v hv
    let u : K := ⟨⟨(v:ℂ),mem_sphere_zero_iff_norm.mpr hv⟩,mem_algebraicClosure_iff.mp v.property⟩
    obtain ⟨s,hs,hsg⟩ := hS (mulRot u)
    refine ⟨kCoeff (rotMul s),Finset.mem_image.mpr ⟨s,hs,rfl⟩,?_⟩
    rw [massReal_abs μ q hq hqcov]
    have he : kCoeff (rotMul (mulRot u+s)) = kCoeff (rotMul s)*v := by
      change kCoeff (u*rotMul s) = _
      rw [kCoeff_mul,mul_comm]
      rfl
    rw [he] at hsg
    exact hsg.le

end PlaneFiveColor.Spectral
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlaneFiveColor.Spectral.radial_positive_near_zero_oai.{u_1} := @OAI.PlaneFiveColor.Spectral.radial_positive_near_zero_oai.{u_1}
