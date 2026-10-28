-- Prove2me | solution 1 for OAI.PlaneFiveColor.Spectral.massReal_difference
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:16:10.061034+00:00
-- url     : https://prove2.me/submissions/8984c007-fe68-496a-a8f3-d920fa226528

import Mathlib
import Definitions.Def_OAIQ5T4002

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
lemma conditional_pair_energy (M : Amenable.Mean G) (φ : G →+ G)
    (hs : Function.Surjective φ) (f h : Func X) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q (Family.const f * Family.orbit φ h))) =
      ‖l2 (μ.map q) (conditional μ q f)‖^2 * ‖l2 (μ.map q) (conditional μ q h)‖^2 := by
  have : ErgodicVAdd G Y (μ.map q) := factor_ergodic μ q hq hqcov
  have hp := pairVanishing_of_ergodic μ q hq M
  have he := covariance_mean_zero μ q hq hqcov M hp φ hs f h
  have hv := Family.energy_mean_eq_of_meanNorm_zero (μ.map q) M _ _ he
  rw [hv]
  exact pair_energy_mean (μ.map q) M φ hs (conditional μ q f) (conditional μ q h)
include hq hqcov in
lemma conditional_integer_triple_energy
    (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (M : Amenable.Mean G) (f h k : Func X) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q
      (Family.orbit (scaleHom 0) f * Family.orbit (scaleHom 1) h * Family.orbit (scaleHom 2) k))) =
    M.map (Family.energy (μ.map q)
      (Family.orbit (scaleHom 0) (conditional μ q f) * Family.orbit (scaleHom 1) (conditional μ q h) *
        Family.orbit (scaleHom 2) (conditional μ q k))) := by
  have hp := pairVanishing_of_ergodic μ q hq M
  have hn : Set.InjOn (![(0:ℤ),1,2]) (Finset.univ : Finset (Fin 3)) := by
    intro i _ j _ he
    fin_cases i <;> fin_cases j <;> simp_all
  have he := conditional_integer_multiple_mean_zero μ q hq hqcov hdiv M hp
    Finset.univ ![(0:ℤ),1,2] ![f,h,k] hn
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at he
  exact Family.energy_mean_eq_of_meanNorm_zero (μ.map q) M _ _ he
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
-- module Solutions.OAIQ5_T4.PlaneSpectrum_RadialEnergy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.Spectral.instCountableRot _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
lemma equal_moduli_quadratic (A B L : ℝ) (hL : L^2 = A*B) (u : Circle) :
    ‖(A : ℂ) - B*(u : ℂ)^2‖ =
      ‖-(L : ℂ) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2‖ := by
  have hu : (u : ℂ) * conj (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hreal : (u : ℂ).re^2 + (u : ℂ).im^2 = 1 := by
    simpa only [Complex.normSq_apply, sq] using Circle.normSq_coe u
  have hleft : (A : ℂ) - B*(u : ℂ)^2 =
      (u : ℂ) * ((A : ℂ)*conj (u : ℂ) - B*(u : ℂ)) := by
    calc
      _ = A*((u : ℂ)*conj (u : ℂ)) - B*(u : ℂ)^2 := by rw [hu, mul_one]
      _ = _ := by ring
  have hright : -(L : ℂ) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2 =
      (u : ℂ) * (((A-B : ℝ) : ℂ) + L*((u : ℂ)-conj (u : ℂ))) := by
    calc
      _ = -L*((u : ℂ)*conj (u : ℂ)) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2 := by rw [hu, mul_one]
      _ = _ := by ring
  rw [hleft, hright, norm_mul, norm_mul, Circle.norm_coe, one_mul, one_mul]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.mul_im,
    Complex.add_re, Complex.add_im, zero_mul, sub_zero, zero_add, add_zero]
  nlinarith [mul_self_nonneg (A-B), mul_self_nonneg (A+B),
    congrArg (fun x : ℝ => (A-B)^2*x) hreal,
    congrArg (fun x : ℝ => 4*x*(u : ℂ).im^2) hL]
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
lemma projectedMass_pair_mean [IsProbabilityMeasure (μ.map q)] (M : Amenable.Mean Rot) (a b : E) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q
      (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b)))) =
      projectedMass μ q a * projectedMass μ q b := by
  exact conditional_pair_energy μ q hq (fun g : Rot => hqcov (rotMul g)) M
    (scaleHom (G := Rot) 2) (rot_zsmul_surjective 2 (by decide)) (char a) (char b)

lemma kCoeff_scale_two (g : Rot) : kCoeff (rotMul ((scaleHom (G := Rot) 2) g)) = kCoeff (rotMul g)^2 := by
  change kCoeff ((rotMul g)^2) = _
  simp only [pow_two, kCoeff_mul]
lemma kCoeff_scale_one (g : Rot) : kCoeff (rotMul ((scaleHom (G := Rot) 1) g)) = kCoeff (rotMul g) := by
  change kCoeff (rotMul ((1:ℤ) • g)) = _
  rw [one_zsmul]
lemma char_two_term (a b : E) (g : Rot) :
    (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b)) g =
      char (a + kCoeff (rotMul g)^2*b) := by
  simp only [Family.mul_apply, Family.const_apply, Family.orbit_apply, char_act,
    kCoeff_scale_two, char_add]
lemma char_three_term (a b c : E) (g : Rot) :
    (Family.orbit (scaleHom (G := Rot) 0) (char a) * Family.orbit (scaleHom (G := Rot) 1) (char b) *
      Family.orbit (scaleHom (G := Rot) 2) (char c)) g =
      char (a+kCoeff (rotMul g)*b+kCoeff (rotMul g)^2*c) := by
  simp only [Family.mul_apply, Family.orbit_apply, char_act, kCoeff_scale_one, kCoeff_scale_two,
    char_add]
  congr 2
  change char (kCoeff (rotMul ((0:ℤ) • g))*a) = char a
  simp only [zero_zsmul]
  change char (1*a) = char a
  rw [one_mul]

include hq hqcov in
lemma quadratic_mass_inequality (a b l h k : E)
    (hn : ∀ u : K, ‖((a + kCoeff u^2*b : E) : ℂ)‖ =
      ‖((l+kCoeff u*h+kCoeff u^2*k : E) : ℂ)‖) :
    projectedMass μ q a * projectedMass μ q b ≤ projectedMass μ q h := by
  haveI : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map hq.aemeasurable
  let : ErgodicVAdd Rot Y (μ.map q) := factor_ergodic μ q hq (fun g : Rot => hqcov (rotMul g))
  let M : Amenable.Mean Rot := MovingMean.toMean (fun _ => 0)
  have he : Family.energy (μ.map q) (Family.conditional μ q
      (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b))) =
      Family.energy (μ.map q) (Family.conditional μ q
        (Family.orbit (scaleHom (G := Rot) 0) (char l) * Family.orbit (scaleHom (G := Rot) 1) (char h) *
          Family.orbit (scaleHom (G := Rot) 2) (char k))) := by
    ext g
    simp only [Family.energy_apply, Family.conditional_apply, char_two_term, char_three_term]
    exact projectedMass_radial μ q hq hqcov (hn (rotMul g))
  rw [← projectedMass_pair_mean μ q hq hqcov M a b, he,
    conditional_integer_triple_energy μ q hq (fun g : Rot => hqcov (rotMul g)) rot_zsmul_surjective]
  calc
    _ ≤ M.map (BoundedContinuousFunction.const Rot (projectedMass μ q h)) := by
      apply M.mono
      intro g
      simp only [Family.energy_apply, Family.mul_apply, Family.orbit_apply,
        BoundedContinuousFunction.const_apply]
      have h1 := l2_mul_norm_le (μ.map q)
        (act (scaleHom (G := Rot) 0 g) (conditional μ q (char l)) * act (scaleHom (G := Rot) 1 g) (conditional μ q (char h)))
        (act (scaleHom (G := Rot) 2 g) (conditional μ q (char k)))
        (fun y => projected_char_bound μ q k ((scaleHom (G := Rot) 2 g) +ᵥ y))
      have h2 := l2_norm_mul_le (μ.map q)
        (act (scaleHom (G := Rot) 0 g) (conditional μ q (char l))) (act (scaleHom (G := Rot) 1 g) (conditional μ q (char h)))
        (fun y => projected_char_bound μ q l ((scaleHom (G := Rot) 0 g) +ᵥ y))
      simp only [one_mul, l2_act, LinearIsometryEquiv.norm_map] at h1 h2
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    _ = _ := M.map_const _
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
lemma projectedMass_neg (a : E) : projectedMass μ q (-a) = projectedMass μ q a := by
  apply projectedMass_radial μ q hq hqcov
  exact norm_neg (a : ℂ)
include hq hqcov in
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
lemma massReal_abs (a : F) : massReal μ q |a| = massReal μ q a := by
  apply projectedMass_radial μ q hq hqcov
  rw [norm_ofF, norm_ofF]
  change abs (abs (a : ℝ)) = abs (a : ℝ)
  exact abs_abs _
include hq hqcov in
lemma massReal_difference_oai (A B : F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    massReal μ q A * massReal μ q B ≤ massReal μ q |A-B| := by
  let l := sqrtF (A*B)
  have hl : (l : ℝ)^2 = (A : ℝ)*(B : ℝ) := by
    exact congrArg (fun x : F => (x : ℝ)) (sqrtF_sq (A*B) (mul_nonneg hA hB))
  have he := quadratic_mass_inequality μ q hq hqcov (ofF A) (-ofF B) (-ofF l) (ofF (A-B)) (ofF l) (fun u => by
    have hh := equal_moduli_quadratic (A : ℝ) (B : ℝ) (l : ℝ) hl u.val
    convert hh using 1 <;> congr 1 <;> simp only [map_sub, ofF, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, kCoeff] <;> push_cast <;> ring)
  rw [projectedMass_neg μ q hq hqcov] at he
  rw [massReal_abs μ q hq hqcov]
  exact he
end PlaneFiveColor.Spectral
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlaneFiveColor.Spectral.massReal_difference_oai.{u_1} := @OAI.PlaneFiveColor.Spectral.massReal_difference_oai.{u_1}
