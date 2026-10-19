-- Prove2me | solution 1 for OAI.Problem356.coulomb_counterexample_and_equal_infima
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:47:45.875136+00:00
-- url     : https://prove2.me/submissions/3b3b3be6-0d54-4bca-9a05-9768f2ddbff0

import Mathlib
import Definitions.Def_CoulombCounterexample

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

universe uE uF uP uS uR uAlpha uBeta uX uY uIndex uA uKappa uM uN uD

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem356.AnalyticCoulomb

/-- Inverse distance is real analytic off the diagonal; the statement
also supplies every finite or infinite differentiability order. -/
theorem contDiffAt_inverseDistance {E : Type uE} {F : Type uF}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : WithTop ENat} {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hne : f x ≠ g x) :
    ContDiffAt ℝ n (fun y => ‖f y - g y‖⁻¹) x := by
  exact ((hf.sub hg).norm ℝ (sub_ne_zero.mpr hne)).inv
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))

/-- The real-valued Coulomb formula is analytic at every collision-free triple. -/
theorem contDiffAt_cost {n : WithTop ENat} (t : Triple)
    (h12 : t.1 ≠ t.2.1) (h13 : t.1 ≠ t.2.2) (h23 : t.2.1 ≠ t.2.2) :
    ContDiffAt ℝ n (fun p : Triple =>
      ‖p.1 - p.2.1‖⁻¹ + ‖p.1 - p.2.2‖⁻¹ + ‖p.2.1 - p.2.2‖⁻¹) t := by
  have h1 : ContDiffAt ℝ n (fun p : Triple => p.1) t := contDiffAt_fst
  have h2 : ContDiffAt ℝ n (fun p : Triple => p.2.1) t := contDiffAt_snd.fst
  have h3 : ContDiffAt ℝ n (fun p : Triple => p.2.2) t := contDiffAt_snd.snd
  exact ((contDiffAt_inverseDistance h1 h2 h12).add
    (contDiffAt_inverseDistance h1 h3 h13)).add
    (contDiffAt_inverseDistance h2 h3 h23)

/-- Analyticity of a parameter-dependent partial derivative.  This is the
stationarity-map regularity needed by the analytic implicit-function theorem. -/
theorem contDiffAt_partialFDeriv {P : Type uP} {S : Type uS} {R : Type uR}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {F : P × S → R} {p : P × S}
    (hF : ContDiffAt ℝ (⊤ : WithTop ENat) F p) :
    ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : P × S => fderiv ℝ (fun s => F (q.1, s)) q.2) p := by
  have hpair : ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : (P × S) × S => (q.1.1, q.2)) (p, p.2) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have hcomp : ContDiffAt ℝ (⊤ : WithTop ENat)
      (Function.uncurry (fun (q : P × S) (s : S) => F (q.1, s))) (p, p.2) :=
    hF.comp _ hpair
  exact hcomp.fderiv contDiffAt_snd le_top

/-- Joint analyticity of the state Hessian, hence its continuity for the
positive-definiteness persistence step. -/
theorem contDiffAt_partialHessian {P : Type uP} {S : Type uS} {R : Type uR}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {F : P × S → R} {p : P × S}
    (hF : ContDiffAt ℝ (⊤ : WithTop ENat) F p) :
    ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : P × S => fderiv ℝ
        (fun s => fderiv ℝ (fun r => F (q.1, r)) s) q.2) p := by
  exact contDiffAt_partialFDeriv (contDiffAt_partialFDeriv hF)

/-- In parameter/state coordinates `(y,(x,z))`, subtracting arbitrary analytic
central and outer potentials leaves an analytic Coulomb stationarity map. -/
theorem contDiffAt_stationarity
    (u v : E3 → ℝ) (p : E3 × (E3 × E3))
    (hu : ContDiffAt ℝ (⊤ : WithTop ENat) u p.2.1)
    (hv : ContDiffAt ℝ (⊤ : WithTop ENat) v p.2.2)
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hyz : p.1 ≠ p.2.2) :
    ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : E3 × (E3 × E3) =>
        fderiv ℝ (fun s : E3 × E3 =>
          ‖s.1 - q.1‖⁻¹ + ‖s.1 - s.2‖⁻¹ + ‖q.1 - s.2‖⁻¹ - u s.1 - v s.2)
          q.2) p := by
  apply contDiffAt_partialFDeriv (F := fun q : E3 × (E3 × E3) =>
    ‖q.2.1 - q.1‖⁻¹ + ‖q.2.1 - q.2.2‖⁻¹ + ‖q.1 - q.2.2‖⁻¹ - u q.2.1 - v q.2.2)
  have hx : ContDiffAt ℝ (⊤ : WithTop ENat) (fun q : E3 × (E3 × E3) => q.2.1) p :=
    contDiffAt_snd.fst
  have hy : ContDiffAt ℝ (⊤ : WithTop ENat) (fun q : E3 × (E3 × E3) => q.1) p :=
    contDiffAt_fst
  have hz : ContDiffAt ℝ (⊤ : WithTop ENat) (fun q : E3 × (E3 × E3) => q.2.2) p :=
    contDiffAt_snd.snd
  exact ((((contDiffAt_inverseDistance hx hy hxy).add
    (contDiffAt_inverseDistance hx hz hxz)).add
    (contDiffAt_inverseDistance hy hz hyz)).sub (hu.comp p hx)).sub (hv.comp p hz)

end Problem356.AnalyticCoulomb

end

end OAI
end
end

section
section
namespace OAI


/-! # Atomlessness of injective measurable pushforwards

This supports the standard-Borel-to-real reduction in the construction of
measure-preserving maps.
-/

open MeasureTheory

namespace Problem356

variable {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]

/-- An injective measurable map preserves the property of having null
singletons. No probability or finiteness hypothesis is needed. -/
theorem nullSingletonClass_map_of_injective (μ : Measure α)
    [NullSingletonClass μ] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable f) (hinj : Function.Injective f) :
    NullSingletonClass (Measure.map f μ) := by
  constructor
  intro y
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  have hsub : (f ⁻¹' {y}).Subsingleton := by
    intro x hx z hz
    apply hinj
    exact hx.trans hz.symm
  exact hsub.countable.measure_zero μ

/-- The real-valued measurable embedding used for standard Borel spaces
sends a singleton-null measure to a singleton-null real measure. -/
theorem nullSingletonClass_map_embeddingReal (μ : Measure α)
    [StandardBorelSpace α] [NullSingletonClass μ] :
    NullSingletonClass (Measure.map (embeddingReal α) μ) :=
  nullSingletonClass_map_of_injective μ (measurable_embeddingReal α)
    (measurableEmbedding_embeddingReal α).injective

end Problem356

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology unitInterval

namespace Problem356.Transport

/-- Every probability level strictly between zero and one is achieved by a continuous CDF. -/
theorem exists_cdf_eq_of_continuous (μ : Measure ℝ)
    (hc : Continuous (cdf μ)) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ x : ℝ, cdf μ x = u := by
  have h := isPreconnected_univ.intermediate_value_Ioo
    (l₁ := atBot) (l₂ := atTop) (by simp) (by simp) hc.continuousOn
    (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ) ⟨hu0, hu1⟩
  simpa only [image_univ, mem_range] using h

/-- The probability integral transform, expressed on CDF sublevel sets. -/
theorem measureReal_cdf_sublevel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    μ.real {x : ℝ | cdf μ x ≤ u} = u := by
  let s : Set ℝ := {x | cdf μ x ≤ u}
  have hs0 : 0 ≤ μ.real s := measureReal_nonneg
  have hs1 : μ.real s ≤ 1 := measureReal_le_one
  apply le_antisymm
  · by_contra! h
    obtain ⟨v, huv, hvs⟩ := exists_between h
    obtain ⟨x, hx⟩ := exists_cdf_eq_of_continuous μ hc (hu0.trans_lt huv) (hvs.trans_le hs1)
    have hsub : s ⊆ Iic x := by
      intro y hy
      change y ≤ x
      by_contra! hxy
      have hmon := monotone_cdf μ hxy.le
      have hy' : cdf μ y ≤ u := hy
      rw [hx] at hmon
      linarith
    have hle := measureReal_mono (μ := μ) hsub
    rw [← cdf_eq_real μ x, hx] at hle
    linarith
  · by_contra! h
    obtain ⟨v, hsv, hvu⟩ := exists_between h
    obtain ⟨x, hx⟩ := exists_cdf_eq_of_continuous μ hc (hs0.trans_lt hsv) (hvu.trans_le hu1)
    have hsub : Iic x ⊆ s := by
      intro y hy
      have hmon := monotone_cdf μ hy
      change cdf μ y ≤ u
      rw [hx] at hmon
      exact hmon.trans hvu.le
    have hle := measureReal_mono (μ := μ) hsub
    rw [← cdf_eq_real μ x, hx] at hle
    linarith

/-- A continuous CDF sends its law to uniform probability on the unit interval. -/
theorem map_cdf_unitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) :
    μ.map (fun x : ℝ => (⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩ : I)) = volume := by
  let f : ℝ → I := fun x => ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩
  have hf : Measurable f := hc.measurable.subtype_mk
  apply Measure.ext_of_Iic
  intro u
  rw [Measure.map_apply hf measurableSet_Iic, unitInterval.volume_Iic]
  change μ {x : ℝ | cdf μ x ≤ (u : ℝ)} = ENNReal.ofReal (u : ℝ)
  rw [← ofReal_measureReal (measure_ne_top μ _),
    measureReal_cdf_sublevel μ hc u.property.1 u.property.2]

end Problem356.Transport

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory Function
open scoped Topology ENNReal

namespace Problem356

/-- A Stieltjes function has no jumps when its associated measure has no point atoms. -/
theorem continuous_stieltjesFunction_of_nullSingletonClass
    (f : StieltjesFunction ℝ) [NullSingletonClass f.measure] : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply f.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [f.rightLim_eq]
  have hz : ENNReal.ofReal (f x - leftLim f x) = 0 := by
    rw [← f.measure_singleton]
    exact measure_singleton x
  exact le_antisymm (f.mono.leftLim_le le_rfl)
    (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz))

/-- The cumulative distribution function of an atomless real probability measure is continuous. -/
theorem continuous_cdf_of_nullSingletonClass (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (ProbabilityTheory.cdf mu) := by
  have : NullSingletonClass (ProbabilityTheory.cdf mu).measure := by
    rw [ProbabilityTheory.measure_cdf]
    infer_instance
  exact continuous_stieltjesFunction_of_nullSingletonClass _

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval

namespace Problem356.Transport

/-- Every atomless standard Borel probability admits a uniform random variable. -/
theorem exists_uniform_map {X : Type uX} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ f : X → I, Measurable f ∧ Measure.map f μ = volume := by
  let e := embeddingReal X
  have he : Measurable e := measurable_embeddingReal X
  let η := Measure.map e μ
  have : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map he.aemeasurable
  have : NullSingletonClass η := nullSingletonClass_map_embeddingReal μ
  have hc : Continuous (cdf η) := continuous_cdf_of_nullSingletonClass η
  let F : ℝ → I := fun x => ⟨cdf η x, cdf_nonneg η x, cdf_le_one η x⟩
  have hF : Measurable F := hc.measurable.subtype_mk
  refine ⟨F ∘ e, hF.comp he, ?_⟩
  rw [← Measure.map_map hF he]
  exact map_cdf_unitInterval η hc

/-- A singleton-null standard Borel probability can be transported measurably to
any probability on a nonempty standard Borel target. -/
theorem exists_measurable_transport {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ] :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by
  obtain ⟨f, hf, hfμ⟩ := exists_uniform_map μ
  obtain ⟨g, hg, hgν⟩ := ν.exists_measurable_map_eq
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  rw [← Measure.map_map hg hf, hfμ, hgν]

/-- Equal finite masses can be transported provided the source has no point atoms. -/
theorem exists_measurable_transport_finite {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ]
    (hmass : μ univ = ν univ) :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [← hmass, hμ]
      simp
    exact ⟨fun _ => Classical.choice inferInstance, measurable_const, by simp [hμ, hν]⟩
  · have : NeZero μ := ⟨hμ⟩
    have hν : ν ≠ 0 := by
      intro hν
      apply hμ
      apply Measure.measure_univ_eq_zero.mp
      rw [hmass, hν]
      simp
    have : NeZero ν := ⟨hν⟩
    have : NullSingletonClass ((μ univ)⁻¹ • μ) := ⟨fun x => by simp⟩
    obtain ⟨Q, hQ, hmap⟩ := exists_measurable_transport
      ((μ univ)⁻¹ • μ) ((ν univ)⁻¹ • ν)
    refine ⟨Q, hQ, ?_⟩
    have hscale := congrArg (fun m : Measure Y => μ univ • m) hmap
    rw [Measure.map_smul, smul_smul, ENNReal.mul_inv_cancel
      (NeZero.ne (μ univ)) (measure_ne_top μ univ), one_smul] at hscale
    rw [hmass, smul_smul, ENNReal.mul_inv_cancel
      (NeZero.ne (ν univ)) (measure_ne_top ν univ), one_smul] at hscale
    exact hscale

/-- A restricted atomless measure can be redistributed proportionally over any
positive-mass target cell. The input cell is allowed to have mass zero. -/
theorem exists_measurable_transport_restrict {X : Type uX}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (A B : Set X) (hA : μ A ≠ 0) :
    ∃ Q : X → X, Measurable Q ∧
      Measure.map Q (μ.restrict B) = (μ B / μ A) • μ.restrict A := by
  have hmass : ((μ B / μ A) • μ.restrict A) univ = μ B := by
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.div_mul_cancel hA (measure_ne_top μ A)
  have : IsFiniteMeasure ((μ B / μ A) • μ.restrict A) :=
    ⟨by rw [hmass]; exact measure_lt_top μ B⟩
  apply exists_measurable_transport_finite
  rw [Measure.restrict_apply_univ, hmass]

/-- The transport to a measurable target cell can be chosen to take every value
inside that cell, by resetting outputs on a source-null set. -/
theorem exists_measurable_transport_restrict_mem {X : Type uX}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (A B : Set X) (hAm : MeasurableSet A) (hA : μ A ≠ 0) :
    ∃ Q : X → X, Measurable Q ∧
      Measure.map Q (μ.restrict B) = (μ B / μ A) • μ.restrict A ∧
      ∀ x, Q x ∈ A := by
  classical
  obtain ⟨Q, hQ, hmap⟩ := exists_measurable_transport_restrict μ A B hA
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero hA
  let R : X → X := fun x => if Q x ∈ A then Q x else a
  have hR : Measurable R := hQ.ite (hAm.preimage hQ) measurable_const
  have hmem : ∀ᵐ x ∂μ.restrict B, Q x ∈ A := by
    apply (ae_map_iff hQ.aemeasurable hAm).mp
    rw [hmap]
    exact Measure.ae_smul_measure (ae_restrict_mem hAm) _
  have heq : R =ᵐ[μ.restrict B] Q := by
    filter_upwards [hmem] with x hx
    simp [R, hx]
  refine ⟨R, hR, (Measure.map_congr heq).trans hmap, ?_⟩
  intro x
  by_cases hx : Q x ∈ A <;> simp [R, hx, ha]

end Problem356.Transport

end

end OAI
end
end

section
section
namespace OAI

/-! Explicit nondegeneracy algebra for the two local Coulomb branches.
The Hessian eigenvalues are 2 in the axial direction and -1 transversely.
A common regularization parameter K = 20 works in every direction. -/

noncomputable section

namespace Problem356.LocalHessian

open Matrix

/-- Eigenvalue of the inverse-distance Hessian at a unit coordinate vector. -/
def eigenvalue (k i : Fin 3) : ℝ := if i = k then 2 else -1

/-- The inverse-distance Hessian at either chosen unit coordinate vector. -/
def pairHessian (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal (eigenvalue k)

/-- First derivative of the central stationary branch for K = 20. -/
def centralDerivative (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => if i = k then 9 / 106 else -15 / 271

/-- First derivative of the opposite stationary branch for K = 20. -/
def oppositeDerivative (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => if i = k then 1 / 53 else -1 / 271

/-- Upper diagonal block of the regularized Hessian. -/
def upperBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => 20 + 2 * eigenvalue k i

/-- Lower diagonal block of the regularized Hessian. -/
def lowerBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => 20 + (9 / 8) * eigenvalue k i

/-- Mixed block of the regularized Hessian. -/
def mixedBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => -eigenvalue k i

/-- The full six-dimensional regularized Hessian. -/
def regularizedHessian (k : Fin 3) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks (upperBlock k) (mixedBlock k) (mixedBlock k) (lowerBlock k)

lemma eigenvalue_cases (k i : Fin 3) :
    eigenvalue k i = 2 ∨ eigenvalue k i = -1 := by
  unfold eigenvalue
  split_ifs <;> simp

lemma scalar_quadratic_coercive {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) :
    16 * (x ^ 2 + z ^ 2) ≤
      (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
        (20 + (9 / 8) * q) * z ^ 2 := by
  rcases hq with rfl | rfl
  · nlinarith [sq_nonneg (x - z), sq_nonneg x, sq_nonneg z]
  · nlinarith [sq_nonneg (x + z), sq_nonneg x, sq_nonneg z]

lemma scalar_quadratic_positive {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) (hxz : x ≠ 0 ∨ z ≠ 0) :
    0 < (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
      (20 + (9 / 8) * q) * z ^ 2 := by
  have hsum : 0 < x ^ 2 + z ^ 2 := by
    rcases hxz with hx | hz
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg z)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hz)
  rcases hq with rfl | rfl
  · nlinarith [sq_nonneg (x - z), sq_nonneg x, sq_nonneg z]
  · nlinarith [sq_nonneg (x + z), sq_nonneg x, sq_nonneg z]

lemma scalar_quadratic_nonnegative {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) :
    0 ≤ (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
      (20 + (9 / 8) * q) * z ^ 2 := by
  by_cases hx : x = 0
  · by_cases hz : z = 0
    · simp [hx, hz]
    · exact (scalar_quadratic_positive hq (Or.inr hz)).le
  · exact (scalar_quadratic_positive hq (Or.inl hx)).le

lemma centralDerivative_isUnit (k : Fin 3) : IsUnit (centralDerivative k) := by
  rw [centralDerivative, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> norm_num

lemma oppositeDerivative_isUnit (k : Fin 3) : IsUnit (oppositeDerivative k) := by
  rw [oppositeDerivative, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> norm_num

lemma central_stationary_equation (k : Fin 3) :
    upperBlock k * centralDerivative k + mixedBlock k * oppositeDerivative k =
      pairHessian k := by
  simp only [upperBlock, centralDerivative, mixedBlock, oppositeDerivative,
    pairHessian, diagonal_mul_diagonal, diagonal_add]
  congr 1
  funext i
  unfold eigenvalue
  split_ifs <;> norm_num

lemma opposite_stationary_equation (k : Fin 3) :
    mixedBlock k * centralDerivative k + lowerBlock k * oppositeDerivative k =
      diagonal (fun i => (eigenvalue k i) / 8) := by
  simp only [mixedBlock, centralDerivative, lowerBlock, oppositeDerivative,
    diagonal_mul_diagonal, diagonal_add]
  congr 1
  funext i
  unfold eigenvalue
  split_ifs <;> norm_num

lemma regularizedHessian_quadratic (k : Fin 3) (v : Fin 3 ⊕ Fin 3 → ℝ) :
    star v ⬝ᵥ ((regularizedHessian k) *ᵥ v) =
      ∑ i : Fin 3, ((20 + 2 * eigenvalue k i) * v (Sum.inl i) ^ 2 -
        2 * eigenvalue k i * v (Sum.inl i) * v (Sum.inr i) +
        (20 + (9 / 8) * eigenvalue k i) * v (Sum.inr i) ^ 2) := by
  simp only [regularizedHessian, fromBlocks_mulVec, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, star_trivial, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, upperBlock, lowerBlock, mixedBlock,
    mulVec_diagonal, Function.comp_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma regularizedHessian_isHermitian (k : Fin 3) :
    (regularizedHessian k).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_diagonal _
  · exact Matrix.isHermitian_diagonal _
  · exact Matrix.isHermitian_diagonal _

lemma regularizedHessian_posDef (k : Fin 3) :
    (regularizedHessian k).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (regularizedHessian_isHermitian k)
  intro v hv
  rw [regularizedHessian_quadratic]
  apply Finset.sum_pos'
  · intro i hi
    exact scalar_quadratic_nonnegative (eigenvalue_cases k i)
  · have hex : ∃ j, v j ≠ 0 := by
      contrapose! hv
      ext j
      exact hv j
    obtain ⟨j, hj⟩ := hex
    cases j with
    | inl i =>
      exact ⟨i, Finset.mem_univ _,
        scalar_quadratic_positive (eigenvalue_cases k i) (Or.inl hj)⟩
    | inr i =>
      exact ⟨i, Finset.mem_univ _,
        scalar_quadratic_positive (eigenvalue_cases k i) (Or.inr hj)⟩

lemma regularizedHessian_isUnit (k : Fin 3) : IsUnit (regularizedHessian k) :=
  (regularizedHessian_posDef k).isUnit

lemma stationary_equation (k : Fin 3) :
    regularizedHessian k * fromRows (centralDerivative k) (oppositeDerivative k) =
      fromRows (pairHessian k) (diagonal fun i => (eigenvalue k i) / 8) := by
  rw [regularizedHessian, fromBlocks_mul_fromRows,
    central_stationary_equation, opposite_stationary_equation]

end Problem356.LocalHessian

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A graph with all three coordinates explicitly specified. -/
def branchGraph (f g h : E3 → E3) : E3 → Triple := fun x => (f x, (g x, h x))

lemma measurable_branchGraph {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (branchGraph f g h) := hf.prodMk (hg.prodMk hh)

/-- The marginal used by the two-branch construction. -/
def branchMarginal (nu : Measure E3) (H1 H2 H3 H4 : E3 → E3) : Measure E3 :=
  (1 / 3 : ℝ≥0∞) • nu +
    (1 / 6 : ℝ≥0∞) • (Measure.map H1 nu + Measure.map H2 nu +
      Measure.map H3 nu + Measure.map H4 nu)

/-- Each branch is averaged over its three cyclic coordinate orderings. -/
def branchCoupling (nu : Measure E3) (H1 H2 H3 H4 : E3 → E3) : Measure Triple :=
  (1 / 6 : ℝ≥0∞) •
    (Measure.map (branchGraph id H1 H2) nu +
      Measure.map (branchGraph H1 H2 id) nu +
      Measure.map (branchGraph H2 id H1) nu +
      Measure.map (branchGraph id H3 H4) nu +
      Measure.map (branchGraph H3 H4 id) nu +
      Measure.map (branchGraph H4 id H3) nu)

lemma map_tripleFst_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleFst (Measure.map (branchGraph f g h) nu) = Measure.map f nu := by
  rw [Measure.map_map (show Measurable tripleFst from measurable_fst) (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleSnd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleSnd (Measure.map (branchGraph f g h) nu) = Measure.map g nu := by
  rw [Measure.map_map (show Measurable tripleSnd from measurable_fst.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleThd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleThd (Measure.map (branchGraph f g h) nu) = Measure.map h nu := by
  rw [Measure.map_map (show Measurable tripleThd from measurable_snd.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma six_smul_group (a b c d e : Measure E3) :
    (1 / 6 : ℝ≥0∞) • (a + b + c + a + d + e) =
      (1 / 3 : ℝ≥0∞) • a + (1 / 6 : ℝ≥0∞) • (b + c + d + e) := by
  have h : (1 / 3 : ℝ≥0∞) = 1 / 6 + 1 / 6 := by
    simp only [one_div]
    change ((3 : NNReal) : ℝ≥0∞)⁻¹ = ((6 : NNReal) : ℝ≥0∞)⁻¹ +
      ((6 : NNReal) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (6 : NNReal) ≠ 0), ← ENNReal.coe_add]
    norm_num
  rw [h, add_smul]
  simp only [smul_add]
  ac_rfl

lemma map_tripleFst_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleFst (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleFst := measurable_fst
  simp only [branchCoupling, Measure.map_smul, Measure.map_add _ _ hp,
    map_tripleFst_branchGraph nu measurable_id h1 h2,
    map_tripleFst_branchGraph nu h1 h2 measurable_id,
    map_tripleFst_branchGraph nu h2 measurable_id h1,
    map_tripleFst_branchGraph nu measurable_id h3 h4,
    map_tripleFst_branchGraph nu h3 h4 measurable_id,
    map_tripleFst_branchGraph nu h4 measurable_id h3, Measure.map_id]
  exact six_smul_group _ _ _ _ _

lemma map_tripleSnd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleSnd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleSnd := measurable_fst.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul, Measure.map_add _ _ hp,
    map_tripleSnd_branchGraph nu measurable_id h1 h2,
    map_tripleSnd_branchGraph nu h1 h2 measurable_id,
    map_tripleSnd_branchGraph nu h2 measurable_id h1,
    map_tripleSnd_branchGraph nu measurable_id h3 h4,
    map_tripleSnd_branchGraph nu h3 h4 measurable_id,
    map_tripleSnd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

lemma map_tripleThd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleThd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleThd := measurable_snd.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul, Measure.map_add _ _ hp,
    map_tripleThd_branchGraph nu measurable_id h1 h2,
    map_tripleThd_branchGraph nu h1 h2 measurable_id,
    map_tripleThd_branchGraph nu h2 measurable_id h1,
    map_tripleThd_branchGraph nu measurable_id h3 h4,
    map_tripleThd_branchGraph nu h3 h4 measurable_id,
    map_tripleThd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

lemma isProbabilityMeasure_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchCoupling nu H1 H2 H3 H4) := by
  constructor
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply (measurable_branchGraph measurable_id h1 h2) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h1 h2 measurable_id) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h2 measurable_id h1) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph measurable_id h3 h4) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h3 h4 measurable_id) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h4 measurable_id h3) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, smul_eq_mul]
  norm_num only [one_div, show (1 + 1 + 1 + 1 + 1 + 1 : ℝ≥0∞) = 6 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The explicit two-branch mixture is an admissible coupling of its five-component marginal. -/
theorem isThreeCoupling_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    IsThreeCoupling (branchMarginal nu H1 H2 H3 H4) (branchCoupling nu H1 H2 H3 H4) :=
  ⟨isProbabilityMeasure_branchCoupling nu h1 h2 h3 h4,
    map_tripleFst_branchCoupling nu h1 h2 h3 h4,
    map_tripleSnd_branchCoupling nu h1 h2 h3 h4,
    map_tripleThd_branchCoupling nu h1 h2 h3 h4⟩

lemma isProbabilityMeasure_branchMarginal (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchMarginal nu H1 H2 H3 H4) := by
  have := isProbabilityMeasure_branchCoupling nu h1 h2 h3 h4
  rw [← map_tripleFst_branchCoupling nu h1 h2 h3 h4]
  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- Any measurable cyclically invariant property holding on the two branches
also holds almost everywhere for their explicit coupling. -/
theorem ae_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) {P : Triple → Prop} (hP : MeasurableSet {t | P t})
    (hcycle : ∀ x y z, P (x, (y, z)) → P (y, (z, x)))
    (h12 : ∀ᵐ x ∂nu, P (x, (H1 x, H2 x)))
    (h34 : ∀ᵐ x ∂nu, P (x, (H3 x, H4 x))) :
    ∀ᵐ t ∂branchCoupling nu H1 H2 H3 H4, P t := by
  have h12r : ∀ᵐ x ∂nu, P (branchGraph H1 H2 id x) :=
    h12.mono fun x hx => hcycle _ _ _ hx
  have h12rr : ∀ᵐ x ∂nu, P (branchGraph H2 id H1 x) :=
    h12r.mono fun x hx => hcycle _ _ _ hx
  have h34r : ∀ᵐ x ∂nu, P (branchGraph H3 H4 id x) :=
    h34.mono fun x hx => hcycle _ _ _ hx
  have h34rr : ∀ᵐ x ∂nu, P (branchGraph H4 id H3 x) :=
    h34r.mono fun x hx => hcycle _ _ _ hx
  unfold branchCoupling
  apply Measure.ae_smul_measure
  simp only [ae_add_measure_iff,
    ae_map_iff (measurable_branchGraph measurable_id h1 h2).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h1 h2 measurable_id).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h2 measurable_id h1).aemeasurable hP,
    ae_map_iff (measurable_branchGraph measurable_id h3 h4).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h3 h4 measurable_id).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h4 measurable_id h3).aemeasurable hP]
  exact ⟨⟨⟨⟨⟨h12, h12r⟩, h12rr⟩, h34⟩, h34r⟩, h34rr⟩

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem356

/-- Disjoint nonnegative summands allow the square root of a weighted sum of
squares to be written without any nonsmooth square-root composition. -/
theorem sqrt_sum_disjoint_squares {ι : Type uIndex} {X : Type uX} (s : Finset ι)
    (a : ι → ℝ) (g : ι → X → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (x : X) :
    Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, Real.sqrt (a i) * g i x := by
  classical
  by_cases h : ∃ i ∈ s, g i x ≠ 0
  · obtain ⟨i, hi, hix⟩ := h
    have hz : ∀ j ∈ s, j ≠ i → g j x = 0 := by
      intro j hj hji
      by_contra hjx
      exact Set.disjoint_left.mp (hd i hi j hj hji.symm) hix hjx
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · rw [Real.sqrt_mul (ha i hi), Real.sqrt_sq (hg i hi x)]
    · intro j hj hji
      simp [hz j hj hji]
    · exact fun hni => False.elim (hni hi)
    · intro j hj hji
      simp [hz j hj hji]
    · exact fun hni => False.elim (hni hi)
  · have hz : ∀ i ∈ s, g i x = 0 := by
      intro i hi
      by_contra hix
      exact h ⟨i, hi, hix⟩
    have hleft : (∑ i ∈ s, a i * (g i x) ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])
    have hright : (∑ i ∈ s, Real.sqrt (a i) * g i x) = 0 :=
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])
    rw [hleft, hright, Real.sqrt_zero]

/-- A finite disjoint family of smooth compactly supported nonnegative square
roots yields a density satisfying both smoothness requirements of the target. -/
theorem isSmoothCompactProbabilityDensity_sum_disjoint_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hmass : (∫ x : E3, (∑ i ∈ s, a i * (g i x) ^ 2)
      ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  have hsqrt : (fun x => Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2)) =
      (fun x => ∑ i ∈ s, Real.sqrt (a i) * g i x) := by
    funext x
    exact sqrt_sum_disjoint_squares s a g ha hg hd x
  refine ⟨?_, ?_, ?_, ?_, ?_, hmass⟩
  · intro x
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))
  · exact ContDiff.sum (fun i hi => contDiff_const.mul ((hsm i hi).pow 2))
  · have hterm : ∀ i ∈ s, HasCompactSupport (fun x => a i * (g i x) ^ 2) := by
      intro i hi
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => a i * y ^ 2) (by simp)
    simpa only [Finset.sum_fn] using HasCompactSupport.finset_sum hterm
  · rw [hsqrt]
    exact ContDiff.sum (fun i hi => contDiff_const.mul (hsm i hi))
  · rw [hsqrt]
    have hterm : ∀ i ∈ s, HasCompactSupport (fun x => Real.sqrt (a i) * g i x) := by
      intro i hi
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => Real.sqrt (a i) * y) (by simp)
    simpa only [Finset.sum_fn] using HasCompactSupport.finset_sum hterm

/-- Convenient normalization form for the five component densities: every
square has unit mass, and the component weights sum to one. -/
theorem isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
    {ι : Type uIndex} (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hgint : ∀ i ∈ s, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1)
    (haint : (∑ i ∈ s, a i) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  apply isSmoothCompactProbabilityDensity_sum_disjoint_squares s a g ha hg hsm hcs hd
  have hint : ∀ i ∈ s, Integrable (fun x => a i * (g i x) ^ 2)
      (volume : Measure E3) := by
    intro i hi
    have hcomp : HasCompactSupport (fun x => (g i x) ^ 2) := by
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact ((hsm i hi).continuous.pow 2).integrable_of_hasCompactSupport hcomp |>.const_mul (a i)
  rw [integral_finsetSum s hint]
  calc
    (∑ i ∈ s, ∫ x : E3, a i * (g i x) ^ 2 ∂(volume : Measure E3)) =
        ∑ i ∈ s, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, hgint i hi, mul_one]
    _ = 1 := haint

/-- The density assembled from weighted squares represents the corresponding
finite mixture of component measures. No disjointness is needed here. -/
theorem densityMeasure_sum_weighted_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hgm : ∀ i ∈ s, Measurable (g i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (fun x => (g i x) ^ 2) := by
  have hpoint : ∀ x, ENNReal.ofReal (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i hi => ENNReal.ofReal_mul (ha i hi))
  ext A hA
  simp only [Measure.finsetSum_apply, Measure.smul_apply, densityMeasure,
    withDensity_apply _ hA, smul_eq_mul]
  simp_rw [hpoint]
  rw [lintegral_finsetSum s (f := fun i x => ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2))
    (fun i hi => measurable_const.mul ((hgm i hi).pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_const_mul _ ((hgm i hi).pow_const 2).ennreal_ofReal

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Problem356

/-- Probability of a square density gives its ordinary integral normalization. -/
theorem integral_sq_eq_one_of_densityMeasure_probability
    {g : E3 → ℝ} (hg : Measurable g)
    [IsProbabilityMeasure (densityMeasure (fun x => (g x) ^ 2))] :
    (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))
    (hg.pow_const 2).aestronglyMeasurable]
  have hmass := measure_univ (μ := densityMeasure (fun x => (g x) ^ 2))
  simp only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at hmass
  rw [hmass, ENNReal.toReal_one]

/-- A smooth compact unit square defines a probability measure. -/
theorem isProbabilityMeasure_densityMeasure_unit_sq
    {g : E3 → ℝ}
    (hsm : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hcs : HasCompactSupport g)
    (hmass : (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1) :
    IsProbabilityMeasure (densityMeasure (fun x => (g x) ^ 2)) := by
  have hcomp : HasCompactSupport (fun x => (g x) ^ 2) := by
    simpa only [Function.comp_def] using
      hcs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hint : Integrable (fun x => (g x) ^ 2) (volume : Measure E3) :=
    (hsm.continuous.pow 2).integrable_of_hasCompactSupport hcomp
  constructor
  simp only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x))), hmass]
  exact ENNReal.ofReal_one

/-- The weights of the central and four outer squares. -/
def branchDensityWeight (i : Fin 5) : ℝ := if i = 0 then 1 / 3 else 1 / 6

lemma branchDensityWeight_nonneg (i : Fin 5) : 0 ≤ branchDensityWeight i := by
  unfold branchDensityWeight
  split <;> norm_num

lemma sum_branchDensityWeight : ∑ i : Fin 5, branchDensityWeight i = 1 := by
  norm_num [branchDensityWeight, Fin.sum_univ_succ]

/-- Five disjoint square amplitudes, with the four outer square laws obtained
by the prescribed branch pushforwards, form the exact smooth branch marginal. -/
theorem exists_smooth_density_eq_branchMarginal
    (g : Fin 5 → E3 → ℝ) (H : Fin 4 → E3 → E3)
    (hgn : ∀ i x, 0 ≤ g i x)
    (hgs : ∀ i, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hgc : ∀ i, HasCompactSupport (g i))
    (hgd : Pairwise fun i j =>
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hzero : (∫ x : E3, (g 0 x) ^ 2 ∂(volume : Measure E3)) = 1)
    (hH : ∀ i, Measurable (H i))
    (hmap : ∀ i : Fin 4,
      densityMeasure (fun x => (g i.succ x) ^ 2) =
        Measure.map (H i) (densityMeasure (fun x => (g 0 x) ^ 2))) :
    ∃ rho : E3 → ℝ,
      IsSmoothCompactProbabilityDensity rho ∧
      densityMeasure rho =
        branchMarginal (densityMeasure (fun x => (g 0 x) ^ 2))
          (H 0) (H 1) (H 2) (H 3) := by
  have := isProbabilityMeasure_densityMeasure_unit_sq (hgs 0) (hgc 0) hzero
  have hmass : ∀ i : Fin 5, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1 := by
    intro i
    refine Fin.cases hzero (fun j => ?_) i
    have hp : IsProbabilityMeasure (densityMeasure (fun x => (g j.succ x) ^ 2)) := by
      rw [hmap j]
      exact (Measure.isProbabilityMeasure_map_iff (hH j).aemeasurable).mpr inferInstance
    have := hp
    exact integral_sq_eq_one_of_densityMeasure_probability (hgs j.succ).continuous.measurable
  refine ⟨fun x => ∑ i : Fin 5, branchDensityWeight i * (g i x) ^ 2, ?_, ?_⟩
  · exact isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
      Finset.univ branchDensityWeight g
      (fun i _ => branchDensityWeight_nonneg i) (fun i _ => hgn i)
      (fun i _ => hgs i) (fun i _ => hgc i)
      (fun i _ j _ hij => hgd hij) (fun i _ => hmass i) sum_branchDensityWeight
  · rw [densityMeasure_sum_weighted_squares Finset.univ branchDensityWeight g
      (fun i _ => branchDensityWeight_nonneg i)
      (fun i _ => (hgs i).continuous.measurable)]
    simp only [Fin.sum_univ_succ, branchDensityWeight, Fin.succ_ne_zero,
      ite_true, ite_false]
    simp only [hmap]
    unfold branchMarginal
    norm_num [ENNReal.ofReal_div_of_pos, smul_add]
    simp only [add_assoc]
    rfl

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem356

/-- Finitely many pairwise disjoint compact components in a metric space have
one positive separation bound. Empty components and an empty index type are
allowed, so no auxiliary nonemptiness assumptions are needed. -/
theorem exists_uniform_compact_separation {α : Type uAlpha} {ι : Type uIndex} [MetricSpace α] [Finite ι]
    (K : ι → Set α) (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, eta ≤ dist x y := by
  let P := {p : ι × ι // p.1 ≠ p.2}
  let S : Set (α × α) := ⋃ p : P, K p.val.1 ×ˢ K p.val.2
  have hS : IsCompact S :=
    isCompact_iUnion (fun p : P => (hcompact p.val.1).prod (hcompact p.val.2))
  have hmem (i j : ι) (hij : i ≠ j) (x y : α) (hx : x ∈ K i) (hy : y ∈ K j) :
      (x, y) ∈ S := by
    exact Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, hx, hy⟩
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hpmin⟩ := hS.exists_isMinOn hne continuous_dist.continuousOn
    have hpne : p.1 ≠ p.2 := by
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hp
      intro heq
      exact Set.disjoint_left.mp (hdisjoint q.property) hq.1 (heq ▸ hq.2)
    refine ⟨dist p.1 p.2, dist_pos.mpr hpne, ?_⟩
    intro i j hij x hx y hy
    exact hpmin (hmem i j hij x y hx hy)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i j hij x hx y hy
    exact False.elim (hne ⟨(x, y), hmem i j hij x y hx hy⟩)

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.CoulombEstimates

/-- The reciprocal is uniformly Lipschitz away from zero. -/
theorem abs_inv_sub_inv_le {a b eta L : ℝ}
    (heta : 0 < eta) (ha : eta ≤ a) (hb : eta ≤ b)
    (hL : |a - b| ≤ L) :
    |a⁻¹ - b⁻¹| ≤ L / eta ^ 2 := by
  have ha0 : 0 < a := heta.trans_le ha
  have hb0 : 0 < b := heta.trans_le hb
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have hab : eta ^ 2 ≤ a * b := by
    nlinarith [mul_le_mul ha hb (le_of_lt heta) (le_of_lt ha0)]
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
  exact (div_le_div_of_nonneg_right hL (le_of_lt (mul_pos ha0 hb0))).trans
    (div_le_div_of_nonneg_left hL0 (sq_pos_of_pos heta) hab)

/-- Moving both endpoints by at most `delta` changes distance by at most `2 * delta`. -/
theorem abs_dist_sub_dist_le {E : Type uE} [PseudoMetricSpace E]
    {x y x' y' : E} {delta : ℝ}
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |dist x y - dist x' y'| ≤ 2 * delta := by
  have h := abs_dist_sub_le x x' y
  have h' := abs_dist_sub_le y y' x'
  calc
    |dist x y - dist x' y'| ≤
        |dist x y - dist x' y| + |dist x' y - dist x' y'| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (dist x y - dist x' y) (dist x' y - dist x' y')
    _ ≤ dist x x' + dist y y' := by
      exact add_le_add h (by simpa only [dist_comm] using h')
    _ ≤ 2 * delta := by linarith

/-- Coulomb pair interaction has a quantitative oscillation estimate on separated products. -/
theorem abs_inv_dist_sub_inv_dist_le {E : Type uE} [PseudoMetricSpace E]
    {x y x' y' : E} {eta delta : ℝ}
    (heta : 0 < eta) (hxy : eta ≤ dist x y) (hxy' : eta ≤ dist x' y')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |(dist x y)⁻¹ - (dist x' y')⁻¹| ≤ (2 * delta) / eta ^ 2 :=
  abs_inv_sub_inv_le heta hxy hxy' (abs_dist_sub_dist_le hx hy)

/-- Real-valued three-particle Coulomb cost on an arbitrary metric space. -/
def realCost {E : Type uE} [PseudoMetricSpace E] (x y z : E) : ℝ :=
  (dist x y)⁻¹ + (dist x z)⁻¹ + (dist y z)⁻¹

/-- Uniform boundedness of the Coulomb cost on a separated triple. -/
theorem realCost_le {E : Type uE} [PseudoMetricSpace E]
    {x y z : E} {eta : ℝ} (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    realCost x y z ≤ 3 / eta := by
  have h1 := one_div_le_one_div_of_le heta hxy
  have h2 := one_div_le_one_div_of_le heta hxz
  have h3 := one_div_le_one_div_of_le heta hyz
  simp only [one_div] at h1 h2 h3
  unfold realCost
  rw [div_eq_mul_inv]
  linarith

/-- Oscillation of the three-particle Coulomb cost on separated, small cells. -/
theorem abs_realCost_sub_realCost_le {E : Type uE} [PseudoMetricSpace E]
    {x y z x' y' z' : E} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    |realCost x y z - realCost x' y' z'| ≤ (6 * delta) / eta ^ 2 := by
  have h1 := abs_inv_dist_sub_inv_dist_le heta hxy hxy' hx hy
  have h2 := abs_inv_dist_sub_inv_dist_le heta hxz hxz' hx hz
  have h3 := abs_inv_dist_sub_inv_dist_le heta hyz hyz' hy hz
  have habs : |realCost x y z - realCost x' y' z'| ≤
      |(dist x y)⁻¹ - (dist x' y')⁻¹| +
      |(dist x z)⁻¹ - (dist x' z')⁻¹| +
      |(dist y z)⁻¹ - (dist y' z')⁻¹| := by
    unfold realCost
    calc
      _ = |((dist x y)⁻¹ - (dist x' y')⁻¹) +
          ((dist x z)⁻¹ - (dist x' z')⁻¹) +
          ((dist y z)⁻¹ - (dist y' z')⁻¹)| := by congr 1; ring
      _ ≤ _ := abs_add_three _ _ _
  calc
    _ ≤ _ := habs
    _ ≤ (2 * delta) / eta ^ 2 + (2 * delta) / eta ^ 2 +
        (2 * delta) / eta ^ 2 := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- The real formula agrees with the extended-valued cost away from collisions. -/
theorem coulombCost_eq_ofReal_realCost {x y z : E3}
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    coulombCost (x, (y, z)) = ENNReal.ofReal (realCost x y z) := by
  unfold realCost
  rw [ENNReal.ofReal_add (add_nonneg (inv_nonneg.mpr dist_nonneg)
        (inv_nonneg.mpr dist_nonneg)) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_add (inv_nonneg.mpr dist_nonneg) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_inv_of_pos hxy, ENNReal.ofReal_inv_of_pos hxz,
    ENNReal.ofReal_inv_of_pos hyz]
  rfl

/-- The exact extended-valued Coulomb cost is uniformly bounded on separated triples. -/
theorem coulombCost_le_of_separated {x y z : E3} {eta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    coulombCost (x, (y, z)) ≤ ENNReal.ofReal (3 / eta) := by
  rw [coulombCost_eq_ofReal_realCost (heta.trans_le hxy)
    (heta.trans_le hxz) (heta.trans_le hyz)]
  exact ENNReal.ofReal_le_ofReal (realCost_le heta hxy hxz hyz)

/-- Separated triples have finite Coulomb cost. -/
theorem coulombCost_lt_top_of_separated {x y z : E3} {eta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    coulombCost (x, (y, z)) < ⊤ :=
  (coulombCost_le_of_separated heta hxy hxz hyz).trans_lt ENNReal.ofReal_lt_top

/-- One-sided extended-valued oscillation bound, suitable for lower integrals. -/
theorem coulombCost_le_add_of_separated {x y z x' y' z' : E3} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    coulombCost (x, (y, z)) ≤ coulombCost (x', (y', z')) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) := by
  have hdelta : 0 ≤ delta := dist_nonneg.trans hx
  have hcost : 0 ≤ realCost x' y' z' := by unfold realCost; positivity
  have herr : 0 ≤ (6 * delta) / eta ^ 2 := by positivity
  have h := (abs_sub_le_iff.mp (abs_realCost_sub_realCost_le heta
    hxy hxz hyz hxy' hxz' hyz' hx hy hz)).1
  have hle : realCost x y z ≤ realCost x' y' z' + (6 * delta) / eta ^ 2 := by
    linarith
  rw [coulombCost_eq_ofReal_realCost (heta.trans_le hxy)
      (heta.trans_le hxz) (heta.trans_le hyz),
    coulombCost_eq_ofReal_realCost (heta.trans_le hxy')
      (heta.trans_le hxz') (heta.trans_le hyz'),
    ← ENNReal.ofReal_add hcost herr]
  exact ENNReal.ofReal_le_ofReal hle

/-- Pairwise separation of the coordinates of a triple. -/
def Separated (eta : ℝ) (t : Triple) : Prop :=
  eta ≤ dist t.1 t.2.1 ∧ eta ≤ dist t.1 t.2.2 ∧ eta ≤ dist t.2.1 t.2.2

/-- A lower-integral bound requiring only almost-everywhere separation. -/
theorem lintegral_coulombCost_le_of_ae_separated (mu : Measure Triple) {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ t ∂mu, Separated eta t) :
    (∫⁻ t, coulombCost t ∂mu) ≤ ENNReal.ofReal (3 / eta) * mu Set.univ := by
  calc
    _ ≤ ∫⁻ _t : Triple, ENNReal.ofReal (3 / eta) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with t ht
      rcases t with ⟨x, y, z⟩
      exact coulombCost_le_of_separated heta ht.1 ht.2.1 ht.2.2
    _ = _ := lintegral_const _

/-- On finite measures, almost-everywhere separation guarantees finite cost. -/
theorem lintegral_coulombCost_lt_top_of_ae_separated (mu : Measure Triple)
    [IsFiniteMeasure mu] {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ t ∂mu, Separated eta t) :
    (∫⁻ t, coulombCost t ∂mu) < ⊤ :=
  (lintegral_coulombCost_le_of_ae_separated mu heta hsep).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top mu Set.univ))

/-- A uniform graph-cost bound; no regularity of the maps is needed for this bound. -/
theorem graphCost_le_of_ae_separated (mu : Measure E3) {T2 T3 : E3 → E3} {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ x ∂mu, Separated eta (x, (T2 x, T3 x))) :
    graphCost mu T2 T3 ≤ ENNReal.ofReal (3 / eta) * mu Set.univ := by
  unfold graphCost
  calc
    _ ≤ ∫⁻ _x : E3, ENNReal.ofReal (3 / eta) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with x hx
      exact coulombCost_le_of_separated heta hx.1 hx.2.1 hx.2.2
    _ = _ := lintegral_const _

/-- The finite-cost condition in finite Monge approximation follows from separation. -/
theorem graphCost_lt_top_of_ae_separated (mu : Measure E3) [IsFiniteMeasure mu]
    {T2 T3 : E3 → E3} {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ x ∂mu, Separated eta (x, (T2 x, T3 x))) :
    graphCost mu T2 T3 < ⊤ :=
  (graphCost_le_of_ae_separated mu heta hsep).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top mu Set.univ))

/-- Integrating the pointwise oscillation bound under a common parametrization. -/
theorem lintegral_coulombCost_le_add_of_ae_close
    {A : Type uA} [MeasurableSpace A] (mu : Measure A) {P Q : A → Triple} {eta delta : ℝ}
    (heta : 0 < eta)
    (hsepP : ∀ᵐ a ∂mu, Separated eta (P a))
    (hsepQ : ∀ᵐ a ∂mu, Separated eta (Q a))
    (hclose : ∀ᵐ a ∂mu, dist (P a).1 (Q a).1 ≤ delta ∧
      dist (P a).2.1 (Q a).2.1 ≤ delta ∧ dist (P a).2.2 (Q a).2.2 ≤ delta) :
    (∫⁻ a, coulombCost (P a) ∂mu) ≤ (∫⁻ a, coulombCost (Q a) ∂mu) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) * mu Set.univ := by
  calc
    _ ≤ ∫⁻ a, coulombCost (Q a) + ENNReal.ofReal ((6 * delta) / eta ^ 2) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsepP, hsepQ, hclose] with a hP hQ hc
      exact coulombCost_le_add_of_separated heta hP.1 hP.2.1 hP.2.2
        hQ.1 hQ.2.1 hQ.2.2 hc.1 hc.2.1 hc.2.2
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const]

end Problem356.CoulombEstimates

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.BranchSeparation

/-- The central compact set and its four transported copies. -/
def components (K : Set E3) (H : Fin 4 → E3 → E3) : Fin 5 → Set E3 :=
  Fin.cases K (fun i => H i '' K)

lemma compact_components {K : Set E3} (hK : IsCompact K)
    {H : Fin 4 → E3 → E3} (hH : ∀ i, ContinuousOn (H i) K) :
    ∀ i, IsCompact (components K H i) := by
  intro i
  exact Fin.cases hK (fun j => hK.image_of_continuousOn (hH j)) i

lemma measurableSet_separated (eta : ℝ) :
    MeasurableSet {t : Triple | CoulombEstimates.Separated eta t} := by
  have h12 : Measurable (fun t : Triple => dist t.1 t.2.1) :=
    measurable_fst.dist (measurable_fst.comp measurable_snd)
  have h13 : Measurable (fun t : Triple => dist t.1 t.2.2) :=
    measurable_fst.dist (measurable_snd.comp measurable_snd)
  have h23 : Measurable (fun t : Triple => dist t.2.1 t.2.2) :=
    (measurable_fst.comp measurable_snd).dist (measurable_snd.comp measurable_snd)
  exact (measurableSet_le measurable_const h12).inter
    ((measurableSet_le measurable_const h13).inter (measurableSet_le measurable_const h23))

/-- Uniform separation for the actual cyclic two-branch coupling follows from
compactness and disjointness of its five component sets. -/
theorem exists_ae_separated_branchCoupling
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t := by
  obtain ⟨eta, heta, hsep⟩ := exists_uniform_compact_separation
    (components K H) (compact_components hK hcont) hdisjoint
  have hcentral (i : Fin 4) {x : E3} (hx : x ∈ K) : eta ≤ dist x (H i x) := by
    exact hsep 0 i.succ (Fin.succ_ne_zero i).symm x hx (H i x) (mem_image_of_mem _ hx)
  have houter (i j : Fin 4) (hij : i ≠ j) {x : E3} (hx : x ∈ K) :
      eta ≤ dist (H i x) (H j x) := by
    exact hsep i.succ j.succ (by simpa using hij) (H i x) (mem_image_of_mem _ hx)
      (H j x) (mem_image_of_mem _ hx)
  refine ⟨eta, heta, ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
    (measurableSet_separated eta) ?_ ?_ ?_⟩
  · intro x y z h
    exact ⟨h.2.2, by simpa only [dist_comm] using h.1,
      by simpa only [dist_comm] using h.2.1⟩
  · filter_upwards [hnu] with x hx
    exact ⟨hcentral 0 hx, hcentral 1 hx, houter 0 1 (by decide) hx⟩
  · filter_upwards [hnu] with x hx
    exact ⟨hcentral 2 hx, hcentral 3 hx, houter 2 3 (by decide) hx⟩

/-- The branch marginal is concentrated on the union of the central compact
set and its four images. -/
theorem ae_mem_branchMarginal_components
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3),
      x ∈ ⋃ i, components K H i := by
  have hcompact : IsCompact (⋃ i, components K H i) :=
    isCompact_iUnion (compact_components hK hcont)
  have hcentral : ∀ᵐ x ∂nu, x ∈ ⋃ i, components K H i := by
    filter_upwards [hnu] with x hx
    exact mem_iUnion.mpr ⟨0, hx⟩
  have houter (i : Fin 4) : ∀ᵐ x ∂Measure.map (H i) nu,
      x ∈ ⋃ j, components K H j := by
    apply (ae_map_iff (hH i).aemeasurable hcompact.measurableSet).mpr
    filter_upwards [hnu] with x hx
    exact mem_iUnion.mpr ⟨i.succ, mem_image_of_mem _ hx⟩
  unfold branchMarginal
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure (c := (1 / 3 : ℝ≥0∞)) hcentral
  · apply Measure.ae_smul_measure
    simp only [ae_add_measure_iff]
    exact ⟨⟨⟨houter 0, houter 1⟩, houter 2⟩, houter 3⟩

/-- The compact support and uniformly separated optimizer hypotheses needed
for finite Monge approximation hold for the explicit branch construction. -/
theorem compact_support_and_separation
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    (∃ S : Set E3, IsCompact S ∧
      ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ S) ∧
    (∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t) := by
  exact ⟨⟨⋃ i, components K H i, isCompact_iUnion (compact_components hK hcont),
    ae_mem_branchMarginal_components hK hnu hH hcont⟩,
    exists_ae_separated_branchCoupling hK hnu hH hcont hdisjoint⟩

/-- A compact subcomponent retains disjointness of the larger local domains. -/
lemma disjoint_components_mono {K B : Set E3} (hKB : K ⊆ B)
    {H : Fin 4 → E3 → E3}
    (hB : Pairwise (fun i j => Disjoint (components B H i) (components B H j))) :
    Pairwise (fun i j => Disjoint (components K H i) (components K H j)) := by
  have hsub : ∀ i, components K H i ⊆ components B H i := by
    intro i
    exact Fin.cases hKB (fun j => image_mono hKB) i
  intro i j hij
  exact (hB hij).mono (hsub i) (hsub j)

/-- Under the compact disjoint-component hypotheses, the explicit candidate
already has finite cost, before applying any dual certificate. -/
theorem finite_cost_branchCoupling
    {nu : Measure E3} [IsProbabilityMeasure nu] {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  have := isProbabilityMeasure_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  obtain ⟨eta, heta, hae⟩ := exists_ae_separated_branchCoupling hK hnu hH hcont hdisjoint
  exact CoulombEstimates.lintegral_coulombCost_lt_top_of_ae_separated _ heta hae

end Problem356.BranchSeparation

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.BranchSeparation

/-- The disjointness assumptions supplied by the local branch construction
are exactly pairwise disjointness of the five labelled components. -/
lemma pairwise_components_of_disjoint_branches {B : Set E3} {H : Fin 4 → E3 → E3}
    (hcentral : ∀ i, Disjoint B (H i '' B))
    (houter : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) :
    Pairwise fun i j => Disjoint (components B H i) (components B H j) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact False.elim (h rfl)
    · intro _
      exact hcentral j
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      exact (hcentral i).symm
    · intro h
      exact houter (fun h' => h (congrArg Fin.succ h'))

/-- Compact support and uniform separation follow directly from the local
central/outer disjointness interface used by counterexample assembly. -/
theorem compact_support_and_separation_of_branches
    {nu : Measure E3} {K B : Set E3} (hK : IsCompact K) (hKB : K ⊆ B)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hcentral : ∀ i, Disjoint B (H i '' B))
    (houter : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) :
    (∃ S : Set E3, IsCompact S ∧
      ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ S) ∧
    (∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t) :=
  compact_support_and_separation hK hnu hH hcont
    (disjoint_components_mono hKB (pairwise_components_of_disjoint_branches hcentral houter))

end Problem356.BranchSeparation

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_tripleFst : Measurable tripleFst := measurable_fst
lemma measurable_tripleSnd : Measurable tripleSnd := measurable_fst.comp measurable_snd
lemma measurable_tripleThd : Measurable tripleThd := measurable_snd.comp measurable_snd

lemma measurable_invDistance : Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  exact ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv

lemma measurable_coulombCost : Measurable coulombCost := by
  unfold coulombCost
  exact ((measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleSnd)).add
    (measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleThd))).add
    (measurable_invDistance.comp (measurable_tripleSnd.prodMk measurable_tripleThd))

def graphMap (T2 T3 : E3 → E3) (x : E3) : Triple := (x, (T2 x, T3 x))

def graphMeasure (mu : Measure E3) (T2 T3 : E3 → E3) : Measure Triple :=
  Measure.map (graphMap T2 T3) mu

lemma measurable_graphMap {T2 T3 : E3 → E3} (h2 : Measurable T2) (h3 : Measurable T3) :
    Measurable (graphMap T2 T3) := measurable_id.prodMk (h2.prodMk h3)

lemma graphMeasure_isThreeCoupling (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    IsThreeCoupling mu (graphMeasure mu T2 T3) := by
  have hm := measurable_graphMap h2.1 h3.1
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance,
    ?_, ?_, ?_⟩
  · rw [graphMeasure, Measure.map_map measurable_tripleFst hm]
    change Measure.map id mu = mu
    exact Measure.map_id
  · rw [graphMeasure, Measure.map_map measurable_tripleSnd hm]
    exact h2.2
  · rw [graphMeasure, Measure.map_map measurable_tripleThd hm]
    exact h3.2

lemma lintegral_graphMeasure (mu : Measure E3) {T2 T3 : E3 → E3}
    (h2 : Measurable T2) (h3 : Measurable T3) :
    (∫⁻ t, coulombCost t ∂graphMeasure mu T2 T3) = graphCost mu T2 T3 := by
  exact lintegral_map measurable_coulombCost (measurable_graphMap h2 h3)

lemma kantorovichValue_le_graphCost (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    kantorovichValue mu ≤ graphCost mu T2 T3 := by
  rw [← lintegral_graphMeasure mu h2.1 h3.1]
  exact iInf₂_le (graphMeasure mu T2 T3) (graphMeasure_isThreeCoupling mu h2 h3)

lemma kantorovichValue_le_mongeValue (mu : Measure E3) [IsProbabilityMeasure mu] :
    kantorovichValue mu ≤ mongeValue mu := by
  unfold mongeValue
  exact le_iInf fun T2 => le_iInf fun T3 => le_iInf fun h2 => le_iInf fun h3 =>
    kantorovichValue_le_graphCost mu h2 h3

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A property holding almost everywhere for the common marginal holds in all
three coordinates of every feasible coupling. No measurability of the property
is needed for this direction of transport. -/
lemma IsThreeCoupling.ae_coordinates {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {p : E3 → Prop} (hp : ∀ᵐ x ∂mu, p x) :
    ∀ᵐ t ∂pi, p (tripleFst t) ∧ p (tripleSnd t) ∧ p (tripleThd t) := by
  have h1 : ∀ᵐ t ∂pi, p (tripleFst t) := by
    apply ae_of_ae_map measurable_tripleFst.aemeasurable
    simpa only [hpi.2.1] using hp
  have h2 : ∀ᵐ t ∂pi, p (tripleSnd t) := by
    apply ae_of_ae_map measurable_tripleSnd.aemeasurable
    simpa only [hpi.2.2.1] using hp
  have h3 : ∀ᵐ t ∂pi, p (tripleThd t) := by
    apply ae_of_ae_map measurable_tripleThd.aemeasurable
    simpa only [hpi.2.2.2] using hp
  exact h1.and (h2.and h3)

/-- Full marginal mass on a measurable set gives almost-everywhere membership. -/
lemma ae_mem_of_probability_measure_eq_one {mu : Measure E3} [IsProbabilityMeasure mu]
    {U : Set E3} (hU : MeasurableSet U) (hfull : mu U = 1) :
    ∀ᵐ x ∂mu, x ∈ U := by
  rw [ae_iff]
  change mu Uᶜ = 0
  rw [measure_compl hU (by simp [hfull]), measure_univ, hfull, tsub_self]

/-- Every coupling of a probability carried by `U` is carried by `U³`. -/
lemma IsThreeCoupling.ae_mem_cube {mu : Measure E3} [IsProbabilityMeasure mu]
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    {U : Set E3} (hU : MeasurableSet U) (hfull : mu U = 1) :
    ∀ᵐ t ∂pi, tripleFst t ∈ U ∧ tripleSnd t ∈ U ∧ tripleThd t ∈ U :=
  hpi.ae_coordinates (ae_mem_of_probability_measure_eq_one hU hfull)

/-- A pointwise certificate on the full-mass cube may be used almost everywhere
against any feasible coupling. -/
lemma IsThreeCoupling.ae_of_on_cube {mu : Measure E3} [IsProbabilityMeasure mu]
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    {U : Set E3} (hU : MeasurableSet U) (hfull : mu U = 1)
    {P : Triple → Prop}
    (hP : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U → P t) :
    ∀ᵐ t ∂pi, P t := by
  filter_upwards [hpi.ae_mem_cube hU hfull] with t ht
  exact hP t ht.1 ht.2.1 ht.2.2

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A contact condition for optimal couplings also holds along any optimal
admissible graph. This needs no measurable-set hypothesis on `Contact`. -/
lemma ae_contact_of_graphCost_eq {mu : Measure E3} [IsProbabilityMeasure mu]
    {Contact : Triple → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3)
    (hopt : graphCost mu T2 T3 = kantorovichValue mu) :
    ∀ᵐ x ∂mu, Contact (graphMap T2 T3 x) := by
  have hpi := graphMeasure_isThreeCoupling mu h2 h3
  have hcost : (∫⁻ t, coulombCost t ∂graphMeasure mu T2 T3) =
      kantorovichValue mu := (lintegral_graphMeasure mu h2.1 h3.1).trans hopt
  exact ae_of_ae_map (measurable_graphMap h2.1 h3.1).aemeasurable
    (hcontact (graphMeasure mu T2 T3) hpi hcost)

lemma noMongeOptimizer_of_contact_obstruction (mu : Measure E3) [IsProbabilityMeasure mu]
    {Contact : Triple → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    (hobstruction : ∀ T2 T3 : E3 → E3, Preserves mu T2 → Preserves mu T3 →
      ¬ (∀ᵐ x ∂mu, Contact (graphMap T2 T3 x))) :
    NoMongeOptimizer mu := by
  intro T2 T3 h2 h3
  refine lt_of_le_of_ne (kantorovichValue_le_graphCost mu h2 h3) ?_
  intro heq
  exact hobstruction T2 T3 h2 h3 (ae_contact_of_graphCost_eq hcontact h2 h3 heq.symm)

/-- Abstract branch-selection endgame. A contact triple whose first coordinate
lies in `B` forces its second coordinate to satisfy `Select`. If no preserving
map can satisfy that selection almost everywhere for an absolutely continuous
submeasure, no admissible graph is optimal. -/
lemma noMongeOptimizer_of_selection_obstruction
    (mu nu : Measure E3) [IsProbabilityMeasure mu]
    (hnu : nu ≪ mu) {B : Set E3} (hB : ∀ᵐ x ∂nu, x ∈ B)
    {Contact : Triple → Prop} {Select : E3 → E3 → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    (hselect : ∀ x y z : E3, x ∈ B → Contact (x, (y, z)) → Select x y)
    (hobstruction : ∀ T : E3 → E3, Preserves mu T →
      ¬ (∀ᵐ x ∂nu, Select x (T x))) :
    NoMongeOptimizer mu := by
  apply noMongeOptimizer_of_contact_obstruction mu hcontact
  intro T2 T3 h2 h3 hgraph
  apply hobstruction T2 h2
  have hgraph' : ∀ᵐ x ∂nu, Contact (graphMap T2 T3 x) := hnu.ae_le hgraph
  filter_upwards [hB, hgraph'] with x hx hcx
  exact hselect x (T2 x) (T3 x) hx hcx

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356
namespace DualCertificate

/-- The sum of a nonnegative supporting potential over the three coordinates.
A bounded signed potential can be shifted by a constant before using this sum. -/
def potentialSum (v : E3 → ℝ≥0∞) (t : Triple) : ℝ≥0∞ :=
  v (tripleFst t) + v (tripleSnd t) + v (tripleThd t)

lemma measurable_potentialSum {v : E3 → ℝ≥0∞} (hv : Measurable v) :
    Measurable (potentialSum v) := by
  exact ((hv.comp measurable_fst).add
    (hv.comp (measurable_fst.comp measurable_snd))).add
    (hv.comp (measurable_snd.comp measurable_snd))

/-- The integral of a coordinate potential sum depends only on the common marginal. -/
lemma lintegral_potentialSum {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v) :
    (∫⁻ t, potentialSum v t ∂pi) =
      (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) := by
  have hf : Measurable tripleFst := measurable_fst
  have hs : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have ht : Measurable tripleThd := measurable_snd.comp measurable_snd
  simp only [potentialSum]
  have hfs : Measurable (fun t : Triple => v (tripleFst t) + v (tripleSnd t)) :=
    (hv.comp hf).add (hv.comp hs)
  have hf' : Measurable (fun t : Triple => v (tripleFst t)) := hv.comp hf
  rw [lintegral_add_left hfs,
    lintegral_add_left hf',
    ← lintegral_map hv hf, ← lintegral_map hv hs, ← lintegral_map hv ht,
    hpi.2.1, hpi.2.2.1, hpi.2.2.2]

/-- Adding a constant to a nonnegative cost shifts its integral by that constant
under a probability measure; no measurability assumption on the cost is needed. -/
lemma lintegral_add_offset {α : Type uAlpha} [MeasurableSpace α]
    (pi : Measure α) [IsProbabilityMeasure pi] (c : α → ℝ≥0∞) (offset : ℝ≥0∞) :
    (∫⁻ t, c t + offset ∂pi) = (∫⁻ t, c t ∂pi) + offset := by
  rw [lintegral_add_right c measurable_const]
  simp

/-- Complementary slackness for a shifted nonnegative certificate. -/
lemma ae_contact_of_equal_integrals {α : Type uAlpha} [MeasurableSpace α]
    {pi : Measure α} [IsProbabilityMeasure pi] {p c : α → ℝ≥0∞}
    {offset : ℝ≥0∞} (hc : AEMeasurable c pi)
    (hbound : p ≤ᵐ[pi] fun t => c t + offset)
    (hfinite : (∫⁻ t, p t ∂pi) ≠ ⊤)
    (heq : (∫⁻ t, p t ∂pi) = (∫⁻ t, c t ∂pi) + offset) :
    p =ᵐ[pi] fun t => c t + offset := by
  apply ae_eq_of_ae_le_of_lintegral_le hbound hfinite (hc.add aemeasurable_const)
  rw [lintegral_add_offset, heq]

/-- A finite shifted dual value forces every optimal coupling onto the
contact set.  The value identity is the sole input needed from dual optimality. -/
lemma ae_contact_of_optimal_coupling {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hfinite : kantorovichValue mu ≠ ⊤)
    (hcost : AEMeasurable coulombCost pi)
    (hbound : potentialSum v ≤ᵐ[pi] fun t => coulombCost t + offset)
    (hvalue : (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
      kantorovichValue mu + offset)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu) :
    potentialSum v =ᵐ[pi] fun t => coulombCost t + offset := by
  have : IsProbabilityMeasure pi := hpi.1
  have hid := lintegral_potentialSum hpi hv
  rw [hvalue] at hid
  exact ae_contact_of_equal_integrals hcost hbound
    (hid ▸ ENNReal.add_ne_top.mpr ⟨hfinite, hoffset⟩)
    (by rw [hoptimal]; exact hid)

/-- If a feasible coupling is not concentrated on contact, its cost is strictly
larger than a finite calibrated value. This is the contrapositive form needed
for the deterministic-selection obstruction. -/
lemma cost_strictly_above_of_noncontact {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset value : ℝ≥0∞} (hoffset : offset ≠ ⊤) (hfinite : value ≠ ⊤)
    (hcost : AEMeasurable coulombCost pi)
    (hbound : potentialSum v ≤ᵐ[pi] fun t => coulombCost t + offset)
    (hvalue : (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
      value + offset)
    (hnoncontact : ¬ (potentialSum v =ᵐ[pi] fun t => coulombCost t + offset)) :
    value < ∫⁻ t, coulombCost t ∂pi := by
  have : IsProbabilityMeasure pi := hpi.1
  have hid := lintegral_potentialSum hpi hv
  rw [hvalue] at hid
  have hfreq : ∃ᵐ t ∂pi, potentialSum v t ≠ coulombCost t + offset := by
    change ¬ (∀ᵐ t ∂pi, potentialSum v t = coulombCost t + offset) at hnoncontact
    simpa only [Filter.Frequently, not_not] using hnoncontact
  have hstrict := lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
    (hcost.add aemeasurable_const)
    (hid ▸ ENNReal.add_ne_top.mpr ⟨hfinite, hoffset⟩) hbound hfreq
  change (∫⁻ t, potentialSum v t ∂pi) < (∫⁻ t, coulombCost t + offset ∂pi) at hstrict
  rw [hid, lintegral_add_offset] at hstrict
  exact (ENNReal.add_lt_add_iff_right hoffset).mp hstrict

end DualCertificate
end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A nonnegative dual certificate after adding a finite constant to the cost.
The shift permits a signed bounded real-valued supporting potential. -/
structure ShiftedCoulombCertificate (mu : Measure E3) (value : ℝ≥0∞) where
  potential : Triple → ℝ≥0∞
  shift : ℝ≥0∞
  shift_ne_top : shift ≠ ⊤
  lower_bound : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
    ∀ᵐ t ∂pi, potential t ≤ coulombCost t + shift
  integral_eq : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
    (∫⁻ t, potential t ∂pi) = value + shift

namespace ShiftedCoulombCertificate

variable {mu : Measure E3} {value : ℝ≥0∞}

private theorem measurable_coulomb : Measurable coulombCost := by
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  fun_prop

/-- A constant shift integrates to itself under any feasible coupling. -/
theorem lintegral_cost_add (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi) :
    (∫⁻ t, coulombCost t + cert.shift ∂pi) =
      (∫⁻ t, coulombCost t ∂pi) + cert.shift := by
  have : IsProbabilityMeasure pi := hpi.1
  rw [lintegral_add_right _ measurable_const]
  simp

/-- Every coupling has cost at least the certified value. -/
theorem le_cost (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi) :
    value ≤ ∫⁻ t, coulombCost t ∂pi := by
  apply (ENNReal.add_le_add_iff_right cert.shift_ne_top).mp
  rw [← cert.integral_eq pi hpi, ← cert.lintegral_cost_add hpi]
  exact lintegral_mono_ae (cert.lower_bound pi hpi)

/-- A feasible candidate matching a certificate realizes the exact infimum. -/
theorem value_eq (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    kantorovichValue mu = value := by
  apply le_antisymm
  · exact iInf_le_of_le pi (iInf_le_of_le hpi hcost.le)
  · exact le_iInf fun q => le_iInf fun hq => cert.le_cost hq

/-- A matching candidate supplies the attainment assertion. -/
theorem attained (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    KantorovichAttained mu := by
  exact ⟨pi, hpi, hcost.trans (cert.value_eq hpi hcost).symm⟩

/-- Equality of the finite primal and dual integrals forces equality almost
 everywhere in the supporting inequality. -/
theorem ae_contact (cert : ShiftedCoulombCertificate mu value)
    (hfinite : value ≠ ⊤) {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    ∀ᵐ t ∂pi, cert.potential t = coulombCost t + cert.shift := by
  apply ae_eq_of_ae_le_of_lintegral_le (cert.lower_bound pi hpi)
  · rw [cert.integral_eq pi hpi]
    exact ENNReal.add_ne_top.mpr ⟨hfinite, cert.shift_ne_top⟩
  · exact (measurable_coulomb.add measurable_const).aemeasurable
  · rw [cert.lintegral_cost_add hpi, cert.integral_eq pi hpi, hcost]

/-- An optimal plan is concentrated on any prescribed set that contains the
contact locus of the supporting certificate. -/
theorem ae_mem_of_optimal (cert : ShiftedCoulombCertificate mu value)
    (hfinite : value ≠ ⊤) (hvalue : kantorovichValue mu = value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hopt : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {contact : Set Triple}
    (hcontact : ∀ t, cert.potential t = coulombCost t + cert.shift → t ∈ contact) :
    ∀ᵐ t ∂pi, t ∈ contact := by
  exact (cert.ae_contact hfinite hpi (hopt.trans hvalue)).mono hcontact

end ShiftedCoulombCertificate

theorem noMongeOptimizer_of_ne
    {mu : Measure E3}
    (hlower : ∀ T2 T3, Preserves mu T2 → Preserves mu T3 →
      kantorovichValue mu ≤ graphCost mu T2 T3)
    (hne : ∀ T2 T3, Preserves mu T2 → Preserves mu T3 →
      graphCost mu T2 T3 ≠ kantorovichValue mu) :
    NoMongeOptimizer mu := by
  intro T2 T3 h2 h3
  exact lt_of_le_of_ne (hlower T2 T3 h2 h3) (hne T2 T3 h2 h3).symm

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A bounded-below signed potential is made nonnegative by a constant shift. -/
def shiftedPotential (u : E3 → ℝ) (M : ℝ) (x : E3) : ℝ≥0∞ :=
  ENNReal.ofReal (u x + M)

lemma measurable_shiftedPotential {u : E3 → ℝ} (hu : Measurable u) (M : ℝ) :
    Measurable (shiftedPotential u M) :=
  (hu.add_const M).ennreal_ofReal

lemma shifted_three_sum {a b c M : ℝ}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      ENNReal.ofReal (a + b + c + 3 * M) := by
  have ha' : 0 ≤ a + M := by linarith
  have hb' : 0 ≤ b + M := by linarith
  have hc' : 0 ≤ c + M := by linarith
  rw [← ENNReal.ofReal_add ha' hb', ← ENNReal.ofReal_add (add_nonneg ha' hb') hc']
  congr 1
  ring

lemma shifted_three_le {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c)
    (h : ENNReal.ofReal (a + b + c) ≤ z) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) ≤
      z + ENNReal.ofReal (3 * M) := by
  rw [shifted_three_sum ha hb hc]
  exact ENNReal.ofReal_add_le.trans (add_le_add h le_rfl)

lemma shifted_three_eq_of_contact {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (hs : 0 ≤ a + b + c) (hz : ENNReal.ofReal (a + b + c) = z) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M) := by
  rw [shifted_three_sum ha hb hc, ENNReal.ofReal_add hs (by positivity), hz]

lemma contact_of_shifted_three_eq {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (h : ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) +
      ENNReal.ofReal (c + M) = z + ENNReal.ofReal (3 * M)) :
    0 ≤ a + b + c ∧ ENNReal.ofReal (a + b + c) = z := by
  rw [shifted_three_sum ha hb hc] at h
  have hz : z ≠ ⊤ := by
    intro hz
    simp only [hz, top_add] at h
    exact ENNReal.ofReal_ne_top h
  have hs : 0 ≤ a + b + c + 3 * M := by linarith
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal hs, ENNReal.toReal_add hz ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 3 * M)] at ht
  have heq : a + b + c = z.toReal := by linarith
  constructor
  · rw [heq]
    exact ENNReal.toReal_nonneg
  · rw [heq, ENNReal.ofReal_toReal hz]

lemma shifted_three_eq_iff {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M)) ↔
      0 ≤ a + b + c ∧ ENNReal.ofReal (a + b + c) = z := by
  exact ⟨contact_of_shifted_three_eq ha hb hc hM,
    fun h => shifted_three_eq_of_contact ha hb hc hM h.1 h.2⟩

/-- The shift preserves the supporting inequality, including negative signed sums. -/
lemma shifted_three_le_iff {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) ≤
      z + ENNReal.ofReal (3 * M)) ↔ ENNReal.ofReal (a + b + c) ≤ z := by
  constructor
  · intro h
    by_cases hs : 0 ≤ a + b + c
    · rw [shifted_three_sum ha hb hc, ENNReal.ofReal_add hs (by positivity)] at h
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h
    · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge hs)]
      exact bot_le
  · exact shifted_three_le ha hb hc

/-- For a positive cost, equality already forces nonnegativity of the signed sum. -/
lemma shifted_three_eq_iff_of_pos {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (hz : 0 < z) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M)) ↔ ENNReal.ofReal (a + b + c) = z := by
  rw [shifted_three_eq_iff ha hb hc hM]
  constructor
  · exact And.right
  · intro h
    refine ⟨le_of_lt (ENNReal.ofReal_pos.mp ?_), h⟩
    rw [h]
    exact hz

lemma shiftedPotential_certificate {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t))
    (h : ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
      coulombCost t) :
    shiftedPotential u M (tripleFst t) + shiftedPotential u M (tripleSnd t) +
      shiftedPotential u M (tripleThd t) ≤ coulombCost t + ENNReal.ofReal (3 * M) :=
  shifted_three_le h1 h2 h3 h

lemma shiftedPotential_contact_iff {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t)) (hM : 0 ≤ M) :
    (shiftedPotential u M (tripleFst t) + shiftedPotential u M (tripleSnd t) +
      shiftedPotential u M (tripleThd t) = coulombCost t + ENNReal.ofReal (3 * M)) ↔
      0 ≤ u (tripleFst t) + u (tripleSnd t) + u (tripleThd t) ∧
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) =
        coulombCost t :=
  shifted_three_eq_iff h1 h2 h3 hM

/-- An almost-everywhere upper bound suffices for finiteness of the shifted
potential; no signed-integrability conversion is needed. -/
lemma lintegral_shiftedPotential_le_of_ae_le {mu : Measure E3} [IsProbabilityMeasure mu]
    {u : E3 → ℝ} {M A : ℝ} (hbound : ∀ᵐ x ∂mu, u x ≤ A) :
    (∫⁻ x, shiftedPotential u M x ∂mu) ≤ ENNReal.ofReal (A + M) := by
  calc
    (∫⁻ x, shiftedPotential u M x ∂mu) ≤ (∫⁻ _x, ENNReal.ofReal (A + M) ∂mu) := by
      apply lintegral_mono_ae
      exact hbound.mono fun x hx => ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (A + M) := by simp

lemma lintegral_shiftedPotential_lt_top_of_ae_le {mu : Measure E3}
    [IsProbabilityMeasure mu] {u : E3 → ℝ} {M A : ℝ}
    (hbound : ∀ᵐ x ∂mu, u x ≤ A) :
    (∫⁻ x, shiftedPotential u M x ∂mu) < ⊤ :=
  (lintegral_shiftedPotential_le_of_ae_le hbound).trans_lt ENNReal.ofReal_lt_top

lemma lintegral_shiftedPotential {mu : Measure E3} [IsProbabilityMeasure mu]
    {u : E3 → ℝ} (hu : Integrable u mu) (M : ℝ)
    (hbound : ∀ᵐ x ∂mu, -M ≤ u x) :
    (∫⁻ x, shiftedPotential u M x ∂mu) =
      ENNReal.ofReal ((∫ x, u x ∂mu) + M) := by
  have hn : 0 ≤ᵐ[mu] fun x => u x + M := hbound.mono fun x hx => by
    dsimp
    linarith
  have hi : Integrable (fun x => u x + M) mu := hu.add (integrable_const M)
  calc
    (∫⁻ x, shiftedPotential u M x ∂mu) =
        ENNReal.ofReal (∫ x, u x + M ∂mu) :=
      (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    _ = ENNReal.ofReal ((∫ x, u x ∂mu) + M) := by
      rw [integral_add hu (integrable_const M)]
      simp

lemma lintegral_shiftedPotential_lt_top {mu : Measure E3} [IsProbabilityMeasure mu]
    {u : E3 → ℝ} (hu : Integrable u mu) (M : ℝ)
    (hbound : ∀ᵐ x ∂mu, -M ≤ u x) :
    (∫⁻ x, shiftedPotential u M x ∂mu) < ⊤ := by
  rw [lintegral_shiftedPotential hu M hbound]
  exact ENNReal.ofReal_lt_top

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

open DualCertificate

namespace ShiftedCoulombCertificate

/-- A contact candidate calibrates the common marginal potential integral.
This constructs the abstract certificate without assuming the candidate is optimal. -/
def ofContactCandidate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, potentialSum v t ≤ coulombCost t + offset)
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    ShiftedCoulombCertificate mu (∫⁻ t, coulombCost t ∂pi0) where
  potential := potentialSum v
  shift := offset
  shift_ne_top := hoffset
  lower_bound := hbound
  integral_eq := by
    intro pi hpi
    have : IsProbabilityMeasure pi0 := hpi0.1
    rw [lintegral_potentialSum hpi hv, ← lintegral_potentialSum hpi0 hv,
      ← lintegral_add_offset pi0 coulombCost offset]
    exact lintegral_congr_ae hcontact

end ShiftedCoulombCertificate

/-- Finite marginal potential integral makes every contact candidate finite. -/
theorem candidateCost_lt_top_of_contact {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    (hvfinite : (∫⁻ x, v x ∂mu) ≠ ⊤) {offset : ℝ≥0∞}
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    (∫⁻ t, coulombCost t ∂pi0) < ⊤ := by
  have : IsProbabilityMeasure pi0 := hpi0.1
  have hsum : (∫⁻ t, coulombCost t ∂pi0) + offset ≠ ⊤ := by
    rw [← lintegral_add_offset pi0 coulombCost offset,
      ← lintegral_congr_ae hcontact, lintegral_potentialSum hpi0 hv]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hvfinite, hvfinite⟩, hvfinite⟩
  exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mp hsum).1

theorem attained_finite_of_contact_candidate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    (hvfinite : (∫⁻ x, v x ∂mu) ≠ ⊤) {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, potentialSum v t ≤ coulombCost t + offset)
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    KantorovichAttained mu ∧ kantorovichValue mu < ⊤ ∧
      kantorovichValue mu = (∫⁻ t, coulombCost t ∂pi0) ∧
      (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
        kantorovichValue mu + offset := by
  let cert := ShiftedCoulombCertificate.ofContactCandidate hpi0 hv hoffset hbound hcontact
  have hvalue := cert.value_eq hpi0 rfl
  refine ⟨cert.attained hpi0 rfl, ?_, hvalue, ?_⟩
  · rw [hvalue]
    exact candidateCost_lt_top_of_contact hpi0 hv hvfinite hcontact
  · rw [hvalue, ← lintegral_potentialSum hpi0 hv]
    exact cert.integral_eq pi0 hpi0

/-- The sum of the marginal potential over the three coordinates. -/
def triplePotential (p : E3 → ℝ≥0∞) (t : Triple) : ℝ≥0∞ :=
  p (tripleFst t) + p (tripleSnd t) + p (tripleThd t)

theorem measurable_triplePotential {p : E3 → ℝ≥0∞} (hp : Measurable p) :
    Measurable (triplePotential p) := DualCertificate.measurable_potentialSum hp

theorem IsThreeCoupling.ae_of_support_certificate {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {U : Set E3} (hU : MeasurableSet U)
    (hmu : ∀ᵐ x ∂mu, x ∈ U) {P : Triple → Prop}
    (hP : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U → P t) :
    ∀ᵐ t ∂pi, P t := by
  have hf : Measurable tripleFst := measurable_fst
  have hs : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have ht : Measurable tripleThd := measurable_snd.comp measurable_snd
  have h1 : ∀ᵐ t ∂pi, tripleFst t ∈ U :=
    (ae_map_iff hf.aemeasurable hU).mp (by rwa [hpi.2.1])
  have h2 : ∀ᵐ t ∂pi, tripleSnd t ∈ U :=
    (ae_map_iff hs.aemeasurable hU).mp (by rwa [hpi.2.2.1])
  have h3 : ∀ᵐ t ∂pi, tripleThd t ∈ U :=
    (ae_map_iff ht.aemeasurable hU).mp (by rwa [hpi.2.2.2])
  exact (h1.and (h2.and h3)).mono fun t h => hP t h.1 h.2.1 h.2.2

theorem certificate_optimality {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C) :
    (∫⁻ t, coulombCost t ∂pi0) = kantorovichValue mu ∧
      (∫⁻ t, coulombCost t ∂pi0) < ⊤ := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact ⟨h.2.2.1.symm, candidateCost_lt_top_of_contact hpi0 hp hpfinite hcontact⟩

theorem kantorovichAttained_of_certificate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C) :
    KantorovichAttained mu ∧ kantorovichValue mu < ⊤ := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact ⟨h.1, h.2.1⟩

theorem certificate_contact_of_optimal {mu : Measure E3} {pi0 pi : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) (hpi : IsThreeCoupling mu pi)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hcost : Measurable coulombCost)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu) :
    ∀ᵐ t ∂pi, triplePotential p t = coulombCost t + C := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact DualCertificate.ae_contact_of_optimal_coupling hpi hp hC h.2.1.ne
    hcost.aemeasurable (hbound pi hpi) h.2.2.2 hoptimal

end Problem356

end

end OAI
end
end

section
section
namespace OAI


/-!
# The deterministic-selection mass obstruction

A preserving map cannot carry a positive-mass selection set into a target
whose prescribed mass is a strictly smaller multiple of the same reference
mass.  This is the measure-theoretic obstruction in the Coulomb construction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- Preservation and a strict compression of the reference mass force the
selected set to have reference measure zero. -/
theorem reference_mass_zero_of_compression
    {μ ν : Measure α} {T : α → α} {S A : Set α} {c d : ℝ≥0∞}
    (hT : Measurable T) (hpres : Measure.map T μ = μ)
    (hA : MeasurableSet A) (hsub : S ⊆ T ⁻¹' A)
    (hsource : μ S = c * ν S) (htarget : μ A = d * ν S)
    (hdc : d < c) (hfinite : ν S ≠ ⊤) : ν S = 0 := by
  by_contra hne
  have hle : c * ν S ≤ d * ν S := calc
    c * ν S = μ S := hsource.symm
    _ ≤ μ (T ⁻¹' A) := measure_mono hsub
    _ = (Measure.map T μ) A := (Measure.map_apply hT hA).symm
    _ = μ A := by rw [hpres]
    _ = d * ν S := htarget
  exact (not_lt_of_ge hle)
    ((ENNReal.mul_lt_mul_iff_left hne hfinite).2 hdc)

/-- No preserving map can implement a countable almost-everywhere selection
whose source and target masses have a uniformly strict reversed ratio. -/
theorem not_preserving_of_countable_compression [Countable ι]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    {T : α → α} {S A : ι → Set α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0)
    (hA : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, S i ⊆ T ⁻¹' A i)
    (hsource : ∀ i, μ (S i) = c * ν (S i))
    (htarget : ∀ i, μ (A i) = d * ν (S i))
    (hdc : d < c)
    (hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i) :
    ¬ (Measurable T ∧ Measure.map T μ = μ) := by
  rintro ⟨hT, hpres⟩
  have hzero : ∀ i, ν (S i) = 0 := fun i =>
    reference_mass_zero_of_compression hT hpres (hA i) (hsub i)
      (hsource i) (htarget i) hdc (measure_ne_top ν (S i))
  have hnull : ν (⋃ i, S i) = 0 := measure_iUnion_null hzero
  have hfull : (⋃ i, S i) =ᵐ[ν] Set.univ := by
    filter_upwards [hcover] with x hx
    apply propext
    show x ∈ (⋃ i, S i) ↔ x ∈ (Set.univ : Set _)
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hx
  exact hν ((measure_congr hfull).symm.trans hnull)

/-- The branch-selection formulation. The hypotheses about selected-set
masses are exactly those supplied by disjoint weighted pushforward
components. No regularity beyond measurability is imposed on the selector. -/
theorem no_preserving_branch_selection [Countable ι] [MeasurableEq α]
    {μ ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hsource : ∀ S, MeasurableSet S → S ⊆ B → μ S = c * ν S)
    (htarget : ∀ i S, MeasurableSet S → S ⊆ B →
      μ (H i '' S) = d * ν S)
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧ Measure.map T μ = μ ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  rintro ⟨T, hT, hpres, hselect⟩
  let S : ι → Set α := fun i => B ∩ {x | T x = H i x}
  have hS : ∀ i, MeasurableSet (S i) := fun i =>
    hB.inter (measurableSet_eq_fun hT (hH i))
  have hSB : ∀ i, S i ⊆ B := fun _ => Set.inter_subset_left
  have hsub : ∀ i, S i ⊆ T ⁻¹' (H i '' S i) := by
    intro i x hx
    exact ⟨x, hx, hx.2.symm⟩
  have hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i := by
    filter_upwards [hfull, hselect] with x hx hsel
    obtain ⟨i, hi⟩ := hsel
    exact ⟨i, hx, hi⟩
  exact not_preserving_of_countable_compression hν
    (fun i => himage i (S i) (hS i) (hSB i)) hsub
    (fun i => hsource (S i) (hS i) (hSB i))
    (fun i => htarget i (S i) (hS i) (hSB i)) hdc hcover ⟨hT, hpres⟩

end Problem356.Splitting

end

end OAI
end
end

section
section
namespace OAI


/-! Measure identities for the five-component splitting construction. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356
namespace Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- A measure supported almost everywhere on `B` vanishes on any set disjoint from `B`. -/
theorem measure_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hBS : Disjoint B S) : ν S = 0 := by
  apply measure_mono_null (t := Bᶜ)
  · intro x hx
    exact fun hxB => Set.disjoint_left.mp hBS hxB hx
  · exact ae_iff.mp hν

/-- A branch pushforward vanishes away from the image of the central component. -/
theorem map_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hS : MeasurableSet S) (hBS : Disjoint (H '' B) S) :
    (Measure.map H ν) S = 0 := by
  rw [Measure.map_apply hH hS]
  apply measure_eq_zero_of_disjoint ν hν
  exact Set.disjoint_left.mpr fun x hxB hxS =>
    Set.disjoint_left.mp hBS ⟨x, hxB, rfl⟩ hxS

/-- An injective branch has the original mass on the image of each central subset. -/
theorem map_image_eq
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hInj : Set.InjOn H B) (hSB : S ⊆ B)
    (hImage : MeasurableSet (H '' S)) :
    (Measure.map H ν) (H '' S) = ν S := by
  rw [Measure.map_apply hH hImage]
  apply measure_congr
  filter_upwards [hν] with x hx
  apply propext
  change H x ∈ H '' S ↔ x ∈ S
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := hInj (hSB hy) hx hxy
    simpa only [hyx] using hy
  · intro hxS
    exact ⟨x, hxS, rfl⟩

variable [Fintype ι]

/-- The central measure together with finitely many weighted branch pushforwards. -/
def splitMeasure (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞)
    (H : ι → α → α) : Measure α :=
  a • ν + ∑ i, b i • Measure.map (H i) ν

/-- Weights adding to one produce a probability measure. -/
theorem splitMeasure_isProbabilityMeasure
    (ν : Measure α) [IsProbabilityMeasure ν]
    (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    (hH : ∀ i, Measurable (H i)) (hweight : a + ∑ i, b i = 1) :
    IsProbabilityMeasure (splitMeasure ν a b H) := by
  have hmass : ∀ i, (Measure.map (H i) ν) Set.univ = 1 := by
    intro i
    rw [Measure.map_apply (hH i) MeasurableSet.univ]
    simp
  constructor
  simpa [splitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, hmass] using hweight

/-- A nonzero central coefficient transfers all almost-everywhere properties
of the mixture to its central reference measure. -/
theorem absolutelyContinuous_splitMeasure
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    (ha : a ≠ 0) : ν ≪ splitMeasure ν a b H := by
  exact (Measure.absolutelyContinuous_smul ha).add_right _

/-- On the central component, only the central summand contributes. -/
theorem splitMeasure_apply_central
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hSB : S ⊆ B) (hS : MeasurableSet S)
    (hDisj : ∀ i, Disjoint B (H i '' B)) :
    splitMeasure ν a b H S = a * ν S := by
  have hz : ∀ i, (Measure.map (H i) ν) S = 0 := by
    intro i
    apply map_eq_zero_of_disjoint ν hν (hH i) hS
    exact (hDisj i).symm.mono_right hSB
  simp [splitMeasure, Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, hz]

/-- On one branch image only that branch summand contributes. -/
theorem splitMeasure_apply_image
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hInj : ∀ i, Set.InjOn (H i) B)
    (hSB : S ⊆ B) (hImage : ∀ i, MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) (j : ι) :
    splitMeasure ν a b H (H j '' S) = b j * ν S := by
  classical
  have hsub : H j '' S ⊆ H j '' B := Set.image_mono hSB
  have hz : ν (H j '' S) = 0 :=
    measure_eq_zero_of_disjoint ν hν ((hCentral j).mono_right hsub)
  have hij : ∀ i, i ≠ j → (Measure.map (H i) ν) (H j '' S) = 0 := by
    intro i hne
    exact map_eq_zero_of_disjoint ν hν (hH i) (hImage j)
      ((hPair hne).mono_right hsub)
  have hj : (Measure.map (H j) ν) (H j '' S) = ν S :=
    map_image_eq ν hν (hH j) (hInj j) hSB (hImage j)
  simp only [splitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, hz, mul_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · exact congrArg (b j * ·) hj
  · intro i _ hne
    simp [hij i hne]
  · simp

end Splitting
end Problem356

end

end OAI
end
end

section
section
namespace OAI


/-!
# The disjoint-component selection obstruction

This combines the abstract mass argument with the exact mass identities for
a finite mixture of a central measure and its injective branch pushforwards.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356.Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α] [Fintype ι]

/-- A finite family of disjoint injective branches with strictly smaller
outer coefficients cannot support any preserving deterministic selector. -/
theorem no_preserving_splitMeasure_selection [MeasurableEq α]
    {ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧
      Measure.map T (splitMeasure ν c (fun _ => d) H) =
        splitMeasure ν c (fun _ => d) H ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  apply no_preserving_branch_selection hν hB hfull hH himage
  · intro S hS hSB
    exact splitMeasure_apply_central ν c (fun _ => d) H
      hfull hH hSB hS hCentral
  · intro i S hS hSB
    exact splitMeasure_apply_image ν c (fun _ => d) H
      hfull hH hInj hSB (fun j => himage j S hS hSB) hCentral hPair i
  · exact hdc

end Problem356.Splitting

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- The four-map marginal is the generic finite split measure, with central
weight `1/3` and four equal outer weights `1/6`. -/
lemma branchMarginal_eq_splitMeasure (nu : Measure E3) (H : Fin 4 → E3 → E3) :
    branchMarginal nu (H 0) (H 1) (H 2) (H 3) =
      Splitting.splitMeasure nu (1 / 3) (fun _ : Fin 4 => 1 / 6) H := by
  simp [branchMarginal, Splitting.splitMeasure, Fin.sum_univ_succ, smul_add, add_assoc]

/-- Support of the central measure and its four images gives support of the
five-component marginal. -/
lemma ae_branchMarginal_mem (nu : Measure E3) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) {B U : Set E3}
    (hU : MeasurableSet U) (hfull : ∀ᵐ x ∂nu, x ∈ B)
    (hBU : B ⊆ U) (hHU : ∀ i, H i '' B ⊆ U) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U := by
  have hcentral : ∀ᵐ x ∂nu, x ∈ U := hfull.mono fun _ hx => hBU hx
  have houter : ∀ i, ∀ᵐ x ∂Measure.map (H i) nu, x ∈ U := by
    intro i
    apply (ae_map_iff (hH i).aemeasurable hU).mpr
    exact hfull.mono fun x hx => hHU i ⟨x, hx, rfl⟩
  unfold branchMarginal
  apply ae_add_measure_iff.mpr
  refine ⟨Measure.ae_smul_measure hcentral _, Measure.ae_smul_measure ?_ _⟩
  exact ae_add_measure_iff.mpr
    ⟨ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨houter 0, houter 1⟩, houter 2⟩,
      houter 3⟩

private lemma coulombCost_cycle_assembly (x y z : E3) :
    coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev y x, norm_sub_rev z x]
  ac_rfl

private lemma triplePotential_cycle_assembly (p : E3 → ℝ≥0∞) (x y z : E3) :
    triplePotential p (y, (z, x)) = triplePotential p (x, (y, z)) := by
  simp only [triplePotential, tripleFst, tripleSnd, tripleThd]
  ac_rfl

theorem hasCoulombCounterexample_of_branches
    (rho : E3 → ℝ) (hrho : IsSmoothCompactProbabilityDensity rho)
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    (hdensity : densityMeasure rho = branchMarginal nu (H 0) (H 1) (H 2) (H 3))
    {B U : Set E3} (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B → MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C)
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      triplePotential p (x, (y, z)) = coulombCost (x, (y, z)) + C →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by
  let mu := branchMarginal nu (H 0) (H 1) (H 2) (H 3)
  let pi0 := branchCoupling nu (H 0) (H 1) (H 2) (H 3)
  have : IsProbabilityMeasure mu :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hpi0 : IsThreeCoupling mu pi0 :=
    isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU : ∀ᵐ x ∂mu, x ∈ U := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hboundall : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C := by
    intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  have hcontact0 : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C := by
    apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [triplePotential_cycle_assembly, coulombCost_cycle_assembly]
      exact hxyz
    · exact hcontact01
    · exact hcontact23
  obtain ⟨hattained, hfinite⟩ :=
    kantorovichAttained_of_certificate hpi0 hp hpfinite hC hboundall hcontact0
  have hnu : nu ≪ mu := by
    change nu ≪ branchMarginal nu (H 0) (H 1) (H 2) (H 3)
    rw [branchMarginal_eq_splitMeasure]
    exact Splitting.absolutelyContinuous_splitMeasure nu (1 / 3) (fun _ : Fin 4 => 1 / 6) H
      (by norm_num)
  have hno : NoMongeOptimizer mu := by
    apply noMongeOptimizer_of_selection_obstruction mu nu hnu hfull
      (Contact := fun t => tripleSnd t ∈ U ∧ tripleThd t ∈ U ∧
        triplePotential p t = coulombCost t + C)
      (Select := fun x y => ∃ i, y = H i x)
    · intro pi hpi hopt
      have heq := certificate_contact_of_optimal hpi0 hpi hp hpfinite hC
        measurable_coulombCost hboundall hcontact0 hopt
      filter_upwards [hpi.ae_coordinates hmuU, heq] with t ht heq
      exact ⟨ht.2.1, ht.2.2, heq⟩
    · intro x y z hx ht
      exact hselect x y z hx ht.1 ht.2.1 ht.2.2
    · intro T hT hselection
      have hbad := Splitting.no_preserving_splitMeasure_selection
        (H := H) (c := (1 / 3 : ℝ≥0∞)) (d := (1 / 6 : ℝ≥0∞))
        (by simp : nu Set.univ ≠ 0) hB hfull hH hInj himage hCentral hPair
        (by norm_num)
      apply hbad
      refine ⟨T, hT.1, ?_, hselection⟩
      simpa only [← branchMarginal_eq_splitMeasure] using hT.2
  change IsSmoothCompactProbabilityDensity rho ∧
    IsProbabilityMeasure (densityMeasure rho) ∧ kantorovichValue (densityMeasure rho) < ⊤ ∧
    KantorovichAttained (densityMeasure rho) ∧ NoMongeOptimizer (densityMeasure rho)
  rw [hdensity]
  exact ⟨hrho, inferInstanceAs (IsProbabilityMeasure mu), hfinite, hattained, hno⟩

/-- The concrete six-graph coupling is itself the finite optimizer. This
exposes the witness used by the counterexample assembly to the separated
support approximation argument. -/
theorem branchCoupling_optimal_of_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {U : Set E3} (hU : MeasurableSet U)
    (hmuU : ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
      kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  have hpi0 := isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  apply certificate_optimality hpi0 hp hpfinite hC
  · intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  · apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [triplePotential_cycle_assembly, coulombCost_cycle_assembly]
      exact hxyz
    · exact hcontact01
    · exact hcontact23

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

private lemma coulombCost_pos_realAssembly (t : Triple) : 0 < coulombCost t := by
  have hpos : 0 < invDistance (tripleFst t) (tripleSnd t) :=
    ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  unfold coulombCost
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hpos zero_le) zero_le

/-- For the strictly positive Coulomb cost, the shifted and signed contact
conditions are equivalent; no nonnegativity assumption on the signed sum is
needed. -/
lemma triplePotential_shifted_contact_iff {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (hM : 0 ≤ M)
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t)) :
    (triplePotential (shiftedPotential u M) t =
      coulombCost t + ENNReal.ofReal (3 * M)) ↔
    ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) =
      coulombCost t :=
  shifted_three_eq_iff_of_pos h1 h2 h3 hM (coulombCost_pos_realAssembly t)

theorem hasCoulombCounterexample_of_real_branches
    (rho : E3 → ℝ) (hrho : IsSmoothCompactProbabilityDensity rho)
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    (hdensity : densityMeasure rho = branchMarginal nu (H 0) (H 1) (H 2) (H 3))
    {B U : Set E3} (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B → MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 0 x) + u (H 1 x)) = coulombCost (x, (H 0 x, H 1 x)))
    (hcontact23 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 2 x) + u (H 3 x)) = coulombCost (x, (H 2 x, H 3 x)))
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by
  let mu := branchMarginal nu (H 0) (H 1) (H 2) (H 3)
  have : IsProbabilityMeasure mu :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU : ∀ᵐ x ∂mu, x ∈ U := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hfinite : (∫⁻ x, shiftedPotential u M x ∂mu) ≠ ⊤ :=
    (lintegral_shiftedPotential_lt_top_of_ae_le
      (M := M) (hmuU.mono fun x hx => (hubound x hx).2)).ne
  apply hasCoulombCounterexample_of_branches rho hrho nu H hH hdensity
    hB hU hfull hBU hHU hInj himage hCentral hPair
    (measurable_shiftedPotential hu M) hfinite ENNReal.ofReal_ne_top
  · intro t h1 h2 h3
    exact shiftedPotential_certificate (hubound _ h1).1 (hubound _ h2).1
      (hubound _ h3).1 (hbound t h1 h2 h3)
  · filter_upwards [hfull, hcontact01] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 0 x) (hHU 0 ⟨x, hx, rfl⟩)).1
      (hubound (H 1 x) (hHU 1 ⟨x, hx, rfl⟩)).1).mpr
    exact heq
  · filter_upwards [hfull, hcontact23] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 2 x) (hHU 2 ⟨x, hx, rfl⟩)).1
      (hubound (H 3 x) (hHU 3 ⟨x, hx, rfl⟩)).1).mpr
    exact heq
  · intro x y z hx hy hz heq
    apply hselect x y z hx hy hz
    exact (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1 (hubound y hy).1 (hubound z hz).1).mp heq

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

private lemma branchOptimizer_cost_cycle (x y z : E3) :
    coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev y x, norm_sub_rev z x]
  ac_rfl

private lemma branchOptimizer_potential_cycle (p : E3 → ℝ≥0∞) (x y z : E3) :
    triplePotential p (y, (z, x)) = triplePotential p (x, (y, z)) := by
  simp only [triplePotential, tripleFst, tripleSnd, tripleThd]
  ac_rfl

/-- The explicit six-graph branch coupling is itself a finite optimizer.
This preserves the identity of the optimizer, unlike an existential attainment
statement, so its geometric separation can be used in Monge approximation. -/
theorem branchCoupling_optimality_of_shifted_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {U : Set E3} (hU : MeasurableSet U)
    (hmuU : ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  apply certificate_optimality
    (isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)) hp hpfinite hC
  · intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  · apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [branchOptimizer_potential_cycle, branchOptimizer_cost_cycle]
      exact hxyz
    · exact hcontact01
    · exact hcontact23

/-- Signed-potential version of explicit branch optimizer certification.
The assumptions are a subset of the real counterexample assembly assumptions;
no density, injectivity, or nonattainment hypothesis is required. -/
theorem branchCoupling_optimality_of_real_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {B U : Set E3} (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 0 x) + u (H 1 x)) = coulombCost (x, (H 0 x, H 1 x)))
    (hcontact23 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 2 x) + u (H 3 x)) = coulombCost (x, (H 2 x, H 3 x))) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  have : IsProbabilityMeasure (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hfinite : (∫⁻ x, shiftedPotential u M x
      ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤ :=
    (lintegral_shiftedPotential_lt_top_of_ae_le
      (M := M) (hmuU.mono fun x hx => (hubound x hx).2)).ne
  apply branchCoupling_optimality_of_shifted_certificate nu H hH hU hmuU
    (measurable_shiftedPotential hu M) hfinite ENNReal.ofReal_ne_top
  · intro t h1 h2 h3
    exact shiftedPotential_certificate (hubound _ h1).1 (hubound _ h2).1
      (hubound _ h3).1 (hbound t h1 h2 h3)
  · filter_upwards [hfull, hcontact01] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 0 x) (hHU 0 ⟨x, hx, rfl⟩)).1
      (hubound (H 1 x) (hHU 1 ⟨x, hx, rfl⟩)).1).mpr
    exact heq
  · filter_upwards [hfull, hcontact23] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 2 x) (hHU 2 ⟨x, hx, rfl⟩)).1
      (hubound (H 3 x) (hHU 3 ⟨x, hx, rfl⟩)).1).mpr
    exact heq

end Problem356

end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Equal cell-label laws let one compare costs using only their oscillation inside
matching cells. The target-cell condition is needed only on a full-measure set. -/
theorem lintegral_le_of_same_cells
    {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    (p : α → ι) (q : β → ι) (hp : Measurable p) (hq : Measurable q)
    (hlaw : Measure.map p μ = Measure.map q ν)
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) (ε : ℝ≥0∞)
    (t : Set β) (ht : ∀ᵐ y ∂ν, y ∈ t)
    (hosc : ∀ᵐ x ∂μ, ∀ y ∈ t, p x = q y → f x ≤ g y + ε) :
    (∫⁻ x, f x ∂μ) ≤ (∫⁻ y, g y ∂ν) + ε := by
  let c : ι → ℝ≥0∞ := fun i => ⨅ y ∈ t, ⨅ (_ : q y = i), g y
  have hc : Measurable c := measurable_of_countable c
  have hupper : f ≤ᵐ[μ] fun x => c (p x) + ε := by
    filter_upwards [hosc] with x hx
    simp only [c, ENNReal.iInf_add]
    exact le_iInf fun y => le_iInf fun hy => le_iInf fun hi => hx y hy hi.symm
  have hlower : (fun y => c (q y)) ≤ᵐ[ν] g := by
    filter_upwards [ht] with y hy
    exact iInf_le_of_le y (iInf_le_of_le hy (iInf_le_of_le rfl le_rfl))
  have htransport : (∫⁻ x, c (p x) ∂μ) = ∫⁻ y, c (q y) ∂ν := by
    rw [← lintegral_map hc hp, hlaw, lintegral_map hc hq]
  calc
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, c (p x) + ε ∂μ := lintegral_mono_ae hupper
    _ = (∫⁻ x, c (p x) ∂μ) + ε := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ = (∫⁻ y, c (q y) ∂ν) + ε := by rw [htransport]
    _ ≤ (∫⁻ y, g y ∂ν) + ε := add_le_add (lintegral_mono_ae hlower) le_rfl

end Problem356

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Problem356

section FiniteFibers

variable {α : Type uAlpha} {ι : Type uIndex} {κ : Type uKappa} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]

lemma sum_measure_pair_fibers (μ : Measure α) {p : α → ι} {q : α → κ}
    (hp : Measurable p) (hq : Measurable q) :
    (∑ i, ∑ j, μ {x | p x = i ∧ q x = j}) = μ Set.univ := by
  have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset (ι × κ))
    (f := fun x => (p x, q x))
    (fun y _ => (hp.prodMk hq) (measurableSet_singleton y))
  simpa only [Finset.mem_univ, Finset.sum_const_zero,
    Finset.coe_univ, Set.preimage_univ, Fintype.sum_prod_type, Set.preimage, Set.mem_singleton_iff,
    Prod.mk.injEq, Set.mem_univ, Set.ofPred_true] using h

lemma sum_measure_pair_fibers_on (μ : Measure α) {s : Set α}
    (_hs : MeasurableSet s) {p : α → ι} {q : α → κ}
    (hp : Measurable p) (hq : Measurable q) :
    (∑ i, ∑ j, μ {x | x ∈ s ∧ p x = i ∧ q x = j}) = μ s := by
  calc
    _ = ∑ i, ∑ j, (μ.restrict s) {x | p x = i ∧ q x = j} := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hcell : MeasurableSet {x | p x = i ∧ q x = j} := by
        convert (hp (measurableSet_singleton i)).inter (hq (measurableSet_singleton j)) using 1
        ext x
        simp
      rw [Measure.restrict_apply hcell]
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_comm]
    _ = (μ.restrict s) Set.univ := sum_measure_pair_fibers (μ.restrict s) hp hq
    _ = μ s := by simp

end FiniteFibers

section CellTable

variable {ι : Type uIndex} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The joint finite-cell mass table of a triple measure. -/
def cellTable (p : E3 → ι) (π : Measure Triple) (i j k : ι) : ℝ≥0∞ :=
  π {t | p (tripleFst t) = i ∧ p (tripleSnd t) = j ∧ p (tripleThd t) = k}

lemma cellTable_sum_fst {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i : ι) :
    (∑ j, ∑ k, cellTable p π i j k) = μ (p ⁻¹' {i}) := by
  calc
    _ = π {t | p (tripleFst t) = i} :=
      sum_measure_pair_fibers_on π ((hp.comp measurable_tripleFst)
        (measurableSet_singleton i)) (hp.comp measurable_tripleSnd)
          (hp.comp measurable_tripleThd)
    _ = (Measure.map tripleFst π) (p ⁻¹' {i}) := by
      rw [Measure.map_apply measurable_tripleFst (hp (measurableSet_singleton i))]
      rfl
    _ = μ (p ⁻¹' {i}) := by rw [hπ.2.1]

lemma cellTable_sum_snd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (j : ι) :
    (∑ i, ∑ k, cellTable p π i j k) = μ (p ⁻¹' {j}) := by
  have h := sum_measure_pair_fibers_on π ((hp.comp measurable_tripleSnd)
    (measurableSet_singleton j)) (hp.comp measurable_tripleFst)
      (hp.comp measurable_tripleThd)
  calc
    _ = π {t | p (tripleSnd t) = j} := by
      simpa only [cellTable, Set.preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Function.comp_apply,
        and_assoc, and_left_comm] using h
    _ = (Measure.map tripleSnd π) (p ⁻¹' {j}) := by
      rw [Measure.map_apply measurable_tripleSnd (hp (measurableSet_singleton j))]
      rfl
    _ = μ (p ⁻¹' {j}) := by rw [hπ.2.2.1]

lemma cellTable_sum_thd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (k : ι) :
    (∑ i, ∑ j, cellTable p π i j k) = μ (p ⁻¹' {k}) := by
  have h := sum_measure_pair_fibers_on π ((hp.comp measurable_tripleThd)
    (measurableSet_singleton k)) (hp.comp measurable_tripleFst)
      (hp.comp measurable_tripleSnd)
  calc
    _ = π {t | p (tripleThd t) = k} := by
      simpa only [cellTable, Set.preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Function.comp_apply,
        and_assoc, and_comm, and_left_comm] using h
    _ = (Measure.map tripleThd π) (p ⁻¹' {k}) := by
      rw [Measure.map_apply measurable_tripleThd (hp (measurableSet_singleton k))]
      rfl
    _ = μ (p ⁻¹' {k}) := by rw [hπ.2.2.2]

lemma cellTable_le_fst {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i j k : ι) :
    cellTable p π i j k ≤ μ (p ⁻¹' {i}) := by
  calc
    _ ≤ ∑ k', cellTable p π i j k' :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', cellTable p π i j' k' :=
      Finset.single_le_sum (f := fun j' => ∑ k', cellTable p π i j' k') (fun _ _ => zero_le) (Finset.mem_univ j)
    _ = _ := cellTable_sum_fst hπ hp i

lemma cellTable_le_snd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i j k : ι) :
    cellTable p π i j k ≤ μ (p ⁻¹' {j}) := by
  calc
    _ ≤ ∑ k', cellTable p π i j k' :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ k)
    _ ≤ ∑ i', ∑ k', cellTable p π i' j k' :=
      Finset.single_le_sum (f := fun i' => ∑ k', cellTable p π i' j k') (fun _ _ => zero_le) (Finset.mem_univ i)
    _ = _ := cellTable_sum_snd hπ hp j

lemma cellTable_le_thd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i j k : ι) :
    cellTable p π i j k ≤ μ (p ⁻¹' {k}) := by
  calc
    _ ≤ ∑ j', cellTable p π i j' k :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', cellTable p π i' j' k :=
      Finset.single_le_sum (f := fun i' => ∑ j', cellTable p π i' j' k) (fun _ _ => zero_le) (Finset.mem_univ i)
    _ = _ := cellTable_sum_thd hπ hp k

lemma cellTable_pos_cell_masses_pos {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) {i j k : ι}
    (h : 0 < cellTable p π i j k) :
    0 < μ (p ⁻¹' {i}) ∧ 0 < μ (p ⁻¹' {j}) ∧ 0 < μ (p ⁻¹' {k}) :=
  ⟨h.trans_le (cellTable_le_fst hπ hp i j k),
    h.trans_le (cellTable_le_snd hπ hp i j k),
    h.trans_le (cellTable_le_thd hπ hp i j k)⟩

/-- The product label map corresponding to the cell table. -/
def tripleCellLabel (p : E3 → ι) (t : Triple) : ι × (ι × ι) :=
  (p (tripleFst t), (p (tripleSnd t), p (tripleThd t)))

omit [Fintype ι] [MeasurableSingletonClass ι] in
lemma measurable_tripleCellLabel {p : E3 → ι} (hp : Measurable p) :
    Measurable (tripleCellLabel p) :=
  (hp.comp measurable_tripleFst).prodMk
    ((hp.comp measurable_tripleSnd).prodMk (hp.comp measurable_tripleThd))

omit [Fintype ι] in
lemma cellTable_eq_map_singleton {p : E3 → ι} (hp : Measurable p)
    (π : Measure Triple) (i j k : ι) :
    cellTable p π i j k = (Measure.map (tripleCellLabel p) π) {(i, (j, k))} := by
  rw [cellTable, Measure.map_apply (measurable_tripleCellLabel hp) (measurableSet_singleton _)]
  congr 1
  ext t
  simp [tripleCellLabel, Set.mem_preimage]

lemma tripleCellLabel_map_eq_of_table_eq {p : E3 → ι} (hp : Measurable p)
    {π π' : Measure Triple}
    (h : ∀ i j k, cellTable p π i j k = cellTable p π' i j k) :
    Measure.map (tripleCellLabel p) π = Measure.map (tripleCellLabel p) π' := by
  apply Measure.ext_of_singleton
  rintro ⟨i, j, k⟩
  rw [← cellTable_eq_map_singleton hp, ← cellTable_eq_map_singleton hp]
  exact h i j k

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma cellTable_lt_top {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) (p : E3 → ι) (i j k : ι) :
    cellTable p π i j k < ⊤ := by
  have := hπ.1
  exact measure_lt_top π _

lemma cellTable_sum {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) :
    (∑ i, ∑ j, ∑ k, cellTable p π i j k) = 1 := by
  have hsum := sum_measure_pair_fibers π (hp.comp measurable_tripleFst)
    ((hp.comp measurable_tripleSnd).prodMk (hp.comp measurable_tripleThd))
  have := hπ.1
  simpa only [cellTable, Fintype.sum_prod_type, Prod.mk.injEq,
    Function.comp_apply, measure_univ] using hsum

end CellTable

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.PartitionTransport

variable {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]

/-- Gluing measurable transports on a countable measurable partition gives the
sum of their restricted pushforwards. The partition need only cover almost everywhere. -/
theorem exists_map_eq_sum_of_partition [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i)) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧
      Measure.map f μ = Measure.sum (fun i => Measure.map (T i) (μ.restrict (B i))) := by
  obtain ⟨f, hf, hfg⟩ := exists_measurable_piecewise B hB T hT (by
    intro i j hij x hx
    exact False.elim (Set.disjoint_left.mp (hdisj hij) hx.1 hx.2))
  refine ⟨f, hf, hfg, ?_⟩
  have hdecomp : μ = Measure.sum (fun i => μ.restrict (B i)) := by
    rw [← Measure.restrict_iUnion hdisj hB, Measure.restrict_eq_self_of_ae_mem hcover]
  calc
    Measure.map f μ = Measure.map f (Measure.sum (fun i => μ.restrict (B i))) :=
      congrArg (Measure.map f) hdecomp
    _ = Measure.sum (fun i => Measure.map f (μ.restrict (B i))) :=
      Measure.map_sum hf.aemeasurable
    _ = _ := by
      congr 1
      funext i
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (hB i)] with x hx
      exact hfg i hx

/-- Prescribed laws on partition pieces can be glued into a transport to their sum. -/
theorem exists_map_eq_of_partition [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i))
    (ν : ι → Measure β)
    (hmap : ∀ i, Measure.map (T i) (μ.restrict (B i)) = ν i) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧ Measure.map f μ = Measure.sum ν := by
  obtain ⟨f, hf, hfg, hsum⟩ :=
    exists_map_eq_sum_of_partition μ B hB hdisj hcover T hT
  refine ⟨f, hf, hfg, ?_⟩
  simpa only [hmap] using hsum

/-- The finite form, using the usual finite sum of target measures. -/
theorem exists_map_eq_finset_sum_of_partition [Fintype ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i))
    (ν : ι → Measure β)
    (hmap : ∀ i, Measure.map (T i) (μ.restrict (B i)) = ν i) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧ Measure.map f μ = ∑ i, ν i := by
  simpa only [Measure.sum_fintype] using
    exists_map_eq_of_partition μ B hB hdisj hcover T hT ν hmap

/-- The pushforward law of a label that is constant almost everywhere on each
partition piece is the atomic measure with those piece masses. -/
theorem map_eq_sum_dirac_of_partition [Countable ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (L : α → β) (hL : Measurable L) (label : ι → β)
    (hlabel : ∀ i, ∀ᵐ x ∂μ.restrict (B i), L x = label i) :
    Measure.map L μ = Measure.sum (fun i => μ (B i) • Measure.dirac (label i)) := by
  have hdecomp : μ = Measure.sum (fun i => μ.restrict (B i)) := by
    rw [← Measure.restrict_iUnion hdisj hB, Measure.restrict_eq_self_of_ae_mem hcover]
  calc
    Measure.map L μ = Measure.map L (Measure.sum (fun i => μ.restrict (B i))) :=
      congrArg (Measure.map L) hdecomp
    _ = Measure.sum (fun i => Measure.map L (μ.restrict (B i))) :=
      Measure.map_sum hL.aemeasurable
    _ = _ := by
      congr 1
      funext i
      rw [Measure.map_congr (hlabel i), Measure.map_const]
      simp

/-- An exact agreement on a measurable piece gives equality of restricted laws. -/
theorem map_restrict_eq_of_eqOn (μ : Measure α) {B : Set α}
    (hB : MeasurableSet B) {f g : α → β} (heq : EqOn f g B) :
    Measure.map f (μ.restrict B) = Measure.map g (μ.restrict B) := by
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem hB] with x hx
  exact heq hx

/-- Glue two families of transports simultaneously. Their marginal laws and
joint finite-cell law are all explicit. This is the graph-plan step in the
cellwise approximation construction. -/
theorem exists_pair_maps_with_label_law [Countable ι] [Nonempty ι]
    {κ : Type uKappa} [MeasurableSpace κ]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T₂ T₃ : ι → α → α)
    (hT₂ : ∀ i, Measurable (T₂ i)) (hT₃ : ∀ i, Measurable (T₃ i))
    (ν₂ ν₃ : ι → Measure α)
    (hmap₂ : ∀ i, Measure.map (T₂ i) (μ.restrict (B i)) = ν₂ i)
    (hmap₃ : ∀ i, Measure.map (T₃ i) (μ.restrict (B i)) = ν₃ i)
    (hsum₂ : Measure.sum ν₂ = μ) (hsum₃ : Measure.sum ν₃ = μ)
    (p : α → κ) (hp : Measurable p) (l₁ l₂ l₃ : ι → κ)
    (hlabel₁ : ∀ i, ∀ᵐ x ∂μ.restrict (B i), p x = l₁ i)
    (hlabel₂ : ∀ i, ∀ᵐ x ∂ν₂ i, p x = l₂ i)
    (hlabel₃ : ∀ i, ∀ᵐ x ∂ν₃ i, p x = l₃ i) :
    ∃ f g : α → α,
      Measurable f ∧ Measurable g ∧
      Measure.map f μ = μ ∧ Measure.map g μ = μ ∧
      Measure.map (fun x => (p x, (p (f x), p (g x)))) μ =
        Measure.sum (fun i => μ (B i) • Measure.dirac (l₁ i, (l₂ i, l₃ i))) := by
  obtain ⟨f, hf, hfB, hfmap⟩ :=
    exists_map_eq_of_partition μ B hB hdisj hcover T₂ hT₂ ν₂ hmap₂
  obtain ⟨g, hg, hgB, hgmap⟩ :=
    exists_map_eq_of_partition μ B hB hdisj hcover T₃ hT₃ ν₃ hmap₃
  refine ⟨f, g, hf, hg, hfmap.trans hsum₂, hgmap.trans hsum₃, ?_⟩
  apply map_eq_sum_dirac_of_partition μ B hB hdisj hcover
    (fun x => (p x, (p (f x), p (g x))))
    (hp.prodMk ((hp.comp hf).prodMk (hp.comp hg)))
    (fun i => (l₁ i, (l₂ i, l₃ i)))
  intro i
  have hfmapB : Measure.map f (μ.restrict (B i)) = ν₂ i :=
    (map_restrict_eq_of_eqOn μ (hB i) (hfB i)).trans (hmap₂ i)
  have hgmapB : Measure.map g (μ.restrict (B i)) = ν₃ i :=
    (map_restrict_eq_of_eqOn μ (hB i) (hgB i)).trans (hmap₃ i)
  have hfLabel : ∀ᵐ x ∂μ.restrict (B i), p (f x) = l₂ i := by
    refine ae_of_ae_map (μ := μ.restrict (B i)) (p := fun y => p y = l₂ i) hf.aemeasurable ?_
    rw [hfmapB]
    exact hlabel₂ i
  have hgLabel : ∀ᵐ x ∂μ.restrict (B i), p (g x) = l₃ i := by
    refine ae_of_ae_map (μ := μ.restrict (B i)) (p := fun y => p y = l₃ i) hg.aemeasurable ?_
    rw [hgmapB]
    exact hlabel₃ i
  filter_upwards [hlabel₁ i, hfLabel, hgLabel] with x hx hx₂ hx₃
  simp only [hx, hx₂, hx₃]

/-- Redistributing weights to the normalized restrictions of a finite partition
preserves the measure when the weights have the prescribed marginal sums.
Zero-mass cells require no positivity assumption. -/
theorem sum_normalized_restrict_eq [Fintype ι]
    {κ : Type uKappa} [Fintype κ] [DecidableEq κ]
    (μ : Measure α) [IsFiniteMeasure μ] (A : κ → Set α)
    (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ j, A j)
    (label : ι → κ) (w : ι → ℝ≥0∞)
    (hweights : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => label i = j), w i = μ (A j)) :
    (∑ i, (w i / μ (A (label i))) • μ.restrict (A (label i))) = μ := by
  classical
  calc
    (∑ i, (w i / μ (A (label i))) • μ.restrict (A (label i))) =
        ∑ j, ∑ i ∈ Finset.univ.filter (fun i => label i = j),
          (w i / μ (A (label i))) • μ.restrict (A (label i)) :=
      (Finset.sum_fiberwise Finset.univ label _).symm
    _ = ∑ j, μ.restrict (A j) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ i ∈ Finset.univ.filter (fun i => label i = j),
            (w i / μ (A (label i))) • μ.restrict (A (label i))) =
            ∑ i ∈ Finset.univ.filter (fun i => label i = j),
              (w i / μ (A j)) • μ.restrict (A j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = μ.restrict (A j) := by
          by_cases hz : μ (A j) = 0
          · simp [Measure.restrict_eq_zero.mpr hz]
          · rw [← Finset.sum_smul]
            simp_rw [ENNReal.div_eq_inv_mul]
            rw [← Finset.mul_sum, hweights j,
              ENNReal.inv_mul_cancel hz (measure_ne_top μ (A j)), one_smul]
    _ = μ := by
      rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hA,
        Measure.restrict_eq_self_of_ae_mem hcover]

end Problem356.PartitionTransport

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set MeasureTheory Metric

namespace Problem356

/-- Disjointification preserves measurability for finite ordered index sets. -/
theorem measurableSet_disjointed_fin {X : Type uX} [MeasurableSpace X]
    {n : ℕ} {A : Fin n → Set X} (hA : ∀ i, MeasurableSet (A i)) (i : Fin n) :
    MeasurableSet (disjointed A i) := by
  exact disjointedRec (fun _ _ ht => ht.diff (hA _)) (hA i)

/-- A compact metric set admits a finite Borel partition into sets of arbitrarily
small diameter. Empty cells are permitted, so the indexing is uniform. -/
theorem exists_compact_small_partition {X : Type uX} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : Set X} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : Fin n → Set X),
      (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = K ∧
      (∀ i, A i ⊆ K) ∧
      (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y < δ) := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : X => ball x (δ / 2)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, mem_ball_self (half_pos hδ)⟩)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let B : Fin (Fintype.card s) → Set X := fun i => K ∩ ball (e.symm i).val (δ / 2)
  have hB : ∀ i, MeasurableSet (B i) := fun _ =>
    hK.measurableSet.inter measurableSet_ball
  have hCover : (⋃ i, B i) = K := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => inter_subset_left
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
      refine mem_iUnion.mpr ⟨e ⟨y, hy⟩, hx, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hxy
  refine ⟨Fintype.card s, disjointed B, measurableSet_disjointed_fin hB,
    disjoint_disjointed B, ?_, ?_, ?_⟩
  · rw [iUnion_disjointed, hCover]
  · intro i
    exact (disjointed_subset B i).trans inter_subset_left
  · intro i x hx y hy
    have hx' := (disjointed_subset B i hx).2
    have hy' := (disjointed_subset B i hy).2
    calc
      dist x y ≤ dist x (e.symm i).val + dist (e.symm i).val y := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (mem_ball.mp hx') (by simpa only [dist_comm] using (mem_ball.mp hy'))
      _ = δ := by ring

/-- The small cells may simultaneously be chosen inside a prescribed finite
family of pairwise disjoint compact components. -/
theorem exists_compact_component_partition {X : Type uX} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {ι : Type uIndex} [Fintype ι]
    (K : ι → Set X) (hK : ∀ a, IsCompact (K a))
    (hDisjoint : Pairwise (fun a b => Disjoint (K a) (K b)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : ι × Fin n → Set X),
      (∀ p, MeasurableSet (A p)) ∧
      Pairwise (fun p q => Disjoint (A p) (A q)) ∧
      (⋃ p, A p) = ⋃ a, K a ∧
      (∀ p, A p ⊆ K p.1) ∧
      (∀ p, ∀ x ∈ A p, ∀ y ∈ A p, dist x y < δ) := by
  classical
  obtain ⟨n, B, hMeas, hPair, hCover, hSub, hDist⟩ :=
    exists_compact_small_partition (isCompact_iUnion hK) hδ
  let A : ι × Fin n → Set X := fun p => K p.1 ∩ B p.2
  refine ⟨n, A, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hK p.1).measurableSet.inter (hMeas p.2)
  · intro p q hpq
    by_cases hfirst : p.1 = q.1
    · have hsecond : p.2 ≠ q.2 := by
        intro hsecond
        exact hpq (Prod.ext hfirst hsecond)
      exact (hPair hsecond).mono inter_subset_right inter_subset_right
    · exact (hDisjoint hfirst).mono inter_subset_left inter_subset_left
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨p.1, hp.1⟩
    · intro x hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      have hxB : x ∈ ⋃ i, B i := by
        rw [hCover]
        exact mem_iUnion.mpr ⟨a, ha⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxB
      exact mem_iUnion.mpr ⟨(a, i), ha, hi⟩
  · intro p
    exact inter_subset_left
  · intro p x hx y hy
    exact hDist p.2 x hx.2 y hy.2

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set MeasureTheory

namespace Problem356.FiniteCells

/-- The exact label of a point in a disjoint family; points outside all cells
are assigned `none`, without choosing an arbitrary distinguished cell. -/
def cellLabel {X : Type uX} {ι : Type uIndex} (A : ι → Set X) (x : X) : Option ι :=
  by
    classical
    exact if h : ∃ i, x ∈ A i then some (Classical.choose h) else none

lemma cellLabel_eq_some_iff {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (x : X) (i : ι) :
    cellLabel A x = some i ↔ x ∈ A i := by
  classical
  unfold cellLabel
  split_ifs with h
  · constructor
    · intro hi
      have hi' := Option.some.inj hi
      rw [← hi']
      exact Classical.choose_spec h
    · intro hx
      congr 1
      by_contra hne
      exact Set.disjoint_left.mp (hDisjoint hne) (Classical.choose_spec h) hx
  · have hi : x ∉ A i := fun hx => h ⟨i, hx⟩
    simp [hi]

lemma cellLabel_eq_none_iff {X : Type uX} {ι : Type uIndex} (A : ι → Set X) (x : X) :
    cellLabel A x = none ↔ x ∉ ⋃ i, A i := by
  classical
  by_cases h : ∃ i, x ∈ A i
  · simp only [cellLabel, dite_eq_left h, reduceCtorEq, false_iff, not_not]
    exact mem_iUnion.mpr h
  · simp only [cellLabel, dite_eq_right h, true_iff]
    exact fun hx => h (mem_iUnion.mp hx)

lemma cellLabel_fiber_some {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (i : ι) :
    cellLabel A ⁻¹' {some i} = A i := by
  ext x
  exact cellLabel_eq_some_iff hDisjoint x i

lemma cellLabel_fiber_none {X : Type uX} {ι : Type uIndex} (A : ι → Set X) :
    cellLabel A ⁻¹' {none} = (⋃ i, A i)ᶜ := by
  ext x
  exact cellLabel_eq_none_iff A x

lemma measurable_cellLabel {X : Type uX} {ι : Type uIndex} [MeasurableSpace X]
    [MeasurableSpace (Option ι)] [Countable ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i))
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Measurable (cellLabel A) := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
      rw [cellLabel_fiber_none]
      exact (MeasurableSet.iUnion hA).compl
  | some i =>
      rw [cellLabel_fiber_some hDisjoint]
      exact hA i

/-- Equal source cell masses give equal laws of the exact label, provided
both measures are concentrated on the union of the cells. -/
lemma map_cellLabel_eq_of_cell_masses {X : Type uX} {ι : Type uIndex} [MeasurableSpace X]
    [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)] [Countable ι]
    {μ ν : Measure X} {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i))
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hμ : μ (⋃ i, A i)ᶜ = 0) (hν : ν (⋃ i, A i)ᶜ = 0)
    (hmass : ∀ i, μ (A i) = ν (A i)) :
    Measure.map (cellLabel A) μ = Measure.map (cellLabel A) ν := by
  have hm := measurable_cellLabel hA hDisjoint
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply hm (measurableSet_singleton i),
    Measure.map_apply hm (measurableSet_singleton i)]
  cases i with
  | none => simp only [cellLabel_fiber_none, hμ, hν]
  | some i => simpa only [cellLabel_fiber_some hDisjoint] using hmass i

end Problem356.FiniteCells

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.Transport

/-- A finite atomless source admits a lift to any finite law with that source as
marginal, while preserving any prescribed countable measurable label almost everywhere.
This permits cellwise approximation without splitting a three-index mass table. -/
theorem exists_measurable_lift_preserving_label
    {X : Type uX} {Y : Type uY} {ι : Type uIndex} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [Nonempty ι]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f)
    (hmarg : ν.map f = μ) (p : X → ι) (hp : Measurable p) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, p (f (Q x)) = p x := by
  classical
  let B : ι → Set X := fun i => p ⁻¹' {i}
  have hB (i : ι) : MeasurableSet (B i) := hp (measurableSet_singleton i)
  have hdisj : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (hxi.symm.trans hxj)
  have hcover : (⋃ i, B i) = univ := by
    ext x
    simp [B]
  have htransport (i : ι) : ∃ Q : X → Y, Measurable Q ∧
      (μ.restrict (B i)).map Q = ν.restrict (f ⁻¹' B i) := by
    apply exists_measurable_transport_finite
    simp only [Measure.restrict_apply_univ]
    rw [← hmarg, Measure.map_apply hf (hB i)]
  choose T hT hmap using htransport
  obtain ⟨Q, hQ, hQT, hQmap⟩ := PartitionTransport.exists_map_eq_of_partition
    μ B hB hdisj (by simp [hcover]) T hT
    (fun i => ν.restrict (f ⁻¹' B i)) hmap
  have hsum : Measure.sum (fun i => ν.restrict (f ⁻¹' B i)) = ν := by
    rw [← Measure.restrict_iUnion]
    · simp only [← preimage_iUnion, hcover, preimage_univ, Measure.restrict_univ]
    · intro i j hij
      exact (hdisj hij).preimage f
    · intro i
      exact (hB i).preimage hf
  refine ⟨Q, hQ, hQmap.trans hsum, ?_⟩
  have hlabel (i : ι) : ∀ᵐ x ∂μ.restrict (B i), p (f (T i x)) = i := by
    have hmem : ∀ᵐ x ∂μ.restrict (B i), f (T i x) ∈ B i := by
      apply ae_of_ae_map (μ := μ.restrict (B i)) (p := fun y => f y ∈ B i)
        (hT i).aemeasurable
      rw [hmap i]
      exact ae_restrict_mem ((hB i).preimage hf)
    exact hmem
  have hlabel' (i : ι) : ∀ᵐ x ∂μ, x ∈ B i → p (f (T i x)) = i :=
    (ae_restrict_iff' (hB i)).mp (hlabel i)
  have hall : ∀ᵐ x ∂μ, ∀ i, x ∈ B i → p (f (T i x)) = i :=
    ae_all_iff.mpr hlabel'
  filter_upwards [hall] with x hx
  have hxB : x ∈ B (p x) := rfl
  rw [hQT (p x) hxB]
  exact hx (p x) hxB

/-- A lift can preserve the source coordinate to arbitrary precision whenever
that source has compact support. Only the first marginal is approximated; the
entire target law is transported exactly. -/
theorem exists_measurable_lift_close
    {X : Type uX} {Y : Type uY} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f) (hmarg : ν.map f = μ)
    {K : Set X} (hK : IsCompact K) (hfull : μ Kᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, dist x (f (Q x)) < δ := by
  obtain ⟨n, A, hA, hdisj, hcover, _, hdiam⟩ := exists_compact_small_partition hK hδ
  let : MeasurableSpace (Option (Fin n)) := ⊤
  obtain ⟨Q, hQ, hmap, hlabel⟩ := exists_measurable_lift_preserving_label
    μ ν f hf hmarg (FiniteCells.cellLabel A) (FiniteCells.measurable_cellLabel hA hdisj)
  refine ⟨Q, hQ, hmap, ?_⟩
  have hxK : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hfull
  filter_upwards [hlabel, hxK] with x hx hxK
  have hxA : x ∈ ⋃ i, A i := by rwa [hcover]
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
  have hlabelx : FiniteCells.cellLabel A x = some i :=
    (FiniteCells.cellLabel_eq_some_iff hdisj x i).mpr hi
  have hlabelQ : FiniteCells.cellLabel A (f (Q x)) = some i := hx.trans hlabelx
  have hQi : f (Q x) ∈ A i :=
    (FiniteCells.cellLabel_eq_some_iff hdisj (f (Q x)) i).mp hlabelQ
  exact hdiam i x hi (f (Q x)) hQi

end Problem356.Transport

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.CenterCertificate

/-- The center and the two opposite pairs used in the local construction. -/
def point : Fin 5 → E3 :=
  ![0, !₂[1, 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0], !₂[0, -1, 0]]

theorem point_injective : Function.Injective point := by
  intro i j h
  have h0 := congrArg (fun x : E3 => x 0) h
  have h1 := congrArg (fun x : E3 => x 1) h
  clear h
  fin_cases i <;> fin_cases j
  all_goals norm_num [point] at h0
  all_goals norm_num [point] at h1
  all_goals rfl

/-- The prescribed value of the supporting potential at each center. -/
def potential (i : Fin 5) : ℝ≥0∞ := if i = 0 then 5 / 2 else 0

/-- A center triple belongs to one of the two intended contact families. -/
def Good (i j k : Fin 5) : Prop :=
  ({i, j, k} : Finset (Fin 5)) = {0, 1, 2} ∨
    ({i, j, k} : Finset (Fin 5)) = {0, 3, 4}

/-- The finite-set characterization matches permutation of a canonical branch. -/
theorem good_iff_perm (i j k : Fin 5) :
    Good i j k ↔
      List.Perm [i, j, k] [0, 1, 2] ∨ List.Perm [i, j, k] [0, 3, 4] := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> unfold Good <;> decide

/-- Point-valued permutation form of the good-type condition. -/
theorem perm_points_of_good (i j k : Fin 5) (h : Good i j k) :
    List.Perm [point i, point j, point k] [point 0, point 1, point 2] ∨
      List.Perm [point i, point j, point k] [point 0, point 3, point 4] := by
  rcases (good_iff_perm i j k).1 h with h | h
  · exact Or.inl (by simpa using h.map point)
  · exact Or.inr (by simpa using h.map point)

/-- The pairwise distances of the five centers. -/
def distance (i j : Fin 5) : ℝ :=
  if i = j then 0 else
  if i = 0 ∨ j = 0 then 1 else
  if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then 2 else Real.sqrt 2

theorem norm_sub_point (i j : Fin 5) : ‖point i - point j‖ = distance i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [point, distance, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.ext_iff]

theorem invDistance_point (i j : Fin 5) :
    invDistance (point i) (point j) = (ENNReal.ofReal (distance i j))⁻¹ := by
  rw [invDistance, norm_sub_point]

theorem cross_pair_gap :
    (5 / 2 : ℝ≥0∞) < 2 + (ENNReal.ofReal (Real.sqrt 2))⁻¹ := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hsE : ENNReal.ofReal (Real.sqrt 2) < (2 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg (2 : ℝ))).2 hs
  calc
    (5 / 2 : ℝ≥0∞) = 2 + (2 : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add]
    _ < 2 + (ENNReal.ofReal (Real.sqrt 2))⁻¹ :=
      ENNReal.add_lt_add_left (by norm_num) (ENNReal.inv_lt_inv.2 hsE)

theorem supporting_inequality (i j k : Fin 5) :
    potential i + potential j + potential k ≤
      coulombCost (point i, (point j, point k)) := by
  have hgap := cross_pair_gap.le
  have harith : (5 / 2 : ℝ≥0∞) = 2 + 2⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  have hgap' : (5 / 2 : ℝ≥0∞) ≤ 1 + (1 + (ENNReal.ofReal (Real.sqrt 2))⁻¹) := by
    simpa only [← add_assoc, one_add_one_eq_two] using hgap
  have harith' : (5 / 2 : ℝ≥0∞) = 1 + (1 + (2 : ℝ≥0∞)⁻¹) := by
    simpa only [← add_assoc, one_add_one_eq_two] using harith
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [potential, coulombCost, tripleFst, tripleSnd, tripleThd,
      invDistance_point, distance, Fin.ext_iff]
  all_goals first
    | exact hgap
    | exact harith.le
    | simpa only [add_comm, add_left_comm, add_assoc] using hgap'
    | simpa only [add_comm, add_left_comm, add_assoc] using harith'.le

/-- Every undesired component type has a strict supporting gap at its centers. -/
theorem strict_of_not_good (i j k : Fin 5) (h : ¬ Good i j k) :
    potential i + potential j + potential k <
      coulombCost (point i, (point j, point k)) := by
  have hgap := cross_pair_gap
  have hgap' : (5 / 2 : ℝ≥0∞) < 1 + (1 + (ENNReal.ofReal (Real.sqrt 2))⁻¹) := by
    simpa only [← add_assoc, one_add_one_eq_two] using hgap
  have hpos : 0 < (ENNReal.ofReal (Real.sqrt 2))⁻¹ := ENNReal.inv_pos.2 (by simp)
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try exact False.elim (h (by unfold Good; decide))
  all_goals norm_num [potential, coulombCost, tripleFst, tripleSnd, tripleThd,
      invDistance_point, distance, Fin.ext_iff]
  all_goals first
    | exact hgap
    | simpa only [add_comm, add_left_comm, add_assoc] using hgap'
    | positivity
    | finiteness

/-- Both intended contact types attain equality at the centers. -/
theorem equality_of_good (i j k : Fin 5) (h : Good i j k) :
    coulombCost (point i, (point j, point k)) =
      potential i + potential j + potential k := by
  have harith : (2 + (2 : ℝ≥0∞)⁻¹) = 5 / 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  have harith' : 1 + (1 + (2 : ℝ≥0∞)⁻¹) = 5 / 2 := by
    simpa only [← add_assoc, one_add_one_eq_two] using harith
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try (exfalso; revert h; unfold Good; decide)
  all_goals norm_num [potential, coulombCost, tripleFst, tripleSnd, tripleThd,
      invDistance_point, distance, Fin.ext_iff]
  all_goals first
    | exact harith
    | simpa only [add_comm, add_left_comm, add_assoc] using harith'

/-- The five-center supporting certificate has exactly the desired equality types. -/
theorem equality_iff_good (i j k : Fin 5) :
    coulombCost (point i, (point j, point k)) =
      potential i + potential j + potential k ↔ Good i j k := by
  constructor
  · intro h
    by_contra hn
    exact (strict_of_not_good i j k hn).ne h.symm
  · exact equality_of_good i j k

end Problem356.CenterCertificate

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356.Certificate

/-- An integrable signed lower certificate bounds a nonnegative extended integral. -/
theorem ofReal_integral_le_lintegral {α : Type uAlpha} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {g : α → ℝ≥0∞}
    (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hle : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤ g x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := by
  by_cases htop : (∫⁻ x, g x ∂μ) = ⊤
  · simp [htop]
  have hgfin := ae_lt_top' hg htop
  have hgi := integrable_toReal_of_lintegral_ne_top hg htop
  have hreal : f ≤ᵐ[μ] fun x => (g x).toReal := by
    filter_upwards [hle, hgfin] with x hx hxfin
    exact (ENNReal.ofReal_le_iff_le_toReal hxfin.ne).mp hx
  calc
    ENNReal.ofReal (∫ x, f x ∂μ) ≤
        ENNReal.ofReal (∫ x, (g x).toReal ∂μ) :=
      ENNReal.ofReal_le_ofReal (integral_mono_ae hf hgi hreal)
    _ = ∫⁻ x, g x ∂μ := by
      rw [integral_toReal hg hgfin, ENNReal.ofReal_toReal htop]

/-- Equality with a signed lower certificate forces pointwise equality almost everywhere. -/
theorem ae_eq_of_integral_certificate {α : Type uAlpha} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {g : α → ℝ≥0∞}
    (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hle : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤ g x)
    (hnonneg : 0 ≤ ∫ x, f x ∂μ)
    (heq : (∫⁻ x, g x ∂μ) = ENNReal.ofReal (∫ x, f x ∂μ)) :
    ∀ᵐ x ∂μ, g x = ENNReal.ofReal (f x) := by
  have htop : (∫⁻ x, g x ∂μ) ≠ ⊤ := by
    rw [heq]
    exact ENNReal.ofReal_ne_top
  have hgfin := ae_lt_top' hg htop
  have hgi := integrable_toReal_of_lintegral_ne_top hg htop
  have hreal : f ≤ᵐ[μ] fun x => (g x).toReal := by
    filter_upwards [hle, hgfin] with x hx hxfin
    exact (ENNReal.ofReal_le_iff_le_toReal hxfin.ne).mp hx
  have hint : (∫ x, f x ∂μ) = ∫ x, (g x).toReal ∂μ := by
    rw [integral_toReal hg hgfin, heq, ENNReal.toReal_ofReal hnonneg]
  have hae := (integral_eq_iff_of_ae_le hf hgi hreal).mp hint
  filter_upwards [hae, hgfin] with x hx hxfin
  rw [hx, ENNReal.ofReal_toReal hxfin.ne]

/-- The signed three-coordinate dual potential associated with one marginal potential. -/
def potentialSum (u : E3 → ℝ) (t : Triple) : ℝ :=
  u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)

private theorem first_measurable : Measurable tripleFst := measurable_fst
private theorem second_measurable : Measurable tripleSnd := measurable_fst.comp measurable_snd
private theorem third_measurable : Measurable tripleThd := measurable_snd.comp measurable_snd

/-- Marginal identities transfer integrability of a signed potential to its sum. -/
theorem integrable_potentialSum {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ} (hu : Integrable u μ) :
    Integrable (potentialSum u) π := by
  have h₁ : MeasurePreserving tripleFst π μ := ⟨first_measurable, hπ.2.1⟩
  have h₂ : MeasurePreserving tripleSnd π μ := ⟨second_measurable, hπ.2.2.1⟩
  have h₃ : MeasurePreserving tripleThd π μ := ⟨third_measurable, hπ.2.2.2⟩
  exact ((h₁.integrable_comp hu.aestronglyMeasurable).mpr hu |>.add
    ((h₂.integrable_comp hu.aestronglyMeasurable).mpr hu)).add
    ((h₃.integrable_comp hu.aestronglyMeasurable).mpr hu)

/-- The integral of a common potential sum depends only on the common marginal. -/
theorem integral_potentialSum {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ} (hu : Integrable u μ) :
    (∫ t, potentialSum u t ∂π) = 3 * ∫ x, u x ∂μ := by
  have h₁ : MeasurePreserving tripleFst π μ := ⟨first_measurable, hπ.2.1⟩
  have h₂ : MeasurePreserving tripleSnd π μ := ⟨second_measurable, hπ.2.2.1⟩
  have h₃ : MeasurePreserving tripleThd π μ := ⟨third_measurable, hπ.2.2.2⟩
  have hi₁ := (h₁.integrable_comp hu.aestronglyMeasurable).mpr hu
  have hi₂ := (h₂.integrable_comp hu.aestronglyMeasurable).mpr hu
  have hi₃ := (h₃.integrable_comp hu.aestronglyMeasurable).mpr hu
  have he₁ : (∫ t, u (tripleFst t) ∂π) = ∫ x, u x ∂μ := by
    rw [← hπ.2.1]
    exact (integral_map first_measurable.aemeasurable (by rw [hπ.2.1]; exact hu.aestronglyMeasurable)).symm
  have he₂ : (∫ t, u (tripleSnd t) ∂π) = ∫ x, u x ∂μ := by
    rw [← hπ.2.2.1]
    exact (integral_map second_measurable.aemeasurable (by rw [hπ.2.2.1]; exact hu.aestronglyMeasurable)).symm
  have he₃ : (∫ t, u (tripleThd t) ∂π) = ∫ x, u x ∂μ := by
    rw [← hπ.2.2.2]
    exact (integral_map third_measurable.aemeasurable (by rw [hπ.2.2.2]; exact hu.aestronglyMeasurable)).symm
  calc
    (∫ t, potentialSum u t ∂π) =
        (∫ t, u (tripleFst t) + u (tripleSnd t) ∂π) +
        ∫ t, u (tripleThd t) ∂π := integral_add (hi₁.add hi₂) hi₃
    _ = ((∫ t, u (tripleFst t) ∂π) + (∫ t, u (tripleSnd t) ∂π)) +
        ∫ t, u (tripleThd t) ∂π := by
      congr 1
      exact integral_add hi₁ hi₂
    _ = 3 * ∫ x, u x ∂μ := by rw [he₁, he₂, he₃]; ring

private theorem cost_measurable : Measurable coulombCost := by
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  fun_prop

/-- Every coupling is concentrated on the cube of any full-marginal-mass set. -/
theorem coupling_ae_mem {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U) :
    ∀ᵐ t ∂π, tripleFst t ∈ U ∧ tripleSnd t ∈ U ∧ tripleThd t ∈ U := by
  have h₁ : ∀ᵐ t ∂π, tripleFst t ∈ U :=
    ae_of_ae_map first_measurable.aemeasurable (by rwa [hπ.2.1])
  have h₂ : ∀ᵐ t ∂π, tripleSnd t ∈ U :=
    ae_of_ae_map second_measurable.aemeasurable (by rwa [hπ.2.2.1])
  have h₃ : ∀ᵐ t ∂π, tripleThd t ∈ U :=
    ae_of_ae_map third_measurable.aemeasurable (by rwa [hπ.2.2.2])
  filter_upwards [h₁, h₂, h₃] with t ht₁ ht₂ ht₃
  exact ⟨ht₁, ht₂, ht₃⟩

/-- A signed supporting potential on a full-mass region is a Kantorovich lower bound. -/
theorem kantorovich_lower_bound {μ : Measure E3} {u : E3 → ℝ}
    (hu : Integrable u μ) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U)
    (hcert : ∀ t : Triple, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (potentialSum u t) ≤ coulombCost t) :
    ENNReal.ofReal (3 * ∫ x, u x ∂μ) ≤ kantorovichValue μ := by
  apply le_iInf
  intro π
  apply le_iInf
  intro hπ
  rw [← integral_potentialSum hπ hu]
  apply ofReal_integral_le_lintegral (integrable_potentialSum hπ hu)
    cost_measurable.aemeasurable
  filter_upwards [coupling_ae_mem hπ hU] with t ht
  exact hcert t ht.1 ht.2.1 ht.2.2

/-- An explicit finite plan saturating a supporting potential is an optimizer. -/
theorem optimal_plan_of_certificate {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ}
    (hu : Integrable u μ) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U)
    (hcert : ∀ t : Triple, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (potentialSum u t) ≤ coulombCost t)
    (heq : (∫⁻ t, coulombCost t ∂π) = ENNReal.ofReal (3 * ∫ x, u x ∂μ)) :
    (∫⁻ t, coulombCost t ∂π) = kantorovichValue μ ∧
      kantorovichValue μ < ⊤ ∧ KantorovichAttained μ := by
  have hlower := kantorovich_lower_bound hu hU hcert
  have hupper : kantorovichValue μ ≤ ∫⁻ t, coulombCost t ∂π :=
    iInf_le_of_le π (iInf_le_of_le hπ le_rfl)
  have hvalue : (∫⁻ t, coulombCost t ∂π) = kantorovichValue μ :=
    le_antisymm (heq ▸ hlower) hupper
  refine ⟨hvalue, ?_, ⟨π, hπ, hvalue⟩⟩
  rw [← hvalue, heq]
  exact ENNReal.ofReal_lt_top

/-- Every optimal finite plan must lie on the equality set of a supporting potential. -/
theorem optimal_ae_contact {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ}
    (hu : Integrable u μ) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U)
    (hcert : ∀ t : Triple, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (potentialSum u t) ≤ coulombCost t)
    (hnonneg : 0 ≤ 3 * ∫ x, u x ∂μ)
    (hvalue : kantorovichValue μ = ENNReal.ofReal (3 * ∫ x, u x ∂μ))
    (hopt : (∫⁻ t, coulombCost t ∂π) = kantorovichValue μ) :
    ∀ᵐ t ∂π, coulombCost t = ENNReal.ofReal (potentialSum u t) := by
  apply ae_eq_of_integral_certificate (integrable_potentialSum hπ hu)
    cost_measurable.aemeasurable
  · filter_upwards [coupling_ae_mem hπ hU] with t ht
    exact hcert t ht.1 ht.2.1 ht.2.2
  · rwa [integral_potentialSum hπ hu]
  · rw [integral_potentialSum hπ hu, hopt, hvalue]

end Problem356.Certificate

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set Filter Metric
open scoped ENNReal

namespace Problem356

/-- Finitely many eventual properties hold simultaneously on balls with one
common positive radius around their respective centers. -/
theorem finite_eventual_neighborhoods {ι : Type uIndex} {X : Type uX} [PseudoMetricSpace X]
    (s : Finset ι) (p : ι → X) (P : ι → X → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ x in nhds (p i), P i x) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → P i x := by
  classical
  have hone : ∀ i ∈ s, ∃ r : ℝ, 0 < r ∧
      ∀ x, dist x (p i) < r → P i x := by
    intro i hi
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hP i hi)
    exact ⟨r, hr, fun x hx => h hx⟩
  clear hP
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s his ih =>
      obtain ⟨r, hr, hri⟩ := hone i (Finset.mem_insert_self i s)
      obtain ⟨q, hq, hqs⟩ := ih (fun j hj => hone j (Finset.mem_insert_of_mem hj))
      refine ⟨min r q, lt_min hr hq, ?_⟩
      intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hri x (lt_of_lt_of_le hx (min_le_left _ _))
      · exact hqs j hj x (lt_of_lt_of_le hx (min_le_right _ _))

/-- Triple-coordinate ball version of finite eventual shrinking. -/
theorem finite_eventual_triple_neighborhoods {ι : Type uIndex}
    (s : Finset ι) (p : ι → Triple) (P : ι → Triple → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ t in nhds (p i), P i t) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x y z : E3,
      x ∈ ball (p i).1 r → y ∈ ball (p i).2.1 r →
      z ∈ ball (p i).2.2 r → P i (x, (y, z)) := by
  obtain ⟨r, hr, h⟩ := finite_eventual_neighborhoods s p P hP
  refine ⟨r, hr, ?_⟩
  intro i hi x y z hx hy hz
  apply h i hi (x, (y, z))
  simpa only [Prod.dist_eq, max_lt_iff, Metric.mem_ball] using And.intro hx (And.intro hy hz)

/-- Finitely many strict inequalities at their respective centers persist on
one common positive-radius neighborhood. This is the finite shrinking step
for the bad, distinct-center component types in the certificate. -/
theorem finite_strict_neighborhoods {ι : Type uIndex} {X : Type uX} {Y : Type uY} [PseudoMetricSpace X]
    [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y]
    (s : Finset ι) (p : ι → X) (f g : ι → X → Y)
    (hf : ∀ i ∈ s, ContinuousAt (f i) (p i))
    (hg : ∀ i ∈ s, ContinuousAt (g i) (p i))
    (hgap : ∀ i ∈ s, f i (p i) < g i (p i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → f i x < g i x := by
  exact finite_eventual_neighborhoods s p (fun i x => f i x < g i x)
    (fun i hi => (hf i hi).eventually_lt (hg i hi) (hgap i hi))

/-- Product-space version of finite shrinking, expressed by separate ball
conditions on all three coordinates. -/
theorem finite_strict_triple_neighborhoods {ι : Type uIndex} {Y : Type uY}
    [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y]
    (s : Finset ι) (p : ι → Triple) (f g : ι → Triple → Y)
    (hf : ∀ i ∈ s, ContinuousAt (f i) (p i))
    (hg : ∀ i ∈ s, ContinuousAt (g i) (p i))
    (hgap : ∀ i ∈ s, f i (p i) < g i (p i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x y z : E3,
      x ∈ ball (p i).1 r → y ∈ ball (p i).2.1 r →
      z ∈ ball (p i).2.2 r → f i (x, (y, z)) < g i (x, (y, z)) := by
  obtain ⟨r, hr, h⟩ := finite_strict_neighborhoods s p f g hf hg hgap
  refine ⟨r, hr, ?_⟩
  intro i hi x y z hx hy hz
  apply h i hi (x, (y, z))
  simpa only [Prod.dist_eq, max_lt_iff, Metric.mem_ball] using And.intro hx (And.intro hy hz)

end Problem356

end

end OAI
end
end

section
section
namespace OAI


/-!
# Reparametrizing local branches by their common central component

For local homeomorphisms `X,Z` on the parameter component, the central
parametrizations are `X.symm` and `X.symm.trans Z`. Their common source is
open, contains the central base point, and inherits both smooth inverses.
-/

noncomputable section
open Set Metric

namespace Problem356.CommonBranches

variable {E : Type uE} [TopologicalSpace E]

/-- Reparametrization of the second outer branch by the central coordinate. -/
def outer (X Z : OpenPartialHomeomorph E E) : OpenPartialHomeomorph E E :=
  X.symm.trans Z

@[simp] theorem outer_apply (X Z : OpenPartialHomeomorph E E) (x : E) :
    outer X Z x = Z (X.symm x) := rfl

/-- Both local maps being defined at the parameter base point puts the
central image in the source of the reparametrized outer branch. -/
theorem image_mem_outer_source (X Z : OpenPartialHomeomorph E E) {a : E}
    (haX : a ∈ X.source) (haZ : a ∈ Z.source) :
    X a ∈ (outer X Z).source := by
  change X a ∈ X.symm.source ∩ X.symm ⁻¹' Z.source
  refine ⟨X.map_source haX, ?_⟩
  change X.symm (X a) ∈ Z.source
  rw [X.left_inv haX]
  exact haZ

/-- The common source permits both the inverse branch and the second outer
branch, with their expected component containment and inverse identity. -/
theorem outer_source_properties (X Z : OpenPartialHomeomorph E E) {x : E}
    (hx : x ∈ (outer X Z).source) :
    x ∈ X.target ∧ X.symm x ∈ X.source ∧ X.symm x ∈ Z.source ∧
      outer X Z x ∈ Z.target ∧ X (X.symm x) = x := by
  change x ∈ X.symm.source ∩ X.symm ⁻¹' Z.source at hx
  exact ⟨hx.1, X.symm.map_source hx.1, hx.2, Z.map_source hx.2,
    X.right_inv hx.1⟩

/-- Every contact predicate on the original graph transfers to the central
parametrization. This includes both supporting equality and stationarity. -/
theorem contact_reparametrize (X Z : OpenPartialHomeomorph E E)
    {C : E × (E × E) → Prop}
    (hC : ∀ y ∈ X.source, C (X y, (y, Z y))) {x : E}
    (hx : x ∈ (outer X Z).source) :
    C (x, (X.symm x, outer X Z x)) := by
  have hp := outer_source_properties X Z hx
  simpa only [hp.2.2.2.2, outer_apply] using hC (X.symm x) hp.2.1

/-- The four ordered outer branches associated with two local families. -/
def four (X Z : Fin 2 → OpenPartialHomeomorph E E) :
    Fin 4 → OpenPartialHomeomorph E E :=
  ![(X 0).symm, outer (X 0) (Z 0), (X 1).symm, outer (X 1) (Z 1)]

/-- A common domain for both composed branches is a common domain for all
four outer branches, in the indexing used by the smooth marginal construction. -/
theorem subset_four_sources (X Z : Fin 2 → OpenPartialHomeomorph E E)
    {B : Set E} (hB : ∀ i, B ⊆ (outer (X i) (Z i)).source) :
    ∀ j, B ⊆ (four X Z j).source := by
  intro j
  fin_cases j
  · intro x hx
    exact (outer_source_properties (X 0) (Z 0) (hB 0 hx)).1
  · exact hB 0
  · intro x hx
    exact (outer_source_properties (X 1) (Z 1) (hB 1 hx)).1
  · exact hB 1

/-- Image containment in the four prescribed outer components. -/
theorem four_images_subset (X Z : Fin 2 → OpenPartialHomeomorph E E)
    {B : Set E} (hB : ∀ i, B ⊆ (outer (X i) (Z i)).source)
    (P Q : Fin 2 → Set E)
    (hP : ∀ i, (X i).source ⊆ P i) (hQ : ∀ i, (Z i).target ⊆ Q i) :
    ∀ j, four X Z j '' B ⊆ ![P 0, Q 0, P 1, Q 1] j := by
  intro j y hy
  obtain ⟨x, hx, rfl⟩ := hy
  fin_cases j
  · exact hP 0 (outer_source_properties (X 0) (Z 0) (hB 0 hx)).2.1
  · exact hQ 0 (outer_source_properties (X 0) (Z 0) (hB 0 hx)).2.2.2.1
  · exact hP 1 (outer_source_properties (X 1) (Z 1) (hB 1 hx)).2.1
  · exact hQ 1 (outer_source_properties (X 1) (Z 1) (hB 1 hx)).2.2.2.1

section Metric

variable {M : Type uM} [PseudoMetricSpace M]

/-- Finitely many pairs of local branches sharing a central base point admit
one positive-radius central ball on which all inverse parametrizations are
defined. The ball may also be kept inside any prescribed central neighborhood. -/
theorem exists_common_central_ball {ι : Type uIndex} [Finite ι]
    (X Z : ι → OpenPartialHomeomorph M M) (a : ι → M) (x : M)
    (haX : ∀ i, a i ∈ (X i).source) (haZ : ∀ i, a i ∈ (Z i).source)
    (hcenter : ∀ i, X i (a i) = x)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      ∀ i, ball x r ⊆ (outer (X i) (Z i)).source := by
  have hopen : IsOpen (U ∩ ⋂ i, (outer (X i) (Z i)).source) :=
    hU.inter (isOpen_iInter_of_finite fun i => (outer (X i) (Z i)).open_source)
  have hx : x ∈ U ∩ ⋂ i, (outer (X i) (Z i)).source := by
    refine ⟨hxU, mem_iInter.mpr ?_⟩
    intro i
    rw [← hcenter i]
    exact image_mem_outer_source (X i) (Z i) (haX i) (haZ i)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen x hx
  exact ⟨r, hr, fun y hy => (hsub hy).1,
    fun i y hy => mem_iInter.mp (hsub hy).2 i⟩

/-- The central ball can simultaneously keep the inverse and composed
branches inside arbitrary prescribed outer neighborhoods. Thus shrinking the
global certificate components does not require changing either local chart. -/
theorem exists_common_central_ball_in_components {ι : Type uIndex} [Finite ι]
    (X Z : ι → OpenPartialHomeomorph M M) (a : ι → M) (x : M)
    (haX : ∀ i, a i ∈ (X i).source) (haZ : ∀ i, a i ∈ (Z i).source)
    (hcenter : ∀ i, X i (a i) = x)
    (P Q : ι → Set M) (hP : ∀ i, IsOpen (P i)) (hQ : ∀ i, IsOpen (Q i))
    (haP : ∀ i, a i ∈ P i) (haQ : ∀ i, Z i (a i) ∈ Q i)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      ∀ i, ∀ y ∈ ball x r,
        y ∈ (outer (X i) (Z i)).source ∧
        (X i).symm y ∈ P i ∧ outer (X i) (Z i) y ∈ Q i := by
  have hbase : ∀ i, x ∈ (outer (X i) (Z i)).source := by
    intro i
    rw [← hcenter i]
    exact image_mem_outer_source (X i) (Z i) (haX i) (haZ i)
  have hinv : ∀ i, (X i).symm x = a i := by
    intro i
    rw [← hcenter i, (X i).left_inv (haX i)]
  have houter : ∀ i, outer (X i) (Z i) x = Z i (a i) := by
    intro i
    rw [outer_apply, hinv i]
  have hnear : ∀ i, ∀ᶠ y in nhds x,
      y ∈ (outer (X i) (Z i)).source ∧
      (X i).symm y ∈ P i ∧ outer (X i) (Z i) y ∈ Q i := by
    intro i
    have hys : x ∈ (X i).symm.source :=
      (outer_source_properties (X i) (Z i) (hbase i)).1
    have hyP := ((X i).symm.continuousAt hys).eventually
      ((hP i).mem_nhds (by rw [hinv i]; exact haP i))
    have hwQ := ((outer (X i) (Z i)).continuousAt (hbase i)).eventually
      ((hQ i).mem_nhds (by rw [houter i]; exact haQ i))
    have hs : ∀ᶠ y in nhds x, y ∈ (outer (X i) (Z i)).source :=
      (outer (X i) (Z i)).open_source.mem_nhds (hbase i)
    exact hs.and (hyP.and hwQ)
  have hu : ∀ᶠ y in nhds x, y ∈ U := hU.mem_nhds hxU
  have hall := hu.and (Filter.eventually_all.mpr hnear)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  exact ⟨r, hr, fun y hy => (hball y hy).1,
    fun i y hy => (hball y hy).2 i⟩

end Metric

section Smooth

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness of the inverse central branch and original outer branch
makes the reparametrized branch smooth on its actual open source. -/
theorem contDiffOn_outer {n : WithTop ENat} (X Z : OpenPartialHomeomorph F F)
    (hX : ContDiffOn ℝ n X.symm X.target)
    (hZ : ContDiffOn ℝ n Z Z.source) :
    ContDiffOn ℝ n (outer X Z) (outer X Z).source := by
  exact hZ.comp_inter hX

/-- The inverse of the reparametrized branch is smooth on its actual target. -/
theorem contDiffOn_outer_symm {n : WithTop ENat} (X Z : OpenPartialHomeomorph F F)
    (hX : ContDiffOn ℝ n X X.source)
    (hZ : ContDiffOn ℝ n Z.symm Z.target) :
    ContDiffOn ℝ n (outer X Z).symm (outer X Z).target := by
  exact hX.comp_inter hZ

/-- Forward smoothness of all four centrally parametrized branches. -/
theorem contDiffOn_four {n : WithTop ENat}
    (X Z : Fin 2 → OpenPartialHomeomorph F F)
    (hX : ∀ i, ContDiffOn ℝ n (X i).symm (X i).target)
    (hZ : ∀ i, ContDiffOn ℝ n (Z i) (Z i).source) :
    ∀ j, ContDiffOn ℝ n (four X Z j) (four X Z j).source := by
  intro j
  fin_cases j
  · exact hX 0
  · exact contDiffOn_outer (X 0) (Z 0) (hX 0) (hZ 0)
  · exact hX 1
  · exact contDiffOn_outer (X 1) (Z 1) (hX 1) (hZ 1)

/-- Inverse smoothness of all four centrally parametrized branches. -/
theorem contDiffOn_four_symm {n : WithTop ENat}
    (X Z : Fin 2 → OpenPartialHomeomorph F F)
    (hX : ∀ i, ContDiffOn ℝ n (X i) (X i).source)
    (hZ : ∀ i, ContDiffOn ℝ n (Z i).symm (Z i).target) :
    ∀ j, ContDiffOn ℝ n (four X Z j).symm (four X Z j).target := by
  intro j
  fin_cases j
  · exact hX 0
  · exact contDiffOn_outer_symm (X 0) (Z 0) (hX 0) (hZ 0)
  · exact hX 1
  · exact contDiffOn_outer_symm (X 1) (Z 1) (hX 1) (hZ 1)

end Smooth
end Problem356.CommonBranches

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.FirstCoordinateLift

open CoulombEstimates

/-- Replacing only the first coordinate by a nearby point preserves half the
separation, without any component-label hypothesis. -/
lemma separated_replace_first {η δ : ℝ} {t : Triple} {x : E3}
    (hη : 0 < η) (ht : Separated η t)
    (hclose : dist x t.1 ≤ δ) (hδ : δ ≤ η / 2) :
    Separated (η / 2) (x, t.2) := by
  rcases t with ⟨a, b, c⟩
  rcases ht with ⟨hab, hac, hbc⟩
  have hx : dist a x ≤ δ := by simpa only [dist_comm] using hclose
  have hab' := dist_triangle a x b
  have hac' := dist_triangle a x c
  refine ⟨?_, ?_, ?_⟩ <;> dsimp at * <;> linarith

/-- Weakening separation to half its value. -/
lemma separated_half {η : ℝ} {t : Triple} (hη : 0 < η)
    (ht : Separated η t) : Separated (η / 2) t := by
  rcases ht with ⟨h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The two noncentral coordinates of a measure-valued lift preserve the marginal. -/
lemma preserves_coordinates {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {Q : E3 → Triple}
    (hQ : Measurable Q) (hmap : Measure.map Q μ = π) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) := by
  constructor
  · refine ⟨measurable_tripleSnd.comp hQ, ?_⟩
    rw [← Measure.map_map measurable_tripleSnd hQ, hmap]
    exact hπ.2.2.1
  · refine ⟨measurable_tripleThd.comp hQ, ?_⟩
    rw [← Measure.map_map measurable_tripleThd hQ, hmap]
    exact hπ.2.2.2

/-- A lift of a separated coupling, whose first coordinate remains nearby,
gives a finite-cost preserving pair and the quantitative Coulomb estimate. -/
theorem graph_cost_of_lift {μ : Measure E3} [IsProbabilityMeasure μ]
    {π : Measure Triple} (hπ : IsThreeCoupling μ π)
    {Q : E3 → Triple} (hQ : Measurable Q) (hmap : Measure.map Q μ = π)
    {η δ : ℝ} (hη : 0 < η) (hδ : δ ≤ η / 2)
    (hsep : ∀ᵐ t ∂π, Separated η t)
    (hclose : ∀ᵐ x ∂μ, dist x (Q x).1 ≤ δ) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) < ⊤ ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂π) + ENNReal.ofReal (24 * δ / η ^ 2) := by
  have hsepQ : ∀ᵐ x ∂μ, Separated η (Q x) :=
    ae_of_ae_map hQ.aemeasurable (by rwa [hmap])
  have hsepP : ∀ᵐ x ∂μ, Separated (η / 2) (x, (Q x).2) := by
    filter_upwards [hsepQ, hclose] with x hx hc
    exact separated_replace_first hη hx hc hδ
  have hsepQ' : ∀ᵐ x ∂μ, Separated (η / 2) (Q x) :=
    hsepQ.mono fun _ hx => separated_half hη hx
  have hc : ∀ᵐ x ∂μ, dist (x, (Q x).2).1 (Q x).1 ≤ δ ∧
      dist (x, (Q x).2).2.1 (Q x).2.1 ≤ δ ∧
      dist (x, (Q x).2).2.2 (Q x).2.2 ≤ δ := by
    filter_upwards [hclose] with x hx
    have hδ0 : 0 ≤ δ := dist_nonneg.trans hx
    exact ⟨hx, by simpa using hδ0, by simpa using hδ0⟩
  have hbound := lintegral_coulombCost_le_add_of_ae_close μ (half_pos hη)
    hsepP hsepQ' hc
  have herr : (6 * δ) / (η / 2) ^ 2 = 24 * δ / η ^ 2 := by
    field_simp
    ring
  rw [measure_univ, mul_one, herr] at hbound
  have hint : (∫⁻ x, coulombCost (Q x) ∂μ) = ∫⁻ t, coulombCost t ∂π := by
    rw [← lintegral_map measurable_coulombCost hQ, hmap]
  rw [hint] at hbound
  exact ⟨(preserves_coordinates hπ hQ hmap).1,
    (preserves_coordinates hπ hQ hmap).2,
    graphCost_lt_top_of_ae_separated μ (half_pos hη) hsepP, hbound⟩

end Problem356.FirstCoordinateLift

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Arbitrarily small first-coordinate lifts of a uniformly separated optimal
coupling give finite Monge approximation. Only the first coordinate is adjusted
to obtain a graph, and uniform separation controls the cost of that adjustment. -/
theorem finiteMongeApproximation_of_near_fst_lifts
    {mu : Measure E3} [IsProbabilityMeasure mu] {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t)
    (hlifts : ∀ delta : ℝ, 0 < delta →
      ∃ Q : E3 → Triple, Measurable Q ∧ Measure.map Q mu = pi ∧
        ∀ᵐ x ∂mu, dist x (Q x).1 ≤ delta) :
    FiniteMongeApproximation mu := by
  intro epsilon hepsilon
  let delta : ℝ := min (eta / 2) (epsilon * eta ^ 2 / 24)
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply lt_min
    · positivity
    · positivity
  obtain ⟨Q, hQ, hmap, hclose⟩ := hlifts delta hdelta
  have hdelta_eta : delta ≤ eta / 2 := min_le_left _ _
  obtain ⟨h2, h3, hfinite, hcost⟩ :=
    FirstCoordinateLift.graph_cost_of_lift hpi hQ hmap heta hdelta_eta hseparated hclose
  refine ⟨tripleSnd ∘ Q, tripleThd ∘ Q, h2, h3, hfinite, ?_⟩
  have herror : 24 * delta / eta ^ 2 ≤ epsilon := by
    apply (div_le_iff₀ (sq_pos_of_pos heta)).2
    have hdelta_eps : delta ≤ epsilon * eta ^ 2 / 24 := min_le_right _ _
    linarith
  calc
    graphCost mu (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂pi) + ENNReal.ofReal (24 * delta / eta ^ 2) := hcost
    _ ≤ kantorovichValue mu + ENNReal.ofReal epsilon := by
      rw [hoptimal]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal herror)

/-- A uniformly separated optimal coupling has finite value. -/
theorem kantorovichValue_lt_top_of_separated_optimizer
    {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    kantorovichValue mu < ⊤ := by
  have : IsProbabilityMeasure pi := hpi.1
  rw [← hoptimal]
  exact CoulombEstimates.lintegral_coulombCost_lt_top_of_ae_separated pi heta hseparated

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Every measure obtained from a density is absolutely continuous with respect to volume. -/
theorem densityMeasure_absolutelyContinuous (rho : E3 → ℝ) :
    densityMeasure rho ≪ (volume : Measure E3) :=
  withDensity_absolutelyContinuous _ _

/-- A density measure has no point atoms, without any regularity assumption on the density. -/
instance densityMeasure_nullSingletonClass (rho : E3 → ℝ) :
    NullSingletonClass (densityMeasure rho) := by
  unfold densityMeasure
  infer_instance

/-- A density measure gives no mass to the complement of its topological support. -/
theorem densityMeasure_tsupport_compl (rho : E3 → ℝ) :
    densityMeasure rho (tsupport rho)ᶜ = 0 := by
  rw [densityMeasure, withDensity_apply _ (isClosed_tsupport rho).measurableSet.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (isClosed_tsupport rho).measurableSet.compl] with x hx
  simp only [Pi.zero_apply]
  rw [image_eq_zero_of_notMem_tsupport hx, ENNReal.ofReal_zero]

/-- Compact support of the density provides an explicit compact set of full measure. -/
theorem densityMeasure_exists_compact_conull {rho : E3 → ℝ}
    (hrho : HasCompactSupport rho) :
    ∃ K : Set E3, IsCompact K ∧ densityMeasure rho Kᶜ = 0 :=
  ⟨tsupport rho, hrho, densityMeasure_tsupport_compl rho⟩

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Every feasible Monge pair bounds its defining infimum from above. -/
theorem mongeValue_le_graphCost (mu : Measure E3) {T2 T3 : E3 → E3}
    (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    mongeValue mu ≤ graphCost mu T2 T3 := by
  exact iInf_le_of_le T2 (iInf_le_of_le T3 (iInf_le_of_le h2 (iInf_le _ h3)))

/-- Arbitrarily accurate finite preserving-map approximations imply equality of values. -/
theorem FiniteMongeApproximation.equal_infima {mu : Measure E3}
    [IsProbabilityMeasure mu] (h : FiniteMongeApproximation mu) :
    mongeValue mu = kantorovichValue mu := by
  apply le_antisymm _ (kantorovichValue_le_mongeValue mu)
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  obtain ⟨T2, T3, h2, h3, _, hcost⟩ := h epsilon hepsilon
  exact (mongeValue_le_graphCost mu h2 h3).trans (by simpa using hcost)

/-- Finite equality of values already supplies finite near-minimizing preserving maps. -/
theorem finiteMongeApproximation_of_equal_infima {mu : Measure E3}
    (hfinite : kantorovichValue mu < ⊤)
    (heq : mongeValue mu = kantorovichValue mu) :
    FiniteMongeApproximation mu := by
  intro epsilon hepsilon
  have hlt : mongeValue mu < kantorovichValue mu + ENNReal.ofReal epsilon := by
    rw [heq]
    exact ENNReal.lt_add_right hfinite.ne
      (ne_of_gt (ENNReal.ofReal_pos.mpr hepsilon))
  unfold mongeValue at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T2, T3, h2, h3, hcost⟩ := hlt
  refine ⟨T2, T3, h2, h3, ?_, hcost.le⟩
  exact hcost.trans (ENNReal.add_lt_top.mpr ⟨hfinite, ENNReal.ofReal_lt_top⟩)

/-- Under finiteness, equal infima and finite Monge approximation are equivalent. -/
theorem finiteMongeApproximation_iff_equal_infima {mu : Measure E3}
    [IsProbabilityMeasure mu] (hfinite : kantorovichValue mu < ⊤) :
    FiniteMongeApproximation mu ↔ mongeValue mu = kantorovichValue mu :=
  ⟨FiniteMongeApproximation.equal_infima, finiteMongeApproximation_of_equal_infima hfinite⟩

/-- The full target conclusion follows once the counterexample and finite approximation
have been constructed for the same density. -/
theorem HasCoulombCounterexample.fullConclusion {rho : E3 → ℝ}
    (h : HasCoulombCounterexample rho)
    (happrox : FiniteMongeApproximation (densityMeasure rho)) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := h.2.1
  exact ⟨h, happrox.equal_infima, happrox⟩

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Problem356

/-- A compactly supported atomless marginal and a uniformly separated optimal
coupling admit finite-cost deterministic approximations. -/
theorem finiteMongeApproximation_of_compact_separated_optimizer
    {mu : Measure E3} [IsProbabilityMeasure mu] [NullSingletonClass mu]
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {K : Set E3} (hK : IsCompact K) (hfull : mu Kᶜ = 0)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    FiniteMongeApproximation mu := by
  have : IsProbabilityMeasure pi := hpi.1
  apply finiteMongeApproximation_of_near_fst_lifts hpi hoptimal heta hseparated
  intro delta hdelta
  obtain ⟨Q, hQ, hmap, hclose⟩ := Transport.exists_measurable_lift_close
    mu pi tripleFst measurable_tripleFst hpi.2.1 hK hfull hdelta
  exact ⟨Q, hQ, hmap, hclose.mono fun _ hx => hx.le⟩

/-- A Coulomb counterexample with a separated optimal plan and compactly supported
density has equal Monge and Kantorovich infima and finite-cost Monge approximations. -/
theorem HasCoulombCounterexample.hasFull_of_separated_optimizer
    {rho : E3 → ℝ} (hcounter : HasCoulombCounterexample rho)
    {pi : Measure Triple} (hpi : IsThreeCoupling (densityMeasure rho) pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue (densityMeasure rho))
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := hcounter.2.1
  obtain ⟨K, hK, hfull⟩ := densityMeasure_exists_compact_conull hcounter.1.2.2.1
  have happ := finiteMongeApproximation_of_compact_separated_optimizer
    hpi hoptimal hK hfull heta hseparated
  exact hcounter.fullConclusion happ

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.ComponentPotential

variable {ι : Type uIndex} [Fintype ι]

/-- Glue local potentials on disjoint components, with value zero outside them. -/
def glue (U : ι → Set E3) (u : ι → E3 → ℝ) (x : E3) : ℝ :=
  ∑ i, (U i).indicator (u i) x

theorem glue_eq {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) {i : ι} {x : E3}
    (hx : x ∈ U i) : glue U u x = u i x := by
  classical
  unfold glue
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_notMem
    intro hxj
    exact Set.disjoint_left.mp (hdisj hji) hxj hx
  · simp

theorem glue_eq_zero {U : ι → Set E3} {u : ι → E3 → ℝ} {x : E3}
    (hx : x ∉ ⋃ i, U i) : glue U u x = 0 := by
  classical
  unfold glue
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hxi
  exact hx (mem_iUnion.mpr ⟨i, hxi⟩)

/-- Local continuity is sufficient for global Borel measurability of the extension. -/
theorem measurable_glue {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hU : ∀ i, MeasurableSet (U i)) (hu : ∀ i, ContinuousOn (u i) (U i)) :
    Measurable (glue U u) := by
  classical
  unfold glue
  apply Finset.measurable_sum
  intro i _
  change Measurable ((U i).piecewise (u i) (fun _ => 0))
  exact (hu i).measurable_piecewise continuousOn_const (hU i)

/-- Gluing preserves continuity on the open union of pairwise disjoint components. -/
theorem continuousOn_glue {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hU : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hu : ∀ i, ContinuousOn (u i) (U i)) :
    ContinuousOn (glue U u) (⋃ i, U i) := by
  apply ContinuousOn.iUnion_of_isOpen _ hU
  intro i
  apply (hu i).congr
  intro x hx
  exact glue_eq hdisj hx

/-- A common absolute bound passes to the glued potential, globally if it is nonnegative. -/
theorem abs_glue_le {U : ι → Set E3} {u : ι → E3 → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hu : ∀ i, ∀ x ∈ U i, |u i x| ≤ M) (x : E3) :
    |glue U u x| ≤ M := by
  by_cases hx : x ∈ ⋃ i, U i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rw [glue_eq hdisj hxi]
    exact hu i x hxi
  · rw [glue_eq_zero hx, abs_zero]
    exact hM

/-- A bounded glued potential is integrable against every finite marginal. -/
theorem integrable_glue {U : ι → Set E3} {u : ι → E3 → ℝ} {M : ℝ}
    {mu : Measure E3} [IsFiniteMeasure mu]
    (hM : 0 ≤ M) (hU : ∀ i, MeasurableSet (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hc : ∀ i, ContinuousOn (u i) (U i))
    (hb : ∀ i, ∀ x ∈ U i, |u i x| ≤ M) :
    Integrable (glue U u) mu := by
  apply Integrable.of_bound (measurable_glue hU hc).aestronglyMeasurable M
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_glue_le hM hdisj hb x

end Problem356.ComponentPotential

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma invDistance_pos (x y : E3) : 0 < invDistance x y := by
  simp [invDistance]

lemma coulombCost_pos (t : Triple) : 0 < coulombCost t := by
  unfold coulombCost
  exact lt_of_lt_of_le (invDistance_pos _ _)
    ((le_add_right le_rfl).trans (le_add_right le_rfl))

lemma continuous_invDistance : Continuous (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  exact (ENNReal.continuous_ofReal.comp (continuous_fst.sub continuous_snd).norm).inv

lemma continuous_coulombCost : Continuous coulombCost := by
  unfold coulombCost
  have h1 : Continuous tripleFst := continuous_fst
  have h2 : Continuous tripleSnd := continuous_fst.comp continuous_snd
  have h3 : Continuous tripleThd := continuous_snd.comp continuous_snd
  exact ((continuous_invDistance.comp (h1.prodMk h2)).add
    (continuous_invDistance.comp (h1.prodMk h3))).add
    (continuous_invDistance.comp (h2.prodMk h3))

lemma lowerSemicontinuous_coulombCost : LowerSemicontinuous coulombCost :=
  continuous_coulombCost.lowerSemicontinuous

lemma graphCost_congr_ae (mu : Measure E3) {T2 T3 S2 S3 : E3 → E3}
    (h2 : T2 =ᵐ[mu] S2) (h3 : T3 =ᵐ[mu] S3) :
    graphCost mu T2 T3 = graphCost mu S2 S3 := by
  apply lintegral_congr_ae
  filter_upwards [h2, h3] with x hx2 hx3
  simp only [hx2, hx3]

lemma graphMeasure_congr_ae (mu : Measure E3) {T2 T3 S2 S3 : E3 → E3}
    (h2 : T2 =ᵐ[mu] S2) (h3 : T3 =ᵐ[mu] S3) :
    graphMeasure mu T2 T3 = graphMeasure mu S2 S3 := by
  apply Measure.map_congr
  filter_upwards [h2, h3] with x hx2 hx3
  simp only [graphMap, hx2, hx3]

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- Every bad center type with a strict extended-valued cost gap retains that
gap on small component balls. The finite index set may include repeated-center
types, since extended-valued Coulomb cost is continuous at collisions. -/
theorem finite_bad_component_neighborhoods {ι : Type uIndex}
    (s : Finset (ι × (ι × ι))) (p : ι → E3) (v : ι → E3 → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i))
    (hgap : ∀ a ∈ s,
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ s, ∀ x y z : E3,
      x ∈ ball (p a.1) r → y ∈ ball (p a.2.1) r → z ∈ ball (p a.2.2) r →
      ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) <
        coulombCost (x, (y, z)) := by
  apply finite_strict_triple_neighborhoods s
    (fun a => (p a.1, (p a.2.1, p a.2.2)))
    (fun a t => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
    (fun _ => coulombCost)
  · intro a _
    have h₁ : ContinuousAt (fun t : Triple => v a.1 t.1)
        (p a.1, (p a.2.1, p a.2.2)) :=
      (hv a.1).comp (f := fun t : Triple => t.1) continuousAt_fst
    have h₂ : ContinuousAt (fun t : Triple => v a.2.1 t.2.1)
        (p a.1, (p a.2.1, p a.2.2)) :=
      (hv a.2.1).comp (f := fun t : Triple => t.2.1)
        (continuousAt_fst.comp continuousAt_snd)
    have h₃ : ContinuousAt (fun t : Triple => v a.2.2 t.2.2)
        (p a.1, (p a.2.1, p a.2.2)) :=
      (hv a.2.2).comp (f := fun t : Triple => t.2.2)
        (continuousAt_snd.comp continuousAt_snd)
    exact ENNReal.continuous_ofReal.continuousAt.comp ((h₁.add h₂).add h₃)
  · intro _ _
    exact continuous_coulombCost.continuousAt
  · exact hgap

/-- Continuity of the sum of the three local potentials in one component type. -/
theorem continuousAt_component_sum {ι : Type uIndex} (p : ι → E3) (v : ι → E3 → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) (a : ι × (ι × ι)) :
    ContinuousAt
      (fun t : Triple => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
      (p a.1, (p a.2.1, p a.2.2)) := by
  have h₁ : ContinuousAt (fun t : Triple => v a.1 t.1)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.1).comp (f := fun t : Triple => t.1) continuousAt_fst
  have h₂ : ContinuousAt (fun t : Triple => v a.2.1 t.2.1)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.1).comp (f := fun t : Triple => t.2.1)
      (continuousAt_fst.comp continuousAt_snd)
  have h₃ : ContinuousAt (fun t : Triple => v a.2.2 t.2.2)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.2).comp (f := fun t : Triple => t.2.2)
      (continuousAt_snd.comp continuousAt_snd)
  exact ENNReal.continuous_ofReal.continuousAt.comp ((h₁.add h₂).add h₃)

/-- The local-to-global finite-type certificate step. Local supporting
inequalities and exact contact sets are needed only at the good types;
strict gaps at every other center type are enough for all remaining types.
A single radius works for the inequalities and exact equality characterization. -/
theorem finite_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (v : ι → E3 → ℝ)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hv : ∀ i, ContinuousAt (v i) (p i))
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ a, ∀ x y z : E3,
      x ∈ ball (p a.1) r → y ∈ ball (p a.2.1) r → z ∈ ball (p a.2.2) r →
      ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) = coulombCost (x, (y, z)) ↔
        Good a ∧ Contact a (x, (y, z))) := by
  classical
  have hevent : ∀ a ∈ (Finset.univ : Finset (ι × (ι × ι))),
      ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Good a ∧ Contact a t) := by
    intro a _
    by_cases ha : Good a
    · filter_upwards [hgood a ha] with t ht
      exact ⟨ht.1, by simpa [ha] using ht.2⟩
    · have he := (continuousAt_component_sum p v hv a).eventually_lt
        continuous_coulombCost.continuousAt (hbad a ha)
      filter_upwards [he] with t ht
      exact ⟨ht.le, by simp [ha, ht.ne]⟩
  obtain ⟨r, hr, h⟩ := finite_eventual_triple_neighborhoods Finset.univ
    (fun a : ι × (ι × ι) => (p a.1, (p a.2.1, p a.2.2))) _ hevent
  exact ⟨r, hr, fun a => h a (Finset.mem_univ a)⟩

/-- Once all ordered component types have been certified, the glued potential
satisfies the supporting inequality on the entire component union. -/
theorem componentPotential_supporting_inequality {ι : Type uIndex} [Fintype ι]
    (U : ι → Set E3) (v : ι → E3 → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hlocal : ∀ i j k, ∀ x ∈ U i, ∀ y ∈ U j, ∀ z ∈ U k,
      ENNReal.ofReal (v i x + v j y + v k z) ≤ coulombCost (x, (y, z)))
    {x y z : E3} (hx : x ∈ ⋃ i, U i) (hy : y ∈ ⋃ i, U i)
    (hz : z ∈ ⋃ i, U i) :
    ENNReal.ofReal (ComponentPotential.glue U v x + ComponentPotential.glue U v y +
      ComponentPotential.glue U v z) ≤ coulombCost (x, (y, z)) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  rw [ComponentPotential.glue_eq hdisj hi, ComponentPotential.glue_eq hdisj hj,
    ComponentPotential.glue_eq hdisj hk]
  exact hlocal i j k x hi y hj z hk

/-- Strict inequalities on bad ordered component types exclude those types
from the contact set of the glued potential. -/
theorem componentPotential_contact_good {ι : Type uIndex} [Fintype ι]
    (U : ι → Set E3) (v : ι → E3 → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (Good : ι → ι → ι → Prop)
    (hbad : ∀ i j k, ¬ Good i j k → ∀ x ∈ U i, ∀ y ∈ U j, ∀ z ∈ U k,
      ENNReal.ofReal (v i x + v j y + v k z) < coulombCost (x, (y, z)))
    {i j k : ι} {x y z : E3} (hx : x ∈ U i) (hy : y ∈ U j) (hz : z ∈ U k)
    (hcontact : ENNReal.ofReal (ComponentPotential.glue U v x + ComponentPotential.glue U v y +
      ComponentPotential.glue U v z) = coulombCost (x, (y, z))) : Good i j k := by
  classical
  by_contra hnot
  have hlt := hbad i j k hnot x hx y hy z hz
  rw [ComponentPotential.glue_eq hdisj hx, ComponentPotential.glue_eq hdisj hy,
    ComponentPotential.glue_eq hdisj hz] at hcontact
  exact (ne_of_lt hlt) hcontact

end Problem356

end

end OAI
end
end

section
section
namespace OAI


/-! The combinatorial step from a permuted contact triple to branch selection. -/

namespace Problem356
namespace ContactSelection

variable {α : Type uAlpha} {ι : Type uIndex}

/-- If precisely the first source entry belongs to the central set, any
permutation whose first target entry is central has the same first entry. -/
theorem first_eq_of_perm
    {B : Set α} {x y z p q r : α}
    (hperm : List.Perm [x, y, z] [p, q, r])
    (hx : x ∈ B) (hq : q ∉ B) (hr : r ∉ B) : x = p := by
  have hm : x ∈ [p, q, r] := hperm.mem_iff.mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hp | hq' | hr'
  · exact hp
  · exact False.elim (hq (hq' ▸ hx))
  · exact False.elim (hr (hr' ▸ hx))

/-- After identifying the central entry, each remaining entry is one of the
other two entries of the contact triple. -/
theorem second_eq_or_third_of_perm
    {B : Set α} {x y z p q r : α}
    (hperm : List.Perm [x, y, z] [p, q, r])
    (hx : x ∈ B) (hq : q ∉ B) (hr : r ∉ B) : y = q ∨ y = r := by
  have hxp := first_eq_of_perm hperm hx hq hr
  subst p
  have hp : List.Perm [y, z] [q, r] := hperm.cons_inv
  have hm : y ∈ [q, r] := hp.mem_iff.mp (by simp)
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hm

/-- A contact triple parameterized by `s`, with central branch `X`,
selects either `Y x` or `W x` once `Y` inverts `X` on the parameter domain. -/
theorem second_selects_inverse_branch
    {B P : Set α} {X Z Y W : α → α} {x y z s : α}
    (hperm : List.Perm [x, y, z] [X s, s, Z s])
    (hx : x ∈ B) (hs : s ∈ P)
    (hOuter : ∀ a ∈ P, a ∉ B ∧ Z a ∉ B)
    (hInverse : ∀ a ∈ P, Y (X a) = a)
    (hW : ∀ a ∈ B, W a = Z (Y a)) : y = Y x ∨ y = W x := by
  have hout := hOuter s hs
  have hcentral := first_eq_of_perm hperm hx hout.1 hout.2
  have hinv : Y x = s := by rw [hcentral]; exact hInverse s hs
  rcases second_eq_or_third_of_perm hperm hx hout.1 hout.2 with hy | hy
  · exact Or.inl (hy.trans hinv.symm)
  · exact Or.inr (hy.trans (by rw [hW x hx, hinv]))

end ContactSelection
end Problem356

end OAI
end
end

section
section
namespace OAI


/-!
# From permuted contact triples to deterministic branch selection

The central component is disjoint from every outer branch image. Therefore,
when a contact triple is written with its first coordinate in the central
component, its second coordinate must be an outer branch of that same point.
The statements are independent of the analytic construction of the branches.
-/

open MeasureTheory
open scoped ENNReal

namespace Problem356.ContactSelection

variable {α : Type uAlpha} {ι : Type uIndex}

/-- A deliberately broad contact relation: any pair of outer branches is
allowed. A more precise geometric contact set can imply this relation. -/
def BranchContact (B : Set α) (H : ι → α → α) (t : α × (α × α)) : Prop :=
  ∃ x ∈ B, ∃ i j, List.Perm [t.1, t.2.1, t.2.2] [x, H i x, H j x]

/-- Removing the unique central entry of a permuted triple leaves two outer
entries. Neither injectivity nor pairwise disjointness of the outer images
is required for this step. -/
theorem second_eq_outer_of_perm {B : Set α} {a b c x y z : α}
    (ha : a ∈ B) (hy : y ∉ B) (hz : z ∉ B)
    (hp : List.Perm [a, b, c] [x, y, z]) : b = y ∨ b = z := by
  have ha' : a = x ∨ a = y ∨ a = z := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      (hp.mem_iff.mp (by simp : a ∈ [a, b, c]))
  have hax : a = x := ha'.resolve_right (by
    rintro (h | h)
    · exact hy (h ▸ ha)
    · exact hz (h ▸ ha))
  subst x
  have hp' : List.Perm [b, c] [y, z] := List.Perm.cons_inv hp
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using
    (hp'.mem_iff.mp (by simp : b ∈ [b, c]))

theorem second_selects_of_contact {B : Set α} {H : ι → α → α}
    (houter : ∀ i x, x ∈ B → H i x ∉ B)
    {t : α × (α × α)} (hfirst : t.1 ∈ B) (hcontact : BranchContact B H t) :
    ∃ i, t.2.1 = H i t.1 := by
  rcases hcontact with ⟨x, hx, i, j, hp⟩
  have hm : t.1 = x ∨ t.1 = H i x ∨ t.1 = H j x := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      (hp.mem_iff.mp (by simp : t.1 ∈ [t.1, t.2.1, t.2.2]))
  have hcentral : t.1 = x := hm.resolve_right (by
    rintro (h | h)
    · exact houter i x hx (h ▸ hfirst)
    · exact houter j x hx (h ▸ hfirst))
  rcases second_eq_outer_of_perm hfirst (houter i x hx) (houter j x hx) hp with h | h
  · exact ⟨i, h.trans (congrArg (H i) hcentral.symm)⟩
  · exact ⟨j, h.trans (congrArg (H j) hcentral.symm)⟩

theorem second_selects_of_contact_disjoint {B : Set α} {H : ι → α → α}
    (houter : ∀ i, Disjoint B (H i '' B))
    {t : α × (α × α)} (hfirst : t.1 ∈ B) (hcontact : BranchContact B H t) :
    ∃ i, t.2.1 = H i t.1 := by
  apply second_selects_of_contact (B := B) (H := H) ?_ hfirst hcontact
  intro i x hx hix
  exact Set.disjoint_left.mp (houter i) hix ⟨x, hx, rfl⟩

variable [MeasurableSpace α]

/-- Transfer the contact relation from the marginal to a central component
measure, and then extract the branch selected by the second graph map. -/
theorem ae_selects_of_ae_contact {μ ν : Measure α} {B : Set α}
    {H : ι → α → α} {T₂ T₃ : α → α}
    (hac : ν ≪ μ) (hB : ∀ᵐ x ∂ν, x ∈ B)
    (houter : ∀ i, Disjoint B (H i '' B))
    (hcontact : ∀ᵐ x ∂μ, BranchContact B H (x, (T₂ x, T₃ x))) :
    ∀ᵐ x ∂ν, ∃ i, T₂ x = H i x := by
  filter_upwards [hB, hac.ae_le hcontact] with x hx hc
  exact second_selects_of_contact_disjoint houter hx hc

/-- A positive-weight component is absolutely continuous with respect to any
measure dominating it, including the five-component branch mixture. -/
theorem absolutelyContinuous_of_smul_le {μ ν : Measure α} {a : ℝ≥0∞}
    (ha : a ≠ 0) (hdom : a • ν ≤ μ) : ν ≪ μ :=
  (Measure.absolutelyContinuous_smul ha).trans hdom.absolutelyContinuous

theorem ae_selects_of_smul_le_of_ae_contact {μ ν : Measure α} {a : ℝ≥0∞}
    {B : Set α} {H : ι → α → α} {T₂ T₃ : α → α}
    (ha : a ≠ 0) (hdom : a • ν ≤ μ) (hB : ∀ᵐ x ∂ν, x ∈ B)
    (houter : ∀ i, Disjoint B (H i '' B))
    (hcontact : ∀ᵐ x ∂μ, BranchContact B H (x, (T₂ x, T₃ x))) :
    ∀ᵐ x ∂ν, ∃ i, T₂ x = H i x :=
  ae_selects_of_ae_contact (absolutelyContinuous_of_smul_le ha hdom) hB houter hcontact

end Problem356.ContactSelection

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace Problem356.LocalImplicit

variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- Analytic implicit-function theorem, packaged on open product neighborhoods.
The equation is normalized to zero, as for a stationary-point equation. -/
theorem exists_analytic_implicit_branch
    (G : P × S → S) (p : P) (s : S)
    (hG : ContDiffAt ℝ ω G (p, s))
    (hzero : G (p, s) = 0)
    (hinv : (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).IsInvertible) :
    ∃ (ψ : P → S) (U : Set P) (V : Set S),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ s ∈ V ∧
      ContDiffOn ℝ ω ψ U ∧ MapsTo ψ U V ∧ ψ p = s ∧
      (∀ y ∈ U, G (y, ψ y) = 0) ∧
      (∀ y ∈ U, ∀ z ∈ V, G (y, z) = 0 ↔ ψ y = z) ∧
      HasStrictFDerivAt ψ
        (-(fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).inverse ∘L
          (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ P S)) p := by
  let ψ : P → S := hG.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ω ψ p := hG.contDiffAt_implicitFunction (by simp) hinv
  have hψp : ψ p = s := hG.implicitFunction_apply_self (by simp) hinv
  have heq : ∀ᶠ q in 𝓝 (p, s), G q = 0 ↔ ψ q.1 = q.2 := by
    simpa only [hzero] using hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  obtain ⟨U₀, hU₀, V₀, hV₀, hprod⟩ := mem_nhds_prod_iff.mp heq
  obtain ⟨V, hVV₀, hVopen, hsV⟩ := mem_nhds_iff.mp hV₀
  have hmaps : ψ ⁻¹' V ∈ 𝓝 p := hψ.continuousAt.preimage_mem_nhds (by
    rw [hψp]
    exact hVopen.mem_nhds hsV)
  have hcont : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ ω ψ y := hψ.eventually (by simp)
  have heqn : ∀ᶠ y in 𝓝 p, G (y, ψ y) = 0 := by
    simpa only [hzero] using hG.eventually_apply_implicitFunction (by simp) hinv
  obtain ⟨U, hUsub, hUopen, hpU⟩ :=
    mem_nhds_iff.mp (inter_mem hU₀ (inter_mem hmaps (hcont.and heqn)))
  refine ⟨ψ, U, V, hUopen, hpU, hVopen, hsV, ?_, ?_, hψp, ?_, ?_, ?_⟩
  · exact hUopen.contDiffOn_iff.mpr (fun _ hy => (hUsub hy).2.2.1)
  · exact fun y hy => (hUsub hy).2.1
  · exact fun y hy => (hUsub hy).2.2.2
  · intro y hy z hz
    exact hprod ⟨(hUsub hy).1, hVV₀ hz⟩
  · exact hG.hasStrictFDerivAt_implicitFunction (by simp) hinv

omit [CompleteSpace S] in
/-- A map analytic at one point with invertible derivative is analytic in both
 directions on a suitable open partial homeomorphism. -/
theorem exists_analytic_local_diffeomorph
    (f : P → S) (p : P)
    (hf : ContDiffAt ℝ ω f p)
    (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ e : OpenPartialHomeomorph P S,
      (e : P → S) = f ∧ p ∈ e.source ∧
      ContDiffOn ℝ ω e e.source ∧ ContDiffOn ℝ ω e.symm e.target := by
  obtain ⟨A, hA⟩ := hinv
  have hderiv : HasFDerivAt f (A : P →L[ℝ] S) p := by
    rw [hA]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let e₀ := hf.toOpenPartialHomeomorph f hderiv (by simp)
  have he₀ : (e₀ : P → S) = f := rfl
  have hp₀ : p ∈ e₀.source := hf.mem_toOpenPartialHomeomorph_source hderiv (by simp)
  have hfp₀ : f p ∈ e₀.target := hf.image_mem_toOpenPartialHomeomorph_target hderiv (by simp)
  have hinverse : ContDiffAt ℝ ω e₀.symm (f p) := by
    have hleft : e₀.symm (f p) = p := e₀.left_inv hp₀
    apply e₀.contDiffAt_symm hfp₀
    · simpa only [hleft, he₀] using hderiv
    · simpa only [hleft, he₀] using hf
  obtain ⟨V, hVsub, hVopen, hfpV⟩ :=
    mem_nhds_iff.mp (hinverse.eventually (by simp))
  have hpre : f ⁻¹' V ∈ 𝓝 p := hf.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hfpV)
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (inter_mem (e₀.open_source.mem_nhds hp₀) (inter_mem (hf.eventually (by simp)) hpre))
  refine ⟨e₀.restrOpen U hUopen, rfl, ⟨hp₀, hpU⟩, ?_, ?_⟩
  · apply (e₀.restrOpen U hUopen).open_source.contDiffOn_iff.mpr
    intro x hx
    exact (hUsub hx.2).2.1
  · apply (e₀.restrOpen U hUopen).open_target.contDiffOn_iff.mpr
    intro y hy
    have hx := (e₀.restrOpen U hUopen).map_target hy
    have hxy := (e₀.restrOpen U hUopen).right_inv hy
    apply hVsub
    have hmem := (hUsub hx.2).2.2
    change f ((e₀.restrOpen U hUopen).symm y) ∈ V at hmem
    change f ((e₀.restrOpen U hUopen).symm y) = y at hxy
    exact hxy ▸ hmem

omit [CompleteSpace S] in
/-- The two projections of a local branch can be made analytic diffeomorphisms
on one common source neighborhood, contained in any prescribed neighborhood. -/
theorem exists_two_analytic_local_charts
    (ψ : P → S × S) (p : P) (U : Set P) (hU : U ∈ 𝓝 p)
    (hψ : ContDiffAt ℝ ω ψ p)
    (hinv₁ : (fderiv ℝ (fun y => (ψ y).1) p).IsInvertible)
    (hinv₂ : (fderiv ℝ (fun y => (ψ y).2) p).IsInvertible) :
    ∃ e₁ e₂ : OpenPartialHomeomorph P S,
      (e₁ : P → S) = (fun y => (ψ y).1) ∧
      (e₂ : P → S) = (fun y => (ψ y).2) ∧
      p ∈ e₁.source ∧ e₁.source = e₂.source ∧ e₁.source ⊆ U ∧
      ContDiffOn ℝ ω e₁ e₁.source ∧ ContDiffOn ℝ ω e₁.symm e₁.target ∧
      ContDiffOn ℝ ω e₂ e₂.source ∧ ContDiffOn ℝ ω e₂.symm e₂.target := by
  obtain ⟨e₁, he₁, hp₁, hc₁, hi₁⟩ :=
    exists_analytic_local_diffeomorph (fun y => (ψ y).1) p hψ.fst hinv₁
  obtain ⟨e₂, he₂, hp₂, hc₂, hi₂⟩ :=
    exists_analytic_local_diffeomorph (fun y => (ψ y).2) p hψ.snd hinv₂
  obtain ⟨O, hOU, hOopen, hpO⟩ := mem_nhds_iff.mp hU
  let W := e₁.source ∩ (e₂.source ∩ O)
  have hWopen : IsOpen W := e₁.open_source.inter (e₂.open_source.inter hOopen)
  have hW₁ : W ⊆ e₁.source := fun _ h => h.1
  have hW₂ : W ⊆ e₂.source := fun _ h => h.2.1
  have hs₁ : (e₁.restrOpen W hWopen).source = W := inter_eq_right.mpr hW₁
  have hs₂ : (e₂.restrOpen W hWopen).source = W := inter_eq_right.mpr hW₂
  refine ⟨e₁.restrOpen W hWopen, e₂.restrOpen W hWopen, he₁, he₂, ?_,
    hs₁.trans hs₂.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs₁]
    exact ⟨hp₁, hp₂, hpO⟩
  · rw [hs₁]
    exact fun _ h => hOU h.2.2
  · exact hc₁.mono (fun _ h => h.1)
  · exact hi₁.mono (fun _ h => h.1)
  · exact hc₂.mono (fun _ h => h.1)
  · exact hi₂.mono (fun _ h => h.1)

/-- The derivative supplied by the implicit-function theorem, with parameter first. -/
def implicitDerivative (G : P × (S × S) → S × S) (p : P) (s : S × S) :
    P →L[ℝ] S × S :=
  -(fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P (S × S)).inverse ∘L
    (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ P (S × S))

/-- Two separately invertible coordinates of one local stationary branch. -/
structure AnalyticStationaryCharts (G : P × (S × S) → S × S) (p : P) (s : S × S) where
  central : OpenPartialHomeomorph P S
  opposite : OpenPartialHomeomorph P S
  source_eq : central.source = opposite.source
  point_mem : p ∈ central.source
  central_value : central p = s.1
  opposite_value : opposite p = s.2
  stateDomain : Set (S × S)
  stateDomain_open : IsOpen stateDomain
  state_mem : s ∈ stateDomain
  mapsTo_state : MapsTo (fun y => (central y, opposite y)) central.source stateDomain
  stationary : ∀ y ∈ central.source, G (y, (central y, opposite y)) = 0
  unique_zero : ∀ y ∈ central.source, ∀ z ∈ stateDomain,
    G (y, z) = 0 ↔ (central y, opposite y) = z
  central_analytic : ContDiffOn ℝ ω central central.source
  central_inverse_analytic : ContDiffOn ℝ ω central.symm central.target
  opposite_analytic : ContDiffOn ℝ ω opposite opposite.source
  opposite_inverse_analytic : ContDiffOn ℝ ω opposite.symm opposite.target

/-- Local stationarity plus the three invertibility checks produces two genuine
analytic charts on a common open source. -/
theorem nonempty_analyticStationaryCharts
    (G : P × (S × S) → S × S) (p : P) (s : S × S)
    (hG : ContDiffAt ℝ ω G (p, s)) (hzero : G (p, s) = 0)
    (hinv : (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P (S × S)).IsInvertible)
    (hcentral : (ContinuousLinearMap.fst ℝ S S ∘L implicitDerivative G p s).IsInvertible)
    (hopposite : (ContinuousLinearMap.snd ℝ S S ∘L implicitDerivative G p s).IsInvertible) :
    Nonempty (AnalyticStationaryCharts G p s) := by
  obtain ⟨ψ, U, V, hUopen, hpU, hVopen, hsV, hψU, hψV, hψp, heqn, huniq, hd⟩ :=
    exists_analytic_implicit_branch G p s hG hzero hinv
  have hψ : ContDiffAt ℝ ω ψ p := hUopen.contDiffOn_iff.mp hψU hpU
  have hd₁ : HasFDerivAt (fun y => (ψ y).1)
      (ContinuousLinearMap.fst ℝ S S ∘L implicitDerivative G p s) p :=
    hd.hasFDerivAt.fst
  have hd₂ : HasFDerivAt (fun y => (ψ y).2)
      (ContinuousLinearMap.snd ℝ S S ∘L implicitDerivative G p s) p :=
    hd.hasFDerivAt.snd
  obtain ⟨e₁, e₂, he₁, he₂, hp, hsource, hsub, hc₁, hi₁, hc₂, hi₂⟩ :=
    exists_two_analytic_local_charts ψ p U (hUopen.mem_nhds hpU) hψ
      (by rw [hd₁.fderiv]; exact hcentral) (by rw [hd₂.fderiv]; exact hopposite)
  refine ⟨{
    central := e₁
    opposite := e₂
    source_eq := hsource
    point_mem := hp
    central_value := ?_
    opposite_value := ?_
    stateDomain := V
    stateDomain_open := hVopen
    state_mem := hsV
    mapsTo_state := ?_
    stationary := ?_
    unique_zero := ?_
    central_analytic := hc₁
    central_inverse_analytic := hi₁
    opposite_analytic := hc₂
    opposite_inverse_analytic := hi₂ }⟩
  · simp only [he₁, hψp]
  · simp only [he₂, hψp]
  · intro y hy
    simpa only [he₁, he₂, Prod.eta] using hψV (hsub hy)
  · intro y hy
    simpa only [he₁, he₂, Prod.eta] using heqn y (hsub hy)
  · intro y hy z hz
    simpa only [he₁, he₂, Prod.eta] using huniq y (hsub hy) z hz

namespace AnalyticStationaryCharts

variable {G : P × (S × S) → S × S} {p : P} {s : S × S}

omit [CompleteSpace P] [CompleteSpace S]

/-- Restrict both parameter charts to the same additional open neighborhood. -/
def restrictSource (c : AnalyticStationaryCharts G p s)
    (U : Set P) (hU : IsOpen U) (hp : p ∈ U) : AnalyticStationaryCharts G p s where
  central := c.central.restrOpen U hU
  opposite := c.opposite.restrOpen U hU
  source_eq := by
    change c.central.source ∩ U = c.opposite.source ∩ U
    rw [c.source_eq]
  point_mem := ⟨c.point_mem, hp⟩
  central_value := c.central_value
  opposite_value := c.opposite_value
  stateDomain := c.stateDomain
  stateDomain_open := c.stateDomain_open
  state_mem := c.state_mem
  mapsTo_state := fun _ hy => c.mapsTo_state hy.1
  stationary := fun y hy => c.stationary y hy.1
  unique_zero := fun y hy z hz => c.unique_zero y hy.1 z hz
  central_analytic := c.central_analytic.mono (fun _ h => h.1)
  central_inverse_analytic := c.central_inverse_analytic.mono (fun _ h => h.1)
  opposite_analytic := c.opposite_analytic.mono (fun _ h => h.1)
  opposite_inverse_analytic := c.opposite_inverse_analytic.mono (fun _ h => h.1)

@[simp] theorem restrictSource_central_coe
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    ((c.restrictSource U hU hp).central : P → S) = c.central := rfl

@[simp] theorem restrictSource_opposite_coe
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    ((c.restrictSource U hU hp).opposite : P → S) = c.opposite := rfl

@[simp] theorem restrictSource_source
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    (c.restrictSource U hU hp).central.source = c.central.source ∩ U := rfl

/-- Any smaller open state neighborhood can be used after shrinking the common
parameter domain. All chart functions and all uniqueness conclusions are preserved. -/
theorem exists_restrict_state
    (c : AnalyticStationaryCharts G p s) (W : Set (S × S))
    (hW : IsOpen W) (hsW : s ∈ W) (hWV : W ⊆ c.stateDomain) :
    ∃ d : AnalyticStationaryCharts G p s,
      d.stateDomain = W ∧ d.central.source ⊆ c.central.source ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  have hp₂ : p ∈ c.opposite.source := c.source_eq ▸ c.point_mem
  have hc₁ : ContinuousAt c.central p :=
    c.central.continuousOn.continuousAt (c.central.open_source.mem_nhds c.point_mem)
  have hc₂ : ContinuousAt c.opposite p :=
    c.opposite.continuousOn.continuousAt (c.opposite.open_source.mem_nhds hp₂)
  have hval : (c.central p, c.opposite p) = s :=
    Prod.ext c.central_value c.opposite_value
  have hpre : (fun y => (c.central y, c.opposite y)) ⁻¹' W ∈ 𝓝 p :=
    (hc₁.prodMk hc₂).preimage_mem_nhds (by rw [hval]; exact hW.mem_nhds hsW)
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hpre
  let c₀ := c.restrictSource U hUopen hpU
  let d : AnalyticStationaryCharts G p s := {
    c₀ with
      stateDomain := W
      stateDomain_open := hW
      state_mem := hsW
      mapsTo_state := fun _ hy => hUsub hy.2
      unique_zero := fun y hy z hz => c.unique_zero y hy.1 z (hWV hz) }
  exact ⟨d, rfl, (fun _ hy => hy.1), rfl, rfl⟩

/-- The common source can be chosen to be a genuine positive-radius ball,
inside any prescribed parameter neighborhood, without changing either chart function. -/
theorem exists_restrict_ball
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : U ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ ∃ d : AnalyticStationaryCharts G p s,
      d.central.source = Metric.ball p r ∧ d.central.source ⊆ U ∧
      d.stateDomain = c.stateDomain ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (c.central.open_source.mem_nhds c.point_mem) hU)
  let d := c.restrictSource (Metric.ball p r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hsource : d.central.source = Metric.ball p r :=
    inter_eq_right.mpr (fun _ hx => (hball hx).1)
  refine ⟨r, hr, d, hsource, ?_, rfl, rfl, rfl⟩
  rw [hsource]
  exact fun _ hx => (hball hx).2

end AnalyticStationaryCharts

end Problem356.LocalImplicit

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem356.LocalHessian

open Matrix
open scoped RealInnerProductSpace

/-- Invertible matrices induce invertible continuous linear maps in Euclidean coordinates. -/
lemma toEuclideanCLM_isInvertible {n : Type uN} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).IsInvertible := by
  obtain ⟨u, hu⟩ := hA.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toMonoidHom
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

abbrev AxisSpace := EuclideanSpace ℝ (Fin 3)
abbrev StateSpace := AxisSpace × AxisSpace
abbrev JointSpace := EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)

/-- Passing from sum coordinates to the product coordinates used by the implicit function theorem. -/
def stateCoordinates : JointSpace ≃L[ℝ] StateSpace := EuclideanSpace.sumEquivProd

/-- The regularized state derivative as a continuous linear map on product space. -/
def stateOperator (k : Fin 3) : StateSpace →L[ℝ] StateSpace :=
  stateCoordinates.toContinuousLinearMap ∘L
    (Matrix.toEuclideanCLM (n := Fin 3 ⊕ Fin 3) (𝕜 := ℝ) (regularizedHessian k)) ∘L
      stateCoordinates.symm.toContinuousLinearMap

lemma stateOperator_isInvertible (k : Fin 3) : (stateOperator k).IsInvertible := by
  exact ContinuousLinearMap.IsInvertible.comp
    (ContinuousLinearMap.isInvertible_equiv (f := stateCoordinates))
    (ContinuousLinearMap.IsInvertible.comp
      (toEuclideanCLM_isInvertible _ (regularizedHessian_isUnit k))
      (ContinuousLinearMap.isInvertible_equiv (f := stateCoordinates.symm)))

lemma centralDerivativeCLM_isInvertible (k : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (centralDerivative k)).IsInvertible :=
  toEuclideanCLM_isInvertible _ (centralDerivative_isUnit k)

lemma oppositeDerivativeCLM_isInvertible (k : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (oppositeDerivative k)).IsInvertible :=
  toEuclideanCLM_isInvertible _ (oppositeDerivative_isUnit k)

lemma regularizedHessian_coercive (k : Fin 3) (v : JointSpace) :
    16 * ‖v‖ ^ 2 ≤ ⟪v, Matrix.toEuclideanCLM (n := Fin 3 ⊕ Fin 3) (𝕜 := ℝ) (regularizedHessian k) v⟫ := by
  rw [Matrix.inner_toEuclideanCLM]
  have hq := regularizedHessian_quadratic k (WithLp.ofLp v)
  simp only [star_trivial] at hq
  rw [hq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
    mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_add] using
    (scalar_quadratic_coercive (x := v (Sum.inl i)) (z := v (Sum.inr i))
      (eigenvalue_cases k i))

@[simp] lemma stateCoordinates_symm_inl (v : StateSpace) (i : Fin 3) :
    stateCoordinates.symm v (Sum.inl i) = v.1 i := rfl

@[simp] lemma stateCoordinates_symm_inr (v : StateSpace) (i : Fin 3) :
    stateCoordinates.symm v (Sum.inr i) = v.2 i := rfl

lemma stateOperator_fst_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).1 i =
      (20 + 2 * eigenvalue k i) * v.1 i - eigenvalue k i * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inl i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [upperBlock, mixedBlock, mulVec_diagonal, sub_eq_add_neg]

lemma stateOperator_snd_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).2 i =
      -eigenvalue k i * v.1 i + (20 + (9 / 8) * eigenvalue k i) * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inr i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [lowerBlock, mixedBlock, mulVec_diagonal]

lemma stateOperator_joint_coercive (k : Fin 3) (v : StateSpace) :
    16 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) ≤
      ⟪v.1, (stateOperator k v).1⟫ + ⟪v.2, (stateOperator k v).2⟫ := by
  simp only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, stateOperator_fst_apply, stateOperator_snd_apply,
    mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := scalar_quadratic_coercive (x := v.1 i) (z := v.2 i) (eigenvalue_cases k i)
  nlinarith

lemma stateOperator_coercive (k : Fin 3) (v : StateSpace) :
    16 * ‖v‖ ^ 2 ≤
      ⟪v.1, (stateOperator k v).1⟫ + ⟪v.2, (stateOperator k v).2⟫ := by
  have hn : ‖v‖ ^ 2 ≤ ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖v.1‖ ‖v.2‖ with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ‖v.1‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ‖v.2‖]
  nlinarith [stateOperator_joint_coercive k v]

/-- The derivative in the parameter variable at the center. -/
def parameterOperator (k : Fin 3) : AxisSpace →L[ℝ] StateSpace :=
  let Q := Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (pairHessian k)
  (-Q).prod ((-(1 / 8 : ℝ)) • Q)

/-- The derivative of the stationary branch: central and opposite components. -/
def branchOperator (k : Fin 3) : AxisSpace →L[ℝ] StateSpace :=
  (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (centralDerivative k)).prod
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (oppositeDerivative k))

@[simp] lemma branchOperator_fst_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (branchOperator k v).1 i = (if i = k then 9 / 106 else -15 / 271) * v i := by
  change ((centralDerivative k) *ᵥ WithLp.ofLp v) i = _
  simp [centralDerivative, mulVec_diagonal]

@[simp] lemma branchOperator_snd_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (branchOperator k v).2 i = (if i = k then 1 / 53 else -1 / 271) * v i := by
  change ((oppositeDerivative k) *ᵥ WithLp.ofLp v) i = _
  simp [oppositeDerivative, mulVec_diagonal]

@[simp] lemma parameterOperator_fst_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (parameterOperator k v).1 i = -eigenvalue k i * v i := by
  change -(((pairHessian k) *ᵥ WithLp.ofLp v) i) = _
  simp [pairHessian, mulVec_diagonal]

@[simp] lemma parameterOperator_snd_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (parameterOperator k v).2 i = -(eigenvalue k i * v i) / 8 := by
  change (-(1 / 8 : ℝ)) * (((pairHessian k) *ᵥ WithLp.ofLp v) i) = _
  simp [pairHessian, mulVec_diagonal]
  ring

lemma stateOperator_comp_branchOperator (k : Fin 3) :
    stateOperator k ∘L branchOperator k = -parameterOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    simp only [ContinuousLinearMap.comp_apply, stateOperator_fst_apply,
      branchOperator_fst_apply, branchOperator_snd_apply,
      _root_.neg_apply, Prod.fst_neg, PiLp.neg_apply,
      parameterOperator_fst_apply]
    unfold eigenvalue
    split_ifs <;> ring
  · ext i
    simp only [ContinuousLinearMap.comp_apply, stateOperator_snd_apply,
      branchOperator_fst_apply, branchOperator_snd_apply,
      _root_.neg_apply, Prod.snd_neg, PiLp.neg_apply,
      parameterOperator_snd_apply]
    unfold eigenvalue
    split_ifs <;> ring

lemma neg_inverse_comp_parameterOperator (k : Fin 3) :
    -((stateOperator k).inverse ∘L parameterOperator k) = branchOperator k := by
  calc
    -((stateOperator k).inverse ∘L parameterOperator k) =
        (stateOperator k).inverse ∘L (-parameterOperator k) := by
          rw [ContinuousLinearMap.comp_neg]
    _ = (stateOperator k).inverse ∘L (stateOperator k ∘L branchOperator k) := by
          rw [stateOperator_comp_branchOperator]
    _ = branchOperator k := by
          rw [← ContinuousLinearMap.comp_assoc,
            (stateOperator_isInvertible k).inverse_comp_self, ContinuousLinearMap.id_comp]

lemma central_inverse_block_isInvertible (k : Fin 3) :
    ((ContinuousLinearMap.fst ℝ AxisSpace AxisSpace) ∘L
      (-((stateOperator k).inverse ∘L parameterOperator k))).IsInvertible := by
  rw [neg_inverse_comp_parameterOperator]
  exact centralDerivativeCLM_isInvertible k

lemma opposite_inverse_block_isInvertible (k : Fin 3) :
    ((ContinuousLinearMap.snd ℝ AxisSpace AxisSpace) ∘L
      (-((stateOperator k).inverse ∘L parameterOperator k))).IsInvertible := by
  rw [neg_inverse_comp_parameterOperator]
  exact oppositeDerivativeCLM_isInvertible k

end Problem356.LocalHessian

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped Topology ContDiff

namespace Problem356.CoulombBranches

open LocalImplicit LocalHessian

/-- The concrete K=20 matrix certificate discharges every invertibility premise
of the local branch theorem once the two partial derivatives are identified. -/
theorem stationary_charts_of_center_derivatives
    (G : E3 × (E3 × E3) → E3 × E3) (k : Fin 3) (p : E3) (s : E3 × E3)
    (hG : ContDiffAt ℝ ω G (p, s)) (hzero : G (p, s) = 0)
    (hstate : fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ E3 (E3 × E3) =
      stateOperator k)
    (hparameter : fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ E3 (E3 × E3) =
      parameterOperator k) :
    Nonempty (AnalyticStationaryCharts G p s) := by
  apply nonempty_analyticStationaryCharts G p s hG hzero
  · rw [hstate]
    exact stateOperator_isInvertible k
  · unfold implicitDerivative
    rw [hstate, hparameter]
    exact central_inverse_block_isInvertible k
  · unfold implicitDerivative
    rw [hstate, hparameter]
    exact opposite_inverse_block_isInvertible k

end Problem356.CoulombBranches

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real-valued radial Coulomb interaction, used only away from the origin. -/
def pairCost (x : E) : ℝ := ‖x‖⁻¹

/-- The gradient of the real radial Coulomb interaction. -/
def pairGradient (x : E) : E := -(‖x‖ ^ 3)⁻¹ • x

lemma hasFDerivAt_norm_explicit {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg x)] at h
  convert h using 1
  · ext y
    simp [Real.sqrt_sq (norm_nonneg y)]
  · ext y
    simp only [smul_apply, smul_eq_mul]
    field_simp
    simp [mul_comm]

lemma hasFDerivAt_pairCost {x : E} (hx : x ≠ 0) :
    HasFDerivAt (pairCost : E → ℝ) (-(‖x‖ ^ 3)⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasDerivAt_inv hn).comp_hasFDerivAt x (hasFDerivAt_norm_explicit hx)
  have hs : -(‖x‖ ^ 2)⁻¹ * ‖x‖⁻¹ = -(‖x‖ ^ 3)⁻¹ := by
    field_simp
  convert! h using 1
  simp only [smul_smul, hs]

lemma contDiffAt_pairCost {n : WithTop ENat} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n (pairCost : E → ℝ) x := by
  exact (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)

/-- The Hessian of the real radial Coulomb interaction. -/
def pairHessian (x : E) : E →L[ℝ] E :=
  -(‖x‖ ^ 3)⁻¹ • ContinuousLinearMap.id ℝ E +
    (3 * (‖x‖ ^ 5)⁻¹) • (innerSL ℝ x).smulRight x

lemma hasFDerivAt_radialFactor {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => -(‖y‖ ^ 3)⁻¹)
      ((3 * (‖x‖ ^ 5)⁻¹) • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := ((hasFDerivAt_pairCost hx).pow 3).neg
  convert! h using 1
  · ext y
    simp [pairCost, inv_pow]
  · ext y
    simp only [smul_apply, smul_eq_mul, neg_apply, pairCost]
    norm_num
    field_simp

lemma hasFDerivAt_pairGradient {x : E} (hx : x ≠ 0) :
    HasFDerivAt (pairGradient : E → E) (pairHessian x) x := by
  have h := (hasFDerivAt_radialFactor hx).smul (hasFDerivAt_id x)
  convert! h using 1
  ext y
  simp [pairHessian, ContinuousLinearMap.smulRight_apply, smul_smul]

lemma contDiffAt_pairGradient {n : WithTop ENat} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n (pairGradient : E → E) x := by
  exact (((contDiffAt_norm ℝ hx).pow 3).inv
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))).neg.smul contDiffAt_id

omit [InnerProductSpace ℝ E] in
@[simp] lemma pairCost_neg (x : E) : pairCost (-x) = pairCost x := by
  simp [pairCost]

@[simp] lemma pairGradient_neg (x : E) : pairGradient (-x) = -pairGradient x := by
  simp [pairGradient]

@[simp] lemma pairHessian_neg (x : E) : pairHessian (-x) = pairHessian x := by
  ext y
  simp [pairHessian]

lemma pairHessian_apply (x y : E) :
    pairHessian x y = -(‖x‖ ^ 3)⁻¹ • y +
      (3 * (‖x‖ ^ 5)⁻¹ * ⟪x, y⟫) • x := by
  simp [pairHessian, smul_smul]

lemma pairHessian_apply_self {x : E} (hx : x ≠ 0) :
    pairHessian x x = (2 * (‖x‖ ^ 3)⁻¹) • x := by
  rw [pairHessian_apply, real_inner_self_eq_norm_sq, ← add_smul]
  congr 1
  have hn := norm_ne_zero_iff.mpr hx
  field_simp
  ring

lemma pairHessian_apply_orthogonal {x y : E} (hxy : ⟪x, y⟫ = 0) :
    pairHessian x y = -(‖x‖ ^ 3)⁻¹ • y := by
  simp [pairHessian_apply, hxy]

lemma pairHessian_symmetric (x y z : E) :
    ⟪pairHessian x y, z⟫ = ⟪y, pairHessian x z⟫ := by
  simp only [pairHessian_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm y x]
  ring

lemma pairHessian_smul_pos (x : E) {r : ℝ} (hr : 0 < r) :
    pairHessian (r • x) = (r ^ 3)⁻¹ • pairHessian x := by
  ext y
  simp only [pairHessian_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    real_inner_smul_left, smul_apply, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

lemma pairHessian_apply_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) (y : E) :
    pairHessian x y = -y + (3 * ⟪x, y⟫) • x := by
  simp [pairHessian_apply, hx]

lemma pairHessian_injective {x : E} (hx : x ≠ 0) :
    Function.Injective (pairHessian x) := by
  apply (injective_iff_map_eq_zero (pairHessian x)).2
  intro y hy
  have hn : (‖x‖ ^ 3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))
  have hxy : ⟪x, y⟫ = 0 := by
    have h := pairHessian_symmetric x x y
    rw [pairHessian_apply_self hx, hy, inner_zero_right, real_inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hn)
  rw [pairHessian_apply_orthogonal hxy] at hy
  exact (smul_eq_zero.mp hy).resolve_left (neg_ne_zero.mpr hn)

lemma pairHessian_isInvertible [FiniteDimensional ℝ E] {x : E} (hx : x ≠ 0) :
    (pairHessian x).IsInvertible := by
  have hi := pairHessian_injective hx
  have hs : Function.Surjective (pairHessian x).toLinearMap :=
    LinearMap.surjective_of_injective hi
  refine ⟨(LinearEquiv.ofBijective (pairHessian x).toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, ?_⟩
  rfl

lemma fderiv_pairCost {x : E} (hx : x ≠ 0) :
    fderiv ℝ (pairCost : E → ℝ) x = innerSL ℝ (pairGradient x) := by
  rw [(hasFDerivAt_pairCost hx).fderiv]
  simp [pairGradient]

lemma hasFDerivAt_fderiv_pairCost {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fderiv ℝ (pairCost : E → ℝ))
      ((innerSL ℝ).comp (pairHessian x)) x := by
  have h := (innerSL ℝ).hasFDerivAt.comp x (hasFDerivAt_pairGradient hx)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact fderiv_pairCost hy

lemma secondFDeriv_pairCost_apply {x : E} (hx : x ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (pairCost : E → ℝ)) x v w = ⟪pairHessian x v, w⟫ := by
  rw [(hasFDerivAt_fderiv_pairCost hx).fderiv]
  rfl

lemma pairHessian_quadratic_lower (x y : E) :
    -(‖x‖ ^ 3)⁻¹ * ‖y‖ ^ 2 ≤ ⟪pairHessian x y, y⟫ := by
  rw [pairHessian_apply, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  apply le_add_of_nonneg_right
  have hn : 0 ≤ 3 * (‖x‖ ^ 5)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg (norm_nonneg x) 5))
  nlinarith [mul_nonneg hn (sq_nonneg ⟪x, y⟫)]

end Problem356.CoulombCalculus

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.GeometryJets

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative interface supplied by the inverse-norm calculus. -/
def KernelDerivative : Prop :=
  ∀ b : E, b ≠ 0 → HasFDerivAt (fun v : E => ‖v‖⁻¹)
    ((-(‖b‖ ^ 3)⁻¹) • innerSL ℝ b) b

private theorem kernelDerivative : KernelDerivative (E := E) := by
  intro b hb
  exact CoulombCalculus.hasFDerivAt_pairCost hb

omit [InnerProductSpace ℝ E] in
theorem center_nonzero {a : E} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h
  simp [h] at ha

/-- The two opposite outer centers cancel the derivative in the central coordinate. -/
theorem hasFDerivAt_center_x
    (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt
      (fun x : E => ‖x - a‖⁻¹ + ‖x - (-a)‖⁻¹ + ‖a - (-a)‖⁻¹)
      (0 : E →L[ℝ] ℝ) (0 : E) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have h1 := (kernelDerivative (0 - a) (by simpa using hneg)).comp (0 : E)
    ((hasFDerivAt_id (0 : E)).sub_const a)
  have h2 := (kernelDerivative (0 - (-a)) (by simpa using ha0)).comp (0 : E)
    ((hasFDerivAt_id (0 : E)).sub_const (-a))
  have hs := (h1.add h2).add_const (‖a - (-a)‖⁻¹)
  simpa [ha, innerSL, ContinuousLinearMap.comp_id] using hs

/-- The derivative in the negative outer coordinate at an opposite unit pair. -/
theorem hasFDerivAt_center_z
    (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt
      (fun z : E => ‖(0 : E) - a‖⁻¹ + ‖(0 : E) - z‖⁻¹ + ‖a - z‖⁻¹)
      ((5 / 4 : ℝ) • innerSL ℝ a) (-a) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : -a - a = (-2 : ℝ) • a := by module
  have hnorm : ‖-a - a‖ = 2 := by rw [hvec, norm_smul, ha]; norm_num
  have hdouble : -a - a ≠ 0 := by
    intro heq
    simp [heq] at hnorm
  have h1 := kernelDerivative (-a) hneg
  have h2 := (kernelDerivative (-a - a) hdouble).comp (-a)
    ((hasFDerivAt_id (-a)).sub_const a)
  have hs := ((hasFDerivAt_const (‖a‖⁻¹) (-a)).add h1).add h2
  convert! hs using 1
  · ext z
    simp [norm_sub_rev]
  · ext v
    simp [hvec, norm_smul, ha, innerSL]
    ring

/-- Joint state derivative, with the positive outer coordinate held fixed. -/
theorem hasFDerivAt_center_state
    (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt
      (fun p : E × E => ‖p.1 - a‖⁻¹ + ‖p.1 - p.2‖⁻¹ + ‖a - p.2‖⁻¹)
      ((5 / 4 : ℝ) • (innerSL ℝ a).comp (ContinuousLinearMap.snd ℝ E E))
      (0, -a) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hnorm : ‖a - -a‖ = 2 := by rw [hvec, norm_smul, ha]; norm_num
  have hdouble : a - -a ≠ 0 := by
    intro heq
    simp [heq] at hnorm
  have hf : HasFDerivAt (fun p : E × E => p.1)
      (ContinuousLinearMap.fst ℝ E E) (0, -a) := hasFDerivAt_fst
  have hz : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) (0, -a) := hasFDerivAt_snd
  have h1 := (kernelDerivative (0 - a) (by simpa using hneg)).comp (0, -a)
    (hf.sub_const a)
  have h2 := (kernelDerivative (0 - -a) (by simpa using ha0)).comp (0, -a)
    (hf.sub hz)
  have h3 := (kernelDerivative (a - -a) hdouble).comp (0, -a)
    (hz.const_sub a)
  convert! (h1.add h2).add h3 using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [hvec, norm_smul, ha, innerSL]
  ring

/-- Subtracting the common central and negative outer potentials makes the center stationary. -/
theorem hasFDerivAt_center_stationary
    (a : E) (ha : ‖a‖ = 1) (K : ℝ) :
    HasFDerivAt
      (fun p : E × E =>
        (‖p.1 - a‖⁻¹ + ‖p.1 - p.2‖⁻¹ + ‖a - p.2‖⁻¹) -
        ((5 / 2 : ℝ) - K / 2 * ‖p.1‖ ^ 2) -
        ((5 / 4 : ℝ) * inner ℝ a (p.2 + a) - K / 2 * ‖p.2 + a‖ ^ 2))
      (0 : (E × E) →L[ℝ] ℝ) (0, -a) := by
  have hf : HasFDerivAt (fun p : E × E => p.1)
      (ContinuousLinearMap.fst ℝ E E) (0, -a) := hasFDerivAt_fst
  have hz : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) (0, -a) := hasFDerivAt_snd
  have hu := (hf.norm_sq.const_mul (K / 2)).const_sub (5 / 2)
  have hza := hz.add_const a
  have hv1 := ((innerSL ℝ a).hasFDerivAt.comp (0, -a) hza).const_mul (5 / 4)
  have hv2 := hza.norm_sq.const_mul (K / 2)
  have hs := ((hasFDerivAt_center_state a ha).sub hu).sub (hv1.sub hv2)
  convert! hs using 1
  simp

end Problem356.GeometryJets

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem356.GeometryJets

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The state gradient of the regularized three-body Coulomb cost.
The input is `(parameter, (central point, negative outer point))`. -/
def stationaryEquation (K : ℝ) (a : E) (p : E × (E × E)) : E × E :=
  (pairGradient (p.2.1 - p.1) + pairGradient (p.2.1 - p.2.2) + K • p.2.1,
   -pairGradient (p.2.1 - p.2.2) - pairGradient (p.1 - p.2.2) -
     (5 / 4 : ℝ) • a + K • (p.2.2 + a))

/-- The center state Hessian, expressed using the single-pair unit-center Hessian. -/
def centerStateHessian (K : ℝ) (Q : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  (((2 : ℝ) • Q + K • ContinuousLinearMap.id ℝ E).comp
      (ContinuousLinearMap.fst ℝ E E) - Q.comp (ContinuousLinearMap.snd ℝ E E)).prod
    (-(Q.comp (ContinuousLinearMap.fst ℝ E E)) +
      ((9 / 8 : ℝ) • Q + K • ContinuousLinearMap.id ℝ E).comp
        (ContinuousLinearMap.snd ℝ E E))

/-- The center derivative with respect to the moving positive outer point. -/
def centerParameterDerivative (Q : E →L[ℝ] E) : E →L[ℝ] (E × E) :=
  (-Q).prod ((-1 / 8 : ℝ) • Q)

lemma stationaryEquation_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    stationaryEquation K a (a, (0, -a)) = 0 := by
  have hvec : a - -a = (2 : ℝ) • a := by module
  simp [stationaryEquation, pairGradient, hvec, norm_smul, ha]
  module

private lemma hessian_neg_center (a : E) : pairHessian (-a) = pairHessian a := by
  apply ContinuousLinearMap.ext
  intro v
  simp [pairHessian, innerSL, ContinuousLinearMap.smulRight_apply]

private lemma hessian_double_center (a : E) (ha : ‖a‖ = 1) :
    pairHessian ((2 : ℝ) • a) = (1 / 8 : ℝ) • pairHessian a := by
  apply ContinuousLinearMap.ext
  intro v
  simp [pairHessian, innerSL, ContinuousLinearMap.smulRight_apply, norm_smul, ha]
  module

lemma hasFDerivAt_stationary_state_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (fun p : E × E => stationaryEquation K a (a, p))
      (centerStateHessian K (pairHessian a)) (0, -a) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hdouble : a - -a ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (by norm_num) ha0
  have hf : HasFDerivAt (fun p : E × E => p.1)
      (ContinuousLinearMap.fst ℝ E E) (0, -a) := hasFDerivAt_fst
  have hz : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) (0, -a) := hasFDerivAt_snd
  have h1 := (hasFDerivAt_pairGradient (show (0 : E) - a ≠ 0 by simpa using hneg)).comp
    (0, -a) (hf.sub_const a)
  have h2 := (hasFDerivAt_pairGradient (show (0 : E) - -a ≠ 0 by simpa using ha0)).comp
    (0, -a) (hf.sub hz)
  have h3 := (hasFDerivAt_pairGradient hdouble).comp (0, -a) (hz.const_sub a)
  have hx := (h1.add h2).add (hf.const_smul K)
  have hzz := ((h2.neg.sub h3).sub_const ((5 / 4 : ℝ) • a)).add
    ((hz.add_const a).const_smul K)
  convert! hx.prodMk hzz using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [centerStateHessian, hvec, hessian_double_center a ha]
  constructor <;> module

lemma hasFDerivAt_stationary_parameter_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (fun y : E => stationaryEquation K a (y, (0, -a)))
      (centerParameterDerivative (pairHessian a)) a := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hdouble : a - -a ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (by norm_num) ha0
  have hy := hasFDerivAt_id (𝕜 := ℝ) a
  have h1 := (hasFDerivAt_pairGradient (show (0 : E) - a ≠ 0 by simpa using hneg)).comp
    a (hy.const_sub 0)
  have h3 := (hasFDerivAt_pairGradient hdouble).comp a (hy.sub_const (-a))
  have hx := (h1.add_const (pairGradient ((0 : E) - -a))).add_const (K • (0 : E))
  have hz := ((h3.const_sub (-pairGradient ((0 : E) - -a))).sub_const
    ((5 / 4 : ℝ) • a)).add_const (K • (-a + a))
  convert! hx.prodMk hz using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [centerParameterDerivative, hvec, hessian_double_center a ha]
  module

lemma contDiffAt_stationaryEquation {n : WithTop ENat} (K : ℝ) (a : E)
    (p : E × (E × E)) (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2)
    (hyz : p.1 ≠ p.2.2) : ContDiffAt ℝ n (stationaryEquation K a) p := by
  have hy : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hx : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p := contDiffAt_snd.fst
  have hz : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p := contDiffAt_snd.snd
  have h1 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxy)).comp p (hx.sub hy)
  have h2 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxz)).comp p (hx.sub hz)
  have h3 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hyz)).comp p (hy.sub hz)
  exact ((h1.add h2).add (hx.const_smul K)).prodMk
    (((h2.neg.sub h3).sub contDiffAt_const).add ((hz.add contDiffAt_const).const_smul K))

lemma contDiffAt_stationaryEquation_center {n : WithTop ENat}
    (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    ContDiffAt ℝ n (stationaryEquation K a) (a, (0, -a)) := by
  have ha0 := center_nonzero ha
  apply contDiffAt_stationaryEquation
  · exact ha0.symm
  · exact (neg_ne_zero.mpr ha0).symm
  · intro h
    have hnorm : ‖a - -a‖ = 2 := by
      have hvec : a - -a = (2 : ℝ) • a := by module
      rw [hvec, norm_smul, ha]
      norm_num
    change a = -a at h
    rw [sub_eq_zero.mpr h, norm_zero] at hnorm
    norm_num at hnorm

/-- Total differential with the parameter block followed by the state block. -/
def centerTotalDerivative (K : ℝ) (Q : E →L[ℝ] E) :
    (E × (E × E)) →L[ℝ] (E × E) :=
  (centerParameterDerivative Q).comp (ContinuousLinearMap.fst ℝ E (E × E)) +
    (centerStateHessian K Q).comp (ContinuousLinearMap.snd ℝ E (E × E))

lemma hasFDerivAt_stationary_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (stationaryEquation K a)
      (centerTotalDerivative K (pairHessian a)) (a, (0, -a)) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hdouble : a - -a ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (by norm_num) ha0
  have hy : HasFDerivAt (fun p : E × (E × E) => p.1)
      (ContinuousLinearMap.fst ℝ E (E × E)) (a, (0, -a)) := hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : E × (E × E) => p.2)
      (ContinuousLinearMap.snd ℝ E (E × E)) (a, (0, -a)) := hasFDerivAt_snd
  have hx := hs.fst
  have hz := hs.snd
  have h1 := (hasFDerivAt_pairGradient (show (0 : E) - a ≠ 0 by simpa using hneg)).comp
    (a, (0, -a)) (hx.sub hy)
  have h2 := (hasFDerivAt_pairGradient (show (0 : E) - -a ≠ 0 by simpa using ha0)).comp
    (a, (0, -a)) (hx.sub hz)
  have h3 := (hasFDerivAt_pairGradient hdouble).comp (a, (0, -a)) (hy.sub hz)
  have hfirst := (h1.add h2).add (hx.const_smul K)
  have hsecond := ((h2.neg.sub h3).sub_const ((5 / 4 : ℝ) • a)).add
    ((hz.add_const a).const_smul K)
  convert! hfirst.prodMk hsecond using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [centerTotalDerivative, centerParameterDerivative, centerStateHessian,
    hvec, hessian_double_center a ha]
  constructor <;> module

end Problem356.GeometryJets

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped RealInnerProductSpace
open Matrix

namespace Problem356.CoulombCalculus

/-- Unit coordinate vector for either local Coulomb branch. -/
def axisVector (k : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single k 1

@[simp] theorem norm_axisVector (k : Fin 3) : ‖axisVector k‖ = 1 := by
  simp [axisVector]

@[simp] theorem inner_axisVector (k : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    ⟪axisVector k, v⟫ = v k := by
  simp [axisVector, EuclideanSpace.inner_single_left]

/-- The analytic Coulomb Hessian at a coordinate axis is precisely the diagonal
matrix used in the finite-dimensional local nondegeneracy calculation. -/
theorem pairHessian_axisVector (k : Fin 3) :
    pairHessian (axisVector k) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  ext v i
  rw [pairHessian_apply_of_norm_eq_one (norm_axisVector k), inner_axisVector]
  change (-v + (3 * v k) • axisVector k) i =
    (LocalHessian.pairHessian k *ᵥ WithLp.ofLp v) i
  simp only [LocalHessian.pairHessian, Matrix.mulVec_diagonal]
  by_cases hi : i = k
  · subst i
    simp [LocalHessian.eigenvalue, axisVector]
    ring
  · simp [LocalHessian.eigenvalue, axisVector, hi]

@[simp] theorem axisVector_ne_zero (k : Fin 3) : axisVector k ≠ 0 := by
  intro h
  have hn := norm_axisVector k
  rw [h, norm_zero] at hn
  norm_num at hn

theorem pairHessian_axisVector_apply (k : Fin 3) (v : EuclideanSpace ℝ (Fin 3))
    (i : Fin 3) :
    pairHessian (axisVector k) v i = LocalHessian.eigenvalue k i * v i := by
  rw [pairHessian_axisVector]
  change (LocalHessian.pairHessian k *ᵥ WithLp.ofLp v) i = _
  simp [LocalHessian.pairHessian, Matrix.mulVec_diagonal]

theorem pairHessian_neg_axisVector (k : Fin 3) :
    pairHessian (-axisVector k) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  rw [pairHessian_neg, pairHessian_axisVector]

theorem pairHessian_two_axisVector (k : Fin 3) :
    pairHessian ((2 : ℝ) • axisVector k) =
      (1 / 8 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  rw [pairHessian_smul_pos _ (by norm_num), pairHessian_axisVector]
  norm_num

theorem pairHessian_neg_two_axisVector (k : Fin 3) :
    pairHessian (-((2 : ℝ) • axisVector k)) =
      (1 / 8 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  rw [pairHessian_neg, pairHessian_two_axisVector]

end Problem356.CoulombCalculus

namespace Problem356.GeometryJets

open CoulombCalculus

/-- Identification of the center state derivative with the positive definite
operator verified by the explicit finite matrix calculation. -/
theorem centerStateHessian_axisVector (k : Fin 3) :
    centerStateHessian 20 (pairHessian (axisVector k)) = LocalHessian.stateOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    change ((2 : ℝ) • pairHessian (axisVector k) v.1 + (20 : ℝ) • v.1 -
      pairHessian (axisVector k) v.2) i = (LocalHessian.stateOperator k v).1 i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      pairHessian_axisVector_apply, LocalHessian.stateOperator_fst_apply]
    ring
  · ext i
    change (-pairHessian (axisVector k) v.1 +
      ((9 / 8 : ℝ) • pairHessian (axisVector k) v.2 + (20 : ℝ) • v.2)) i =
      (LocalHessian.stateOperator k v).2 i
    simp only [PiLp.neg_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      pairHessian_axisVector_apply, LocalHessian.stateOperator_snd_apply]
    ring

theorem centerParameterDerivative_axisVector (k : Fin 3) :
    centerParameterDerivative (pairHessian (axisVector k)) =
      LocalHessian.parameterOperator k := by
  rw [pairHessian_axisVector]
  unfold centerParameterDerivative LocalHessian.parameterOperator
  congr 2
  norm_num

/-- State partial derivative of the actual stationary field at an axis center. -/
theorem fderiv_stationary_axis_state (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
      (axisVector k, (0, -axisVector k)) ∘L
        ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =
      LocalHessian.stateOperator k := by
  rw [(hasFDerivAt_stationary_center 20 _ (norm_axisVector k)).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change centerParameterDerivative (pairHessian (axisVector k)) 0 +
    centerStateHessian 20 (pairHessian (axisVector k)) v = _
  simp [centerStateHessian_axisVector]

/-- Parameter partial derivative of the actual stationary field at an axis center. -/
theorem fderiv_stationary_axis_parameter (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
      (axisVector k, (0, -axisVector k)) ∘L
        ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =
      LocalHessian.parameterOperator k := by
  rw [(hasFDerivAt_stationary_center 20 _ (norm_axisVector k)).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change centerParameterDerivative (pairHessian (axisVector k)) v +
    centerStateHessian 20 (pairHessian (axisVector k)) 0 = _
  simp [centerParameterDerivative_axisVector]

end Problem356.GeometryJets

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem356.CoulombCharts

open CoulombCalculus GeometryJets LocalImplicit

/-- The computed state derivative is the coercive, invertible operator certified
by the finite-dimensional algebra, in the actual product-space coordinates. -/
theorem centerStateHessian_axis_eq (k : Fin 3) :
    centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) =
      LocalHessian.stateOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    simp [centerStateHessian, LocalHessian.stateOperator_fst_apply,
      pairHessian_axisVector_apply]
    ring
  · ext i
    simp [centerStateHessian, LocalHessian.stateOperator_snd_apply,
      pairHessian_axisVector_apply]
    ring

/-- The computed parameter derivative agrees with the mixed Hessian block. -/
theorem centerParameterDerivative_axis_eq (k : Fin 3) :
    centerParameterDerivative (CoulombCalculus.pairHessian (axisVector k)) =
      LocalHessian.parameterOperator k := by
  rw [pairHessian_axisVector]
  unfold centerParameterDerivative LocalHessian.parameterOperator
  dsimp
  congr 1
  module

theorem stationary_state_partial_eq (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) = LocalHessian.stateOperator k := by
  rw [(hasFDerivAt_stationary_center 20 (axisVector k) (norm_axisVector k)).fderiv]
  have h : centerTotalDerivative 20 (CoulombCalculus.pairHessian (axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) =
      centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [centerTotalDerivative]
  rw [h, centerStateHessian_axis_eq]

/-- Identification of the actual partial parameter derivative. -/
theorem stationary_parameter_partial_eq (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k)) ∘L
      ContinuousLinearMap.inl ℝ E3 (E3 × E3) = LocalHessian.parameterOperator k := by
  rw [(hasFDerivAt_stationary_center 20 (axisVector k) (norm_axisVector k)).fderiv]
  have h : centerTotalDerivative 20 (CoulombCalculus.pairHessian (axisVector k)) ∘L
      ContinuousLinearMap.inl ℝ E3 (E3 × E3) =
      centerParameterDerivative (CoulombCalculus.pairHessian (axisVector k)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [centerTotalDerivative]
  rw [h, centerParameterDerivative_axis_eq]

/-- Nonlinear local Coulomb branches exist at every coordinate-axis reference triple.
Both branch coordinates are analytic local diffeomorphisms on one common source. -/
theorem nonempty_coulombCharts (k : Fin 3) :
    Nonempty (AnalyticStationaryCharts
      (stationaryEquation 20 (axisVector k)) (axisVector k) (0, -axisVector k)) := by
  apply nonempty_analyticStationaryCharts
  · exact contDiffAt_stationaryEquation_center 20 (axisVector k) (norm_axisVector k)
  · exact stationaryEquation_center 20 (axisVector k) (norm_axisVector k)
  · rw [stationary_state_partial_eq]
    exact LocalHessian.stateOperator_isInvertible k
  · unfold implicitDerivative
    rw [stationary_state_partial_eq, stationary_parameter_partial_eq]
    exact LocalHessian.central_inverse_block_isInvertible k
  · unfold implicitDerivative
    rw [stationary_state_partial_eq, stationary_parameter_partial_eq]
    exact LocalHessian.opposite_inverse_block_isInvertible k

end Problem356.CoulombCharts

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A uniform lower Hessian bound away from a Coulomb collision. -/
theorem pairHessian_quadratic_lower_of_two_thirds {a : E}
    (ha : (2 : ℝ) / 3 ≤ ‖a‖) (u : E) :
    -(27 / 8 : ℝ) * ‖u‖ ^ 2 ≤ ⟪u, pairHessian a u⟫ := by
  have hn : 0 < ‖a‖ := lt_of_lt_of_le (by norm_num) ha
  have hp : ((2 : ℝ) / 3) ^ 3 ≤ ‖a‖ ^ 3 :=
    pow_le_pow_left₀ (by norm_num) ha 3
  have hi : (‖a‖ ^ 3)⁻¹ ≤ (27 / 8 : ℝ) := by
    have hh := (inv_le_inv₀ (pow_pos hn 3) (by norm_num : 0 < ((2 : ℝ) / 3) ^ 3)).2 hp
    norm_num at hh ⊢
    exact hh
  have hm := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖u‖)
  have hl := pairHessian_quadratic_lower a u
  rw [real_inner_comm] at hl
  linarith

/-- The explicit K=20 regularization dominates every negative Coulomb Hessian
contribution on a domain where all three pair distances are at least 2/3. -/
theorem regularized_hessian_coercive_of_separated
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖) (u v : E) :
    (79 / 8 : ℝ) * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤
      20 * (‖u‖ ^ 2 + ‖v‖ ^ 2) +
        ⟪u, pairHessian a u⟫ +
        ⟪u - v, pairHessian b (u - v)⟫ +
        ⟪v, pairHessian c v⟫ := by
  have h₁ := pairHessian_quadratic_lower_of_two_thirds ha u
  have h₂ := pairHessian_quadratic_lower_of_two_thirds hb (u - v)
  have h₃ := pairHessian_quadratic_lower_of_two_thirds hc v
  have hnorm : ‖u - v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have hsq := pow_le_pow_left₀ (norm_nonneg (u - v)) (norm_sub_le u v) 2
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  linarith

/-- Strict positivity for every nonzero state direction. -/
theorem regularized_hessian_pos_of_separated
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖)
    {u v : E} (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < 20 * (‖u‖ ^ 2 + ‖v‖ ^ 2) +
        ⟪u, pairHessian a u⟫ +
        ⟪u - v, pairHessian b (u - v)⟫ +
        ⟪v, pairHessian c v⟫ := by
  have hsum : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rcases huv with hu | hv
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hu)) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hv))
  exact lt_of_lt_of_le (mul_pos (by norm_num) hsum)
    (regularized_hessian_coercive_of_separated ha hb hc u v)

/-- The regularized state-Jacobian, written in component form suitable for the
parameter/state stationarity equation. -/
def regularizedStateHessian (a b c : E) : (E × E) →L[ℝ] E × E :=
  (((pairHessian a).comp (ContinuousLinearMap.fst ℝ E E) +
      (pairHessian b).comp
        (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)) +
      (20 : ℝ) • ContinuousLinearMap.fst ℝ E E).prod
    ((-((pairHessian b).comp
        (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)) +
      (pairHessian c).comp (ContinuousLinearMap.snd ℝ E E)) +
      (20 : ℝ) • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem regularizedStateHessian_apply (a b c u v : E) :
    regularizedStateHessian a b c (u, v) =
      (pairHessian a u + pairHessian b (u - v) + (20 : ℝ) • u,
        -(pairHessian b (u - v)) + pairHessian c v + (20 : ℝ) • v) := rfl

/-- Expansion of the product-state quadratic form. -/
theorem regularizedStateHessian_quadratic (a b c : E) (q : E × E) :
    ⟪q.1, (regularizedStateHessian a b c q).1⟫ +
        ⟪q.2, (regularizedStateHessian a b c q).2⟫ =
      20 * (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) +
        ⟪q.1, pairHessian a q.1⟫ +
        ⟪q.1 - q.2, pairHessian b (q.1 - q.2)⟫ +
        ⟪q.2, pairHessian c q.2⟫ := by
  rcases q with ⟨u, v⟩
  simp only [regularizedStateHessian_apply, inner_add_right, inner_neg_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, inner_sub_left]
  ring

/-- Quantitative coercivity of the state-Jacobian in the actual max product norm. -/
theorem regularizedStateHessian_coercive
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖) (q : E × E) :
    (79 / 8 : ℝ) * ‖q‖ ^ 2 ≤
      ⟪q.1, (regularizedStateHessian a b c q).1⟫ +
        ⟪q.2, (regularizedStateHessian a b c q).2⟫ := by
  rw [regularizedStateHessian_quadratic]
  have hnorm : ‖q‖ ^ 2 ≤ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖q.1‖ ‖q.2‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (sq_nonneg _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hnorm (by norm_num)).trans
    (regularized_hessian_coercive_of_separated ha hb hc q.1 q.2)

/-- Strict positivity in every nonzero direction. -/
theorem regularizedStateHessian_pos
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖)
    {q : E × E} (hq : q ≠ 0) :
    0 < ⟪q.1, (regularizedStateHessian a b c q).1⟫ +
        ⟪q.2, (regularizedStateHessian a b c q).2⟫ :=
  lt_of_lt_of_le (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hq)))
    (regularizedStateHessian_coercive ha hb hc q)

/-- The explicit Jacobian of the regularized Coulomb stationarity equation.
The constant vector in the second component accommodates the chosen outer
potential and has no effect on the Hessian. -/
theorem hasFDerivAt_regularizedStateGradient (y k : E) {s : E × E}
    (hxy : s.1 - y ≠ 0) (hxz : s.1 - s.2 ≠ 0) (hzy : s.2 - y ≠ 0) :
    HasFDerivAt
      (fun p : E × E =>
        (pairGradient (p.1 - y) + pairGradient (p.1 - p.2) + (20 : ℝ) • p.1,
          -pairGradient (p.1 - p.2) + pairGradient (p.2 - y) +
            (20 : ℝ) • p.2 + k))
      (regularizedStateHessian (s.1 - y) (s.1 - s.2) (s.2 - y)) s := by
  have hx : HasFDerivAt (fun p : E × E => p.1) (ContinuousLinearMap.fst ℝ E E) s :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hz : HasFDerivAt (fun p : E × E => p.2) (ContinuousLinearMap.snd ℝ E E) s :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have h₁ := (hasFDerivAt_pairGradient hxy).comp s (hx.sub_const y)
  have h₂ := (hasFDerivAt_pairGradient hxz).comp s (hx.sub hz)
  have h₃ := (hasFDerivAt_pairGradient hzy).comp s (hz.sub_const y)
  exact ((h₁.add h₂).add (hx.const_smul (20 : ℝ))).prodMk
    (((h₂.neg.add h₃).add (hz.const_smul (20 : ℝ))).add_const k)

end Problem356.CoulombCalculus

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set Filter
open scoped Topology

namespace Problem356

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A stationary point of a convex differentiable function is a global minimizer
on its convexity domain. -/
theorem convex_isMinOn_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := by
  intro y hy
  have hline := hf.comp_affineMap (AffineMap.lineMap x y)
  have hderiv : HasDerivAt (f ∘ AffineMap.lineMap x y) 0 (0 : ℝ) := by
    have hd' : HasFDerivAt f (0 : E →L[ℝ] ℝ) ((AffineMap.lineMap x y) (0 : ℝ)) := by
      simpa using hd
    have h := hd'.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap : HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ))
    simpa using h
  have hle := hline.le_slope_of_hasDerivAt
    (by simpa using hx) (by simpa using hy) (by norm_num : (0 : ℝ) < 1) hderiv
  simpa [slope_def_field] using hle

/-- Strict convexity upgrades a stationary point to the unique minimum. -/
theorem strictConvex_eq_iff_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : StrictConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) {y : E} (hy : y ∈ s) :
    f y = f x ↔ y = x := by
  have hmin := convex_isMinOn_of_hasFDerivAt_zero hf.convexOn hx hd
  constructor
  · intro heq
    have hymin : IsMinOn f s y := by
      intro z hz
      change f y ≤ f z
      rw [heq]
      exact hmin hz
    exact hf.eq_of_isMinOn hymin hmin hy hx
  · rintro rfl
    rfl

/-- Strict positivity of second derivatives on nonconstant line segments implies
strict convexity in an arbitrary real normed space. -/
theorem strictConvexOn_of_line_deriv2_pos {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < deriv (deriv (f ∘ AffineMap.lineMap x y)) t) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := by
    intro t ht
    rw [AffineMap.lineMap_apply_module]
    exact hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcont : ContinuousOn (f ∘ AffineMap.lineMap x y) (Icc (0 : ℝ) 1) :=
    hf.comp (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E).differentiable.continuous.continuousOn hmaps
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (f ∘ AffineMap.lineMap x y) := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) hcont
    intro t ht
    exact hpos x hx y hy hxy t (by simpa using ht)
  have hh := hstrict.2 (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1)
    ha hb hab
  have ha1 : 1 - b = a := by linarith
  simpa [AffineMap.lineMap_apply_module, ha1] using hh

/-- A positive-definite second Fréchet derivative gives strict convexity on an
open convex domain. The two derivative fields are explicit, so this applies
directly to computed Hessians without rewriting `fderiv`. -/
theorem strictConvexOn_of_positive_hessian {s : Set E} {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hs : Convex ℝ s) (hsopen : IsOpen s)
    (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z)
    (hf' : ∀ z ∈ s, HasFDerivAt f' (f'' z) z)
    (hpos : ∀ z ∈ s, ∀ v : E, v ≠ 0 → 0 < f'' z v v) :
    StrictConvexOn ℝ s f := by
  apply strictConvexOn_of_line_deriv2_pos hs
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
  intro x hx y hy hxy t ht
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := by
    intro u hu
    rw [AffineMap.lineMap_apply_module]
    exact hs hx hy (sub_nonneg.mpr hu.2) hu.1 (by ring)
  have hz : AffineMap.lineMap x y t ∈ s := hmaps ⟨ht.1.le, ht.2.le⟩
  have hnear : ∀ᶠ u in 𝓝 t, AffineMap.lineMap x y u ∈ s :=
    AffineMap.lineMap_continuous.continuousAt.eventually_mem (hsopen.mem_nhds hz)
  have hfirst : deriv (f ∘ AffineMap.lineMap x y) =ᶠ[𝓝 t]
      (fun u => f' (AffineMap.lineMap x y u) (y - x)) := by
    filter_upwards [hnear] with u hu
    exact ((hf _ hu).comp_hasDerivAt u AffineMap.hasDerivAt_lineMap).deriv
  have hsecond : HasDerivAt (fun u : ℝ => f' (AffineMap.lineMap x y u) (y - x))
      (f'' (AffineMap.lineMap x y t) (y - x) (y - x)) t := by
    have hcomp := (hf' _ hz).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
    simpa using hcomp.clm_apply (hasDerivAt_const t (y - x))
  rw [hfirst.deriv_eq, hsecond.deriv]
  exact hpos _ hz (y - x) (sub_ne_zero.mpr hxy.symm)

/-- A smooth stationary branch in strictly convex state slices defines a smooth
supporting value, and its graph is exactly the contact set. -/
theorem stationary_family_certificate
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {V : Set E} {n : WithTop ENat}
    {F : P × E → ℝ} {ψ : P → E}
    (hF : ContDiffOn ℝ n F (U ×ˢ V)) (hψ : ContDiffOn ℝ n ψ U)
    (hψV : MapsTo ψ U V)
    (hconv : ∀ p ∈ U, StrictConvexOn ℝ V (fun z => F (p, z)))
    (hstat : ∀ p ∈ U, HasFDerivAt (fun z => F (p, z))
      (0 : E →L[ℝ] ℝ) (ψ p)) :
    ContDiffOn ℝ n (fun p => F (p, ψ p)) U ∧
      ∀ p ∈ U, ∀ z ∈ V,
        F (p, ψ p) ≤ F (p, z) ∧ (F (p, z) = F (p, ψ p) ↔ z = ψ p) := by
  constructor
  · exact hF.comp (contDiffOn_id.prodMk hψ) (fun p hp => ⟨hp, hψV hp⟩)
  · intro p hp z hz
    exact ⟨convex_isMinOn_of_hasFDerivAt_zero (hconv p hp).convexOn
      (hψV hp) (hstat p hp) hz,
      strictConvex_eq_iff_of_hasFDerivAt_zero (hconv p hp) (hψV hp) (hstat p hp) hz⟩

/-- Version of `stationary_family_certificate` using explicit positive Hessians.
This is the analytic supporting-certificate step of the local construction. -/
theorem stationary_family_certificate_of_positive_hessian
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {V : Set E} {n : WithTop ENat}
    {F : P × E → ℝ} {ψ : P → E}
    {D : P → E → E →L[ℝ] ℝ} {H : P → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hF : ContDiffOn ℝ n F (U ×ˢ V)) (hψ : ContDiffOn ℝ n ψ U)
    (hψV : MapsTo ψ U V) (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hD : ∀ p ∈ U, ∀ z ∈ V, HasFDerivAt (fun z => F (p, z)) (D p z) z)
    (hH : ∀ p ∈ U, ∀ z ∈ V, HasFDerivAt (D p) (H p z) z)
    (hpos : ∀ p ∈ U, ∀ z ∈ V, ∀ v : E, v ≠ 0 → 0 < H p z v v)
    (hstat : ∀ p ∈ U, D p (ψ p) = 0) :
    ContDiffOn ℝ n (fun p => F (p, ψ p)) U ∧
      ∀ p ∈ U, ∀ z ∈ V,
        F (p, ψ p) ≤ F (p, z) ∧ (F (p, z) = F (p, ψ p) ↔ z = ψ p) := by
  apply stationary_family_certificate hF hψ hψV
  · intro p hp
    exact strictConvexOn_of_positive_hessian hV hVopen (hD p hp) (hH p hp) (hpos p hp)
  · intro p hp
    simpa [hstat p hp] using hD p hp (ψ p) (hψV hp)

end Problem356

end

end OAI
end
end

section
section
namespace OAI


open Filter
open scoped Topology

namespace Problem356

/-- A quantitative lower bound on a bilinear form survives a small operator-norm
perturbation. No finite-dimensional hypothesis is needed. -/
theorem bilinear_coercive_of_norm_sub_le
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (a δ : ℝ)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) (hclose : ‖C - B‖ ≤ δ) :
    ∀ v, (a - δ) * ‖v‖ ^ 2 ≤ C v v := by
  intro v
  have hv := (C - B).le_opNorm₂ v v
  have hmul : ‖C - B‖ * ‖v‖ * ‖v‖ ≤ δ * ‖v‖ ^ 2 := by
    calc
      ‖C - B‖ * ‖v‖ * ‖v‖ = ‖C - B‖ * ‖v‖ ^ 2 := by ring
      _ ≤ δ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hclose (sq_nonneg _)
  have hdiff : |C v v - B v v| ≤ δ * ‖v‖ ^ 2 := by
    simpa only [sub_apply, Real.norm_eq_abs] using hv.trans hmul
  have hlo := (abs_le.mp hdiff).1
  have hb := hB v
  nlinarith

/-- A continuous family of coercive bilinear forms remains uniformly coercive
near the base point, with half the original lower-bound constant. -/
theorem eventually_bilinear_coercive
    {X : Type uX} {E : Type uE} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X) (a : ℝ)
    (ha : 0 < a) (hcont : ContinuousAt B x₀)
    (hbase : ∀ v, a * ‖v‖ ^ 2 ≤ B x₀ v v) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, (a / 2) * ‖v‖ ^ 2 ≤ B x v v := by
  have hnear : ∀ᶠ x in 𝓝 x₀, dist (B x) (B x₀) < a / 2 :=
    (Metric.tendsto_nhds.mp hcont.tendsto) (a / 2) (half_pos ha)
  filter_upwards [hnear] with x hx
  have h := bilinear_coercive_of_norm_sub_le (B x₀) (B x) a (a / 2) hbase
    (by rw [← dist_eq_norm (B x) (B x₀)]; exact hx.le)
  have haeq : a - a / 2 = a / 2 := by ring
  simpa only [haeq] using h

/-- In finite dimension, strict positivity of a continuous bilinear form gives
one uniform positive quadratic lower bound. -/
theorem exists_bilinear_coercivity_of_pos
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ a : ℝ, 0 < a ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  | inr h =>
    have := h
    obtain ⟨u, hu⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
    have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨u, by simpa using hu⟩
    have hcont : Continuous (fun v => B v v) := B.continuous.clm_apply continuous_id
    obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
      hcont.continuousOn
    have hwNorm : ‖w‖ = 1 := by simpa using hw
    have hwne : w ≠ 0 := by intro hw0; simp [hw0] at hwNorm
    refine ⟨B w w, hpos w hwne, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hynorm : ‖(‖v‖)⁻¹ • v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
    have hy : (‖v‖)⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by simpa using hynorm
    have hmin : B w w ≤ B ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) := hwmin hy
    have hscale : B ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) * ‖v‖ ^ 2 = B v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      field_simp
    have hmul := mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖v‖)
    rwa [hscale] at hmul

/-- Positive definiteness is an open condition for continuous bilinear families
on finite-dimensional real normed spaces. -/
theorem eventually_bilinear_pos
    {X : Type uX} {E : Type uE} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X)
    (hcont : ContinuousAt B x₀) (hpos : ∀ v, v ≠ 0 → 0 < B x₀ v v) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, v ≠ 0 → 0 < B x v v := by
  obtain ⟨a, ha, hbase⟩ := exists_bilinear_coercivity_of_pos (B x₀) hpos
  filter_upwards [eventually_bilinear_coercive B x₀ a ha hcont hbase] with x hx
  intro v hv
  exact lt_of_lt_of_le (mul_pos (half_pos ha) (sq_pos_of_pos (norm_pos_iff.mpr hv))) (hx v)

/-- Metric-ball version of openness of positive definiteness. -/
theorem exists_ball_bilinear_pos
    {X : Type uX} {E : Type uE} [PseudoMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X)
    (hcont : ContinuousAt B x₀) (hpos : ∀ v, v ≠ 0 → 0 < B x₀ v v) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball x₀ r, ∀ v, v ≠ 0 → 0 < B x v v := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (eventually_bilinear_pos B x₀ hcont hpos)
  exact ⟨r, hr, fun x hx => hball hx⟩

/-- A positive-definite Hessian at a point stays positive definite on a ball
when the function is twice continuously differentiable there. -/
theorem exists_ball_hessian_pos
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (x₀ : E) (hf : ContDiffAt ℝ 2 f x₀)
    (hpos : ∀ v, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x₀ v v) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball x₀ r, ∀ v, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ f) x v v := by
  have hfirst : ContDiffAt ℝ 1 (fderiv ℝ f) x₀ := hf.fderiv_right (by norm_num)
  exact exists_ball_bilinear_pos (fderiv ℝ (fderiv ℝ f)) x₀
    (hfirst.continuousAt_fderiv (by norm_num)) hpos

end Problem356

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Problem356.LocalGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local exact supporting certificate, with the stationary branches retained
as analytic local diffeomorphisms and both domains shrunk to metric balls. -/
structure LocalSupportingCharts (F : E × (E × E) → ℝ)
    (G : E × (E × E) → E × E) (p : E) (s : E × E) where
  charts : LocalImplicit.AnalyticStationaryCharts G p s
  parameterRadius : ℝ
  parameterRadius_pos : 0 < parameterRadius
  source_ball : charts.central.source = Metric.ball p parameterRadius
  stateRadius : ℝ
  stateRadius_pos : 0 < stateRadius
  state_ball : charts.stateDomain = Metric.ball s stateRadius
  value : E → ℝ
  value_analytic : ContDiffOn ℝ ω value charts.central.source
  value_eq : ∀ y, value y = F (y, (charts.central y, charts.opposite y))
  value_base : value p = F (p, s)
  supporting : ∀ y ∈ charts.central.source, ∀ z ∈ charts.stateDomain,
    value y ≤ F (y, z)
  contact : ∀ y ∈ charts.central.source, ∀ z ∈ charts.stateDomain,
    F (y, z) = value y ↔ z = (charts.central y, charts.opposite y)

/-- Positive Hessian at the base point, together with separate local branch
invertibility, yields the full neighborhood-level supporting certificate. -/
theorem nonempty_localSupportingCharts [CompleteSpace E] [FiniteDimensional ℝ E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E}
    {D : E → (E × E) → (E × E) →L[ℝ] ℝ}
    {H : E → (E × E) → (E × E) →L[ℝ] ((E × E) →L[ℝ] ℝ)}
    {p : E} {s : E × E}
    (C : LocalImplicit.AnalyticStationaryCharts G p s)
    (hF : ContDiffAt ℝ ω F (p, s))
    (hD : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (fun z => F (q.1, z)) (D q.1 q.2) q.2)
    (hH : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (D q.1) (H q.1 q.2) q.2)
    (hHcont : ContinuousAt (fun q : E × (E × E) => H q.1 q.2) (p, s))
    (hHpos : ∀ v : E × E, v ≠ 0 → 0 < H p s v v)
    (hcompatible : ∀ q : E × (E × E), G q = 0 → D q.1 q.2 = 0) :
    Nonempty (LocalSupportingCharts F G p s) := by
  let ψ : E → E × E := fun y => (C.central y, C.opposite y)
  have hψsmooth : ContDiffOn ℝ ω ψ C.central.source :=
    C.central_analytic.prodMk (C.source_eq ▸ C.opposite_analytic)
  have hψbase : ψ p = s := by simp [ψ, C.central_value, C.opposite_value]
  have hHnear := eventually_bilinear_pos (fun q : E × (E × E) => H q.1 q.2)
    (p, s) hHcont hHpos
  have hgood : ∀ᶠ q in 𝓝 (p, s), ContDiffAt ℝ ω F q ∧
      HasFDerivAt (fun z => F (q.1, z)) (D q.1 q.2) q.2 ∧
      HasFDerivAt (D q.1) (H q.1 q.2) q.2 ∧
      ∀ v : E × E, v ≠ 0 → 0 < H q.1 q.2 v v := by
    filter_upwards [hF.eventually (by simp), hD, hH, hHnear] with q h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hgood
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hB (C.stateDomain_open.mem_nhds C.state_mem))
  have hψcont : ContinuousAt ψ p :=
    (hψsmooth.contDiffAt (C.central.open_source.mem_nhds C.point_mem)).continuousAt
  have hψball : ∀ᶠ y in 𝓝 p, ψ y ∈ Metric.ball s r := by
    apply hψcont.preimage_mem_nhds
    rw [hψbase]
    exact Metric.ball_mem_nhds s hr
  have hUgood : ∀ᶠ y in 𝓝 p,
      y ∈ C.central.source ∧ y ∈ A ∧ ψ y ∈ Metric.ball s r := by
    filter_upwards [C.central.open_source.mem_nhds C.point_mem, hA, hψball]
      with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨t, ht, htU⟩ := Metric.mem_nhds_iff.mp hUgood
  let U := Metric.ball p t
  have hUcentral : U ⊆ C.central.source := fun _ hy => (htU hy).1
  have hUopposite : U ⊆ C.opposite.source := C.source_eq ▸ hUcentral
  let X := C.central.restrOpen U Metric.isOpen_ball
  let Z := C.opposite.restrOpen U Metric.isOpen_ball
  have hXsource : X.source = U := inter_eq_right.mpr hUcentral
  have hZsource : Z.source = U := inter_eq_right.mpr hUopposite
  have hpair : (fun y => (X y, Z y)) = ψ := rfl
  have hproperties : ∀ y ∈ U, ∀ z ∈ Metric.ball s r,
      ContDiffAt ℝ ω F (y, z) ∧
      HasFDerivAt (fun z => F (y, z)) (D y z) z ∧
      HasFDerivAt (D y) (H y z) z ∧
      ∀ v : E × E, v ≠ 0 → 0 < H y z v v := by
    intro y hy z hz
    exact hAB ⟨(htU hy).2.1, (hrB hz).1⟩
  have hψU : ContDiffOn ℝ ω ψ U := hψsmooth.mono hUcentral
  have hψUmap : MapsTo ψ U (Metric.ball s r) := fun _ hy => (htU hy).2.2
  have hstatU : ∀ y ∈ U, D y (ψ y) = 0 := by
    intro y hy
    exact hcompatible (y, ψ y) (C.stationary y (hUcentral hy))
  have hcert := stationary_family_certificate_of_positive_hessian
    (fun q hq => (hproperties q.1 hq.1 q.2 hq.2).1.contDiffWithinAt)
    hψU hψUmap (convex_ball s r) Metric.isOpen_ball
    (fun y hy z hz => (hproperties y hy z hz).2.1)
    (fun y hy z hz => (hproperties y hy z hz).2.2.1)
    (fun y hy z hz => (hproperties y hy z hz).2.2.2) hstatU
  let C' : LocalImplicit.AnalyticStationaryCharts G p s := {
    central := X
    opposite := Z
    source_eq := hXsource.trans hZsource.symm
    point_mem := by rw [hXsource]; exact Metric.mem_ball_self ht
    central_value := C.central_value
    opposite_value := C.opposite_value
    stateDomain := Metric.ball s r
    stateDomain_open := Metric.isOpen_ball
    state_mem := Metric.mem_ball_self hr
    mapsTo_state := by rw [hpair, hXsource]; exact hψUmap
    stationary := fun y hy => C.stationary y hy.1
    unique_zero := fun y hy z hz => C.unique_zero y hy.1 z (hrB hz).2
    central_analytic := C.central_analytic.mono (fun _ hy => hy.1)
    central_inverse_analytic := C.central_inverse_analytic.mono (fun _ hy => hy.1)
    opposite_analytic := C.opposite_analytic.mono (fun _ hy => hy.1)
    opposite_inverse_analytic := C.opposite_inverse_analytic.mono (fun _ hy => hy.1) }
  refine ⟨{
    charts := C'
    parameterRadius := t
    parameterRadius_pos := ht
    source_ball := hXsource
    stateRadius := r
    stateRadius_pos := hr
    state_ball := rfl
    value := fun y => F (y, ψ y)
    value_analytic := ?_
    value_eq := fun _ => rfl
    value_base := by rw [hψbase]
    supporting := ?_
    contact := ?_ }⟩
  · change ContDiffOn ℝ ω (fun y => F (y, ψ y)) X.source
    rw [hXsource]
    exact hcert.1
  · intro y hy z hz
    exact (hcert.2 y (hXsource ▸ hy) z hz).1
  · intro y hy z hz
    exact (hcert.2 y (hXsource ▸ hy) z hz).2

/-- A local certificate survives arbitrary further neighborhood restrictions.
First shrink the state ball, and only then shrink the parameter ball so that
both branches still land in the new state ball. The functions and value are
unchanged, so previously established center values are preserved. -/
theorem LocalSupportingCharts.exists_shrink [CompleteSpace E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E} {p : E} {s : E × E}
    (C : LocalSupportingCharts F G p s) (rp rs : ℝ) (hp : 0 < rp) (hs : 0 < rs) :
    ∃ D : LocalSupportingCharts F G p s,
      D.charts.central.source ⊆ C.charts.central.source ∩ Metric.ball p rp ∧
      D.charts.stateDomain ⊆ C.charts.stateDomain ∩ Metric.ball s rs ∧
      (D.charts.central : E → E) = C.charts.central ∧
      (D.charts.opposite : E → E) = C.charts.opposite ∧ D.value = C.value := by
  let r := min C.stateRadius rs
  have hr : 0 < r := lt_min C.stateRadius_pos hs
  have hball : Metric.ball s r ⊆ C.charts.stateDomain := by
    rw [C.state_ball]
    exact Metric.ball_subset_ball (min_le_left _ _)
  obtain ⟨d, hdstate, hdsource, hdX, hdZ⟩ := C.charts.exists_restrict_state
    (Metric.ball s r) Metric.isOpen_ball (Metric.mem_ball_self hr) hball
  have hU : d.central.source ∩ Metric.ball p rp ∈ 𝓝 p :=
    inter_mem (d.central.open_source.mem_nhds d.point_mem) (Metric.ball_mem_nhds p hp)
  obtain ⟨t, ht, e, hesource, heU, hestate, heX, heZ⟩ :=
    d.exists_restrict_ball (d.central.source ∩ Metric.ball p rp) hU
  have hsource : e.central.source ⊆ C.charts.central.source :=
    fun _ hy => hdsource (heU hy).1
  have hstate : e.stateDomain ⊆ C.charts.stateDomain := by
    rw [hestate, hdstate]
    exact hball
  have hsameX : (e.central : E → E) = C.charts.central := heX.trans hdX
  have hsameZ : (e.opposite : E → E) = C.charts.opposite := heZ.trans hdZ
  let D : LocalSupportingCharts F G p s := {
    charts := e
    parameterRadius := t
    parameterRadius_pos := ht
    source_ball := hesource
    stateRadius := r
    stateRadius_pos := hr
    state_ball := hestate.trans hdstate
    value := C.value
    value_analytic := C.value_analytic.mono hsource
    value_eq := by
      intro y
      rw [hsameX, hsameZ]
      exact C.value_eq y
    value_base := C.value_base
    supporting := fun y hy z hz => C.supporting y (hsource hy) z (hstate hz)
    contact := by
      intro y hy z hz
      rw [hsameX, hsameZ]
      exact C.contact y (hsource hy) z (hstate hz) }
  refine ⟨D, ?_, ?_, hsameX, hsameZ, rfl⟩
  · exact fun _ hy => ⟨hsource hy, (heU hy).2⟩
  · intro z hz
    refine ⟨hstate hz, ?_⟩
    change z ∈ e.stateDomain at hz
    rw [hestate, hdstate] at hz
    exact Metric.ball_subset_ball (min_le_right _ _) hz

end Problem356.LocalGeometry

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.StationaryMap

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The state potential with the explicit common central quadratic, K = 20. -/
def statePotential (a y : E) (s : E × E) : ℝ :=
  pairCost (s.1 - y) + pairCost (s.1 - s.2) + pairCost (s.2 - y) -
    ((5 : ℝ) / 2 - 10 * ‖s.1‖ ^ 2) -
    ((5 : ℝ) / 4 * ⟪a, s.2 + a⟫ - 10 * ‖s.2 + a‖ ^ 2)

/-- The concrete stationary equation, with parameter first and state second. -/
def stationary (a : E) (p : E × (E × E)) : E × E :=
  (pairGradient (p.2.1 - p.1) + pairGradient (p.2.1 - p.2.2) + (20 : ℝ) • p.2.1,
   pairGradient (p.2.2 - p.2.1) + pairGradient (p.2.2 - p.1) -
     (5 / 4 : ℝ) • a + (20 : ℝ) • (p.2.2 + a))

/-- Analyticity of the actual stationary equation on pairwise-distinct triples. -/
theorem contDiffAt_stationary (a : E) {p : E × (E × E)}
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hzy : p.2.2 ≠ p.1)
    {n : WithTop ENat} : ContDiffAt ℝ n (stationary a) p := by
  have hY : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hX : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p :=
    contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p :=
    contDiffAt_snd.snd
  have hXY := (contDiffAt_pairGradient (sub_ne_zero.mpr hxy)).comp p (hX.sub hY)
  have hXZ := (contDiffAt_pairGradient (sub_ne_zero.mpr hxz)).comp p (hX.sub hZ)
  have hZX := (contDiffAt_pairGradient (sub_ne_zero.mpr hxz.symm)).comp p (hZ.sub hX)
  have hZY := (contDiffAt_pairGradient (sub_ne_zero.mpr hzy)).comp p (hZ.sub hY)
  exact ((hXY.add hXZ).add (hX.const_smul (20 : ℝ))).prodMk
    (((hZX.add hZY).sub contDiffAt_const).add ((hZ.add contDiffAt_const).const_smul (20 : ℝ)))

/-- Analyticity of the state potential away from all collisions. -/
theorem contDiffAt_statePotential (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y)
    {n : WithTop ENat} : ContDiffAt ℝ n (statePotential a y) s := by
  have hX : ContDiffAt ℝ n (fun q : E × E => q.1) s := contDiffAt_fst
  have hZ : ContDiffAt ℝ n (fun q : E × E => q.2) s := contDiffAt_snd
  have hXY := (contDiffAt_pairCost (sub_ne_zero.mpr hxy)).comp s
    (hX.sub contDiffAt_const)
  have hXZ := (contDiffAt_pairCost (sub_ne_zero.mpr hxz)).comp s (hX.sub hZ)
  have hZY := (contDiffAt_pairCost (sub_ne_zero.mpr hzy)).comp s
    (hZ.sub contDiffAt_const)
  exact (((hXY.add hXZ).add hZY).sub
    (contDiffAt_const.sub (contDiffAt_const.mul (hX.norm_sq ℝ)))).sub
    ((contDiffAt_const.mul (contDiffAt_const.inner ℝ (hZ.add contDiffAt_const))).sub
      (contDiffAt_const.mul ((hZ.add contDiffAt_const).norm_sq ℝ)))

/-- The scalar potential with parameter and state bundled together. -/
def jointPotential (a : E) (p : E × (E × E)) : ℝ := statePotential a p.1 p.2

/-- Joint parameter/state analyticity on pairwise-distinct triples. -/
theorem contDiffAt_jointPotential (a : E) {p : E × (E × E)}
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hzy : p.2.2 ≠ p.1)
    {n : WithTop ENat} : ContDiffAt ℝ n (jointPotential a) p := by
  have hY : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hX : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p := contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p := contDiffAt_snd.snd
  have hXY := (contDiffAt_pairCost (sub_ne_zero.mpr hxy)).comp p (hX.sub hY)
  have hXZ := (contDiffAt_pairCost (sub_ne_zero.mpr hxz)).comp p (hX.sub hZ)
  have hZY := (contDiffAt_pairCost (sub_ne_zero.mpr hzy)).comp p (hZ.sub hY)
  exact (((hXY.add hXZ).add hZY).sub
    (contDiffAt_const.sub (contDiffAt_const.mul (hX.norm_sq ℝ)))).sub
    ((contDiffAt_const.mul (contDiffAt_const.inner ℝ (hZ.add contDiffAt_const))).sub
      (contDiffAt_const.mul ((hZ.add contDiffAt_const).norm_sq ℝ)))

/-- The linear form represented by the two components of the stationary map. -/
def stateDifferential (a y : E) (s : E × E) : E × E →L[ℝ] ℝ :=
  (innerSL ℝ (stationary a (y, s)).1).comp (ContinuousLinearMap.fst ℝ E E) +
    (innerSL ℝ (stationary a (y, s)).2).comp (ContinuousLinearMap.snd ℝ E E)

/-- The displayed stationary equation really is the state derivative of the supporting potential. -/
theorem hasFDerivAt_statePotential (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y) :
    HasFDerivAt (statePotential a y) (stateDifferential a y s) s := by
  have hX : HasFDerivAt (fun q : E × E => q.1)
      (ContinuousLinearMap.fst ℝ E E) s := hasFDerivAt_fst
  have hZ : HasFDerivAt (fun q : E × E => q.2)
      (ContinuousLinearMap.snd ℝ E E) s := hasFDerivAt_snd
  have hXY := (hasFDerivAt_pairCost (sub_ne_zero.mpr hxy)).comp s (hX.sub_const y)
  have hXZ := (hasFDerivAt_pairCost (sub_ne_zero.mpr hxz)).comp s (hX.sub hZ)
  have hZY := (hasFDerivAt_pairCost (sub_ne_zero.mpr hzy)).comp s (hZ.sub_const y)
  have h := (((hXY.add hXZ).add hZY).sub
    ((hasFDerivAt_const ((5 : ℝ) / 2) s).sub (hX.norm_sq.const_mul 10))).sub
    ((((hasFDerivAt_const a s).inner ℝ (hZ.add_const a)).const_mul ((5 : ℝ) / 4)).sub
      ((hZ.add_const a).norm_sq.const_mul 10))
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [stateDifferential, stationary, pairGradient, mul_sub, norm_sub_rev s.2 s.1]
  ring

/-- The full parameter/state derivative of the concrete stationary equation. -/
def stationaryDifferential (p : E × (E × E)) :
    E × (E × E) →L[ℝ] E × E :=
  let Y := ContinuousLinearMap.fst ℝ E (E × E)
  let X := (ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))
  let Z := (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))
  ((pairHessian (p.2.1 - p.1)).comp (X - Y) +
      (pairHessian (p.2.1 - p.2.2)).comp (X - Z) + (20 : ℝ) • X).prod
    ((pairHessian (p.2.2 - p.2.1)).comp (Z - X) +
      (pairHessian (p.2.2 - p.1)).comp (Z - Y) + (20 : ℝ) • Z)

theorem hasFDerivAt_stationary (a : E) {p : E × (E × E)}
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hzy : p.2.2 ≠ p.1) :
    HasFDerivAt (stationary a) (stationaryDifferential p) p := by
  have hY : HasFDerivAt (fun q : E × (E × E) => q.1)
      (ContinuousLinearMap.fst ℝ E (E × E)) p := hasFDerivAt_fst
  have hX : HasFDerivAt (fun q : E × (E × E) => q.2.1)
      ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))) p :=
    (hasFDerivAt_fst (𝕜 := ℝ)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hZ : HasFDerivAt (fun q : E × (E × E) => q.2.2)
      ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))) p :=
    (hasFDerivAt_snd (𝕜 := ℝ)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hXY := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hxy)).comp p (hX.sub hY)
  have hXZ := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hxz)).comp p (hX.sub hZ)
  have hZX := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hxz.symm)).comp p (hZ.sub hX)
  have hZY := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hzy)).comp p (hZ.sub hY)
  exact ((hXY.add hXZ).add (hX.const_smul (20 : ℝ))).prodMk
    (((hZX.add hZY).sub_const ((5 / 4 : ℝ) • a)).add ((hZ.add_const a).const_smul (20 : ℝ)))

/-- A zero of the explicit stationary map is a stationary point of the scalar potential. -/
theorem hasFDerivAt_statePotential_zero (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y)
    (hzero : stationary a (y, s) = 0) :
    HasFDerivAt (statePotential a y) (0 : E × E →L[ℝ] ℝ) s := by
  have h := hasFDerivAt_statePotential a y hxy hxz hzy
  simpa [stateDifferential, hzero] using h

end Problem356.StationaryMap

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.LocalGeometry

open StationaryMap CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem statePotential_center_value {a : E} (ha : ‖a‖ = 1) :
    statePotential a a (0, -a) = 0 := by
  have hvec : -a - a = (-2 : ℝ) • a := by module
  have hnorm : ‖-a - a‖ = 2 := by rw [hvec, norm_smul, ha]; norm_num
  simp [statePotential, pairCost, ha, hnorm]
  norm_num

/-- The branch value vanishes at the center, as required to glue the five
local potentials with values `5/2,0,0,0,0`. -/
theorem localSupporting_value_center {a : E} (ha : ‖a‖ = 1)
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)) :
    C.value a = 0 := by
  rw [C.value_base]
  exact statePotential_center_value ha

/-- Restore the central and opposite quadratic potentials in the local
supporting inequality. This is the literal three-point Coulomb formula. -/
theorem local_coulomb_supporting {a : E}
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a))
    {x y z : E}
    (hy : y ∈ Metric.ball a C.parameterRadius)
    (hx : x ∈ Metric.ball (0 : E) C.stateRadius)
    (hz : z ∈ Metric.ball (-a) C.stateRadius) :
    ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫ - 10 * ‖z + a‖ ^ 2) ≤
      ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹ := by
  have hy' : y ∈ C.charts.central.source := C.source_ball ▸ hy
  have hs : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, ← ball_prod_same]
    exact ⟨hx, hz⟩
  have h := C.supporting y hy' (x, z) hs
  simp only [jointPotential, statePotential, pairCost, norm_sub_rev z y] at h
  linarith

/-- Equality in the supporting inequality is exactly the stationary branch,
not merely inclusion of the branch in the contact set. -/
theorem local_coulomb_contact {a : E}
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a))
    {x y z : E}
    (hy : y ∈ Metric.ball a C.parameterRadius)
    (hx : x ∈ Metric.ball (0 : E) C.stateRadius)
    (hz : z ∈ Metric.ball (-a) C.stateRadius) :
    (‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹ =
      ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫ - 10 * ‖z + a‖ ^ 2)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y := by
  have hy' : y ∈ C.charts.central.source := C.source_ball ▸ hy
  have hs : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, ← ball_prod_same]
    exact ⟨hx, hz⟩
  have h := C.contact y hy' (x, z) hs
  simp only [jointPotential, statePotential, pairCost, norm_sub_rev z y, Prod.mk.injEq] at h
  rw [← h]
  constructor <;> intro heq <;> linarith

end Problem356.LocalGeometry

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A nonnegative smooth compactly supported square with mass one is an
admissible density, including the extra square-root regularity. -/
theorem isSmoothCompactProbabilityDensity_sq
    {g : E3 → ℝ}
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_smooth : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hg_compact : HasCompactSupport g)
    (hg_mass : (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => (g x) ^ 2) := by
  have hsqrt : (fun x : E3 => Real.sqrt ((g x) ^ 2)) = g := by
    funext x
    exact Real.sqrt_sq (hg_nonneg x)
  refine ⟨fun x => sq_nonneg (g x), hg_smooth.pow 2, ?_, ?_, ?_, hg_mass⟩
  · simpa only [pow_two, Pi.mul_def] using hg_compact.mul_left (f := g)
  · simpa only [hsqrt] using hg_smooth
  · simpa only [hsqrt] using hg_compact

/-- Normalizing a nonnegative smooth square preserves smoothness of its square root. -/
theorem isSmoothCompactProbabilityDensity_normalized_sq
    {g : E3 → ℝ}
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_smooth : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hg_compact : HasCompactSupport g)
    (hg_mass_pos : 0 < ∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) :
    IsSmoothCompactProbabilityDensity
      (fun x => (g x / Real.sqrt (∫ y : E3, (g y) ^ 2 ∂(volume : Measure E3))) ^ 2) := by
  apply isSmoothCompactProbabilityDensity_sq
  · intro x
    exact div_nonneg (hg_nonneg x) (Real.sqrt_nonneg _)
  · exact hg_smooth.div_const _
  · simpa only [div_eq_mul_inv, Pi.mul_def] using
      hg_compact.mul_right (f' := fun _ =>
        (Real.sqrt (∫ y : E3, (g y) ^ 2 ∂(volume : Measure E3)))⁻¹)
  · simp_rw [div_pow]
    rw [integral_div, Real.sq_sqrt hg_mass_pos.le, div_self hg_mass_pos.ne']

/-- A normalized nonnegative smooth square can be placed in any positive-radius ball. -/
theorem exists_normalized_smooth_square_in_ball (c : E3) {r : ℝ} (hr : 0 < r) :
    ∃ g : E3 → ℝ,
      (∀ x, 0 ≤ g x) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
      HasCompactSupport g ∧
      tsupport g ⊆ Metric.ball c r ∧
      (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by
  let b : ContDiffBump c := ⟨r / 4, r / 2, by linarith, by linarith⟩
  have hb_compact : HasCompactSupport (fun x : E3 => (b x) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using
      b.hasCompactSupport.mul_left (f := fun x => b x)
  have hb_center : b c = 1 := by
    exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hm : 0 < ∫ x : E3, (b x) ^ 2 ∂(volume : Measure E3) := by
    apply (b.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := c) hb_compact (fun x => sq_nonneg (b x))
    change (b c) ^ 2 ≠ 0
    rw [hb_center]
    norm_num
  let g : E3 → ℝ := fun x => b x /
    Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3))
  refine ⟨g, fun x => div_nonneg b.nonneg (Real.sqrt_nonneg _),
    b.contDiff.div_const _, ?_, ?_, ?_⟩
  · simpa only [g, div_eq_mul_inv, Pi.mul_def] using
      b.hasCompactSupport.mul_right (f' := fun _ =>
        (Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3)))⁻¹)
  · have hs : tsupport g ⊆ tsupport (fun x : E3 => b x) := by
      simpa only [g, div_eq_mul_inv, Pi.mul_def] using
        (tsupport_mul_subset_left (f := fun x : E3 => b x)
          (g := fun _ => (Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3)))⁻¹))
    apply hs.trans
    rw [b.tsupport_eq]
    intro x hx
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    change dist x c ≤ r / 2 at hx'
    linarith
  · dsimp only [g]
    simp_rw [div_pow]
    rw [integral_div, Real.sq_sqrt hm.le, div_self hm.ne']

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- The nonnegative real-density constructor respects finite scalar multiples. -/
theorem densityMeasure_const_mul {a : ℝ} (ha : 0 ≤ a) (rho : E3 → ℝ) :
    densityMeasure (fun x => a * rho x) = ENNReal.ofReal a • densityMeasure rho := by
  unfold densityMeasure
  simp_rw [ENNReal.ofReal_mul ha]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

/-- The real density constructor is additive on nonnegative densities. -/
theorem densityMeasure_add {rho sigma : E3 → ℝ}
    (hrho : ∀ x, 0 ≤ rho x) (hsigma : ∀ x, 0 ≤ sigma x)
    (hm : Measurable rho) :
    densityMeasure (fun x => rho x + sigma x) =
      densityMeasure rho + densityMeasure sigma := by
  unfold densityMeasure
  simp_rw [ENNReal.ofReal_add (hrho _) (hsigma _)]
  exact withDensity_add_left hm.ennreal_ofReal _

/-- Finite nonnegative density mixtures agree with mixtures of the induced
measures. This identifies the smooth marginal with the branch-plan marginal. -/
theorem densityMeasure_finset_mixture {ι : Type uIndex} (s : Finset ι)
    (a : ι → ℝ) (rho : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hrho : ∀ i ∈ s, ∀ x, 0 ≤ rho i x)
    (hm : ∀ i ∈ s, Measurable (rho i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * rho i x) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (rho i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [densityMeasure]
  | @insert i s hi ih =>
    have hai : 0 ≤ a i := ha i (Finset.mem_insert_self _ _)
    have hri : ∀ x, 0 ≤ rho i x := hrho i (Finset.mem_insert_self _ _)
    have hmi : Measurable (rho i) := hm i (Finset.mem_insert_self _ _)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hrs : ∀ j ∈ s, ∀ x, 0 ≤ rho j x :=
      fun j hj => hrho j (Finset.mem_insert_of_mem hj)
    have hms : ∀ j ∈ s, Measurable (rho j) :=
      fun j hj => hm j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [densityMeasure_add (fun x => mul_nonneg hai (hri x))
      (fun x => Finset.sum_nonneg (fun j hj => mul_nonneg (has j hj) (hrs j hj x)))
      (measurable_const.mul hmi), densityMeasure_const_mul hai, ih has hrs hms]

/-- Fintype form of the density-mixture identity. -/
theorem densityMeasure_fintype_mixture {ι : Type uIndex} [Fintype ι]
    (a : ι → ℝ) (rho : ι → E3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hrho : ∀ i x, 0 ≤ rho i x)
    (hm : ∀ i, Measurable (rho i)) :
    densityMeasure (fun x => ∑ i, a i * rho i x) =
      ∑ i, ENNReal.ofReal (a i) • densityMeasure (rho i) := by
  exact densityMeasure_finset_mixture Finset.univ a rho
    (fun i _ => ha i) (fun i _ => hrho i) (fun i _ => hm i)

theorem densityMeasure_five_component_mixture
    (rho0 : E3 → ℝ) (rho : Fin 4 → E3 → ℝ)
    (h0 : ∀ x, 0 ≤ rho0 x) (h : ∀ i x, 0 ≤ rho i x)
    (hm0 : Measurable rho0) (hm : ∀ i, Measurable (rho i)) :
    densityMeasure (fun x => (1 / 3 : ℝ) * rho0 x +
      ∑ i, (1 / 6 : ℝ) * rho i x) =
      (1 / 3 : ℝ≥0∞) • densityMeasure rho0 +
      ∑ i, (1 / 6 : ℝ≥0∞) • densityMeasure (rho i) := by
  rw [densityMeasure_add (fun x => mul_nonneg (by norm_num) (h0 x))
    (fun x => Finset.sum_nonneg (fun i _ => mul_nonneg (by norm_num) (h i x)))
    (measurable_const.mul hm0)]
  rw [densityMeasure_const_mul (by norm_num),
    densityMeasure_fintype_mixture (fun _ : Fin 4 => (1 / 6 : ℝ)) rho
      (fun _ => by norm_num) h hm]
  norm_num [ENNReal.ofReal_div_of_pos]

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Finite graph approximants give the reverse relaxation inequality, hence
identify the Monge and Kantorovich infima. -/
theorem mongeValue_eq_kantorovichValue_of_finiteMongeApproximation
    (mu : Measure E3) [IsProbabilityMeasure mu] (happrox : FiniteMongeApproximation mu) :
    mongeValue mu = kantorovichValue mu := by
  apply le_antisymm ?_ (kantorovichValue_le_mongeValue mu)
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  have hepsilon' : (0 : ℝ) < epsilon := by exact_mod_cast hepsilon
  obtain ⟨T2, T3, h2, h3, _hfinite, hcost⟩ := happrox epsilon hepsilon'
  have hmonge : mongeValue mu ≤ graphCost mu T2 T3 := by
    unfold mongeValue
    exact iInf_le_of_le T2 (iInf_le_of_le T3
      (iInf_le_of_le h2 (iInf_le_of_le h3 le_rfl)))
  exact hmonge.trans (by simpa using hcost)

/-- The final logical closure: counterexample construction plus finite Monge
approximation gives the complete qualified conclusion without changing any
of its predicates. -/
theorem hasFullCoulombConclusion_of_counterexample_of_approximation
    {rho : E3 → ℝ} (hcounter : HasCoulombCounterexample rho)
    (happrox : FiniteMongeApproximation (densityMeasure rho)) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := hcounter.2.1
  exact ⟨hcounter,
    mongeValue_eq_kantorovichValue_of_finiteMongeApproximation (densityMeasure rho) happrox,
    happrox⟩

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Set

namespace Problem356
namespace LocalBranchMeasure

variable {α : Type uAlpha} {β : Type uBeta} [TopologicalSpace α] [TopologicalSpace β]
  [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

/-- A local branch extended by a fixed value outside its source. -/
def extendedBranch (e : OpenPartialHomeomorph α β) (z : β) : α → β := by
  classical
  exact e.source.piecewise e (fun _ => z)

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
@[simp] theorem extendedBranch_apply_of_mem
    (e : OpenPartialHomeomorph α β) (z : β) {x : α} (hx : x ∈ e.source) :
    extendedBranch e z x = e x := by
  classical
  simp [extendedBranch, hx]

/-- The extension is Borel measurable even if the local map is arbitrary outside its source. -/
theorem measurable_extendedBranch (e : OpenPartialHomeomorph α β) (z : β) :
    Measurable (extendedBranch e z) := by
  classical
  exact e.continuousOn.measurable_piecewise continuous_const.continuousOn
    e.open_source.measurableSet

/-- Restricting the domain of a local branch to a measurable set gives a measurable image. -/
theorem measurableSet_image (e : OpenPartialHomeomorph α β)
    {S : Set α} (hS : MeasurableSet S) (hSub : S ⊆ e.source) :
    MeasurableSet (e '' S) := by
  have h := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (hS.preimage measurable_subtype_coe)
  simpa only [Set.image_domRestrict, Set.inter_eq_left.mpr hSub] using h

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
/-- Extension preserves every image of a subset of the local source. -/
theorem extendedBranch_image (e : OpenPartialHomeomorph α β) (z : β)
    {S : Set α} (hSub : S ⊆ e.source) :
    extendedBranch e z '' S = e '' S := by
  apply Set.image_congr
  intro x hx
  exact extendedBranch_apply_of_mem e z (hSub hx)

/-- Measurability of selected branch images required by deterministic-selection obstructions. -/
theorem measurableSet_extendedBranch_image (e : OpenPartialHomeomorph α β) (z : β)
    {S : Set α} (hS : MeasurableSet S) (hSub : S ⊆ e.source) :
    MeasurableSet (extendedBranch e z '' S) := by
  rw [extendedBranch_image e z hSub]
  exact measurableSet_image e hS hSub

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
/-- Injectivity of the extension on any subset of the source. -/
theorem injOn_extendedBranch (e : OpenPartialHomeomorph α β) (z : β)
    {B : Set α} (hB : B ⊆ e.source) : InjOn (extendedBranch e z) B := by
  intro x hx y hy hxy
  apply e.injOn (hB hx) (hB hy)
  simpa only [extendedBranch_apply_of_mem e z (hB hx),
    extendedBranch_apply_of_mem e z (hB hy)] using hxy

omit [BorelSpace α] [BorelSpace β] in
/-- Extending outside the source does not change pushforwards of measures concentrated there. -/
theorem map_extendedBranch (e : OpenPartialHomeomorph α β) (z : β)
    (ν : Measure α) (hν : ∀ᵐ x ∂ν, x ∈ e.source) :
    Measure.map (extendedBranch e z) ν = Measure.map e ν := by
  apply Measure.map_congr
  filter_upwards [hν] with x hx
  exact extendedBranch_apply_of_mem e z hx

/-- A measurable selector's coincidence set with an extended local branch is measurable. -/
theorem measurableSet_selection [MeasurableEq β]
    (e : OpenPartialHomeomorph α β) (z : β) {B : Set α}
    (hB : MeasurableSet B) {T : α → β} (hT : Measurable T) :
    MeasurableSet (B ∩ {x | T x = extendedBranch e z x}) :=
  hB.inter (measurableSet_eq_fun hT (measurable_extendedBranch e z))

/-- Selected coincidence sets have measurable branch images. -/
theorem measurableSet_selection_image [MeasurableEq β]
    (e : OpenPartialHomeomorph α β) (z : β) {B : Set α}
    (hB : MeasurableSet B) (hSub : B ⊆ e.source)
    {T : α → β} (hT : Measurable T) :
    MeasurableSet (extendedBranch e z '' (B ∩ {x | T x = extendedBranch e z x})) := by
  apply measurableSet_extendedBranch_image e z (measurableSet_selection e z hB hT)
  exact inter_subset_left.trans hSub

end LocalBranchMeasure
end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Problem356

/-- A smooth function on an open set extends smoothly by zero whenever its
closed support stays in that open set.  The function is already defined
on the ambient space; the support hypothesis expresses the extension. -/
theorem contDiff_of_contDiffOn_of_tsupport_subset
    {f : E3 → ℝ} {s : Set E3} {n : WithTop ENat}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (hfs : tsupport f ⊆ s) :
    ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact hf.contDiffAt (hs.mem_nhds hx)
  · have hxt : x ∉ tsupport f := fun ht => hx (hfs ht)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
    exact image_eq_zero_of_notMem_tsupport hy

/-- Transport of a compactly supported amplitude through a local
homeomorphism, with a prescribed Jacobian square-root factor. -/
def localTransportAmplitude (e : OpenPartialHomeomorph E3 E3)
    (g J : E3 → ℝ) : E3 → ℝ :=
  e.target.indicator (fun y => g (e.symm y) * J y)

theorem localTransportAmplitude_nonneg
    (e : OpenPartialHomeomorph E3 E3) {g J : E3 → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hJ : ∀ y ∈ e.target, 0 ≤ J y) :
    ∀ y, 0 ≤ localTransportAmplitude e g J y := by
  intro y
  by_cases hy : y ∈ e.target
  · simp only [localTransportAmplitude, indicator_of_mem hy]
    exact mul_nonneg (hg _) (hJ _ hy)
  · simp [localTransportAmplitude, hy]

theorem support_localTransportAmplitude_subset
    (e : OpenPartialHomeomorph E3 E3) (g J : E3 → ℝ) :
    Function.support (localTransportAmplitude e g J) ⊆ e '' tsupport g := by
  intro y hy
  have hyt : y ∈ e.target := by
    by_contra hn
    exact hy (by simp [localTransportAmplitude, hn])
  refine ⟨e.symm y, ?_, e.right_inv hyt⟩
  apply subset_tsupport g
  intro hz
  apply hy
  simp [localTransportAmplitude, hyt, hz]

theorem tsupport_localTransportAmplitude_subset
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    tsupport (localTransportAmplitude e g J) ⊆ e '' tsupport g := by
  apply closure_minimal (support_localTransportAmplitude_subset e g J)
  exact (hg.image_of_continuousOn (e.continuousOn.mono hgs)).isClosed

theorem hasCompactSupport_localTransportAmplitude
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    HasCompactSupport (localTransportAmplitude e g J) := by
  exact (hg.image_of_continuousOn (e.continuousOn.mono hgs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_localTransportAmplitude_subset e J hg hgs)

theorem tsupport_localTransportAmplitude_subset_target
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    tsupport (localTransportAmplitude e g J) ⊆ e.target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_localTransportAmplitude_subset e J hg hgs hy
  exact e.map_source (hgs hx)

theorem contDiff_localTransportAmplitude
    (e : OpenPartialHomeomorph E3 E3) {g J : E3 → ℝ} {n : WithTop ENat}
    (hg : ContDiff ℝ n g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ e.source)
    (he : ContDiffOn ℝ n e.symm e.target)
    (hJ : ContDiffOn ℝ n J e.target) :
    ContDiff ℝ n (localTransportAmplitude e g J) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset e.open_target
    _ (tsupport_localTransportAmplitude_subset_target e J hgc hgs)
  have hcomp : ContDiffOn ℝ n (fun y => g (e.symm y) * J y) e.target :=
    (hg.comp_contDiffOn he).mul hJ
  refine hcomp.congr ?_
  intro y hy
  simp [localTransportAmplitude, hy]

/-- The inverse-Jacobian change-of-variables formula for a local
homeomorphism.  No global behavior outside its source is required. -/
theorem map_withDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (w : E3 → ℝ≥0∞)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (((volume : Measure E3).restrict e.source).withDensity w) =
      ((volume : Measure E3).restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(D y).det| * w (e.symm y)) := by
  have he : AEMeasurable e ((volume : Measure E3).restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hew : AEMeasurable e
      (((volume : Measure E3).restrict e.source).withDensity w) :=
    he.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext
  intro s hs
  have hpre : NullMeasurableSet (e ⁻¹' s)
      ((volume : Measure E3).restrict e.source) :=
    he.nullMeasurableSet_preimage hs
  rw [Measure.map_apply_of_aemeasurable hew hs,
    withDensity_apply₀ _ hpre, withDensity_apply _ hs,
    Measure.restrict_restrict₀ hpre, Measure.restrict_restrict hs]
  have hset : e.symm '' (s ∩ e.target) = e ⁻¹' s ∩ e.source := by
    ext x
    constructor
    · rintro ⟨y, ⟨hys, hyt⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, e.right_inv hyt] using hys,
        e.symm.map_source hyt⟩
    · rintro ⟨hxs, hxe⟩
      exact ⟨e x, ⟨hxs, e.map_source hxe⟩, e.left_inv hxe⟩
  rw [← hset]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (hs.inter e.open_target.measurableSet)
    (fun y hy => (hD y hy.2).hasFDerivWithinAt)
    (e.symm.injOn.mono inter_subset_right) w

/-- The local inverse-Jacobian formula carries a square density to a
square density, exactly as required by the five-component construction. -/
theorem map_squareDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (g : E3 → ℝ)
    (hgs : tsupport g ⊆ e.source)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y =>
        localTransportAmplitude e g (fun z => Real.sqrt |(D z).det|) y ^ 2) := by
  have hsource : densityMeasure (fun x => g x ^ 2) =
      ((volume : Measure E3).restrict e.source).withDensity
        (fun x => ENNReal.ofReal (g x ^ 2)) := by
    rw [densityMeasure, ← withDensity_indicator e.open_source.measurableSet]
    congr 1
    ext x
    by_cases hx : x ∈ e.source
    · simp [hx]
    · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hgs h))
      simp [hx, hgx]
  rw [hsource, map_withDensity_localHomeomorph e _ D hD, densityMeasure,
    ← withDensity_indicator e.open_target.measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ e.target
  · simp only [indicator_of_mem hy, localTransportAmplitude, mul_pow,
      Real.sq_sqrt (abs_nonneg _)]
    rw [mul_comm (g (e.symm y) ^ 2), ENNReal.ofReal_mul (abs_nonneg _)]
  · simp [localTransportAmplitude, hy]

end Problem356

end

end OAI
end
end

section
section
namespace OAI

/-! Square-density transport through globally measurable extensions of local branches. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem356

/-- A square density is concentrated on every measurable set containing the amplitude's support. -/
theorem squareDensity_ae_mem_of_tsupport_subset
    (g : E3 → ℝ) {U : Set E3} (hU : MeasurableSet U) (hg : tsupport g ⊆ U) :
    ∀ᵐ x ∂densityMeasure (fun x => g x ^ 2), x ∈ U := by
  apply ae_iff.mpr
  change densityMeasure (fun x => g x ^ 2) Uᶜ = 0
  rw [densityMeasure, withDensity_apply _ hU.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hU.compl] with x hx
  have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hg ht))
  simp [hgx]

/-- Extending a local branch by a fixed value outside its source does not affect
its transport of a square density supported strictly inside that source. -/
theorem map_extendedBranch_squareDensity
    (e : OpenPartialHomeomorph E3 E3) (z : E3) (g : E3 → ℝ)
    (hg : tsupport g ⊆ e.source) :
    Measure.map (LocalBranchMeasure.extendedBranch e z)
        (densityMeasure (fun x => g x ^ 2)) =
      Measure.map e (densityMeasure (fun x => g x ^ 2)) :=
  LocalBranchMeasure.map_extendedBranch e z _
    (squareDensity_ae_mem_of_tsupport_subset g e.open_source.measurableSet hg)

/-- The exact inverse-Jacobian pushforward formula for a globally Borel branch. -/
theorem map_squareDensity_extendedBranch
    (e : OpenPartialHomeomorph E3 E3) (z : E3) (g : E3 → ℝ)
    (hgs : tsupport g ⊆ e.source)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map (LocalBranchMeasure.extendedBranch e z)
        (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y =>
        localTransportAmplitude e g (fun t => Real.sqrt |(D t).det|) y ^ 2) := by
  rw [map_extendedBranch_squareDensity e z g hgs]
  exact map_squareDensity_localHomeomorph e g hgs D hD

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Problem356

/-- The cumulative mass of a finite real measure with null singletons is continuous. -/
theorem continuous_real_cumulative (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : Continuous (fun t : ℝ => μ.real (Iic t)) := by
  have hc : Continuous (fun t : ℝ => ∫ x in Iic t, (1 : ℝ) ∂μ) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (t + 1)) μ :=
      (integrable_const (1 : ℝ)).integrableOn
    exact hi.continuousOn_Iic_primitive_Iic.continuousAt (Iic_mem_nhds (by linarith))
  simpa using hc

/-- Every strictly intermediate mass is the mass of a lower interval. -/
theorem exists_real_cumulative_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {r : ℝ} (hr : 0 < r) (hrμ : r < μ.real univ) :
    ∃ t : ℝ, μ.real (Iic t) = r := by
  have hbot : Tendsto (fun t : ℝ => μ.real (Iic t)) atBot (𝓝 0) := by
    simpa using (tendsto_integral_Iic_zero (μ := μ) (f := fun _ : ℝ => (1 : ℝ))
      (a := id) tendsto_id)
  have htop : Tendsto (fun t : ℝ => μ.real (Iic t)) atTop (𝓝 (μ.real univ)) := by
    exact (ENNReal.continuousAt_toReal (measure_ne_top μ univ)).tendsto.comp
      (tendsto_measure_Iic_atTop μ)
  exact mem_range_of_exists_le_of_exists_ge (continuous_real_cumulative μ)
    ((hbot.eventually (gt_mem_nhds hr)).exists.imp (fun _ h => h.le))
    ((htop.eventually (lt_mem_nhds hrμ)).exists.imp (fun _ h => h.le))

/-- A finite measure with null singletons on a standard Borel space can realize
any prescribed mass inside any measurable set. -/
theorem exists_measurable_subset_measure_eq {α : Type uAlpha} [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {A : Set α} (hA : MeasurableSet A)
    {r : ℝ≥0∞} (hr : r ≤ μ A) :
    ∃ B : Set α, MeasurableSet B ∧ B ⊆ A ∧ μ B = r := by
  by_cases hzero : r = 0
  · exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [hzero]⟩
  by_cases hfull : r = μ A
  · exact ⟨A, hA, Subset.rfl, hfull.symm⟩
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real α
  let ν : Measure ℝ := Measure.map e (μ.restrict A)
  have : NullSingletonClass ν := by
    constructor
    intro y
    rw [show ν {y} = (μ.restrict A) (e ⁻¹' {y}) from
      Measure.map_apply he.measurable (measurableSet_singleton y)]
    have hs : (e ⁻¹' {y}).Subsingleton := by
      intro x hx z hz
      exact he.injective (hx.trans hz.symm)
    exact hs.measure_zero (μ.restrict A)
  have hν : ν univ = μ A := by simp [ν, Measure.map_apply, he.measurable]
  have hrfinite : r ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ A) hr
  have hpos : 0 < r.toReal := ENNReal.toReal_pos hzero hrfinite
  have hlt : r.toReal < ν.real univ := by
    rw [measureReal_def, hν]
    exact (ENNReal.toReal_lt_toReal hrfinite (measure_ne_top μ A)).2
      (lt_of_le_of_ne hr hfull)
  obtain ⟨t, ht⟩ := exists_real_cumulative_eq ν hpos hlt
  have hmass : ν (Iic t) = r := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _) hrfinite).1
    exact ht
  refine ⟨e ⁻¹' Iic t ∩ A, (he.measurable measurableSet_Iic).inter hA,
    inter_subset_right, ?_⟩
  simpa [ν, Measure.map_apply he.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply
      (he.measurable measurableSet_Iic)] using hmass

/-- Finitely many prescribed masses whose total does not exceed the mass of a
measurable set can be realized by pairwise disjoint measurable subsets. -/
theorem exists_fin_disjoint_subsets_measure {α : Type uAlpha} [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (q : Fin n → ℝ≥0∞)
    {A : Set α} (hA : MeasurableSet A) (hq : ∑ i, q i ≤ μ A) :
    ∃ B : Fin n → Set α,
      (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧ (∀ i, μ (B i) = q i) := by
  classical
  induction n generalizing A with
  | zero =>
      exact ⟨Fin.elim0, by simp, by simp, by simp [Pairwise], by simp⟩
  | succ n ih =>
      have hq0 : q 0 ≤ μ A := by
        exact (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ 0)).trans hq
      obtain ⟨B0, hm0, hs0, hmass0⟩ := exists_measurable_subset_measure_eq μ hA hq0
      have htail : ∑ i : Fin n, q i.succ ≤ μ (A \ B0) := by
        rw [measure_sdiff hs0 hm0.nullMeasurableSet (measure_ne_top μ B0), hmass0]
        apply ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top (measure_ne_top μ A) hq0)
        simpa [Fin.sum_univ_succ] using hq
      obtain ⟨B, hm, hs, hd, hmass⟩ := ih (fun i => q i.succ) (hA.diff hm0) htail
      refine ⟨Fin.cons B0 B, ?_, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases hm0 hm i
      · intro i
        exact Fin.cases hs0 (fun i => (hs i).trans sdiff_subset) i
      · intro i j hij
        cases i using Fin.cases <;> cases j using Fin.cases
        · exact (hij rfl).elim
        · simpa using (disjoint_sdiff_right.mono_right (hs _))
        · simpa using (disjoint_sdiff_right.mono_right (hs _)).symm
        · exact hd (fun h => hij (congrArg Fin.succ h))
      · intro i
        exact Fin.cases hmass0 hmass i

/-- Fintype-indexed version of finite prescribed-mass splitting. -/
theorem exists_finite_disjoint_subsets_measure {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]
    [StandardBorelSpace α] [Fintype ι] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (q : ι → ℝ≥0∞)
    {A : Set α} (hA : MeasurableSet A) (hq : ∑ i, q i ≤ μ A) :
    ∃ B : ι → Set α,
      (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧ (∀ i, μ (B i) = q i) := by
  classical
  let e := Fintype.equivFin ι
  have hsum : ∑ i, q (e.symm i) ≤ μ A := by
    simpa only [e.symm.sum_comp] using hq
  obtain ⟨B, hm, hs, hd, hmass⟩ :=
    exists_fin_disjoint_subsets_measure μ (fun i => q (e.symm i)) hA hsum
  refine ⟨fun i => B (e i), fun i => hm (e i), fun i => hs (e i), ?_, ?_⟩
  · intro i j hij
    exact hd (fun h => hij (e.injective h))
  · intro i
    simpa using hmass (e i)

/-- When prescribed masses exhaust the source mass, the disjoint subsets cover
it up to a null remainder. Empty index types are allowed. -/
theorem exists_finite_mass_partition_ae {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]
    [StandardBorelSpace α] [Fintype ι] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (q : ι → ℝ≥0∞)
    {A : Set α} (hA : MeasurableSet A) (hq : ∑ i, q i = μ A) :
    ∃ B : ι → Set α,
      (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, μ (B i) = q i) ∧ μ (A \ ⋃ i, B i) = 0 := by
  obtain ⟨B, hm, hs, hd, hmass⟩ := exists_finite_disjoint_subsets_measure μ q hA hq.le
  refine ⟨B, hm, hs, hd, hmass, ?_⟩
  have hmass_union : μ (⋃ i, B i) = μ A := by
    rw [measure_iUnion hd hm, tsum_fintype]
    simpa only [hmass] using hq
  rw [measure_sdiff (iUnion_subset hs) (MeasurableSet.iUnion hm).nullMeasurableSet
    (measure_ne_top μ _), hmass_union, tsub_self]

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open Set Filter Metric
open scoped BigOperators
namespace Problem356

/-- Continuity of finitely many potentials at their centers gives one
positive radius and one positive absolute bound on every component ball. -/
theorem exists_uniform_local_potential_bound {ι : Type uIndex} {X : Type uX} [Fintype ι]
    [PseudoMetricSpace X] (p : ι → X) (v : ι → X → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) :
    ∃ M : ℝ, 0 < M ∧ ∃ r : ℝ, 0 < r ∧
      ∀ i x, x ∈ ball (p i) r → |v i x| ≤ M := by
  classical
  let M : ℝ := (∑ i, |v i (p i)|) + 1
  have hsum : 0 ≤ ∑ i, |v i (p i)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hM : 0 < M := by dsimp [M]; linarith
  have hgap : ∀ i ∈ (Finset.univ : Finset ι), |v i (p i)| < M := by
    intro i _
    have hi : |v i (p i)| ≤ ∑ j, |v j (p j)| :=
      Finset.single_le_sum (f := fun j => |v j (p j)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [M]
    linarith
  obtain ⟨r, hr, h⟩ := finite_strict_neighborhoods Finset.univ p
    (fun i x => |v i x|) (fun _ _ => M)
    (fun i _ => (hv i).abs) (fun _ _ => continuousAt_const) hgap
  refine ⟨M, hM, r, hr, ?_⟩
  intro i x hx
  exact (h i (Finset.mem_univ i) x hx).le

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter Metric Set

namespace Problem356.Geometry

/-- A finite family of positive radii admits a common positive lower bound,
including when the indexing type is empty. -/
theorem exists_uniform_positive_radius {ι : Type uIndex} [Finite ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset ℝ := insert 1 (Finset.univ.image r)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · apply (Finset.lt_min'_iff s hs).2
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact hr i
  · intro i
    exact Finset.min'_le s (r i) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

/-- A common ball around a point contained in finitely many open sets.
This applies to the open images of the local inverse branches. -/
theorem finite_common_ball {ι : Type uIndex} {X : Type uX} [Finite ι] [PseudoMetricSpace X]
    (a : X) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (ha : ∀ i, a ∈ U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, ball a δ ⊆ U i := by
  have hopen : IsOpen (⋂ i, U i) := isOpen_iInter_of_finite hU
  have hamem : a ∈ ⋂ i, U i := mem_iInter.mpr ha
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen a hamem
  exact ⟨δ, hδ, fun i x hx => mem_iInter.mp (hsub hx) i⟩

/-- Distinct finitely many centers admit a common positive radius with
pairwise disjoint closed balls. -/
theorem finite_disjoint_closedBalls {ι : Type uIndex} {X : Type uX} [Finite ι] [MetricSpace X]
    (a : ι → X) (ha : Function.Injective a) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (fun i j =>
      Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by
  let J := {q : ι × ι // q.1 ≠ q.2}
  let r : J → ℝ := fun q => dist (a q.val.1) (a q.val.2) / 3
  have hr : ∀ q, 0 < r q := by
    intro q
    exact div_pos (dist_pos.mpr (ha.ne q.property)) (by norm_num)
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_positive_radius r hr
  refine ⟨δ, hδ, ?_⟩
  intro i j hij
  apply Metric.closedBall_disjoint_closedBall
  have h := hbound ⟨(i, j), hij⟩
  change δ ≤ dist (a i) (a j) / 3 at h
  linarith

/-- One radius may simultaneously separate all components and keep each
closed component ball inside a prescribed open neighborhood. -/
theorem finite_disjoint_closedBalls_subset {ι : Type uIndex} {X : Type uX} [Finite ι]
    [MetricSpace X] (a : ι → X) (ha : Function.Injective a)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (haU : ∀ i, a i ∈ U i) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, closedBall (a i) δ ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by
  have hlocal : ∀ i, ∃ r : ℝ, 0 < r ∧ ball (a i) r ⊆ U i := by
    intro i
    exact Metric.isOpen_iff.mp (hU i) (a i) (haU i)
  choose r hr hsub using hlocal
  obtain ⟨ε, hε, hεr⟩ := exists_uniform_positive_radius r hr
  obtain ⟨η, hη, hdisj⟩ := finite_disjoint_closedBalls a ha
  refine ⟨min (ε / 2) η, lt_min (half_pos hε) hη, ?_, ?_⟩
  · intro i x hx
    apply hsub i
    rw [mem_ball]
    have hx' : dist x (a i) ≤ min (ε / 2) η := hx
    have hsmall : min (ε / 2) η ≤ ε / 2 := min_le_left _ _
    have hri := hεr i
    linarith
  · intro i j hij
    exact (hdisj hij).mono
      (closedBall_subset_closedBall (min_le_right _ _))
      (closedBall_subset_closedBall (min_le_right _ _))

end Problem356.Geometry

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- A contact triple on a finite union, with its ordered component labels. -/
def componentContact {ι : Type uIndex} (U : ι → Set E3)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop) (t : Triple) : Prop :=
  ∃ a, t.1 ∈ U a.1 ∧ t.2.1 ∈ U a.2.1 ∧ t.2.2 ∈ U a.2.2 ∧
    Good a ∧ Contact a t

/-- Local good-type certificates and strict bad-center gaps produce an actual
bounded, measurable supporting potential on disjoint small component balls,
with the precise union of the prescribed contact sets. -/
theorem exists_glued_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) ↔
          componentContact U Good Contact (x, (y, z)))) := by
  classical
  have hvAt : ∀ i, ContinuousAt (v i) (p i) :=
    fun i => (hv i).continuousAt ((hV i).mem_nhds (hpV i))
  obtain ⟨rC, hrC, hcert⟩ := finite_component_certificate p v Good Contact hvAt hgood hbad
  obtain ⟨M, hM, rB, hrB, hbound⟩ := exists_uniform_local_potential_bound p v hvAt
  obtain ⟨rV, hrV, hsubV, hdisjV⟩ :=
    Geometry.finite_disjoint_closedBalls_subset p hp V hV hpV
  let r : ℝ := min rC (min rB rV)
  have hr : 0 < r := lt_min hrC (lt_min hrB hrV)
  have hrC' : r ≤ rC := min_le_left _ _
  have hrB' : r ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hrV' : r ≤ rV := (min_le_right _ _).trans (min_le_right _ _)
  let U : ι → Set E3 := fun i => ball (p i) r
  have hUV : ∀ i, U i ⊆ V i := by
    intro i
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV')).trans (hsubV i)
  have hUdisj : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    exact (hdisjV hij).mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV'))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV'))
  have huCont : ∀ i, ContinuousOn (v i) (U i) := fun i => (hv i).mono (hUV i)
  have hUbound : ∀ i, ∀ x ∈ U i, |v i x| ≤ M := by
    intro i x hx
    exact hbound i x (ball_subset_ball hrB' hx)
  refine ⟨r, M, hr, hM, hUV, hUdisj, ?_, ?_, ?_, ?_⟩
  · exact ComponentPotential.measurable_glue (fun _ => isOpen_ball.measurableSet) huCont
  · exact ComponentPotential.continuousOn_glue (fun _ => isOpen_ball) hUdisj huCont
  · exact ComponentPotential.abs_glue_le hM.le hUdisj hUbound
  · intro x hx y hy z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    have hc := hcert (i, (j, k)) x y z
      (ball_subset_ball hrC' hi) (ball_subset_ball hrC' hj) (ball_subset_ball hrC' hk)
    rw [ComponentPotential.glue_eq hUdisj hi, ComponentPotential.glue_eq hUdisj hj,
      ComponentPotential.glue_eq hUdisj hk]
    refine ⟨hc.1, ?_⟩
    constructor
    · intro heq
      exact ⟨(i, (j, k)), hi, hj, hk, (hc.2.mp heq).1, (hc.2.mp heq).2⟩
    · rintro ⟨a, ha₁, ha₂, ha₃, hgooda, hcontact⟩
      have heq := (hcert a x y z (ball_subset_ball hrC' ha₁)
        (ball_subset_ball hrC' ha₂) (ball_subset_ball hrC' ha₃)).2.mpr ⟨hgooda, hcontact⟩
      have hxv : v a.1 x = v i x := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₁, ComponentPotential.glue_eq hUdisj hi]
      have hyv : v a.2.1 y = v j y := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₂, ComponentPotential.glue_eq hUdisj hj]
      have hzv : v a.2.2 z = v k z := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₃, ComponentPotential.glue_eq hUdisj hk]
      simpa only [hxv, hyv, hzv] using heq

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.TriplePermutation

private lemma pair_symm (x y : E3) : invDistance x y = invDistance y x := by
  simp only [invDistance, norm_sub_rev]

lemma cost_swap_first (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (y, (x, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm y x]
  ac_rfl

lemma cost_swap_last (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (x, (z, y)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm z y]
  ac_rfl

lemma cost_rotate (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (z, (x, y)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm z x, pair_symm z y]
  ac_rfl

private lemma cost_eq_of_same_first {x y z b c : E3}
    (h : List.Perm [x, y, z] [x, b, c]) :
    coulombCost (x, (y, z)) = coulombCost (x, (b, c)) := by
  have hp := List.perm_pair.mp (List.Perm.cons_inv h)
  simp only [List.cons.injEq, and_true] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact cost_swap_last _ _ _

/-- The extended Coulomb cost is invariant under every permutation, including
triples with coincident points and infinite cost. -/
lemma cost_eq_of_perm {x y z a b c : E3}
    (h : List.Perm [x, y, z] [a, b, c]) :
    coulombCost (x, (y, z)) = coulombCost (a, (b, c)) := by
  have ha : a ∈ [x, y, z] := h.mem_iff.mpr (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ha | ha | ha
  · subst a
    exact cost_eq_of_same_first h
  · subst a
    have hs : List.Perm [y, x, z] [x, y, z] := List.Perm.swap x y [z]
    exact (cost_swap_first x y z).trans (cost_eq_of_same_first (hs.trans h))
  · subst a
    have hs : List.Perm [z, x, y] [x, y, z] := by
      simpa using (show List.Perm ([z] ++ [x, y]) ([x, y] ++ [z]) from List.perm_append_comm)
    exact (cost_rotate x y z).trans (cost_eq_of_same_first (hs.trans h))

/-- A common signed potential sum is invariant under the same permutation. -/
lemma real_sum_eq_of_perm {x y z a b c : E3} (u : E3 → ℝ)
    (h : List.Perm [x, y, z] [a, b, c]) :
    u x + u y + u z = u a + u b + u c := by
  have hs := (h.map u).sum_eq
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc] using hs

/-- The same invariance is available after shifting to a nonnegative potential. -/
lemma ennreal_sum_eq_of_perm {x y z a b c : E3} (u : E3 → ℝ≥0∞)
    (h : List.Perm [x, y, z] [a, b, c]) :
    u x + u y + u z = u a + u b + u c := by
  have hs := (h.map u).sum_eq
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc] using hs

/-- An ordered supporting certificate can be transported to any of its six orders. -/
lemma certificate_iff_of_perm {x y z a b c : E3} (u : E3 → ℝ)
    (h : List.Perm [x, y, z] [a, b, c]) :
    (ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z))) ↔
      ENNReal.ofReal (u a + u b + u c) ≤ coulombCost (a, (b, c)) := by
  rw [real_sum_eq_of_perm u h, cost_eq_of_perm h]

/-- The equality relation is transported at the same time as the inequality. -/
lemma contact_iff_of_perm {x y z a b c : E3} (u : E3 → ℝ)
    (h : List.Perm [x, y, z] [a, b, c]) :
    (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z))) ↔
      ENNReal.ofReal (u a + u b + u c) = coulombCost (a, (b, c)) := by
  rw [real_sum_eq_of_perm u h, cost_eq_of_perm h]

end Problem356.TriplePermutation

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.GoodTypePermutation

/-- A supporting certificate on an ordered component product, with the
one-way contact localization needed for excluding deterministic optimizers. -/
def LocalTypeCertificate (U : Fin 5 → Set E3) (v : Fin 5 → E3 → ℝ)
    (Contact : Triple → Prop) (i j k : Fin 5) : Prop :=
  ∀ x ∈ U i, ∀ y ∈ U j, ∀ z ∈ U k,
    ENNReal.ofReal (v i x + v j y + v k z) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (v i x + v j y + v k z) = coulombCost (x, (y, z)) →
      Contact (x, (y, z)))

variable {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ}
  {Contact : Triple → Prop}

/-- Contact localization is transported along a swap of the first two entries. -/
theorem LocalTypeCertificate.swap_first {i j k : Fin 5}
    (h : LocalTypeCertificate U v Contact i j k)
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c))) :
    LocalTypeCertificate U v Contact j i k := by
  intro x hx y hy z hz
  have hc := h y hy x hx z hz
  rw [add_comm (v i y) (v j x), TriplePermutation.cost_swap_first y x z] at hc
  exact ⟨hc.1, fun heq => hperm (List.Perm.swap x y [z]) (hc.2 heq)⟩

/-- Contact localization is transported along a swap of the last two entries. -/
theorem LocalTypeCertificate.swap_last {i j k : Fin 5}
    (h : LocalTypeCertificate U v Contact i j k)
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c))) :
    LocalTypeCertificate U v Contact i k j := by
  intro x hx y hy z hz
  have hc := h x hx z hz y hy
  have hsum : v i x + v j z + v k y = v i x + v k y + v j z := by ac_rfl
  rw [hsum, TriplePermutation.cost_swap_last x z y] at hc
  exact ⟨hc.1, fun heq => hperm ((List.Perm.swap y z []).cons x) (hc.2 heq)⟩

/-- The two canonical component orders supply every good component type.
No converse from the abstract contact predicate to equality is assumed. -/
theorem certificate_of_good
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    LocalTypeCertificate U v Contact i j k := by
  have h102 := h012.swap_first hperm
  have h021 := h012.swap_last hperm
  have h120 := h102.swap_last hperm
  have h201 := h021.swap_first hperm
  have h210 := h201.swap_last hperm
  have h304 := h034.swap_first hperm
  have h043 := h034.swap_last hperm
  have h340 := h304.swap_last hperm
  have h403 := h043.swap_first hperm
  have h430 := h403.swap_last hperm
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first | assumption | (exfalso; revert hgood; unfold CenterCertificate.Good; decide)

/-- Neighborhood form directly usable by a finite component gluing argument. -/
theorem eventually_certificate_of_good
    (p : Fin 5 → E3) (hU : ∀ i, U i ∈ nhds (p i))
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    ∀ᶠ t : Triple in nhds (p i, (p j, p k)),
      ENNReal.ofReal (v i t.1 + v j t.2.1 + v k t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v i t.1 + v j t.2.1 + v k t.2.2) = coulombCost t →
        Contact t) := by
  have h1 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.1 ∈ U i :=
    (continuous_fst.tendsto _).eventually (hU i)
  have h2 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.2.1 ∈ U j :=
    ((continuous_fst.comp continuous_snd).tendsto _).eventually (hU j)
  have h3 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.2.2 ∈ U k :=
    ((continuous_snd.comp continuous_snd).tendsto _).eventually (hU k)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  exact certificate_of_good hperm h012 h034 i j k hgood
    t.1 ht1 t.2.1 ht2 t.2.2 ht3

end Problem356.GoodTypePermutation

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.IsometryTransport

/-- Apply the same spatial isometry to each particle. -/
def lift (e : E3 ≃ᵢ E3) : Triple ≃ᵐ Triple :=
  e.toHomeomorph.toMeasurableEquiv.prodCongr
    (e.toHomeomorph.toMeasurableEquiv.prodCongr e.toHomeomorph.toMeasurableEquiv)

@[simp] theorem lift_apply (e : E3 ≃ᵢ E3) (t : Triple) :
    lift e t = (e t.1, (e t.2.1, e t.2.2)) := rfl

@[simp] theorem invDistance_apply (e : E3 ≃ᵢ E3) (x y : E3) :
    invDistance (e x) (e y) = invDistance x y := by
  simp only [invDistance, ← dist_eq_norm, e.dist_eq]

@[simp] theorem cost_lift (e : E3 ≃ᵢ E3) (t : Triple) :
    coulombCost (lift e t) = coulombCost t := by
  simp only [coulombCost, lift_apply, tripleFst, tripleSnd, tripleThd,
    invDistance_apply]

theorem lintegral_map_lift (e : E3 ≃ᵢ E3) (pi : Measure Triple) :
    (∫⁻ t, coulombCost t ∂Measure.map (lift e) pi) = ∫⁻ t, coulombCost t ∂pi := by
  rw [lintegral_map_equiv]
  simp only [cost_lift]

theorem coupling_map_lift (e : E3 ≃ᵢ E3) {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) :
    IsThreeCoupling (Measure.map e mu) (Measure.map (lift e) pi) := by
  have := hpi.1
  refine ⟨Measure.isProbabilityMeasure_map (lift e).measurable.aemeasurable, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_tripleFst (lift e).measurable,
      ← hpi.2.1, Measure.map_map e.continuous.measurable measurable_tripleFst]
    rfl
  · rw [Measure.map_map measurable_tripleSnd (lift e).measurable,
      ← hpi.2.2.1, Measure.map_map e.continuous.measurable measurable_tripleSnd]
    rfl
  · rw [Measure.map_map measurable_tripleThd (lift e).measurable,
      ← hpi.2.2.2, Measure.map_map e.continuous.measurable measurable_tripleThd]
    rfl

theorem kantorovichValue_map_le (e : E3 ≃ᵢ E3) (mu : Measure E3) :
    kantorovichValue (Measure.map e mu) ≤ kantorovichValue mu := by
  unfold kantorovichValue
  refine le_iInf fun pi => le_iInf fun hpi => ?_
  calc
    _ ≤ ∫⁻ t, coulombCost t ∂Measure.map (lift e) pi :=
      iInf₂_le _ (coupling_map_lift e hpi)
    _ = _ := lintegral_map_lift e pi

theorem kantorovichValue_map (e : E3 ≃ᵢ E3) (mu : Measure E3) :
    kantorovichValue (Measure.map e mu) = kantorovichValue mu := by
  apply le_antisymm (kantorovichValue_map_le e mu)
  have h := kantorovichValue_map_le e.symm (Measure.map e mu)
  simpa only [Measure.map_map e.symm.continuous.measurable e.continuous.measurable,
    IsometryEquiv.symm_comp_self, Measure.map_id] using h

/-- Transport a bounded-domain supporting potential without changing the cost. -/
theorem supporting_inequality_image (e : E3 ≃ᵢ E3) (U : Set E3) (u : E3 → ℝ)
    (h : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z))) :
    ∀ x ∈ e '' U, ∀ y ∈ e '' U, ∀ z ∈ e '' U,
      ENNReal.ofReal (u (e.symm x) + u (e.symm y) + u (e.symm z)) ≤
        coulombCost (x, (y, z)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  change ENNReal.ofReal (u (e.symm (e x)) + u (e.symm (e y)) +
    u (e.symm (e z))) ≤ coulombCost (lift e (x, (y, z)))
  rw [cost_lift]
  simpa only [e.symm_apply_apply] using h x hx y hy z hz

theorem supporting_equality_image (e : E3 ≃ᵢ E3) (u : E3 → ℝ) (t : Triple) :
    coulombCost (lift e t) = ENNReal.ofReal
      (u (e.symm (tripleFst (lift e t))) +
        u (e.symm (tripleSnd (lift e t))) + u (e.symm (tripleThd (lift e t)))) ↔
    coulombCost t = ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) := by
  rw [cost_lift]
  simp only [lift_apply, tripleFst, tripleSnd, tripleThd, e.symm_apply_apply]

/-- Orthogonal changes of variables transport a density without a Jacobian factor. -/
theorem map_densityMeasure (e : E3 ≃ₗᵢ[ℝ] E3) (rho : E3 → ℝ)
    (hrho : Measurable rho) :
    Measure.map e (densityMeasure rho) = densityMeasure (fun x => rho (e.symm x)) := by
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs, densityMeasure,
    withDensity_apply _ (e.continuous.measurable hs), densityMeasure,
    withDensity_apply _ hs]
  conv_rhs => rw [← e.measurePreserving.map_eq]
  have hm : Measurable (fun a : E3 => ENNReal.ofReal (rho (e.symm a))) :=
    (hrho.comp e.symm.continuous.measurable).ennreal_ofReal
  rw [setLIntegral_map (μ := (volume : Measure E3)) hs hm e.continuous.measurable]
  simp only [e.symm_apply_apply]

theorem smoothDensity_comp_symm (e : E3 ≃ₗᵢ[ℝ] E3) {rho : E3 → ℝ}
    (hrho : IsSmoothCompactProbabilityDensity rho) :
    IsSmoothCompactProbabilityDensity (fun x => rho (e.symm x)) := by
  refine ⟨fun x => hrho.1 _, hrho.2.1.comp e.symm.contDiff,
    hrho.2.2.1.comp_homeomorph e.symm.toHomeomorph,
    hrho.2.2.2.1.comp e.symm.contDiff,
    hrho.2.2.2.2.1.comp_homeomorph e.symm.toHomeomorph, ?_⟩
  rw [e.symm.measurePreserving.integral_comp e.symm.toMeasurableEquiv.measurableEmbedding]
  exact hrho.2.2.2.2.2

/-- Exchange the first and second Euclidean axes, leaving the third fixed. -/
def axisSwap : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 1)

@[simp] theorem axisSwap_single (i : Fin 3) (a : ℝ) :
    axisSwap (PiLp.single 2 i a) = PiLp.single 2 (Equiv.swap 0 1 i) a := by
  exact LinearIsometryEquiv.piLpCongrLeft_single _ _ _

@[simp] theorem axisSwap_zero : axisSwap (0 : E3) = 0 := map_zero axisSwap

@[simp] theorem axisSwap_first :
    axisSwap (PiLp.single 2 (0 : Fin 3) (1 : ℝ)) = PiLp.single 2 (1 : Fin 3) (1 : ℝ) := by
  simp

@[simp] theorem axisSwap_second :
    axisSwap (PiLp.single 2 (1 : Fin 3) (1 : ℝ)) = PiLp.single 2 (0 : Fin 3) (1 : ℝ) := by
  simp

end Problem356.IsometryTransport

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace Problem356.JacobianSquareRoot

/-- The determinant is a smooth polynomial in the matrix entries. -/
theorem contDiff_matrix_det {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (n : WithTop ENat) : ContDiff ℝ n (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change ContDiff ℝ n (fun M : Matrix ι ι ℝ => M.det)
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact contDiff_apply_apply ℝ ℝ (σ i) i

/-- The determinant is smooth on continuous linear endomorphisms in finite dimension. -/
theorem contDiff_clm_det {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : WithTop ENat) :
    ContDiff ℝ n (fun A : E →L[ℝ] E => A.det) := by
  let b := Module.finBasis ℝ E
  have hM : ContDiff ℝ n (fun A : E →L[ℝ] E =>
      LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)) :=
    (((LinearMap.toMatrix b b).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap).contDiff
  simpa only [Function.comp_def, LinearMap.det_toMatrix] using
    (contDiff_matrix_det n).comp hM

/-- Nonzero determinants yield smooth absolute-Jacobian square roots. -/
theorem contDiffOn_sqrt_abs_det
    {D : Type uD} {E : Type uE} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : WithTop ENat} {U : Set D} {A : D → E →L[ℝ] E}
    (hA : ContDiffOn ℝ n A U) (hdet : ∀ x ∈ U, (A x).det ≠ 0) :
    ContDiffOn ℝ n (fun x => Real.sqrt |(A x).det|) U := by
  have hd : ContDiffOn ℝ n (fun x => (A x).det) U :=
    (contDiff_clm_det n).fun_comp_contDiffOn hA
  have ha : ContDiffOn ℝ n (fun x => |(A x).det|) U := by
    simpa only [Real.norm_eq_abs] using hd.norm ℝ hdet
  exact ha.sqrt (fun x hx => abs_ne_zero.mpr (hdet x hx))

/-- Invertibility of an endomorphism implies its Jacobian determinant is nonzero. -/
theorem det_ne_zero_of_isInvertible
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E →L[ℝ] E} (hA : A.IsInvertible) : A.det ≠ 0 := by
  rcases hA with ⟨e, rfl⟩
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- Smoothness of the square root of the absolute derivative determinant on an open set. -/
theorem contDiffOn_sqrt_abs_det_fderiv
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} {F : E → E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) F U)
    (hdet : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun x => Real.sqrt |(fderiv ℝ F x).det|) U := by
  apply contDiffOn_sqrt_abs_det
  · exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hF).2
  · exact hdet

/-- Multiplication by the composed source amplitude gives the local transported amplitude. -/
theorem contDiffOn_transportedAmplitude
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} {F : E → E} {g : E → ℝ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) F U)
    (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hdet : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun x => g (F x) * Real.sqrt |(fderiv ℝ F x).det|) U :=
  (hg.fun_comp_contDiffOn hF).mul (contDiffOn_sqrt_abs_det_fderiv hU hF hdet)

/-- An eventually defined differentiable left inverse forces a nonzero derivative determinant. -/
theorem det_fderiv_ne_zero_of_eventual_leftInverse
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (F x))
    (hGF : ∀ᶠ y in nhds x, G (F y) = y) : (fderiv ℝ F x).det ≠ 0 := by
  have hc : (fderiv ℝ G (F x)).comp (fderiv ℝ F x) =
      ContinuousLinearMap.id ℝ E :=
    (hG.hasFDerivAt.comp x hF.hasFDerivAt).unique
      ((hasFDerivAt_id x).congr_of_eventuallyEq hGF)
  have hprod := congrArg (fun A : E →L[ℝ] E => A.det) hc
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hprod
  change (fderiv ℝ G (F x)).det * (fderiv ℝ F x).det = 1 at hprod
  intro hz
  rw [hz, mul_zero] at hprod
  exact zero_ne_one hprod

/-- Both smooth directions of an open partial homeomorphism have nonvanishing inverse Jacobian. -/
theorem det_fderiv_symm_ne_zero
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    {y : E} (hy : y ∈ e.target) : (fderiv ℝ e.symm y).det ≠ 0 := by
  apply det_fderiv_ne_zero_of_eventual_leftInverse
    ((he'.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp))
    ((he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp))
  exact e.eventually_right_inverse hy

/-- Smooth inverse-Jacobian factor for a smooth open partial diffeomorphism. -/
theorem contDiffOn_sqrt_abs_det_fderiv_symm
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(fderiv ℝ e.symm y).det|) e.target :=
  contDiffOn_sqrt_abs_det_fderiv e.open_target he'
    (fun _ hy => det_fderiv_symm_ne_zero e he he' hy)

/-- Local transported amplitudes are smooth, with no separate Jacobian hypothesis. -/
theorem contDiffOn_transportedAmplitude_symm
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    {g : E → ℝ} (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => g (e.symm y) * Real.sqrt |(fderiv ℝ e.symm y).det|) e.target :=
  (hg.fun_comp_contDiffOn he').mul (contDiffOn_sqrt_abs_det_fderiv_symm e he he')

/-- The transported amplitude squares to the Jacobian-weighted source density. -/
theorem transportedAmplitude_sq
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (g : E → ℝ) (y : E) :
    (g (F y) * Real.sqrt |(fderiv ℝ F y).det|) ^ 2 =
      |(fderiv ℝ F y).det| * (g (F y)) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (abs_nonneg _), mul_comm]

end Problem356.JacobianSquareRoot

end

end OAI
end
end

section
section
namespace OAI


/-!
# The local-homeomorphism selection obstruction

The local branch maps need not be measurable away from their source. Extending
them by a constant, then using concentration of the reference measure, gives
the exact obstruction stated for the original maps and their pushforwards.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem356.LocalSplitting

open LocalBranchMeasure Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [TopologicalSpace α] [MeasurableSpace α]
  [BorelSpace α] [MeasurableEq α] [Fintype ι]

/-- Local homeomorphic branches on disjoint components cannot admit a
measure-preserving deterministic selector when the central weight is larger. -/
theorem no_preserving_local_branch_selection
    (z : α) (e : ι → OpenPartialHomeomorph α α)
    {ν : Measure α} [IsFiniteMeasure ν] {B : Set α} {c d : ℝ≥0∞}
    (hν : ν univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hSource : ∀ i, B ⊆ (e i).source)
    (hCentral : ∀ i, Disjoint B (e i '' B))
    (hPair : Pairwise fun i j => Disjoint (e i '' B) (e j '' B))
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧
      Measure.map T (splitMeasure ν c (fun _ => d) (fun i => e i)) =
        splitMeasure ν c (fun _ => d) (fun i => e i) ∧
      (∀ᵐ x ∂ν, ∃ i, T x = e i x) := by
  let H : ι → α → α := fun i => extendedBranch (e i) z
  have hImage : ∀ i S, S ⊆ B → H i '' S = e i '' S := by
    intro i S hS
    exact extendedBranch_image (e i) z (hS.trans (hSource i))
  have hMap : ∀ i, Measure.map (H i) ν = Measure.map (e i) ν := by
    intro i
    apply map_extendedBranch (e i) z ν
    exact hfull.mono fun x hx => hSource i hx
  have hMixture : splitMeasure ν c (fun _ => d) H =
      splitMeasure ν c (fun _ => d) (fun i => e i) := by
    unfold splitMeasure
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hMap i]
  have hNo := no_preserving_splitMeasure_selection (H := H) hν hB hfull
    (fun i => measurable_extendedBranch (e i) z)
    (fun i => injOn_extendedBranch (e i) z (hSource i))
    (fun i S hS hSB => measurableSet_extendedBranch_image (e i) z hS
      (hSB.trans (hSource i)))
    (fun i => by rw [hImage i B subset_rfl]; exact hCentral i)
    (fun i j hij => by
      change Disjoint (H i '' B) (H j '' B)
      rw [hImage i B subset_rfl, hImage j B subset_rfl]
      exact hPair hij) hdc
  rintro ⟨T, hT, hPres, hSel⟩
  apply hNo
  refine ⟨T, hT, ?_, ?_⟩
  · simpa only [hMixture] using hPres
  · filter_upwards [hfull, hSel] with x hx hxSel
    obtain ⟨i, hi⟩ := hxSel
    refine ⟨i, ?_⟩
    exact hi.trans (extendedBranch_apply_of_mem (e i) z (hSource i hx)).symm

/-- The coefficients and four branches used by the Coulomb counterexample. -/
theorem no_preserving_four_local_branches
    (z : α) (e : Fin 4 → OpenPartialHomeomorph α α)
    {ν : Measure α} [IsProbabilityMeasure ν] {B : Set α}
    (hB : MeasurableSet B) (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hSource : ∀ i, B ⊆ (e i).source)
    (hCentral : ∀ i, Disjoint B (e i '' B))
    (hPair : Pairwise fun i j => Disjoint (e i '' B) (e j '' B)) :
    ¬ ∃ T : α → α, Measurable T ∧
      Measure.map T (splitMeasure ν (1 / 3) (fun _ => 1 / 6) (fun i => e i)) =
        splitMeasure ν (1 / 3) (fun _ => 1 / 6) (fun i => e i) ∧
      (∀ᵐ x ∂ν, ∃ i, T x = e i x) := by
  apply no_preserving_local_branch_selection z e (by simp) hB hfull hSource hCentral hPair
  norm_num

end Problem356.LocalSplitting

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- The independent triple is always an admissible coupling of a probability. -/
theorem isThreeCoupling_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    IsThreeCoupling mu (mu.prod (mu.prod mu)) := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · change Measure.map Prod.fst (mu.prod (mu.prod mu)) = mu
    simp
  · change Measure.map (Prod.fst ∘ Prod.snd) (mu.prod (mu.prod mu)) = mu
    rw [← Measure.map_map measurable_fst measurable_snd]
    simp
  · change Measure.map (Prod.snd ∘ Prod.snd) (mu.prod (mu.prod mu)) = mu
    rw [← Measure.map_map measurable_snd measurable_snd]
    simp

/-- The Coulomb pair interaction is measurable, including its infinite diagonal. -/
private theorem measurable_pairInteraction :
    Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  fun_prop

theorem map_pair_fst_snd_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    Measure.map (fun t : Triple => (t.1, t.2.1)) (mu.prod (mu.prod mu)) =
      mu.prod mu := by
  change Measure.map (Prod.map id Prod.fst) (mu.prod (mu.prod mu)) = mu.prod mu
  rw [← Measure.map_prod_map mu (mu.prod mu) measurable_id measurable_fst]
  simp

theorem map_pair_fst_thd_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    Measure.map (fun t : Triple => (t.1, t.2.2)) (mu.prod (mu.prod mu)) =
      mu.prod mu := by
  change Measure.map (Prod.map id Prod.snd) (mu.prod (mu.prod mu)) = mu.prod mu
  rw [← Measure.map_prod_map mu (mu.prod mu) measurable_id measurable_snd]
  simp

theorem lintegral_three_pairs_prod (mu : Measure E3) [IsProbabilityMeasure mu]
    (f : E3 × E3 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t : Triple, f (t.1, t.2.1) + f (t.1, t.2.2) + f t.2
      ∂(mu.prod (mu.prod mu))) = 3 * ∫⁻ p, f p ∂(mu.prod mu) := by
  have h12 : (∫⁻ t : Triple, f (t.1, t.2.1) ∂(mu.prod (mu.prod mu))) =
      ∫⁻ p, f p ∂(mu.prod mu) := by
    rw [← lintegral_map (g := fun t : Triple => (t.1, t.2.1)) hf (by fun_prop),
      map_pair_fst_snd_prod]
  have h13 : (∫⁻ t : Triple, f (t.1, t.2.2) ∂(mu.prod (mu.prod mu))) =
      ∫⁻ p, f p ∂(mu.prod mu) := by
    rw [← lintegral_map (g := fun t : Triple => (t.1, t.2.2)) hf (by fun_prop),
      map_pair_fst_thd_prod]
  have h23 : (∫⁻ t : Triple, f t.2 ∂(mu.prod (mu.prod mu))) =
      ∫⁻ p, f p ∂(mu.prod mu) := by
    rw [← lintegral_map hf measurable_snd]
    simp
  rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop), h12, h13, h23]
  ring

/-- The pair interaction energy of an independently sampled pair. -/
def coulombPairEnergy (mu : Measure E3) : ℝ≥0∞ :=
  ∫⁻ p : E3 × E3, invDistance p.1 p.2 ∂(mu.prod mu)

theorem lintegral_coulombCost_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    (∫⁻ t, coulombCost t ∂(mu.prod (mu.prod mu))) = 3 * coulombPairEnergy mu := by
  exact lintegral_three_pairs_prod mu _ measurable_pairInteraction

theorem kantorovichValue_le_three_pairEnergy (mu : Measure E3)
    [IsProbabilityMeasure mu] :
    kantorovichValue mu ≤ 3 * coulombPairEnergy mu := by
  rw [← lintegral_coulombCost_prod]
  exact iInf_le_of_le (mu.prod (mu.prod mu))
    (iInf_le_of_le (isThreeCoupling_prod mu) le_rfl)

theorem kantorovichValue_lt_top_of_pairEnergy_lt_top (mu : Measure E3)
    [IsProbabilityMeasure mu] (h : coulombPairEnergy mu < ⊤) :
    kantorovichValue mu < ⊤ := by
  apply lt_of_le_of_lt (kantorovichValue_le_three_pairEnergy mu)
  exact ENNReal.mul_lt_top (by norm_num) h

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356

theorem integrableOn_inv_norm_ball (r : ℝ) :
    IntegrableOn (fun x : E3 => ‖x‖⁻¹) (Metric.ball 0 r) volume := by
  refine integrableOn_ball_of_norm_le_rpow (by simp [E3]) (C := 1) (α := 1)
    (by norm_num [E3]) ?_ ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp [Real.rpow_neg_one])
  · fun_prop

/-- The Coulomb singularity is integrable on every bounded ball in dimension three. -/
theorem lintegral_invDistance_zero_ball_lt_top (r : ℝ) :
    (∫⁻ x in Metric.ball (0 : E3) r, invDistance 0 x ∂volume) < ⊤ := by
  have heq : (fun x : E3 => invDistance 0 x) =ᵐ[
      (volume : Measure E3).restrict (Metric.ball 0 r)]
      (fun x => ENNReal.ofReal (‖x‖⁻¹)) := by
    filter_upwards [ae_restrict_of_ae ((volume : Measure E3).ae_ne 0)] with x hx
    simp [invDistance, ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hx)]
  rw [lintegral_congr_ae heq]
  exact (integrableOn_inv_norm_ball r).lintegral_lt_top

/-- Local part of the singular kernel; the omitted tail is bounded by one. -/
def localCoulombKernel (x : E3) : ℝ≥0∞ :=
  (Metric.ball (0 : E3) 1).indicator (fun x => invDistance 0 x) x

theorem measurable_localCoulombKernel : Measurable localCoulombKernel := by
  unfold localCoulombKernel
  apply Measurable.indicator _ measurableSet_ball
  unfold invDistance
  fun_prop

theorem lintegral_localCoulombKernel_lt_top :
    (∫⁻ x : E3, localCoulombKernel x ∂volume) < ⊤ := by
  simp only [localCoulombKernel, lintegral_indicator measurableSet_ball]
  exact lintegral_invDistance_zero_ball_lt_top 1

theorem densityMeasure_le_smul_volume_of_le {rho : E3 → ℝ} {M : ℝ}
    (h : ∀ x, rho x ≤ M) :
    densityMeasure rho ≤ ENNReal.ofReal M • (volume : Measure E3) := by
  have hb := withDensity_mono (μ := (volume : Measure E3))
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (h x))
  simpa [densityMeasure, withDensity_const] using hb

theorem invDistance_le_localCoulombKernel_add_one (x y : E3) :
    invDistance x y ≤ localCoulombKernel (x - y) + 1 := by
  by_cases h : x - y ∈ Metric.ball (0 : E3) 1
  · simp only [localCoulombKernel, indicator_of_mem h, invDistance, zero_sub, norm_neg]
    exact le_add_of_nonneg_right zero_le_one
  · simp only [localCoulombKernel, indicator_of_notMem h, zero_add]
    apply ENNReal.inv_le_one.mpr
    have hn : 1 ≤ ‖x - y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using h
    exact_mod_cast (ENNReal.ofReal_le_ofReal hn)

/-- Uniform control of the Coulomb potential for a probability with bounded density. -/
theorem lintegral_invDistance_le_of_measure_le (mu : Measure E3)
    [IsProbabilityMeasure mu] {C : ℝ≥0∞}
    (hmu : mu ≤ C • (volume : Measure E3)) (x : E3) :
    (∫⁻ y, invDistance x y ∂mu) ≤
      C * (∫⁻ y : E3, localCoulombKernel y ∂volume) + 1 := by
  calc
    (∫⁻ y, invDistance x y ∂mu) ≤
        ∫⁻ y, localCoulombKernel (x - y) + 1 ∂mu :=
      lintegral_mono (invDistance_le_localCoulombKernel_add_one x)
    _ = (∫⁻ y, localCoulombKernel (x - y) ∂mu) + 1 := by
      rw [lintegral_add_left (f := fun y : E3 => localCoulombKernel (x - y))
        (measurable_localCoulombKernel.comp (by fun_prop))]
      simp
    _ ≤ (∫⁻ y, localCoulombKernel (x - y) ∂(C • (volume : Measure E3))) + 1 := by
      exact add_le_add (lintegral_mono' hmu le_rfl) le_rfl
    _ = C * (∫⁻ y : E3, localCoulombKernel y ∂volume) + 1 := by
      rw [lintegral_smul_measure, lintegral_sub_left_eq_self]
      rfl

theorem coulombPairEnergy_lt_top_of_measure_le (mu : Measure E3)
    [IsProbabilityMeasure mu] {C : ℝ≥0∞} (hC : C < ⊤)
    (hmu : mu ≤ C • (volume : Measure E3)) :
    coulombPairEnergy mu < ⊤ := by
  have hm : Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
    unfold invDistance
    fun_prop
  unfold coulombPairEnergy
  rw [lintegral_prod _ hm.aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono (lintegral_invDistance_le_of_measure_le mu hmu))
  simp only [lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hC lintegral_localCoulombKernel_lt_top,
    ENNReal.one_lt_top⟩

theorem coulombPairEnergy_densityMeasure_lt_top_of_bounded {rho : E3 → ℝ}
    [IsProbabilityMeasure (densityMeasure rho)] {M : ℝ} (h : ∀ x, rho x ≤ M) :
    coulombPairEnergy (densityMeasure rho) < ⊤ := by
  exact coulombPairEnergy_lt_top_of_measure_le _ ENNReal.ofReal_lt_top
    (densityMeasure_le_smul_volume_of_le h)

theorem coulombPairEnergy_densityMeasure_lt_top {rho : E3 → ℝ}
    [IsProbabilityMeasure (densityMeasure rho)]
    (h : IsSmoothCompactProbabilityDensity rho) :
    coulombPairEnergy (densityMeasure rho) < ⊤ := by
  obtain ⟨M, hM⟩ := h.2.1.continuous.bounded_above_of_compact_support h.2.2.1
  apply coulombPairEnergy_densityMeasure_lt_top_of_bounded (M := M)
  intro x
  exact (le_abs_self (rho x)).trans (hM x)

theorem kantorovichValue_densityMeasure_lt_top {rho : E3 → ℝ}
    [IsProbabilityMeasure (densityMeasure rho)]
    (h : IsSmoothCompactProbabilityDensity rho) :
    kantorovichValue (densityMeasure rho) < ⊤ := by
  exact kantorovichValue_lt_top_of_pairEnergy_lt_top _
    (coulombPairEnergy_densityMeasure_lt_top h)

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.SmoothBranchMarginal

theorem squareDensity_probability {g : E3 → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hmass : (∫ x : E3, g x ^ 2) = 1) :
    IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) := by
  have hcompact : HasCompactSupport (fun x => g x ^ 2) := by
    simpa only [Function.comp_def] using
      hgc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hint : Integrable (fun x => g x ^ 2) (volume : Measure E3) :=
    (hg.pow 2).integrable_of_hasCompactSupport hcompact
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => sq_nonneg (g x))),
    hmass, ENNReal.ofReal_one]

theorem squareDensity_ae_tsupport {g : E3 → ℝ} (hg : Measurable g) :
    ∀ᵐ x ∂densityMeasure (fun x => g x ^ 2), x ∈ tsupport g := by
  rw [densityMeasure, ae_withDensity_iff ((hg.pow_const 2).ennreal_ofReal)]
  apply ae_of_all
  intro x hx
  apply subset_tsupport g
  intro hgx
  exact hx (by simp [hgx])

theorem square_integral_eq_one {g : E3 → ℝ} (hg : Continuous g)
    [IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2))] :
    (∫ x : E3, g x ^ 2) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun x => sq_nonneg (g x))) (hg.pow 2).aestronglyMeasurable]
  have hm := measure_univ (μ := densityMeasure (fun x => g x ^ 2))
  simpa only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hm, ENNReal.toReal_one] using congrArg ENNReal.toReal hm

/-- A normalized smooth amplitude transports to another normalized smooth
amplitude. The derivative and its smooth square-root determinant are explicit
inputs, so the result is compatible with independently constructed local charts. -/
theorem transported_square_amplitude
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ e.source)
    (hmass : (∫ x : E3, g x ^ 2) = 1)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y)
    (hJ : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D y).det|) e.target) :
    ∃ q : E3 → ℝ,
      (∀ y, 0 ≤ q y) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q ∧
      HasCompactSupport q ∧
      tsupport q ⊆ e '' tsupport g ∧
      (∫ y : E3, q y ^ 2) = 1 ∧
      Measure.map (LocalBranchMeasure.extendedBranch e 0)
        (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) := by
  let q := localTransportAmplitude e g (fun y => Real.sqrt |(D y).det|)
  have hq : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q :=
    contDiff_localTransportAmplitude e hg hgc hgs he hJ
  have hm : Measure.map (LocalBranchMeasure.extendedBranch e 0)
      (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) := by
    rw [LocalBranchMeasure.map_extendedBranch e 0 _
      ((squareDensity_ae_tsupport hg.continuous.measurable).mono (fun x hx => hgs hx))]
    exact map_squareDensity_localHomeomorph e g hgs D hD
  have := squareDensity_probability hg.continuous hgc hmass
  have : IsProbabilityMeasure (densityMeasure (fun y => q y ^ 2)) := by
    rw [← hm]
    exact Measure.isProbabilityMeasure_map (LocalBranchMeasure.measurable_extendedBranch e 0).aemeasurable
  refine ⟨q, localTransportAmplitude_nonneg e hg0 (fun y _ => Real.sqrt_nonneg _), hq,
    hasCompactSupport_localTransportAmplitude e _ hgc hgs,
    tsupport_localTransportAmplitude_subset e _ hgc hgs, ?_, hm⟩
  exact square_integral_eq_one hq.continuous

/-- The five component weights are fixed by the counterexample construction. -/
def componentWeight : Option (Fin 4) → ℝ
  | none => 1 / 3
  | some _ => 1 / 6

def componentAmplitude (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ) :
    Option (Fin 4) → E3 → ℝ
  | none => g
  | some i => q i

def componentRegion (B : Set E3) (e : Fin 4 → OpenPartialHomeomorph E3 E3) :
    Option (Fin 4) → Set E3
  | none => B
  | some i => e i '' B

def marginalDensity (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ) (x : E3) : ℝ :=
  ∑ i : Option (Fin 4), componentWeight i * componentAmplitude g q i x ^ 2

def NormalizedAmplitude (g : E3 → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧
  ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
  HasCompactSupport g ∧ (∫ x : E3, g x ^ 2) = 1

theorem marginalDensity_smooth {B : Set E3}
    {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {g : E3 → ℝ} {q : Fin 4 → E3 → ℝ}
    (hg : NormalizedAmplitude g) (hq : ∀ i, NormalizedAmplitude (q i))
    (hgs : tsupport g ⊆ B) (hqs : ∀ i, tsupport (q i) ⊆ e i '' B)
    (hdisj : Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j))) :
    IsSmoothCompactProbabilityDensity (marginalDensity g q) := by
  apply isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
    Finset.univ componentWeight (componentAmplitude g q)
  · intro i _
    cases i <;> norm_num [componentWeight]
  · intro i _
    cases i with
    | none => exact hg.1
    | some i => exact (hq i).1
  · intro i _
    cases i with
    | none => exact hg.2.1
    | some i => exact (hq i).2.1
  · intro i _
    cases i with
    | none => exact hg.2.2.1
    | some i => exact (hq i).2.2.1
  · have hsub : ∀ i, Function.support (componentAmplitude g q i) ⊆ componentRegion B e i := by
      intro i
      cases i with
      | none => exact (subset_tsupport g).trans hgs
      | some i => exact (subset_tsupport (q i)).trans (hqs i)
    intro i _ j _ hij
    exact (hdisj hij).mono (hsub i) (hsub j)
  · intro i _
    cases i with
    | none => exact hg.2.2.2
    | some i => exact (hq i).2.2.2
  · norm_num [componentWeight, Fintype.sum_option]

theorem marginalDensity_measure {g : E3 → ℝ} {q : Fin 4 → E3 → ℝ}
    (hg : Measurable g) (hq : ∀ i, Measurable (q i)) :
    densityMeasure (marginalDensity g q) =
      (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
      ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) • densityMeasure (fun x => q i x ^ 2) := by
  unfold marginalDensity
  rw [densityMeasure_sum_weighted_squares]
  · simp [Fintype.sum_option, componentWeight, componentAmplitude]
  · intro i _
    cases i <;> norm_num [componentWeight]
  · intro i _
    cases i with
    | none => exact hg
    | some i => exact hq i

/-- Construct the actual smooth five-component marginal from local branch
charts on a common ball. All square amplitudes and their exact pushforward
laws are supplied in the conclusion. -/
theorem exists_smooth_branch_marginal
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    (D : Fin 4 → E3 → E3 →L[ℝ] E3)
    (hD : ∀ i y, y ∈ (e i).target → HasFDerivAt (e i).symm (D i y) y)
    (hJ : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D i y).det|) (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by
  obtain ⟨g, hg0, hg, hgc, hgs, hgm⟩ := exists_normalized_smooth_square_in_ball c hr
  have hqexists := fun i => transported_square_amplitude (e i) hg0 hg hgc
    (hgs.trans (hsource i)) hgm (he i) (D i) (hD i) (hJ i)
  choose q hq0 hq hqc hqs hqm hqmap using hqexists
  have hgn : NormalizedAmplitude g := ⟨hg0, hg, hgc, hgm⟩
  have hqn : ∀ i, NormalizedAmplitude (q i) := fun i => ⟨hq0 i, hq i, hqc i, hqm i⟩
  have hqsub : ∀ i, tsupport (q i) ⊆ e i '' Metric.ball c r := fun i =>
    (hqs i).trans (Set.image_mono hgs)
  refine ⟨g, q, hgn, hgs, fun i => ⟨hqn i, hqsub i⟩,
    squareDensity_probability hg.continuous hgc hgm,
    marginalDensity_smooth hgn hqn hgs hqsub hdisj, ?_⟩
  rw [marginalDensity_measure hg.continuous.measurable (fun i => (hq i).continuous.measurable)]
  simp_rw [hqmap]

/-- The preceding construction only needs smoothness in both directions of
the local charts; no determinant or change-of-variables premise remains. -/
theorem exists_smooth_branch_marginal_of_smooth_charts
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by
  apply exists_smooth_branch_marginal c hr e hsource hdisj he'
    (fun i y => fderiv ℝ (e i).symm y)
  · intro i y hy
    exact (((he' i).contDiffAt ((e i).open_target.mem_nhds hy)).differentiableAt
      (by simp)).hasFDerivAt
  · intro i
    exact JacobianSquareRoot.contDiffOn_sqrt_abs_det_fderiv_symm (e i) (he i) (he' i)

/-- The construction data expected by the measure-level nonattainment and
separated-support approximation arguments. -/
structure SmoothBranchData (B : Set E3) where
  rho : E3 → ℝ
  nu : Measure E3
  branch : Fin 4 → E3 → E3
  compactCore : Set E3
  density_smooth : IsSmoothCompactProbabilityDensity rho
  probability : IsProbabilityMeasure nu
  measurable_central : MeasurableSet B
  core_compact : IsCompact compactCore
  core_subset : compactCore ⊆ B
  core_full : ∀ᵐ x ∂nu, x ∈ compactCore
  branch_measurable : ∀ i, Measurable (branch i)
  branch_injective : ∀ i, Set.InjOn (branch i) B
  branch_image_measurable : ∀ i S, MeasurableSet S → S ⊆ B →
    MeasurableSet (branch i '' S)
  branch_continuous : ∀ i, ContinuousOn (branch i) compactCore
  component_disjoint : Pairwise (fun i j : Option (Fin 4) =>
    Disjoint (i.elim B (fun k => branch k '' B)) (j.elim B (fun k => branch k '' B)))
  density_eq : densityMeasure rho =
    (1 / 3 : ℝ≥0∞) • nu + ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) • Measure.map (branch i) nu

theorem SmoothBranchData.central_full {B : Set E3} (d : SmoothBranchData B) :
    ∀ᵐ x ∂d.nu, x ∈ B := d.core_full.mono (fun _ hx => d.core_subset hx)

theorem SmoothBranchData.central_disjoint {B : Set E3} (d : SmoothBranchData B) (i : Fin 4) :
    Disjoint B (d.branch i '' B) :=
  d.component_disjoint (i := none) (j := some i) (by simp)

theorem SmoothBranchData.outer_disjoint {B : Set E3} (d : SmoothBranchData B) :
    Pairwise (fun i j => Disjoint (d.branch i '' B) (d.branch j '' B)) := by
  intro i j hij
  exact d.component_disjoint (i := some i) (j := some j) (by simpa using hij)

/-- The explicit four-term form is definitionally the canonical branch marginal. -/
theorem SmoothBranchData.density_eq_four {B : Set E3} (d : SmoothBranchData B) :
    densityMeasure d.rho = (1 / 3 : ℝ≥0∞) • d.nu + (1 / 6 : ℝ≥0∞) •
      (Measure.map (d.branch 0) d.nu + Measure.map (d.branch 1) d.nu +
        Measure.map (d.branch 2) d.nu + Measure.map (d.branch 3) d.nu) := by
  rw [d.density_eq]
  simp [Fin.sum_univ_succ, smul_add, add_assoc]

/-- A measure-level packaging of the actual smooth marginal construction.
All branch extensions are globally measurable, while continuity is retained
on the compact support where it is needed. -/
theorem exists_smoothBranchData_of_smooth_charts
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target) :
    ∃ d : SmoothBranchData (Metric.ball c r),
      ∀ i x, x ∈ Metric.ball c r → d.branch i x = e i x := by
  obtain ⟨g, q, hg, hgs, _, hprob, hrho, hmeasure⟩ :=
    exists_smooth_branch_marginal_of_smooth_charts c hr e hsource hdisj he he'
  let H : Fin 4 → E3 → E3 := fun i => LocalBranchMeasure.extendedBranch (e i) 0
  have himage : ∀ i, H i '' Metric.ball c r = e i '' Metric.ball c r :=
    fun i => LocalBranchMeasure.extendedBranch_image (e i) 0 (hsource i)
  refine ⟨{
    rho := marginalDensity g q
    nu := densityMeasure (fun x => g x ^ 2)
    branch := H
    compactCore := tsupport g
    density_smooth := hrho
    probability := hprob
    measurable_central := Metric.isOpen_ball.measurableSet
    core_compact := hg.2.2.1
    core_subset := hgs
    core_full := squareDensity_ae_tsupport hg.2.1.continuous.measurable
    branch_measurable := fun i => LocalBranchMeasure.measurable_extendedBranch (e i) 0
    branch_injective := fun i => LocalBranchMeasure.injOn_extendedBranch (e i) 0 (hsource i)
    branch_image_measurable := ?_
    branch_continuous := ?_
    component_disjoint := ?_
    density_eq := hmeasure
  }, ?_⟩
  · intro i S hS hSB
    exact LocalBranchMeasure.measurableSet_extendedBranch_image (e i) 0 hS
      (hSB.trans (hsource i))
  · intro i
    apply ((e i).continuousOn.mono (hgs.trans (hsource i))).congr
    intro x hx
    exact LocalBranchMeasure.extendedBranch_apply_of_mem (e i) 0 (hsource i (hgs hx))
  · intro i j hij
    have h := hdisj hij
    cases i <;> cases j <;> simpa only [Option.elim, componentRegion, himage] using h
  · intro i x hx
    exact LocalBranchMeasure.extendedBranch_apply_of_mem (e i) 0 (hsource i hx)

end Problem356.SmoothBranchMarginal

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set
open scoped InnerProductSpace

namespace Problem356

variable (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The sum of the two component inner products, bundled for the usual
(max-norm) product. No inner-product-space instance on the product is used. -/
def stateDual : (E × F) →L[ℝ] ((E × F) →L[ℝ] ℝ) :=
  (((ContinuousLinearMap.compL ℝ (E × F) E ℝ).flip
      (ContinuousLinearMap.fst ℝ E F)).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.fst ℝ E F))) +
  (((ContinuousLinearMap.compL ℝ (E × F) F ℝ).flip
      (ContinuousLinearMap.snd ℝ E F)).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ E F)))

@[simp] theorem stateDual_apply (u v : E × F) :
    stateDual E F u v = ⟪u.1, v.1⟫_ℝ + ⟪u.2, v.2⟫_ℝ := by
  rfl

theorem stateDual_apply_comm (u v : E × F) :
    stateDual E F u v = stateDual E F v u := by
  simp only [stateDual_apply, real_inner_comm]

/-- Differentiating the scalar representative of a product-state gradient. -/
theorem hasFDerivAt_stateDual_comp {P : Type uP} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {G : P → E × F} {G' : P →L[ℝ] E × F} {p : P}
    (hG : HasFDerivAt G G' p) :
    HasFDerivAt (fun q => stateDual E F (G q)) ((stateDual E F).comp G') p :=
  by
  exact HasFDerivAt.comp (𝕜 := ℝ) (g := stateDual E F) p
    ((stateDual E F).hasFDerivAt (x := G p)) hG

/-- The quadratic form of the scalar Hessian agrees with the product-state
coercivity expression, with the argument order used by matrix certificates. -/
theorem stateDual_comp_quadratic (A : (E × F) →L[ℝ] E × F) (v : E × F) :
    ((stateDual E F).comp A) v v =
      ⟪v.1, (A v).1⟫_ℝ + ⟪v.2, (A v).2⟫_ℝ := by
  simp only [ContinuousLinearMap.comp_apply, stateDual_apply, real_inner_comm]

/-- A gradient with positive product-state Jacobian gives strict convexity of
its scalar potential. This bridges matrix coercivity of the stationarity map
to positivity of the scalar Hessian. -/
theorem strictConvexOn_of_positive_stateGradient
    {s : Set (E × F)} {f : E × F → ℝ} {G : E × F → E × F}
    {A : E × F → (E × F) →L[ℝ] E × F}
    (hs : Convex ℝ s) (hsopen : IsOpen s)
    (hf : ∀ z ∈ s, HasFDerivAt f (stateDual E F (G z)) z)
    (hG : ∀ z ∈ s, HasFDerivAt G (A z) z)
    (hpos : ∀ z ∈ s, ∀ v : E × F, v ≠ 0 →
      0 < ⟪v.1, (A z v).1⟫_ℝ + ⟪v.2, (A z v).2⟫_ℝ) :
    StrictConvexOn ℝ s f := by
  apply strictConvexOn_of_positive_hessian hs hsopen hf
    (fun z hz => hasFDerivAt_stateDual_comp E F (hG z hz))
  intro z hz v hv
  simpa only [stateDual_comp_quadratic] using hpos z hz v hv

/-- Vanishing of the product-state gradient gives the scalar stationary
condition needed by the supporting-certificate theorems. -/
theorem hasFDerivAt_zero_of_stateGradient_eq_zero
    {f : E × F → ℝ} {G : E × F → E × F} {z : E × F}
    (hf : HasFDerivAt f (stateDual E F (G z)) z) (hG : G z = 0) :
    HasFDerivAt f (0 : (E × F) →L[ℝ] ℝ) z := by
  simpa only [hG, map_zero] using hf

end Problem356

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set
open scoped RealInnerProductSpace

namespace Problem356.StationaryMap

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The concrete scalar state differential is the product-state dual of its
stationary vector field. -/
theorem stateDifferential_eq_stateDual (a y : E) (s : E × E) :
    stateDifferential a y s = stateDual E E (stationary a (y, s)) := rfl

/-- The state derivative of the concrete stationary map is the coercive
regularized Coulomb Hessian. -/
theorem hasFDerivAt_stateStationary (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y) :
    HasFDerivAt (fun p : E × E => stationary a (y, p))
      (regularizedStateHessian (s.1 - y) (s.1 - s.2) (s.2 - y)) s := by
  have h := hasFDerivAt_regularizedStateGradient y
    (-((5 / 4 : ℝ) • a) + (20 : ℝ) • a)
    (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxz) (sub_ne_zero.mpr hzy)
  convert h using 1
  funext p
  unfold stationary
  have hp : p.2 - p.1 = -(p.1 - p.2) := by abel
  rw [hp, pairGradient_neg, smul_add]
  congr 1
  abel

/-- Concrete strict convexity on every open convex state domain with the
uniform pair separation used in the local construction. -/
theorem statePotential_strictConvexOn_of_separated (a y : E) {V : Set (E × E)}
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hsep : ∀ s ∈ V, (2 : ℝ) / 3 ≤ ‖s.1 - y‖ ∧
      (2 : ℝ) / 3 ≤ ‖s.1 - s.2‖ ∧ (2 : ℝ) / 3 ≤ ‖s.2 - y‖) :
    StrictConvexOn ℝ V (statePotential a y) := by
  have hne : ∀ {x z : E}, (2 : ℝ) / 3 ≤ ‖x - z‖ → x ≠ z := by
    intro x z h hxz
    norm_num [hxz] at h
  apply strictConvexOn_of_positive_stateGradient E E hV hVopen
    (G := fun s => stationary a (y, s))
    (A := fun s => regularizedStateHessian (s.1 - y) (s.1 - s.2) (s.2 - y))
  · intro s hs
    rw [← stateDifferential_eq_stateDual]
    exact hasFDerivAt_statePotential a y
      (hne (hsep s hs).1) (hne (hsep s hs).2.1) (hne (hsep s hs).2.2)
  · intro s hs
    exact hasFDerivAt_stateStationary a y
      (hne (hsep s hs).1) (hne (hsep s hs).2.1) (hne (hsep s hs).2.2)
  · intro s hs v hv
    exact regularizedStateHessian_pos (hsep s hs).1 (hsep s hs).2.1 (hsep s hs).2.2 hv

/-- A zero of the actual Coulomb stationary map is the unique minimizing state
on a separated open convex domain. -/
theorem statePotential_minimum_and_eq_iff_of_separated (a y : E) {V : Set (E × E)}
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hsep : ∀ s ∈ V, (2 : ℝ) / 3 ≤ ‖s.1 - y‖ ∧
      (2 : ℝ) / 3 ≤ ‖s.1 - s.2‖ ∧ (2 : ℝ) / 3 ≤ ‖s.2 - y‖)
    {s : E × E} (hs : s ∈ V) (hzero : stationary a (y, s) = 0)
    {q : E × E} (hq : q ∈ V) :
    statePotential a y s ≤ statePotential a y q ∧
      (statePotential a y q = statePotential a y s ↔ q = s) := by
  have hne : ∀ {x z : E}, (2 : ℝ) / 3 ≤ ‖x - z‖ → x ≠ z := by
    intro x z h hxz
    norm_num [hxz] at h
  have hconv := statePotential_strictConvexOn_of_separated a y hV hVopen hsep
  have hstat := hasFDerivAt_statePotential_zero a y
    (hne (hsep s hs).1) (hne (hsep s hs).2.1) (hne (hsep s hs).2.2) hzero
  exact ⟨convex_isMinOn_of_hasFDerivAt_zero hconv.convexOn hs hstat hq,
    strictConvex_eq_iff_of_hasFDerivAt_zero hconv hs hstat hq⟩

/-- A smooth branch of zeros of the concrete Coulomb stationary equation
produces a smooth supporting value with its exact contact graph. All analytic
convexity hypotheses are discharged by the explicit distance separation. -/
theorem smooth_stationary_branch_support (a : E)
    {U : Set E} {V : Set (E × E)} {ψ : E → E × E} {n : WithTop ENat}
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hsep : ∀ y ∈ U, ∀ s ∈ V, (2 : ℝ) / 3 ≤ ‖s.1 - y‖ ∧
      (2 : ℝ) / 3 ≤ ‖s.1 - s.2‖ ∧ (2 : ℝ) / 3 ≤ ‖s.2 - y‖)
    (hψ : ContDiffOn ℝ n ψ U) (hψV : MapsTo ψ U V)
    (hzero : ∀ y ∈ U, stationary a (y, ψ y) = 0) :
    ContDiffOn ℝ n (fun y => statePotential a y (ψ y)) U ∧
      ∀ y ∈ U, ∀ s ∈ V,
        statePotential a y (ψ y) ≤ statePotential a y s ∧
          (statePotential a y s = statePotential a y (ψ y) ↔ s = ψ y) := by
  have hne : ∀ {x z : E}, (2 : ℝ) / 3 ≤ ‖x - z‖ → x ≠ z := by
    intro x z h hxz
    norm_num [hxz] at h
  have hF : ContDiffOn ℝ n (jointPotential a) (U ×ˢ V) := by
    intro p hp
    exact (contDiffAt_jointPotential a
      (hne (hsep p.1 hp.1 p.2 hp.2).1)
      (hne (hsep p.1 hp.1 p.2 hp.2).2.1)
      (hne (hsep p.1 hp.1 p.2 hp.2).2.2)).contDiffWithinAt
  constructor
  · exact hF.comp (contDiffOn_id.prodMk hψ) (fun y hy => ⟨hy, hψV hy⟩)
  · intro y hy s hs
    exact statePotential_minimum_and_eq_iff_of_separated a y hV hVopen
      (hsep y hy) (hψV hy) (hzero y hy) hs

end Problem356.StationaryMap

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.Cyclic

/-- The cyclic rotation of the three particles. -/
def rotate : Triple ≃ᵐ Triple where
  toFun t := (t.2.1, (t.2.2, t.1))
  invFun t := (t.2.2, (t.1, t.2.1))
  left_inv t := by rfl
  right_inv t := by rfl
  measurable_toFun := measurable_snd.fst.prodMk
    (measurable_snd.snd.prodMk measurable_fst)
  measurable_invFun := measurable_snd.snd.prodMk
    (measurable_fst.prodMk measurable_snd.fst)

/-- Averaging over the cyclic group already gives identical coordinate marginals. -/
def symmetrize (pi : Measure Triple) : Measure Triple :=
  (3 : ℝ≥0∞)⁻¹ • (pi + Measure.map rotate pi + Measure.map rotate.symm pi)

/-- The common marginal of the cyclic average. -/
def averageMarginal (pi : Measure Triple) : Measure E3 :=
  (3 : ℝ≥0∞)⁻¹ •
    (Measure.map tripleFst pi + Measure.map tripleSnd pi + Measure.map tripleThd pi)

private theorem measurable_fst₃ : Measurable tripleFst := measurable_fst
private theorem measurable_snd₃ : Measurable tripleSnd := measurable_snd.fst
private theorem measurable_thd₃ : Measurable tripleThd := measurable_snd.snd

theorem map_fst_symmetrize (pi : Measure Triple) :
    Measure.map tripleFst (symmetrize pi) = averageMarginal pi := by
  simp only [symmetrize, averageMarginal, Measure.map_smul,
    Measure.map_add _ _ measurable_fst₃,
    Measure.map_map measurable_fst₃ rotate.measurable,
    Measure.map_map measurable_fst₃ rotate.symm.measurable]
  rfl

theorem map_snd_symmetrize (pi : Measure Triple) :
    Measure.map tripleSnd (symmetrize pi) = averageMarginal pi := by
  simp only [symmetrize, averageMarginal, Measure.map_smul,
    Measure.map_add _ _ measurable_snd₃,
    Measure.map_map measurable_snd₃ rotate.measurable,
    Measure.map_map measurable_snd₃ rotate.symm.measurable]
  change (3 : ℝ≥0∞)⁻¹ •
      (Measure.map tripleSnd pi + Measure.map tripleThd pi + Measure.map tripleFst pi) = _
  ac_rfl

theorem map_thd_symmetrize (pi : Measure Triple) :
    Measure.map tripleThd (symmetrize pi) = averageMarginal pi := by
  simp only [symmetrize, averageMarginal, Measure.map_smul,
    Measure.map_add _ _ measurable_thd₃,
    Measure.map_map measurable_thd₃ rotate.measurable,
    Measure.map_map measurable_thd₃ rotate.symm.measurable]
  change (3 : ℝ≥0∞)⁻¹ •
      (Measure.map tripleThd pi + Measure.map tripleFst pi + Measure.map tripleSnd pi) = _
  ac_rfl

theorem symmetrize_probability (pi : Measure Triple) [IsProbabilityMeasure pi] :
    IsProbabilityMeasure (symmetrize pi) := by
  constructor
  simp [symmetrize, Measure.map_apply rotate.measurable,
    Measure.map_apply rotate.symm.measurable]
  rw [← two_mul, ← add_one_mul]
  norm_num only [Nat.reduceAdd]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem symmetrize_isThreeCoupling (pi : Measure Triple) [IsProbabilityMeasure pi] :
    IsThreeCoupling (averageMarginal pi) (symmetrize pi) :=
  ⟨symmetrize_probability pi, map_fst_symmetrize pi,
    map_snd_symmetrize pi, map_thd_symmetrize pi⟩

/-- A cyclically invariant property holding almost everywhere survives symmetrization.
No measurability hypothesis on the property is necessary. -/
theorem ae_symmetrize_of_rotate_invariant (pi : Measure Triple) {P : Triple → Prop}
    (hP : ∀ᵐ t ∂pi, P t) (hrotate : ∀ t, P (rotate t) ↔ P t) :
    ∀ᵐ t ∂symmetrize pi, P t := by
  apply Measure.ae_smul_measure
  rw [ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨hP, rotate.measurableEmbedding.ae_map_iff.mpr ?_⟩,
    rotate.symm.measurableEmbedding.ae_map_iff.mpr ?_⟩
  · exact hP.mono fun t ht => (hrotate t).mpr ht
  · exact hP.mono fun t ht => (hrotate (rotate.symm t)).mp (by simpa using ht)

theorem averageMarginal_probability (pi : Measure Triple) [IsProbabilityMeasure pi] :
    IsProbabilityMeasure (averageMarginal pi) := by
  have := symmetrize_probability pi
  rw [← map_fst_symmetrize pi]
  exact Measure.isProbabilityMeasure_map measurable_fst₃.aemeasurable

private theorem invDistance_comm (x y : E3) : invDistance x y = invDistance y x := by
  simp only [invDistance, norm_sub_rev]

theorem cost_rotate (t : Triple) : coulombCost (rotate t) = coulombCost t := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, rotate,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [invDistance_comm t.2.1 t.1, invDistance_comm t.2.2 t.1]
  ac_rfl

theorem cost_rotate_symm (t : Triple) : coulombCost (rotate.symm t) = coulombCost t := by
  simpa using (cost_rotate (rotate.symm t)).symm

theorem lintegral_symmetrize (pi : Measure Triple) :
    (∫⁻ t, coulombCost t ∂symmetrize pi) = ∫⁻ t, coulombCost t ∂pi := by
  rw [symmetrize, lintegral_smul_measure, lintegral_add_measure,
    lintegral_add_measure, lintegral_map_equiv, lintegral_map_equiv]
  simp only [cost_rotate, cost_rotate_symm, smul_eq_mul]
  rw [← two_mul, ← add_one_mul]
  norm_num only [Nat.reduceAdd]
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

end Problem356.Cyclic

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

theorem exists_fullCoulombConclusion_of_local_geometry
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e i)
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    {U : Set E3} (hU : MeasurableSet U)
    (hBU : Metric.ball c r ⊆ U) (heU : ∀ i, e i '' Metric.ball c r ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 0 x) + u (e 1 x)) = coulombCost (x, (e 0 x, e 1 x)))
    (hcontact23 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 2 x) + u (e 3 x)) = coulombCost (x, (e 2 x, e 3 x)))
    (hselect : ∀ x y z : E3, x ∈ Metric.ball c r → y ∈ U → z ∈ U →
      ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
      ∃ i, y = e i x) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  obtain ⟨d, hd⟩ := SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts
    c hr e hsource hdisj he he'
  have : IsProbabilityMeasure d.nu := d.probability
  have hfull : ∀ᵐ x ∂d.nu, x ∈ Metric.ball c r :=
    d.core_full.mono (fun _ hx => d.core_subset hx)
  have hdensity : densityMeasure d.rho =
      branchMarginal d.nu (d.branch 0) (d.branch 1) (d.branch 2) (d.branch 3) := by
    simpa [branchMarginal, Fin.sum_univ_succ, smul_add, add_assoc] using d.density_eq
  have hHU : ∀ i, d.branch i '' Metric.ball c r ⊆ U := by
    rintro i _ ⟨x, hx, rfl⟩
    rw [hd i x hx]
    exact heU i ⟨x, hx, rfl⟩
  have hCentral : ∀ i, Disjoint (Metric.ball c r) (d.branch i '' Metric.ball c r) := by
    intro i
    exact d.component_disjoint (show (none : Option (Fin 4)) ≠ some i by simp)
  have hPair : Pairwise fun i j =>
      Disjoint (d.branch i '' Metric.ball c r) (d.branch j '' Metric.ball c r) := by
    intro i j hij
    exact d.component_disjoint (show some i ≠ some j by simpa using hij)
  have hc01 : ∀ᵐ x ∂d.nu,
      ENNReal.ofReal (u x + u (d.branch 0 x) + u (d.branch 1 x)) =
        coulombCost (x, (d.branch 0 x, d.branch 1 x)) := by
    filter_upwards [hfull] with x hx
    simpa only [hd 0 x hx, hd 1 x hx] using hcontact01 x hx
  have hc23 : ∀ᵐ x ∂d.nu,
      ENNReal.ofReal (u x + u (d.branch 2 x) + u (d.branch 3 x)) =
        coulombCost (x, (d.branch 2 x, d.branch 3 x)) := by
    filter_upwards [hfull] with x hx
    simpa only [hd 2 x hx, hd 3 x hx] using hcontact23 x hx
  have hcounter : HasCoulombCounterexample d.rho := by
    apply hasCoulombCounterexample_of_real_branches d.rho d.density_smooth d.nu
      d.branch d.branch_measurable hdensity d.measurable_central hU hfull hBU hHU
      d.branch_injective d.branch_image_measurable hCentral hPair
      hu hM hubound hbound hc01 hc23
    intro x y z hx hy hz hc
    obtain ⟨i, hi⟩ := hselect x y z hx hy hz hc
    exact ⟨i, hi.trans (hd i x hx).symm⟩
  have hoptimal := branchCoupling_optimality_of_real_certificate d.nu d.branch
    d.branch_measurable hU hfull hBU hHU hu hM hubound hbound hc01 hc23
  have hdisjoint : Pairwise (fun i j =>
      Disjoint (BranchSeparation.components d.compactCore d.branch i)
        (BranchSeparation.components d.compactCore d.branch j)) := by
    apply BranchSeparation.disjoint_components_mono d.core_subset
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hCentral j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (hCentral i).symm
      | succ j => exact hPair (by simpa using hij)
  obtain ⟨eta, heta, hsep⟩ := BranchSeparation.exists_ae_separated_branchCoupling
    d.core_compact d.core_full d.branch_measurable d.branch_continuous hdisjoint
  refine ⟨d.rho, hcounter.hasFull_of_separated_optimizer ?_ ?_ heta hsep⟩
  · rw [hdensity]
    exact isThreeCoupling_branchCoupling d.nu (d.branch_measurable 0)
      (d.branch_measurable 1) (d.branch_measurable 2) (d.branch_measurable 3)
  · simpa only [hdensity] using hoptimal.1

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.CoulombSupportExistence

open CoulombCalculus GeometryJets LocalGeometry

/-- The two explicit conventions for the stationary field coincide. -/
theorem stationary_eq (a : E3) :
    StationaryMap.stationary a = stationaryEquation 20 a := by
  funext p
  apply Prod.ext
  · rfl
  · simp only [StationaryMap.stationary, stationaryEquation]
    have hn (x y : E3) : pairGradient (x - y) = -pairGradient (y - x) := by
      rw [← neg_sub y x, pairGradient_neg]
    rw [hn p.2.2 p.2.1, hn p.2.2 p.1]
    module

private def D (a y : E3) (s : E3 × E3) : (E3 × E3) →L[ℝ] ℝ :=
  stateDual E3 E3 (stationaryEquation 20 a (y, s))

private def H (a y : E3) (s : E3 × E3) :
    (E3 × E3) →L[ℝ] ((E3 × E3) →L[ℝ] ℝ) :=
  (stateDual E3 E3).comp
    ((fderiv ℝ (stationaryEquation 20 a) (y, s)).comp
      (ContinuousLinearMap.inr ℝ E3 (E3 × E3)))

private theorem D_eq (a y : E3) (s : E3 × E3) :
    D a y s = StationaryMap.stateDifferential a y s := by
  unfold D
  rw [← stationary_eq]
  rfl

/-- The actual Coulomb stationary charts admit a local supporting potential
with exact equality precisely on the stationary branch. -/
theorem nonempty_coulombLocalSupportingCharts (k : Fin 3) :
    Nonempty (LocalSupportingCharts
      (StationaryMap.jointPotential (axisVector k))
      (stationaryEquation 20 (axisVector k))
      (axisVector k) (0, -axisVector k)) := by
  let a : E3 := axisVector k
  have ha : ‖a‖ = 1 := norm_axisVector k
  have ha0 : a ≠ 0 := axisVector_ne_zero k
  have haminus : a ≠ -a := by
    intro h
    have hh := congrArg (fun x : E3 => x k) h
    norm_num [a, axisVector] at hh
  have hsep : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)),
      q.2.1 ≠ q.1 ∧ q.2.1 ≠ q.2.2 ∧ q.2.2 ≠ q.1 := by
    have h₁ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.1 ≠ q.1 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.1)
        (g := fun q => q.1) (by fun_prop) (by fun_prop)).mem_nhds ha0.symm
    have h₂ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.1 ≠ q.2.2 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.1)
        (g := fun q => q.2.2) (by fun_prop) (by fun_prop)).mem_nhds
          (neg_ne_zero.mpr ha0).symm
    have h₃ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.2 ≠ q.1 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.2)
        (g := fun q => q.1) (by fun_prop) (by fun_prop)).mem_nhds haminus.symm
    exact h₁.and (h₂.and h₃)
  obtain ⟨C⟩ := CoulombCharts.nonempty_coulombCharts k
  apply nonempty_localSupportingCharts (D := D a) (H := H a) C
  · exact StationaryMap.contDiffAt_jointPotential a ha0.symm
      (neg_ne_zero.mpr ha0).symm haminus.symm
  · filter_upwards [hsep] with q hq
    change HasFDerivAt (StationaryMap.statePotential a q.1) (D a q.1 q.2) q.2
    rw [D_eq]
    exact StationaryMap.hasFDerivAt_statePotential a q.1 hq.1 hq.2.1 hq.2.2
  · filter_upwards [hsep] with q hq
    have hG := (contDiffAt_stationaryEquation (n := ω) 20 a q hq.1 hq.2.1
      hq.2.2.symm).differentiableAt (by simp)
    have hp : HasFDerivAt (fun z : E3 × E3 => (q.1, z))
        (ContinuousLinearMap.inr ℝ E3 (E3 × E3)) q.2 := by
      exact hasFDerivAt_prodMk_right q.1 q.2
    have hpartial := hG.hasFDerivAt.comp q.2 hp
    convert! hasFDerivAt_stateDual_comp E3 E3 hpartial using 1
  · have hc := (contDiffAt_stationaryEquation_center (n := ω) 20 a ha).continuousAt_fderiv
      (by simp)
    exact continuousAt_const.clm_comp (hc.clm_comp continuousAt_const)
  · intro v hv
    change 0 < ((stateDual E3 E3).comp
      ((fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k))).comp
          (ContinuousLinearMap.inr ℝ E3 (E3 × E3)))) v v
    rw [CoulombCharts.stationary_state_partial_eq, stateDual_comp_quadratic]
    have hc := LocalHessian.stateOperator_coercive k v
    have hp : 0 < (16 : ℝ) * ‖v‖ ^ 2 := by positivity
    exact hp.trans_le hc
  · intro q hq
    simp only [D, a, Prod.eta, hq, map_zero]

/-- The supporting charts in the scalar-potential stationary convention. -/
theorem nonempty_coulombLocalSupportingCharts_stationary (k : Fin 3) :
    Nonempty (LocalSupportingCharts
      (StationaryMap.jointPotential (axisVector k))
      (StationaryMap.stationary (axisVector k))
      (axisVector k) (0, -axisVector k)) := by
  rw [stationary_eq]
  exact nonempty_coulombLocalSupportingCharts k

end Problem356.CoulombSupportExistence

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

abbrev ChartsAt (a : E3) :=
  LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)

/-- The actual five local potentials of the Coulomb construction, with the
same central quadratic for both branches. -/
def potentials (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    Fin 5 → E3 → ℝ :=
  ![fun x => (5 : ℝ) / 2 - 10 * ‖x‖ ^ 2,
    C₁.value,
    fun z => (5 : ℝ) / 4 * ⟪point 1, z + point 1⟫_ℝ - 10 * ‖z + point 1‖ ^ 2,
    C₂.value,
    fun z => (5 : ℝ) / 4 * ⟪point 3, z + point 3⟫_ℝ - 10 * ‖z + point 3‖ ^ 2]

/-- Preliminary domains are unrestricted for the polynomial potentials and
are the actual chart sources for the two supporting-value potentials. -/
def domains (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) : Fin 5 → Set E3 :=
  ![univ, C₁.charts.central.source, univ, C₂.charts.central.source, univ]

lemma norm_point_one : ‖point 1‖ = 1 := by
  change ‖(!₂[1, 0, 0] : E3)‖ = 1
  norm_num [point, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

lemma norm_point_three : ‖point 3‖ = 1 := by
  change ‖(!₂[0, 1, 0] : E3)‖ = 1
  norm_num [point, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

lemma point_two_eq_neg : point 2 = -point 1 := by
  change (!₂[-1, 0, 0] : E3) = -(!₂[1, 0, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma point_four_eq_neg : point 4 = -point 3 := by
  change (!₂[0, -1, 0] : E3) = -(!₂[0, 1, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma domains_open (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, IsOpen (domains C₁ C₂ i) := by
  intro i
  fin_cases i
  · exact isOpen_univ
  · exact C₁.charts.central.open_source
  · exact isOpen_univ
  · exact C₂.charts.central.open_source
  · exact isOpen_univ

lemma point_mem_domains (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, point i ∈ domains C₁ C₂ i := by
  intro i
  fin_cases i
  · exact mem_univ _
  · exact C₁.charts.point_mem
  · exact mem_univ _
  · exact C₂.charts.point_mem
  · exact mem_univ _

lemma continuousOn_potentials (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, ContinuousOn (potentials C₁ C₂ i) (domains C₁ C₂ i) := by
  intro i
  fin_cases i
  · exact (by fun_prop : Continuous (fun x : E3 => (5 : ℝ) / 2 - 10 * ‖x‖ ^ 2)).continuousOn
  · exact C₁.value_analytic.continuousOn
  · exact (by fun_prop : Continuous (fun z : E3 =>
      (5 : ℝ) / 4 * ⟪point 1, z + point 1⟫_ℝ - 10 * ‖z + point 1‖ ^ 2)).continuousOn
  · exact C₂.value_analytic.continuousOn
  · exact (by fun_prop : Continuous (fun z : E3 =>
      (5 : ℝ) / 4 * ⟪point 3, z + point 3⟫_ℝ - 10 * ‖z + point 3‖ ^ 2)).continuousOn

lemma potentials_center_values (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, potentials C₁ C₂ i (point i) = if i = 0 then (5 / 2 : ℝ) else 0 := by
  intro i
  fin_cases i
  · norm_num [potentials, point]
  · exact localSupporting_value_center norm_point_one C₁
  · change (5 : ℝ) / 4 * ⟪point 1, point 2 + point 1⟫_ℝ -
      10 * ‖point 2 + point 1‖ ^ 2 = 0
    rw [point_two_eq_neg]
    simp
  · exact localSupporting_value_center norm_point_three C₂
  · change (5 : ℝ) / 4 * ⟪point 3, point 4 + point 3⟫_ℝ -
      10 * ‖point 4 + point 3‖ ^ 2 = 0
    rw [point_four_eq_neg]
    simp

/-- The actual potentials have the strict bad-type gap supplied by the
finite center certificate. -/
lemma strict_center_gap (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (h : ¬ Good i j k) :
    ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) <
      coulombCost (point i, (point j, point k)) := by
  have he (l : Fin 5) : ENNReal.ofReal (potentials C₁ C₂ l (point l)) = potential l := by
    rw [potentials_center_values]
    by_cases hl : l = 0
    · simp only [hl, ite_eq_left, potential]
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    · simp [potential, hl]
  have hn (l : Fin 5) : 0 ≤ potentials C₁ C₂ l (point l) := by
    rw [potentials_center_values]
    split_ifs <;> norm_num
  rw [ENNReal.ofReal_add (add_nonneg (hn i) (hn j)) (hn k),
    ENNReal.ofReal_add (hn i) (hn j), he i, he j, he k]
  exact strict_of_not_good i j k h

/-- The real local certificate has the exact extended-valued interpretation
on any collision-free triple in its three component balls. -/
theorem ennreal_local_certificate {a : E3} (C : ChartsAt a) {x y z : E3}
    (hy : y ∈ ball a C.parameterRadius)
    (hx : x ∈ ball (0 : E3) C.stateRadius)
    (hz : z ∈ ball (-a) C.stateRadius)
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) = coulombCost (x, (y, z)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y) := by
  let R : ℝ := ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc : coulombCost (x, (y, z)) = ENNReal.ofReal R := by
    simpa only [CoulombEstimates.realCost, dist_eq_norm] using
      CoulombEstimates.coulombCost_eq_ofReal_realCost hxy hxz hyz
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact ENNReal.ofReal_le_ofReal (local_coulomb_supporting C hy hx hz)
  · constructor
    · intro heq
      have hs := (ENNReal.ofReal_pos.mp (heq.symm ▸ coulombCost_pos (x, (y, z)))).le
      have heqR := (ENNReal.ofReal_eq_ofReal_iff hs hR).mp (heq.trans hc)
      exact (local_coulomb_contact C hy hx hz).mp heqR.symm
    · intro hbranch
      have heqR := (local_coulomb_contact C hy hx hz).mpr hbranch
      exact (congrArg ENNReal.ofReal heqR).symm.trans hc.symm

/-- Symmetric union of the two actual local branch graphs. The parameter
remains in the corresponding chart source. -/
def branchContact (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) (t : Triple) : Prop :=
  (∃ y ∈ C₁.charts.central.source,
    List.Perm [t.1, t.2.1, t.2.2] [C₁.charts.central y, y, C₁.charts.opposite y]) ∨
  (∃ y ∈ C₂.charts.central.source,
    List.Perm [t.1, t.2.1, t.2.2] [C₂.charts.central y, y, C₂.charts.opposite y])

lemma branchContact_perm (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    {x y z x' y' z' : E3} (hp : List.Perm [x, y, z] [x', y', z']) :
    branchContact C₁ C₂ (x, (y, z)) ↔ branchContact C₁ C₂ (x', (y', z')) := by
  constructor
  · intro h
    rcases h with ⟨w, hw, hperm⟩ | ⟨w, hw, hperm⟩
    · exact Or.inl ⟨w, hw, hp.symm.trans hperm⟩
    · exact Or.inr ⟨w, hw, hp.symm.trans hperm⟩
  · intro h
    rcases h with ⟨w, hw, hperm⟩ | ⟨w, hw, hperm⟩
    · exact Or.inl ⟨w, hw, hp.trans hperm⟩
    · exact Or.inr ⟨w, hw, hp.trans hperm⟩

end Problem356.FiveComponentGeometry

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal

namespace Problem356.FiveComponentGeometry

open CenterCertificate GoodTypePermutation

/-- Common component neighborhoods on which both canonical Coulomb
certificates hold, including their one-way symmetric contact localization. -/
theorem exists_canonical_neighborhoods
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ W : Fin 5 → Set E3,
      (∀ i, W i ∈ nhds (point i)) ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2 ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4 := by
  let R : Fin 5 → ℝ :=
    ![min C₁.stateRadius C₂.stateRadius, C₁.parameterRadius, C₁.stateRadius,
      C₂.parameterRadius, C₂.stateRadius]
  have hR : ∀ i, 0 < R i := by
    intro i
    fin_cases i
    · exact lt_min C₁.stateRadius_pos C₂.stateRadius_pos
    · exact C₁.parameterRadius_pos
    · exact C₁.stateRadius_pos
    · exact C₂.parameterRadius_pos
    · exact C₂.stateRadius_pos
  obtain ⟨r, hr, hsub, hdisj⟩ := Geometry.finite_disjoint_closedBalls_subset
    point point_injective (fun i => ball (point i) (R i))
    (fun _ => isOpen_ball) (fun i => mem_ball_self (hR i))
  let W : Fin 5 → Set E3 := fun i => ball (point i) r
  have hWsub (i : Fin 5) : W i ⊆ ball (point i) (R i) :=
    ball_subset_closedBall.trans (hsub i)
  have hdist {i j : Fin 5} (hij : i ≠ j) {x y : E3}
      (hx : x ∈ W i) (hy : y ∈ W j) : 0 < dist x y := by
    apply dist_pos.mpr
    intro heq
    exact Set.disjoint_left.mp (hdisj hij)
      (heq ▸ ball_subset_closedBall hx) (ball_subset_closedBall hy)
  refine ⟨W, (fun i => ball_mem_nhds (point i) hr), ?_, ?_⟩
  · intro x hx y hy z hz
    have hx' := hWsub 0 hx
    change x ∈ ball (0 : E3) (min C₁.stateRadius C₂.stateRadius) at hx'
    have hx₁ : x ∈ ball (0 : E3) C₁.stateRadius :=
      ball_subset_ball (min_le_left _ _) hx'
    have hy₁ : y ∈ ball (point 1) C₁.parameterRadius := hWsub 1 hy
    have hz₁ : z ∈ ball (-point 1) C₁.stateRadius := by
      have hz' := hWsub 2 hz
      change z ∈ ball (point 2) C₁.stateRadius at hz'
      simpa only [point_two_eq_neg] using hz'
    have hc := ennreal_local_certificate C₁ hy₁ hx₁ hz₁
      (hdist (by decide : (0 : Fin 5) ≠ 1) hx hy)
      (hdist (by decide : (0 : Fin 5) ≠ 2) hx hz)
      (hdist (by decide : (1 : Fin 5) ≠ 2) hy hz)
    refine ⟨hc.1, ?_⟩
    intro heq
    obtain ⟨hxc, hzc⟩ := hc.2.mp heq
    apply Or.inl
    refine ⟨y, ?_, ?_⟩
    · rw [C₁.source_ball]
      exact hy₁
    · simpa only [hxc, hzc] using
        (List.Perm.refl [C₁.charts.central y, y, C₁.charts.opposite y])
  · intro x hx y hy z hz
    have hx' := hWsub 0 hx
    change x ∈ ball (0 : E3) (min C₁.stateRadius C₂.stateRadius) at hx'
    have hx₂ : x ∈ ball (0 : E3) C₂.stateRadius :=
      ball_subset_ball (min_le_right _ _) hx'
    have hy₂ : y ∈ ball (point 3) C₂.parameterRadius := hWsub 3 hy
    have hz₂ : z ∈ ball (-point 3) C₂.stateRadius := by
      have hz' := hWsub 4 hz
      change z ∈ ball (point 4) C₂.stateRadius at hz'
      simpa only [point_four_eq_neg] using hz'
    have hc := ennreal_local_certificate C₂ hy₂ hx₂ hz₂
      (hdist (by decide : (0 : Fin 5) ≠ 3) hx hy)
      (hdist (by decide : (0 : Fin 5) ≠ 4) hx hz)
      (hdist (by decide : (3 : Fin 5) ≠ 4) hy hz)
    refine ⟨hc.1, ?_⟩
    intro heq
    obtain ⟨hxc, hzc⟩ := hc.2.mp heq
    apply Or.inr
    refine ⟨y, ?_, ?_⟩
    · rw [C₂.source_ball]
      exact hy₂
    · simpa only [hxc, hzc] using
        (List.Perm.refl [C₂.charts.central y, y, C₂.charts.opposite y])

/-- The actual chart pair supplies the neighborhood hypothesis for every
good component type in the finite global gluing theorem. -/
theorem eventually_good_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (hg : Good i j k) :
    ∀ᶠ t : Triple in nhds (point i, (point j, point k)),
      ENNReal.ofReal (potentials C₁ C₂ i t.1 + potentials C₁ C₂ j t.2.1 +
        potentials C₁ C₂ k t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (potentials C₁ C₂ i t.1 + potentials C₁ C₂ j t.2.1 +
        potentials C₁ C₂ k t.2.2) = coulombCost t → branchContact C₁ C₂ t) := by
  obtain ⟨W, hW, h012, h034⟩ := exists_canonical_neighborhoods C₁ C₂
  exact GoodTypePermutation.eventually_certificate_of_good point hW
    (fun hp => (branchContact_perm C₁ C₂ hp).mp) h012 h034 i j k hg

end Problem356.FiveComponentGeometry

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- The finite gluing construction only needs forward contact localization.
The explicit contact candidates may be shown saturated separately, so no
converse from the chosen global contact predicate is required here. -/
theorem exists_glued_component_certificate_forward {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop) (Contact : Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t → Contact t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          Contact (x, (y, z)))) := by
  let C : (ι × (ι × ι)) → Triple → Prop := fun a t =>
    ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) = coulombCost t ∧
      Contact t
  have hgood' : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ C a t) := by
    intro a ha
    filter_upwards [hgood a ha] with t ht
    exact ⟨ht.1, ⟨fun heq => ⟨heq, ht.2 heq⟩, fun hc => hc.1⟩⟩
  obtain ⟨r, M, hr, hM, hUV, hdisj, hmeas, hcont, hbound, hcert⟩ :=
    exists_glued_component_certificate p hp V hV hpV v hv Good C hgood' hbad
  refine ⟨r, M, hr, hM, hUV, hdisj, hmeas, hcont, hbound, ?_⟩
  intro x hx y hy z hz
  have hc := hcert x hx y hy z hz
  refine ⟨hc.1, ?_⟩
  intro heq
  obtain ⟨a, _, _, _, _, hcontact⟩ := hc.2.mp heq
  exact hcontact.2

end Problem356

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry
open CenterCertificate GoodTypePermutation

/-- The actual two canonical local certificates glue into one globally bounded
potential on the five disjoint component balls. -/
theorem exists_global_certificate_of_canonical
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (W : Fin 5 → Set E3) (hW : ∀ i, IsOpen (W i))
    (hpW : ∀ i, point i ∈ W i) (hWD : ∀ i, W i ⊆ domains C₁ C₂ i)
    (h012 : LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2)
    (h034 : LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (point i) r
      let u := ComponentPotential.glue U (potentials C₁ C₂)
      (∀ i, U i ⊆ W i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          branchContact C₁ C₂ (x, (y, z)))) := by
  apply exists_glued_component_certificate_forward point point_injective W hW hpW
    (potentials C₁ C₂)
    (fun i => (continuousOn_potentials C₁ C₂ i).mono (hWD i))
    (fun a => Good a.1 a.2.1 a.2.2) (branchContact C₁ C₂)
  · intro a ha
    exact eventually_certificate_of_good point (fun i => (hW i).mem_nhds (hpW i))
      (fun hp hc => (branchContact_perm C₁ C₂ hp).mp hc)
      h012 h034 a.1 a.2.1 a.2.2 ha
  · intro a ha
    exact strict_center_gap C₁ C₂ a.1 a.2.1 a.2.2 ha

/-- Every collision-free raw branch triple saturates the local potential. -/
lemma ennreal_graph_equality {a : E3} (C : ChartsAt a) {y : E3}
    (hy : y ∈ C.charts.central.source)
    (hxy : 0 < dist (C.charts.central y) y)
    (hxz : 0 < dist (C.charts.central y) (C.charts.opposite y))
    (hyz : 0 < dist y (C.charts.opposite y)) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖C.charts.central y‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, C.charts.opposite y + a⟫_ℝ -
        10 * ‖C.charts.opposite y + a‖ ^ 2)) =
      coulombCost (C.charts.central y, (y, C.charts.opposite y)) := by
  have hs := C.charts.mapsTo_state hy
  rw [C.state_ball, ← ball_prod_same] at hs
  exact (ennreal_local_certificate C (C.source_ball ▸ hy) hs.1 hs.2 hxy hxz hyz).2.mpr
    ⟨rfl, rfl⟩

private lemma ne_of_disjoint_components {U : Fin 5 → Set E3}
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {i j : Fin 5} (hij : i ≠ j) {x y : E3} (hx : x ∈ U i) (hy : y ∈ U j) :
    x ≠ y := by
  intro h
  subst y
  exact Set.disjoint_left.mp (hdisj hij) hx hy

/-- Saturation on the first raw branch, after gluing. -/
theorem glued_saturation_left (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    {U : Fin 5 → Set E3} (hUD : ∀ i, U i ⊆ domains C₁ C₂ i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {x y z : E3} (hx : x ∈ U 0) (hy : y ∈ U 1) (hz : z ∈ U 2)
    (hX : x = C₁.charts.central y) (hZ : z = C₁.charts.opposite y) :
    let u := ComponentPotential.glue U (potentials C₁ C₂)
    ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) := by
  dsimp only
  rw [ComponentPotential.glue_eq hdisj hx, ComponentPotential.glue_eq hdisj hy,
    ComponentPotential.glue_eq hdisj hz]
  have hxy := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 1) hx hy)
  have hxz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 2) hx hz)
  have hyz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (1 : Fin 5) ≠ 2) hy hz)
  subst x
  subst z
  exact ennreal_graph_equality C₁ (hUD 1 hy) hxy hxz hyz

/-- Saturation on the second raw branch, after gluing. -/
theorem glued_saturation_right (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    {U : Fin 5 → Set E3} (hUD : ∀ i, U i ⊆ domains C₁ C₂ i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {x y z : E3} (hx : x ∈ U 0) (hy : y ∈ U 3) (hz : z ∈ U 4)
    (hX : x = C₂.charts.central y) (hZ : z = C₂.charts.opposite y) :
    let u := ComponentPotential.glue U (potentials C₁ C₂)
    ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) := by
  dsimp only
  rw [ComponentPotential.glue_eq hdisj hx, ComponentPotential.glue_eq hdisj hy,
    ComponentPotential.glue_eq hdisj hz]
  have hxy := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 3) hx hy)
  have hxz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 4) hx hz)
  have hyz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (3 : Fin 5) ≠ 4) hy hz)
  subst x
  subst z
  exact ennreal_graph_equality C₂ (hUD 3 hy) hxy hxz hyz

/-- The concrete two Coulomb charts admit a globally bounded measurable
certificate on five disjoint component balls, with contact only on their
actual symmetric graph union. -/
theorem exists_global_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (point i) r
      let u := ComponentPotential.glue U (potentials C₁ C₂)
      (∀ i, U i ⊆ domains C₁ C₂ i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          branchContact C₁ C₂ (x, (y, z)))) := by
  obtain ⟨W, hW, h012, h034⟩ := exists_canonical_neighborhoods C₁ C₂
  apply exists_glued_component_certificate_forward point point_injective
    (domains C₁ C₂) (domains_open C₁ C₂) (point_mem_domains C₁ C₂)
    (potentials C₁ C₂) (continuousOn_potentials C₁ C₂)
    (fun a => Good a.1 a.2.1 a.2.2) (branchContact C₁ C₂)
  · intro a ha
    exact eventually_certificate_of_good point hW
      (fun hp hc => (branchContact_perm C₁ C₂ hp).mp hc)
      h012 h034 a.1 a.2.1 a.2.2 ha
  · intro a ha
    exact strict_center_gap C₁ C₂ a.1 a.2.1 a.2.2 ha

end Problem356.FiveComponentGeometry

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem356.CenterAxis

open CenterCertificate CoulombCalculus

/-- The finite certificate and the analytic construction use the same central point. -/
@[simp] theorem point_zero : point 0 = (0 : E3) := by
  simp [point]

/-- The first positive component is the first analytic axis. -/
@[simp] theorem point_one : point 1 = axisVector 0 := by
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The first negative component is opposite to the first analytic axis. -/
@[simp] theorem point_two : point 2 = -axisVector 0 := by
  change (!₂[-1, 0, 0] : E3) = -axisVector 0
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The second positive component is the second analytic axis. -/
@[simp] theorem point_three : point 3 = axisVector 1 := by
  change (!₂[0, 1, 0] : E3) = axisVector 1
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The second negative component is opposite to the second analytic axis. -/
@[simp] theorem point_four : point 4 = -axisVector 1 := by
  change (!₂[0, -1, 0] : E3) = -axisVector 1
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- Each noncentral certificate point is a unit vector. -/
theorem norm_point_of_ne_zero (i : Fin 5) (hi : i ≠ 0) : ‖point i‖ = 1 := by
  fin_cases i <;> simp_all

/-- The two canonical contact triples coincide literally with the analytic center triples. -/
theorem canonical_center_triples :
    (point 0, (point 1, point 2)) = ((0 : E3), (axisVector 0, -axisVector 0)) ∧
    (point 0, (point 3, point 4)) = ((0 : E3), (axisVector 1, -axisVector 1)) := by
  simp

end Problem356.CenterAxis

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem356.SmoothBranchMarginal

/-- Component containment in the disjoint five certificate regions supplies
exactly the disjointness input of the smooth marginal construction. -/
theorem componentRegion_pairwise_of_subsets
    {B : Set E3} {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {U : Fin 5 → Set E3}
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hB : B ⊆ U 0) (he : ∀ i, e i '' B ⊆ U i.succ) :
    Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      exact (hU (Fin.succ_ne_zero j).symm).mono hB (he j)
  | some i =>
    cases j with
    | none =>
      exact (hU (Fin.succ_ne_zero i)).mono (he i) hB
    | some j =>
      exact (hU (fun h => hij (congrArg some (Fin.succ_injective 4 h)))).mono (he i) (he j)

end Problem356.SmoothBranchMarginal

end

end OAI
end
end

section
section
namespace OAI


/-! Extract the canonical four-branch selector from an original contact graph. -/

namespace Problem356.ContactSelection

variable {E : Type uE} [TopologicalSpace E]

/-- A permuted original contact graph with its first coordinate central selects
one of the four inverse-reparametrized branches, in the canonical ordering
`Y₁,W₁,Y₂,W₂`. Only the two displayed outer points need lie outside `B`. -/
theorem second_selects_common_four
    (X Z : Fin 2 → OpenPartialHomeomorph E E)
    {B : Set E} {x y z s : E} {k : Fin 2}
    (hperm : List.Perm [x, y, z] [X k s, s, Z k s])
    (hx : x ∈ B) (hs : s ∈ (X k).source)
    (hsB : s ∉ B) (hzB : Z k s ∉ B) :
    ∃ i : Fin 4, y = CommonBranches.four X Z i x := by
  have hcentral := first_eq_of_perm hperm hx hsB hzB
  have hinv : (X k).symm x = s := by
    rw [hcentral]
    exact (X k).left_inv hs
  rcases second_eq_or_third_of_perm hperm hx hsB hzB with hy | hy
  · fin_cases k
    · exact ⟨0, hy.trans hinv.symm⟩
    · exact ⟨2, hy.trans hinv.symm⟩
  · have hz : y = Z k ((X k).symm x) :=
      hy.trans (congrArg (fun q => Z k q) hinv.symm)
    fin_cases k
    · exact ⟨1, hz⟩
    · exact ⟨3, hz⟩

end Problem356.ContactSelection

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set Metric

namespace Problem356.CoulombSupportExistence

open LocalGeometry StationaryMap CoulombCalculus

private theorem outside_central_ball {a y : E3} (ha : ‖a‖ = 1)
    (hy : y ∈ ball a (1 / 4 : ℝ)) : y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  intro hx
  have htri := dist_triangle a y (0 : E3)
  rw [dist_zero_right, ha, dist_comm a y] at htri
  have hy' := mem_ball.mp hy
  have hx' := mem_ball.mp hx
  linarith

/-- Shrink both local domains before forming the global contact predicate.
Every parameter of the entire retained graph, not just parameters in a later
component ball, has both outer coordinates outside the fixed central ball. -/
theorem exists_separated_shrink {a : E3} (ha : ‖a‖ = 1)
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)) :
    ∃ D : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a),
      ∀ y ∈ D.charts.central.source,
        y ∉ ball (0 : E3) (1 / 4 : ℝ) ∧
          D.charts.opposite y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  obtain ⟨D, hsource, hstate, _, _, _⟩ :=
    C.exists_shrink (1 / 4) (1 / 4) (by norm_num) (by norm_num)
  refine ⟨D, ?_⟩
  intro y hy
  refine ⟨outside_central_ball ha (hsource hy).2, ?_⟩
  have hs := (hstate (D.charts.mapsTo_state hy)).2
  have hz : D.charts.opposite y ∈ ball (-a) (1 / 4 : ℝ) := by
    rw [← ball_prod_same] at hs
    exact hs.2
  exact outside_central_ball (by simpa only [norm_neg] using ha) hz

/-- Unconditional actual Coulomb supporting charts with graph-wide exclusion
of both outer coordinates from a common fixed central neighborhood. -/
theorem exists_coulombLocalSupportingCharts_separated (k : Fin 3) :
    ∃ C : LocalSupportingCharts (jointPotential (axisVector k))
      (stationary (axisVector k)) (axisVector k) (0, -axisVector k),
      ∀ y ∈ C.charts.central.source,
        y ∉ ball (0 : E3) (1 / 4 : ℝ) ∧
          C.charts.opposite y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  obtain ⟨C⟩ := nonempty_coulombLocalSupportingCharts_stationary k
  exact exists_separated_shrink (norm_axisVector k) C

end Problem356.CoulombSupportExistence

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Set

namespace Problem356.FiveComponentGeometry

/-- The actual symmetric two-graph contact relation yields the exact selector
needed by the final construction. Graph-wide outer exclusions are supplied by
`CoulombSupportExistence.exists_separated_shrink`; the final central ball can
be any subset of the excluded central neighborhood. -/
theorem second_selects_four_of_excluded_charts
    (C₁ : ChartsAt (CenterCertificate.point 1))
    (C₂ : ChartsAt (CenterCertificate.point 3))
    {B V : Set E3} (hB : B ⊆ V)
    (houter₁ : ∀ s ∈ C₁.charts.central.source, s ∉ V ∧ C₁.charts.opposite s ∉ V)
    (houter₂ : ∀ s ∈ C₂.charts.central.source, s ∉ V ∧ C₂.charts.opposite s ∉ V)
    {x y z : E3} (hx : x ∈ B) (hc : branchContact C₁ C₂ (x, (y, z))) :
    ∃ i : Fin 4, y = CommonBranches.four
      ![C₁.charts.central, C₂.charts.central]
      ![C₁.charts.opposite, C₂.charts.opposite] i x := by
  rcases hc with ⟨s, hs, hp⟩ | ⟨s, hs, hp⟩
  · have ho := houter₁ s hs
    exact ContactSelection.second_selects_common_four _ _ (k := 0) hp hx hs
      (fun h => ho.1 (hB h)) (fun h => ho.2 (hB h))
  · have ho := houter₂ s hs
    exact ContactSelection.second_selects_common_four _ _ (k := 1) hp hx hs
      (fun h => ho.1 (hB h)) (fun h => ho.2 (hB h))

end Problem356.FiveComponentGeometry

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry CenterCertificate

theorem ennreal_graph_contact {a : E3} (C : ChartsAt a) {s : E3}
    (hs : s ∈ C.charts.central.source)
    (hxy : 0 < dist (C.charts.central s) s)
    (hxz : 0 < dist (C.charts.central s) (C.charts.opposite s))
    (hyz : 0 < dist s (C.charts.opposite s)) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖C.charts.central s‖ ^ 2) + C.value s +
      ((5 : ℝ) / 4 * ⟪a, C.charts.opposite s + a⟫_ℝ -
        10 * ‖C.charts.opposite s + a‖ ^ 2)) =
      coulombCost (C.charts.central s, (s, C.charts.opposite s)) := by
  have ht := C.charts.mapsTo_state hs
  rw [C.state_ball, ← ball_prod_same] at ht
  exact (ennreal_local_certificate C (C.source_ball ▸ hs) ht.1 ht.2 hxy hxz hyz).2.mpr
    ⟨rfl, rfl⟩

/-- The actual five-component certificate discharges every local-geometry
input, after choosing a sufficiently small common central ball. -/
theorem fullConclusion_of_five_component_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (hout₁ : ∀ s ∈ C₁.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₁.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    (hout₂ : ∀ s ∈ C₂.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₂.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    {R : ℝ} (hR : 0 < R)
    (hdisj : Pairwise (fun i j : Fin 5 => Disjoint (ball (point i) R) (ball (point j) R)))
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x, |u x| ≤ M)
    (hueq : ∀ i x, x ∈ ball (point i) R → u x = potentials C₁ C₂ i x)
    (hcert : ∀ x ∈ ⋃ i : Fin 5, ball (point i) R,
      ∀ y ∈ ⋃ i : Fin 5, ball (point i) R, ∀ z ∈ ⋃ i : Fin 5, ball (point i) R,
      ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
        branchContact C₁ C₂ (x, (y, z)))) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  let X : Fin 2 → OpenPartialHomeomorph E3 E3 := ![C₁.charts.central, C₂.charts.central]
  let Z : Fin 2 → OpenPartialHomeomorph E3 E3 := ![C₁.charts.opposite, C₂.charts.opposite]
  let a : Fin 2 → E3 := ![point 1, point 3]
  let P : Fin 2 → Set E3 := ![ball (point 1) R, ball (point 3) R]
  let Q : Fin 2 → Set E3 := ![ball (point 2) R, ball (point 4) R]
  have haX : ∀ i, a i ∈ (X i).source := by
    intro i; fin_cases i
    · exact C₁.charts.point_mem
    · exact C₂.charts.point_mem
  have haZ : ∀ i, a i ∈ (Z i).source := by
    intro i; fin_cases i
    · exact C₁.charts.source_eq ▸ C₁.charts.point_mem
    · exact C₂.charts.source_eq ▸ C₂.charts.point_mem
  have hcenter : ∀ i, X i (a i) = 0 := by
    intro i; fin_cases i
    · exact C₁.charts.central_value
    · exact C₂.charts.central_value
  have hP : ∀ i, IsOpen (P i) := by intro i; fin_cases i <;> exact isOpen_ball
  have hQ : ∀ i, IsOpen (Q i) := by intro i; fin_cases i <;> exact isOpen_ball
  have haP : ∀ i, a i ∈ P i := by intro i; fin_cases i <;> exact mem_ball_self hR
  have haQ : ∀ i, Z i (a i) ∈ Q i := by
    intro i; fin_cases i
    · change C₁.charts.opposite (point 1) ∈ ball (point 2) R
      rw [C₁.charts.opposite_value, point_two_eq_neg]
      exact mem_ball_self hR
    · change C₂.charts.opposite (point 3) ∈ ball (point 4) R
      rw [C₂.charts.opposite_value, point_four_eq_neg]
      exact mem_ball_self hR
  obtain ⟨r, hr, hsub, hlocal⟩ := CommonBranches.exists_common_central_ball_in_components
    X Z a 0 haX haZ hcenter P Q hP hQ haP haQ
    (isOpen_ball.inter isOpen_ball)
    (show (0 : E3) ∈ ball 0 R ∩ ball 0 (1 / 4) from
      ⟨mem_ball_self hR, mem_ball_self (by norm_num)⟩)
  let e := CommonBranches.four X Z
  have hBS : ∀ i, ball (0 : E3) r ⊆ (CommonBranches.outer (X i) (Z i)).source :=
    fun i x hx => (hlocal i x hx).1
  have hsource : ∀ i, ball (0 : E3) r ⊆ (e i).source :=
    CommonBranches.subset_four_sources X Z hBS
  have hB0 : ball (0 : E3) r ⊆ ball (point 0) R := by
    have hp0 : point 0 = (0 : E3) := by
      ext i; fin_cases i <;> rfl
    rw [hp0]
    exact fun x hx => (hsub hx).1
  have himages : ∀ i, e i '' ball (0 : E3) r ⊆ ball (point i.succ) R := by
    rintro i _ ⟨x, hx, rfl⟩
    fin_cases i
    · exact (hlocal 0 x hx).2.1
    · exact (hlocal 0 x hx).2.2
    · exact (hlocal 1 x hx).2.1
    · exact (hlocal 1 x hx).2.2
  have he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source := by
    apply CommonBranches.contDiffOn_four
    · intro i; fin_cases i
      · exact C₁.charts.central_inverse_analytic.of_le (by simp)
      · exact C₂.charts.central_inverse_analytic.of_le (by simp)
    · intro i; fin_cases i
      · exact C₁.charts.opposite_analytic.of_le (by simp)
      · exact C₂.charts.opposite_analytic.of_le (by simp)
  have he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target := by
    apply CommonBranches.contDiffOn_four_symm
    · intro i; fin_cases i
      · exact C₁.charts.central_analytic.of_le (by simp)
      · exact C₂.charts.central_analytic.of_le (by simp)
    · intro i; fin_cases i
      · exact C₁.charts.opposite_inverse_analytic.of_le (by simp)
      · exact C₂.charts.opposite_inverse_analytic.of_le (by simp)
  have hmem (i : Fin 4) {x : E3} (hx : x ∈ ball (0 : E3) r) :
      e i x ∈ ball (point i.succ) R := himages i ⟨x, hx, rfl⟩
  have hdist {i j : Fin 5} (hij : i ≠ j) {x y : E3}
      (hx : x ∈ ball (point i) R) (hy : y ∈ ball (point j) R) : 0 < dist x y := by
    apply dist_pos.mpr
    intro heq
    exact Set.disjoint_left.mp (hdisj hij) hx (heq ▸ hy)
  have hcontact (i : Fin 2) (x : E3) (hx : x ∈ ball (0 : E3) r) :
      ENNReal.ofReal (u x + u ((X i).symm x) + u (CommonBranches.outer (X i) (Z i) x)) =
        coulombCost (x, ((X i).symm x, CommonBranches.outer (X i) (Z i) x)) := by
    have hprop := CommonBranches.outer_source_properties (X i) (Z i) (hBS i hx)
    fin_cases i
    · change ENNReal.ofReal (u x + u (C₁.charts.central.symm x) +
          u (C₁.charts.opposite (C₁.charts.central.symm x))) =
        coulombCost (x, (C₁.charts.central.symm x, C₁.charts.opposite (C₁.charts.central.symm x)))
      have hy : C₁.charts.central.symm x ∈ ball (point 1) R := hmem 0 hx
      have hz : C₁.charts.opposite (C₁.charts.central.symm x) ∈ ball (point 2) R := hmem 1 hx
      have hinv : C₁.charts.central (C₁.charts.central.symm x) = x := hprop.2.2.2.2
      rw [hueq 0 x (hB0 hx), hueq 1 _ hy, hueq 2 _ hz]
      have hc := ennreal_graph_contact C₁ (s := C₁.charts.central.symm x) hprop.2.1
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 1) (hB0 hx) hy)
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 2) (hB0 hx) hz)
        (hdist (by decide : (1 : Fin 5) ≠ 2) hy hz)
      simpa [potentials, hinv] using hc
    · change ENNReal.ofReal (u x + u (C₂.charts.central.symm x) +
          u (C₂.charts.opposite (C₂.charts.central.symm x))) =
        coulombCost (x, (C₂.charts.central.symm x, C₂.charts.opposite (C₂.charts.central.symm x)))
      have hy : C₂.charts.central.symm x ∈ ball (point 3) R := hmem 2 hx
      have hz : C₂.charts.opposite (C₂.charts.central.symm x) ∈ ball (point 4) R := hmem 3 hx
      have hinv : C₂.charts.central (C₂.charts.central.symm x) = x := hprop.2.2.2.2
      rw [hueq 0 x (hB0 hx), hueq 3 _ hy, hueq 4 _ hz]
      have hc := ennreal_graph_contact C₂ (s := C₂.charts.central.symm x) hprop.2.1
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 3) (hB0 hx) hy)
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 4) (hB0 hx) hz)
        (hdist (by decide : (3 : Fin 5) ≠ 4) hy hz)
      simpa [potentials, hinv] using hc
  apply exists_fullCoulombConclusion_of_local_geometry 0 hr e hsource
    (SmoothBranchMarginal.componentRegion_pairwise_of_subsets hdisj hB0 himages) he he'
    (MeasurableSet.iUnion fun _ => isOpen_ball.measurableSet)
    (fun x hx => mem_iUnion.mpr ⟨0, hB0 hx⟩)
    (fun i x hx => mem_iUnion.mpr ⟨i.succ, himages i hx⟩)
    hu hM (fun x _ => abs_le.mp (hubound x))
    (fun t h1 h2 h3 => (hcert _ h1 _ h2 _ h3).1)
    (hcontact 0) (hcontact 1)
  intro x y z hx hy hz hc
  have hc' := (hcert x (mem_iUnion.mpr ⟨0, hB0 hx⟩) y hy z hz).2 hc
  rcases hc' with ⟨s, hs, hp⟩ | ⟨s, hs, hp⟩
  · have hy' := ContactSelection.second_selects_inverse_branch hp hx hs
      (fun s hs => ⟨fun h => (hout₁ s hs).1 (hsub h).2,
        fun h => (hout₁ s hs).2 (hsub h).2⟩)
      (fun s hs => C₁.charts.central.left_inv hs)
      (show ∀ w ∈ ball (0 : E3) r,
        CommonBranches.outer C₁.charts.central C₁.charts.opposite w =
          C₁.charts.opposite (C₁.charts.central.symm w) from fun _ _ => rfl)
    rcases hy' with hy' | hy'
    · exact ⟨0, hy'⟩
    · exact ⟨1, hy'⟩
  · have hy' := ContactSelection.second_selects_inverse_branch hp hx hs
      (fun s hs => ⟨fun h => (hout₂ s hs).1 (hsub h).2,
        fun h => (hout₂ s hs).2 (hsub h).2⟩)
      (fun s hs => C₂.charts.central.left_inv hs)
      (show ∀ w ∈ ball (0 : E3) r,
        CommonBranches.outer C₂.charts.central C₂.charts.opposite w =
          C₂.charts.opposite (C₂.charts.central.symm w) from fun _ _ => rfl)
    rcases hy' with hy' | hy'
    · exact ⟨2, hy'⟩
    · exact ⟨3, hy'⟩

/-- The unconditional witness: the actual separated local Coulomb charts
and their global certificate supply all inputs of the construction. -/
theorem exists_full_coulomb_conclusion :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  have hp1 : point 1 = CoulombCalculus.axisVector 0 := by
    ext i; fin_cases i <;> norm_num [point, CoulombCalculus.axisVector]
  have hp3 : point 3 = CoulombCalculus.axisVector 1 := by
    change (!₂[0, 1, 0] : E3) = CoulombCalculus.axisVector 1
    ext i; fin_cases i <;> norm_num [CoulombCalculus.axisVector]
  have h₁ := CoulombSupportExistence.exists_coulombLocalSupportingCharts_separated 0
  have h₂ := CoulombSupportExistence.exists_coulombLocalSupportingCharts_separated 1
  rw [← hp1] at h₁
  rw [← hp3] at h₂
  obtain ⟨C₁, hout₁⟩ := h₁
  obtain ⟨C₂, hout₂⟩ := h₂
  obtain ⟨R, M, hR, hM, _, hdisj, hu, _, hubound, hcert⟩ :=
    exists_global_certificate C₁ C₂
  apply fullConclusion_of_five_component_certificate C₁ C₂ hout₁ hout₂ hR hdisj hu
    hM.le hubound ?_ hcert
  intro i x hx
  exact ComponentPotential.glue_eq hdisj hx

end Problem356.FiveComponentGeometry

end

end OAI
end
end

section
section

end
end

section
section
namespace OAI

namespace Problem356

theorem coulomb_counterexample_and_equal_infima_oai :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  exact FiveComponentGeometry.exists_full_coulomb_conclusion

end Problem356

end OAI
end
end

section
section

end
end

theorem solution : type_of% @OAI.Problem356.coulomb_counterexample_and_equal_infima_oai := @OAI.Problem356.coulomb_counterexample_and_equal_infima_oai
