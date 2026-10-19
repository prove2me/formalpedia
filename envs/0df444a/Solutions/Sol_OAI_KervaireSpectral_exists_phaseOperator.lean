-- Prove2me | solution 1 for OAI.KervaireSpectral.exists_phaseOperator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:40:28.360509+00:00
-- url     : https://prove2.me/submissions/01dfbf36-6610-48a3-9010-3d036a3ea25c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralLogarithm.lean:L19-L100
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.exists_phaseOperator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Theorems.Thm_OAI_KervaireSpectral_exists_strongLimit
import Theorems.Thm_OAI_KervaireSpectral_tendsto_calculus
import Theorems.Thm_OAI_KervaireStrong_StrongTendsto_exp
import Theorems.Thm_OAI_KervaireStrong_StrongTendsto_nonneg

-- ---- from OAI.GroupTheory.Kervaire.StrongLimits ----
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace KervaireStrong
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
/-- A strong limit preserves commutation with any fixed bounded operator. -/
theorem StrongTendsto.commute {T : ι → Operator H} {S R : Operator H} [l.NeBot]
    (h : StrongTendsto T l S) (hc : ∀ i, Commute (T i) R) : Commute S R := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact tendsto_nhds_unique (h (R ξ))
    ((R.continuous.tendsto (S ξ)).comp (h ξ) |>.congr fun i =>
      congrArg (fun L : Operator H => L ξ) (hc i).eq.symm)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open scoped ComplexOrder

end KervaireStrong

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralMeasures ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The defining integration identity for the scalar spectral measure. -/
theorem integral_vectorMeasure (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂vectorMeasure U ξ = (inner ℂ ξ (cfcHom hU (complexify f) ξ)).re := by
  let fc : C_c(spectrum ℂ U, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (vectorFunctional U ξ) fc

theorem phase_nonneg (z : ℂ) : 0 ≤ phase z := Int.fract_nonneg _

theorem phase_lt_one (z : ℂ) : phase z < 1 := Int.fract_lt_one _

theorem phaseTriangle_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    0 ≤ phaseTriangle n x := by
  exact le_min hx (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hx'))

theorem phaseTriangle_le_self (n : ℕ) (x : ℝ) : phaseTriangle n x ≤ x := min_le_left _ _

theorem tendsto_phaseTriangle {x : ℝ} (hx : x < 1) :
    Tendsto (fun n => phaseTriangle n x) atTop (𝓝 x) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * (1 - x)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos (by linarith) tendsto_const_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [ht.eventually (eventually_ge_atTop x)] with n hn
  exact (min_eq_left hn).symm

theorem phaseApprox_nonneg (U : Operator H) (hU : U ∈ unitary (Operator H))
    (n : ℕ) (z : spectrum ℂ U) : 0 ≤ phaseApprox U hU n z :=
  phaseTriangle_nonneg n (phase_nonneg _) (phase_lt_one _).le

theorem phaseApprox_le_one (U : Operator H) (hU : U ∈ unitary (Operator H))
    (n : ℕ) (z : spectrum ℂ U) : phaseApprox U hU n z ≤ 1 :=
  (phaseTriangle_le_self n _).trans (phase_lt_one _).le

theorem tendsto_phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H))
    (z : spectrum ℂ U) : Tendsto (fun n => phaseApprox U hU n z) atTop (𝓝 (phase z)) :=
  tendsto_phaseTriangle (phase_lt_one _)

theorem tendsto_integral_phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) : letI := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => ∫ z, phaseApprox U hU n z ∂vectorMeasure U ξ)
      atTop (𝓝 (vectorPhase U ξ)) := by
  let := isStarNormal_of_mem_unitary hU
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (phaseApprox U hU n).continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseApprox_nonneg U hU n z)]
    exact phaseApprox_le_one U hU n z
  · exact Eventually.of_forall (tendsto_phaseApprox U hU)

/-- Exponentiating the chosen phase recovers a point on the unit circle. -/
theorem exp_phase {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp ((2 * Real.pi * phase z : ℝ) * Complex.I) = z := by
  have ha : 2 * Real.pi * phase z = z.arg - 2 * Real.pi *
      (Int.floor (z.arg / (2 * Real.pi)) : ℝ) := by
    unfold phase Int.fract
    field_simp
  change (Circle.exp (2 * Real.pi * phase z) : ℂ) = z
  rw [ha, Circle.exp_sub, Circle.exp_two_pi_mul_int, div_one]
  simpa only [hz, Complex.ofReal_one, one_mul, Circle.coe_exp] using
    Complex.norm_mul_exp_arg_mul_I z

/-- The normed-ring exponential on continuous functions is pointwise. -/
theorem expMap_eq_exp {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, ℂ)) : expMap f = NormedSpace.exp f := by
  ext z
  symm
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ,
    expMap, ContinuousMap.coe_mk] using
    (NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ z) (continuous_eval_const z) f)

/-- The continuous functional calculus respects the operator exponential. -/
theorem calculus_expMap (U : Operator H) [hU : IsStarNormal U]
    (f : C(spectrum ℂ U, ℂ)) :
    cfcHom hU (expMap f) = NormedSpace.exp (cfcHom hU f) := by
  let : NormedAlgebra ℚ (Operator H) := NormedAlgebra.restrictScalars ℚ ℂ (Operator H)
  rw [expMap_eq_exp]
  exact NormedSpace.map_exp (cfcHom hU) (cfcHom_continuous hU) f

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralLogarithm ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open KervaireStrong

theorem exists_phaseOperator (U : Operator H) (hU : U ∈ unitary (Operator H)) :
    letI := isStarNormal_of_mem_unitary hU
    ∃ B : Operator H, 0 ≤ B ∧ B ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      NormedSpace.exp ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • B) = U ∧
      (∀ ξ, (inner ℂ ξ (B ξ)).re = vectorPhase U ξ) ∧
      ∀ R, Commute U R → Commute (star U) R → Commute B R := by
  let hN := isStarNormal_of_mem_unitary hU
  let := hN
  let f (n : ℕ) : C(spectrum ℂ U, ℂ) := complexify (phaseApprox U hU n)
  have hb : ∀ n z, ‖f n z‖ ≤ 1 := by
    intro n z
    simp only [f, complexify_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (phaseApprox_nonneg U hU n z)]
    exact phaseApprox_le_one U hU n z
  have ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (phase z : ℂ)) := by
    intro z
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_phaseApprox U hU z)
  obtain ⟨B, hB, hnormB⟩ := exists_strongLimit U f (fun z => (phase z : ℂ)) 1 zero_le_one hb ht
  have hbs : StrongTendsto (fun n => cfcHom hN (f n)) atTop B := hB
  have hnorm : ∀ n, ‖cfcHom hN (f n)‖ ≤ 1 := by
    intro n
    rw [norm_cfcHom U (f n) hN]
    exact ((f n).norm_le zero_le_one).mpr (hb n)
  have hpos : 0 ≤ B := hbs.nonneg fun n =>
    (cfcHom_nonneg_iff hN).mpr fun z =>
      (Complex.zero_le_real).mpr (phaseApprox_nonneg U hU n z)
  have hle : B ≤ 1 := by
    apply sub_nonneg.mp
    apply KervaireStrong.StrongTendsto.nonneg (T := fun n => 1 - cfcHom hN (f n))
      (l := atTop)
    · intro ξ
      simpa only [sub_apply] using (tendsto_const_nhds (x := (1 : Operator H) ξ)).sub (hB ξ)
    · intro n
      have hn : 0 ≤ cfcHom hN (1 - f n) := by
        apply (cfcHom_nonneg_iff hN).mpr
        intro z
        change 0 ≤ 1 - (phaseApprox U hU n z : ℂ)
        exact sub_nonneg.mpr (by exact_mod_cast phaseApprox_le_one U hU n z)
      simpa only [map_sub, map_one] using hn
  refine ⟨B, hpos, hle, hnormB, ?_, ?_, ?_⟩
  · let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
    have hcbs : StrongTendsto (fun n => c • cfcHom hN (f n)) atTop (c • B) := by
      intro ξ
      exact (hB ξ).const_smul c
    have hcb : ∀ n, ‖c • cfcHom hN (f n)‖ ≤ ‖c‖ := by
      intro n
      rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg c)
    have hexp := hcbs.exp (norm_nonneg c) hcb
    have heq (n : ℕ) : NormedSpace.exp (c • cfcHom hN (f n)) =
        cfcHom hN (expMap (c • f n)) := by
      rw [← map_smul]
      exact (calculus_expMap U (c • f n)).symm
    let g : C(spectrum ℂ U, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
    have hgb : ∀ n z, ‖expMap (c • f n) z‖ ≤ 1 := by
      intro n z
      simp [expMap, f, complexify, c, Complex.norm_exp, Complex.mul_re]
    have hgt : ∀ z, Tendsto (fun n => expMap (c • f n) z) atTop (𝓝 (g z)) := by
      intro z
      have hz := Complex.continuous_exp.continuousAt.tendsto.comp ((ht z).const_mul c)
      have he : Complex.exp (c * (phase z : ℂ)) = (z : ℂ) := by
        convert exp_phase (CStarRing.norm_of_mem_unitary
          (spectrum_subset_unitary_of_mem_unitary hU z.property)) using 1
        · congr 1
          simp only [c, Complex.ofReal_mul]
          ring
      simpa only [expMap, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
        smul_eq_mul, Function.comp_def, he, g, ContinuousMap.restrict_apply,
        ContinuousMap.id_apply] using hz
    have hexpU := tendsto_calculus U (fun n => expMap (c • f n)) g 1 zero_le_one hgb hgt
    apply ContinuousLinearMap.ext
    intro ξ
    apply tendsto_nhds_unique (hexp ξ)
    simpa only [heq, g, cfcHom_id] using hexpU ξ
  · intro ξ
    have ht1 := Complex.continuous_re.continuousAt.tendsto.comp
      (Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := ξ)) (hB ξ))
    have ht2 := tendsto_integral_phaseApprox U hU ξ
    simp_rw [integral_vectorMeasure] at ht2
    exact tendsto_nhds_unique ht1 ht2
  · intro R hR hRstar
    exact hbs.commute fun n => hR.cfcHom hN hRstar (f n)

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open KervaireStrong


theorem solution : type_of% @_root_.OAI.KervaireSpectral.exists_phaseOperator := @_root_.OAI.KervaireSpectral.exists_phaseOperator
