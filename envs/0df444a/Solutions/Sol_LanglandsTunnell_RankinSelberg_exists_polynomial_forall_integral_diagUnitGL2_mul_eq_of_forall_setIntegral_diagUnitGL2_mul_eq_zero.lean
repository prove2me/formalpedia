-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0344bb0f-06a2-5d99-b128-571ecbd99b68

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped Topology

namespace KcTorusMellin

noncomputable section

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem setIntegral_eq_setIntegral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [μ.IsMulLeftInvariant] {S T : Set G} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (k₀ : G) (hST : ∀ y, y ∈ T ↔ k₀⁻¹ * y ∈ S) (f : G → E) :
    ∫ y in T, f y ∂μ = ∫ x in S, f (k₀ * x) ∂μ := by
  rw [← integral_indicator hT, ← integral_indicator hS]
  have hpt : ∀ x, S.indicator (fun x => f (k₀ * x)) x = T.indicator f (k₀ * x) := by
    intro x
    by_cases hx : x ∈ S
    · have : k₀ * x ∈ T := by rw [hST, inv_mul_cancel_left]; exact hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem this]
    · have : k₀ * x ∉ T := by rw [hST, inv_mul_cancel_left]; exact hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
  simp_rw [hpt]
  exact (integral_mul_left_eq_self _ k₀).symm

end Generic

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)

scoped instance borelSpace_units_adic : BorelSpace (HeightOneSpectrum.adicCompletion K v)ˣ := borelSpace_units

def sph : Set (HeightOneSpectrum.adicCompletion K v)ˣ := {u | Valued.v (u : F) = 1}

def shell (n : ℤ) : Set (HeightOneSpectrum.adicCompletion K v)ˣ := {a | Valued.v (a : F) = WithZero.exp (-n)}

theorem val_eq_one_iff_norm_eq_one (x : F) : Valued.v x = 1 ↔ ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def]
  have h1 : (1 : ℝ) = ((1 : NNReal) : ℝ) := rfl
  rw [h1, NNReal.coe_inj, WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v))]

theorem sph_eq_preimage : sph K v = Units.val ⁻¹' Metric.sphere (0 : F) 1 := by
  ext u
  simp only [sph, Set.mem_setOf_eq, Set.mem_preimage, mem_sphere_zero_iff_norm]
  exact val_eq_one_iff_norm_eq_one K v _

theorem isOpen_sph : IsOpen (sph K v) := by
  rw [sph_eq_preimage]
  exact (IsUltrametricDist.isOpen_sphere (0 : F) one_ne_zero).preimage Units.continuous_val

theorem measurableSet_sph : MeasurableSet (sph K v) := (isOpen_sph K v).measurableSet

variable {K v}
variable {ϖ : HeightOneSpectrum.adicCompletionIntegers K v}
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
  (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers K v)
    (HeightOneSpectrum.adicCompletion K v) ϖ) = WithZero.exp (-1 : ℤ))

abbrev piU : (HeightOneSpectrum.adicCompletion K v)ˣ := Units.mk0 (algebraMap _ F ϖ) hπ

include hϖ in
theorem v_piU_zpow (n : ℤ) : Valued.v ((piU hπ ^ n : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  change Valued.v (algebraMap _ F ϖ) ^ n = _
  rw [hϖ, ← WithZero.exp_zsmul]
  congr 1; ring

include hϖ in

theorem mem_shell_iff (n : ℤ) (a : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    a ∈ shell K v n ↔ (piU hπ ^ n)⁻¹ * a ∈ sph K v := by
  simp only [shell, sph, Set.mem_setOf_eq, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    v_piU_zpow hπ hϖ]
  rw [inv_mul_eq_one₀ WithZero.exp_ne_zero]
  exact eq_comm

include hϖ in
theorem shell_eq_preimage (n : ℤ) :
    shell K v n = (fun a => (piU hπ ^ n)⁻¹ * a) ⁻¹' sph K v := by
  ext a; exact mem_shell_iff hπ hϖ n a

include hπ hϖ in
theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell K v n) := by
  rw [shell_eq_preimage hπ hϖ]
  exact ((isOpen_sph K v).preimage (continuous_const.mul continuous_id)).measurableSet

theorem pairwise_disjoint_shell : Pairwise (fun m n : ℤ => Disjoint (shell K v m) (shell K v n)) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro a ha hb
  simp only [shell, Set.mem_setOf_eq] at ha hb
  rw [ha] at hb
  exact hmn (neg_injective (WithZero.exp_injective hb))

theorem iUnion_shell : (⋃ n : ℤ, shell K v n) = Set.univ := by
  refine Set.eq_univ_of_forall fun a => Set.mem_iUnion.mpr ?_
  have ha : Valued.v (a : F) ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact a.ne_zero
  refine ⟨-WithZero.log (Valued.v (a : F)), ?_⟩
  simp only [shell, Set.mem_setOf_eq, neg_neg]
  rw [WithZero.exp_log ha]

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

theorem norm_eq_one_of_v_eq_one {x : F} (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

include hϖ in

theorem norm_uniformizer : ‖algebraMap _ F ϖ‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [this]
  simp

variable (v) in

abbrev qC : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

theorem qC_ne_zero : qC v ≠ 0 := by
  exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)

theorem log_qC_im : (Complex.log (qC v)).im = 0 := by
  rw [qC, show ((Ideal.absNorm v.asIdeal : ℂ)) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_log (by positivity), Complex.ofReal_im]

theorem qC_cpow_cpow (y z : ℂ) (hy : y.im = 0) : ((qC v) ^ y) ^ z = (qC v) ^ (y * z) := by
  rw [Complex.cpow_mul]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos.le]

include hϖ in

theorem modulus_piU_zpow_mul {u : (HeightOneSpectrum.adicCompletion K v)ˣ} (hu : Valued.v (u : F) = 1) (n : ℤ) :
    ((modulus ((piU hπ ^ n * u : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) =
      qC v ^ ((-(n : ℂ))) := by
  rw [coe_modulus_eq_norm, Units.val_mul, norm_mul, norm_eq_one_of_v_eq_one hu, mul_one, Units.val_zpow_eq_zpow_val,
    norm_zpow, show ((piU hπ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = algebraMap _ F ϖ from rfl,
    norm_uniformizer hϖ, inv_zpow', Complex.ofReal_zpow, ← Complex.cpow_intCast]
  push_cast
  rfl

theorem laurent_pack (T : Finset ℤ) (d : ℤ → ℂ) :
    ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ,
      ∑ n ∈ T, d n * qC v ^ (-(n : ℂ) * s) = qC v ^ ((m : ℂ) * s) * P.eval (qC v ^ (-s)) := by
  classical

  set m : ℤ := ∑ n ∈ T, |n| with hm
  have hnm : ∀ n ∈ T, 0 ≤ n + m := by
    intro n hn
    have h1 : |n| ≤ m := by
      rw [hm]; exact Finset.single_le_sum (fun i _ => abs_nonneg i) hn
    have h2 : -n ≤ |n| := neg_le_abs n
    omega
  refine ⟨∑ n ∈ T, Polynomial.C (d n) * Polynomial.X ^ (n + m).toNat, m, fun s => ?_⟩
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Complex.cpow_nat_mul,
    show (((n + m).toNat : ℕ) : ℂ) = ((n + m : ℤ) : ℂ) by rw [← Int.cast_natCast, Int.toNat_of_nonneg (hnm n hn)]]
  have hq := qC_ne_zero (v := v)
  rw [mul_left_comm, ← Complex.cpow_add _ _ hq]
  congr 1
  congr 1
  push_cast
  ring

include hϖ in
theorem main (B : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
    (χ : (HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ)
    (h : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
    (ν : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [ν.IsHaarMeasure]
    (hTF : ∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
      ∫ u in {u : (HeightOneSpectrum.adicCompletion K v)ˣ | Valued.v (u : F) = 1},
        B (diagUnitGL2 (Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers K v)
          (HeightOneSpectrum.adicCompletion K v) ϖ) hπ ^ n * u) * h) * ((χ u : ℂˣ) : ℂ) ∂ν = 0)
    (σ₀ : ℝ)
    (hint : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun a : (HeightOneSpectrum.adicCompletion K v)ˣ =>
        B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (s - 1)) ν) :
    ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ, σ₀ < s.re →
      ∫ a, B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (s - 1) ∂ν =
        (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  classical
  obtain ⟨T, hT⟩ := hTF

  set I : ℤ → ℂ := fun n => ∫ u in sph K v, B (diagUnitGL2 (piU hπ ^ n * u) * h) * ((χ u : ℂˣ) : ℂ) ∂ν with hI
  have hI0 : ∀ n : ℤ, n ∉ T → I n = 0 := fun n hn => hT n hn

  set d : ℤ → ℂ := fun n => ((χ (piU hπ) : ℂˣ) : ℂ) ^ n * qC v ^ ((n : ℂ)) * I n with hd
  obtain ⟨P, m, hP⟩ := laurent_pack (v := v) T d
  refine ⟨P, m, fun s hs => ?_⟩
  have hq := qC_ne_zero (v := v)
  set f : (HeightOneSpectrum.adicCompletion K v)ˣ → ℂ := fun a =>
    B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (s - 1) with hf

  have hsum : HasSum (fun n : ℤ => ∫ a in shell K v n, f a ∂ν) (∫ a, f a ∂ν) := by
    have := hasSum_integral_iUnion (μ := ν) (f := f) (measurableSet_shell hπ hϖ)
      (pairwise_disjoint_shell (K := K) (v := v)) (by rw [iUnion_shell]; exact (hint s hs).integrableOn)
    rwa [iUnion_shell, Measure.restrict_univ] at this

  have hshell : ∀ n : ℤ, ∫ a in shell K v n, f a ∂ν = d n * qC v ^ (-(n : ℂ) * s) := by
    intro n
    rw [setIntegral_eq_setIntegral_comp_mul_left ν (measurableSet_sph K v) (measurableSet_shell hπ hϖ n) (piU hπ ^ n)
      (fun a => mem_shell_iff hπ hϖ n a) f]
    have hpt : ∀ u ∈ sph K v, f (piU hπ ^ n * u) =
        (((χ (piU hπ) : ℂˣ) : ℂ) ^ n * qC v ^ (-(n : ℂ) * (s - 1))) *
          (B (diagUnitGL2 (piU hπ ^ n * u) * h) * ((χ u : ℂˣ) : ℂ)) := by
      intro u hu
      simp only [hf]
      rw [modulus_piU_zpow_mul hπ hϖ hu, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val,
        qC_cpow_cpow _ _ (by simp)]
      ring
    rw [setIntegral_congr_fun (measurableSet_sph K v) hpt, integral_const_mul]
    simp only [hd, hI]
    have hsplit : qC v ^ (-(n : ℂ) * (s - 1)) = qC v ^ ((n : ℂ)) * qC v ^ (-(n : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hq]; congr 1; ring
    rw [hsplit]
    ring

  have hsum' : HasSum (fun n : ℤ => d n * qC v ^ (-(n : ℂ) * s)) (∫ a, f a ∂ν) := by
    simpa only [hshell] using hsum
  have hfin : HasSum (fun n : ℤ => d n * qC v ^ (-(n : ℂ) * s)) (∑ n ∈ T, d n * qC v ^ (-(n : ℂ) * s)) := by
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    simp only [hd]
    rw [hI0 n hn]; ring
  rw [show (∫ a, B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (s - 1) ∂ν) = ∫ a, f a ∂ν
    from rfl, hsum'.unique hfin, hP s]

end

end KcTorusMellin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero.KcTorusMellin"

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (B : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (h : GL (Fin 2) (v.adicCompletion K)) :
    letI := localBorel K v
    ∀ (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      (∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
          B (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n * u) *
            h) * ((χ u : ℂˣ) : ℂ) ∂ν = 0) →
      ∀ σ₀ : ℝ,
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun a : (v.adicCompletion K)ˣ =>
            B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1)) ν) →
        ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ, σ₀ < s.re →
          ∫ a, B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1) ∂ν =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  intro ν _ hTF σ₀ hint
  exact KcTorusMellin.main hπ hϖ B χ h ν hTF σ₀ hint

end S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero (solution)
