-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2de41e32-a6ea-5974-b43d-621eaa3d3c13

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Mathlib
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_finset_eq_sum_smul_shell_character_kirillov_of_cuspidal
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
import Theorems.Thm_LanglandsTunnell_RankinSelberg_shell_constants_mul_eq_centralChar_neg_one_of_weylJ_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal UnramifiedWhittaker Topology Filter
open scoped NNReal ENNReal Classical Pointwise

namespace TorusShellSumEngine

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem norm_eq_zpow_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

theorem modulus_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ m := by
  rw [← NNReal.coe_inj, coe_modulus_of_valued v hx, NNReal.coe_zpow, NNReal.coe_natCast]

theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  positivity

theorem one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    omega
  exact_mod_cast h2

theorem two_le_absNorm : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    omega
  exact_mod_cast h2

theorem isClosed_ball (k : ℤ) : IsClosed {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem isOpen_ball (k : ℤ) : IsOpen {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem sphere_eq_diff (k : ℤ) :
    {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k}
      = {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp k} \
          {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp (k - 1)} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨hy.le, fun h => ?_⟩
    rw [hy, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm]
    congr 1
    omega

theorem isClosed_sphere (k : ℤ) : IsClosed {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

theorem isOpen_sphere (k : ℤ) : IsOpen {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isOpen_ball v _).sdiff (isClosed_ball v _)

theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

theorem isCompact_ball_zero : IsCompact {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

theorem isCompact_units_setF : IsCompact {u : (v.adicCompletion K) | Valued.v u = 1} := by
  refine (isCompact_ball_zero v).of_isClosed_subset ?_ ?_
  · have := isClosed_sphere v 0
    rwa [WithZero.exp_zero] at this
  · intro u hu
    have hu' : Valued.v u = 1 := hu
    show Valued.v u ≤ WithZero.exp 0
    rw [hu', WithZero.exp_zero]

def USet : Set (v.adicCompletion K)ˣ := {u : (v.adicCompletion K)ˣ | Valued.v (u : (v.adicCompletion K)) = 1}

def shell (n : ℤ) : Set (v.adicCompletion K)ˣ :=
  {y : (v.adicCompletion K)ˣ | Valued.v (y : (v.adicCompletion K)) = WithZero.exp (-n)}

theorem shell_zero : shell v 0 = USet v := by
  ext y; simp [shell, USet]

theorem image_val_USet : Units.val '' USet v = {u : (v.adicCompletion K) | Valued.v u = 1} := by
  ext x
  simp only [Set.mem_image, USet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem isCompact_USet : IsCompact (USet v) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, image_val_USet]
  exact isCompact_units_setF v

theorem isClosed_shell (n : ℤ) : IsClosed (shell v n) :=
  (isClosed_sphere v (-n)).preimage Units.continuous_val

theorem isOpen_shell (n : ℤ) : IsOpen (shell v n) :=
  (isOpen_sphere v (-n)).preimage Units.continuous_val

theorem isOpen_USet : IsOpen (USet v) := by rw [← shell_zero]; exact isOpen_shell v 0

theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell v)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro y hym hyn
  simp only [shell, Set.mem_setOf_eq] at hym hyn
  rw [hym] at hyn
  exact hmn (by have := WithZero.exp_injective hyn; omega)

theorem iUnion_shell : (⋃ n, shell v n) = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, shell, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have hne : Valued.v (y : (v.adicCompletion K)) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  exact ⟨-m, by rw [hm, neg_neg]⟩

theorem exists_valued_eq_exp (y : (v.adicCompletion K)ˣ) :
    ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m := by
  have hne : Valued.v (y : (v.adicCompletion K)) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  exact ⟨_, (WithZero.exp_log hne).symm⟩

theorem preimage_shell (n : ℤ) :
    (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) ⁻¹' shell v n = USet v := by
  ext u
  simp only [Set.mem_preimage, shell, USet, Set.mem_setOf_eq, Units.val_mul, map_mul,
    valued_uniformizerUnit_zpow]
  constructor
  · intro h
    have hne : (WithZero.exp (-n) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
    calc Valued.v (u : (v.adicCompletion K))
        = (WithZero.exp (-n))⁻¹ * (WithZero.exp (-n) * Valued.v (u : (v.adicCompletion K))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = 1 := by rw [h, inv_mul_cancel₀ hne]
  · intro h
    rw [h, mul_one]

theorem mul_mem_shell (n : ℤ) {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    uniformizerUnit K v ^ n * u ∈ shell v n := by
  have := preimage_shell v n
  rw [Set.ext_iff] at this
  exact (this u).mpr hu

theorem preimage_mul_left_shell (n : ℤ) {u₀ : (v.adicCompletion K)ˣ} (hu₀ : u₀ ∈ USet v) :
    (fun y : (v.adicCompletion K)ˣ => u₀ * y) ⁻¹' shell v n = shell v n := by
  ext y
  have hu₀' : Valued.v (u₀ : (v.adicCompletion K)) = 1 := hu₀
  simp only [Set.mem_preimage, shell, Set.mem_setOf_eq, Units.val_mul, map_mul, hu₀', one_mul]

theorem modulus_shell {n : ℤ} {y : (v.adicCompletion K)ˣ} (hy : y ∈ shell v n) :
    modulus (y : (v.adicCompletion K)) = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
  modulus_of_valued v hy

theorem modulus_uniformizer_zpow_mul {n : ℤ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    modulus ((uniformizerUnit K v ^ n * u : (v.adicCompletion K)ˣ) : (v.adicCompletion K))
      = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
  modulus_shell v (n := n) (mul_mem_shell v n hu)

theorem isLocallyConstant_of_forall_mul {X : Type*} (f : (v.adicCompletion K)ˣ → X)
    (W : Set (v.adicCompletion K)ˣ) (hW : IsOpen W) (h1 : (1 : (v.adicCompletion K)ˣ) ∈ W)
    (h : ∀ y, ∀ u ∈ W, f (y * u) = f y) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hopen : IsOpen ((fun u => y * u) '' W) := isOpenMap_mul_left y W hW
  have hmem : y ∈ (fun u => y * u) '' W := ⟨1, h1, mul_one y⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact h y u hu

theorem isOpen_setOf_valued_sub_one_le (k : ℤ) :
    IsOpen {u : (v.adicCompletion K)ˣ | Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp k} := by
  have hc : Continuous fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K) - 1 :=
    Units.continuous_val.sub continuous_const
  exact (isOpen_ball v k).preimage hc

theorem valued_eq_one_of_valued_sub_one_lt {x : v.adicCompletion K} (hx : Valued.v (x - 1) < 1) :
    Valued.v x = 1 := by
  have := Valuation.map_one_add_of_lt Valued.v hx
  rwa [show (1 : v.adicCompletion K) + (x - 1) = x by ring] at this

theorem valued_sub_one_le_one_of_valued_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) :
    Valued.v (x - 1) ≤ 1 := by
  refine (Valuation.map_sub Valued.v x 1).trans ?_
  rw [hx, Valuation.map_one, max_self]

theorem exists_bound_USet (f : (v.adicCompletion K)ˣ → ℂ) (hf : IsLocallyConstant f) :
    ∃ B : ℝ, ∀ u ∈ USet v, ‖f u‖ ≤ B :=
  (isCompact_USet v).exists_bound_of_continuousOn hf.continuous.continuousOn

theorem continuous_diagOne :
    Continuous (diagOne : (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun t : (v.adicCompletion K)ˣ => Matrix.diagonal ![(t : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · change Continuous (fun t : (v.adicCompletion K)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

scoped instance borelSpace_unitsKv : BorelSpace (v.adicCompletion K)ˣ := borelSpace_units

scoped instance measurableMul_unitsKv : MeasurableMul (v.adicCompletion K)ˣ := by infer_instance

theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell v n) := (isClosed_shell v n).measurableSet

theorem measurableSet_USet : MeasurableSet (USet v) := by rw [← shell_zero]; exact measurableSet_shell v 0

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

def mulHaar : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (mulMeasure μ)

scoped instance isHaarMeasure_mulHaar : (mulHaar v μ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure K v μ

theorem mulHaar_USet_lt_top : mulHaar v μ (USet v) < ⊤ := (isCompact_USet v).measure_lt_top

theorem setIntegral_shell_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℤ)
    (f : (v.adicCompletion K)ˣ → E) :
    ∫ y in shell v n, f y ∂(mulHaar v μ)
      = ∫ u in USet v, f (uniformizerUnit K v ^ n * u) ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u)
      (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) :=
    (MeasurableEquiv.mulLeft (uniformizerUnit K v ^ n)).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_shell]

theorem setIntegral_shell_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℤ)
    {u₀ : (v.adicCompletion K)ˣ} (hu₀ : u₀ ∈ USet v) (f : (v.adicCompletion K)ˣ → E) :
    ∫ y in shell v n, f (u₀ * y) ∂(mulHaar v μ) = ∫ y in shell v n, f y ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun y : (v.adicCompletion K)ˣ => u₀ * y) (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun y : (v.adicCompletion K)ˣ => u₀ * y) :=
    (MeasurableEquiv.mulLeft u₀).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_mul_left_shell v n hu₀]

theorem integrableOn_shell_iff {E : Type*} [NormedAddCommGroup E] (n : ℤ) (f : (v.adicCompletion K)ˣ → E) :
    IntegrableOn f (shell v n) (mulHaar v μ) ↔
      IntegrableOn (fun u => f (uniformizerUnit K v ^ n * u)) (USet v) (mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u)
      (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) :=
    (MeasurableEquiv.mulLeft (uniformizerUnit K v ^ n)).measurableEmbedding
  rw [← h₁.integrableOn_comp_preimage h₂ (f := f) (s := shell v n), preimage_shell]
  rfl

theorem integrableOn_USet_of_bound (g : (v.adicCompletion K)ˣ → ℂ) (hg : Measurable g) (R : ℝ)
    (hR : ∀ u ∈ USet v, ‖g u‖ ≤ R) : IntegrableOn g (USet v) (mulHaar v μ) := by
  have hfin : mulHaar v μ (USet v) < ⊤ := mulHaar_USet_lt_top v μ
  haveI : IsFiniteMeasure ((mulHaar v μ).restrict (USet v)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine Integrable.mono' (integrable_const R) hg.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_USet v)]
  exact Filter.Eventually.of_forall hR

end Kv

theorem isAddHaarMeasure_selfDualHaarAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal K v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt K v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end TorusShellSumEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

namespace TorusMultOne

open Rat.HeightOneSpectrum

section Span

variable {G : Type*} [Group G]

abbrev cyc (W₀ : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))

theorem translate_mem_cyc (W₀ : G → ℂ) {W : G → ℂ} (hW : W ∈ cyc W₀) (h : G) :
    (fun g => W (g * h)) ∈ cyc W₀ := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g
    simp only [mul_assoc]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    have : (fun g => (x + y) (g * h)) = (fun g => x (g * h)) + fun g => y (g * h) := rfl
    rw [this]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx =>
    have : (fun g => (a • x) (g * h)) = a • fun g => x (g * h) := rfl
    rw [this]
    exact Submodule.smul_mem _ a ihx

theorem self_translate_mem_cyc (W₀ : G → ℂ) (h : G) : (fun g => W₀ (g * h)) ∈ cyc W₀ :=
  Submodule.subset_span ⟨h, rfl⟩

theorem law_of_mem_cyc {X : Type*} (W₀ : G → ℂ) (n : X → G) (ψ : X → ℂ)
    (hlaw : ∀ (x : X) (g : G), W₀ (n x * g) = ψ x * W₀ g) :
    ∀ W ∈ cyc W₀, ∀ (x : X) (g : G), W (n x * g) = ψ x * W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    intro x g
    show W₀ (n x * g * h) = ψ x * W₀ (g * h)
    rw [mul_assoc, hlaw]
  | zero => intro x g; simp
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    intro x g
    simp only [Pi.add_apply]
    rw [ih₁, ih₂, mul_add]
  | smul a W' _ ih =>
    intro x g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem smooth_of_mem_cyc (W₀ : G → ℂ) (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G))
    (hfix : ∀ k ∈ K₀, ∀ g : G, W₀ (g * k) = W₀ g) :
    ∀ W ∈ cyc W₀, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    refine ⟨K₀.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hK₀.preimage ?_
      show Continuous fun k : G => (MulAut.conj h⁻¹) k
      simp only [MulAut.conj_apply, inv_inv]
      fun_prop
    · intro k hk g
      rw [Subgroup.mem_comap] at hk
      have hk' : h⁻¹ * k * h ∈ K₀ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hk
      show W₀ (g * k * h) = W₀ (g * h)
      calc W₀ (g * k * h) = W₀ (g * h * (h⁻¹ * k * h)) := by group
        _ = W₀ (g * h) := hfix _ hk' _
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := ih₁
    obtain ⟨U₂, hU₂, h₂⟩ := ih₂
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply]
    rw [h₁ k hk.1 g, h₂ k hk.2 g]
  | smul a W' _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    refine ⟨U, hU, fun k hk g => ?_⟩
    simp only [Pi.smul_apply]
    rw [h k hk g]

end Span
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

section GL2

variable {F : Type*} [Field F]

theorem unipotent_val (x : F) :
    ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem unipotent_add (x y : F) : unipotent (x + y) = unipotent x * unipotent y := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] ; ring

theorem unipotent_zero : (unipotent (0 : F)) = 1 := by
  apply Units.ext
  simp only [unipotent_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_inv (x : F) : (unipotent x)⁻¹ = unipotent (-x) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← unipotent_add, neg_add_cancel, unipotent_zero]

theorem diagOne_val (y : Fˣ) :
    ((diagOne y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(y : F), 1] := rfl

theorem diagOne_mul_unipotent (y : Fˣ) (x : F) :
    diagOne y * unipotent x = unipotent ((y : F) * x) * diagOne y := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val, diagOne_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_unipotent : Continuous (unipotent : F → GL (Fin 2) F) := by
  have hval : Continuous fun x : F => ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotent_val]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have h : (fun x : F => ((unipotent x)⁻¹ : GL (Fin 2) F).val) =
      fun x : F => ((unipotent (-x) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    funext x; rw [unipotent_inv]
  show Continuous fun x : F => ((unipotent x)⁻¹ : GL (Fin 2) F).val
  rw [h]
  exact hval.comp continuous_neg

variable [ContinuousInv₀ F]

theorem continuous_diagOne : Continuous (diagOne : Fˣ → GL (Fin 2) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun t : Fˣ => Matrix.diagonal ![(t : F), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · change Continuous (fun t : Fˣ => Matrix.diagonal ![((t⁻¹ : Fˣ) : F), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

end GL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

def varpi : F := algebraMap ℚ F ((natGenerator p : ℕ) : ℚ)

theorem valued_varpi : Valued.v (varpi p) = WithZero.exp (-1 : ℤ) := by
  rw [varpi, RatIdele.valued_algebraMap_rat, RatIdele.valuation_natGenerator]

theorem varpi_ne_zero : varpi p ≠ 0 := by
  intro h
  have := valued_varpi p
  rw [h, Valuation.map_zero] at this
  exact WithZero.zero_ne_coe this

theorem valued_varpi_zpow (m : ℤ) : Valued.v (varpi p ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, valued_varpi, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem valued_varpi_pow (n : ℕ) : Valued.v (varpi p ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, valued_varpi_zpow]

theorem natCast_natGenerator : ((natGenerator p : ℕ) : F) = varpi p := by
  rw [varpi, map_natCast]

theorem primesEquiv_val : ((primesEquiv p : Nat.Primes) : ℕ) = natGenerator p := rfl

theorem psiLocal_eq_one_iff (s : F) :
    NumberField.StandardAddChar.psiLocal ℚ p s = 1 ↔ Valued.v s ≤ 1 := by
  haveI : Fact (primesEquiv p : Nat.Primes).1.Prime := ⟨(primesEquiv p).2⟩
  rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV, NumberField.StandardAddChar.psiV_apply]
  constructor
  · intro h
    obtain ⟨a, k, ha⟩ := NumberField.StandardAddChar.exists_pPow_approx (adicCompletion.padicEquiv p s)
    rw [NumberField.StandardAddChar.psiPadic_apply, NumberField.StandardAddChar.psiPadicFun_eq ha,
      Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hqprime : ((primesEquiv p : Nat.Primes) : ℕ).Prime := (primesEquiv p).2
    have hqC : (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqprime.ne_zero

    have h1 : (a : ℂ) / (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ^ k = -(n : ℂ) := by
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ^ k) =
          (2 * (Real.pi : ℂ) * Complex.I) * (-(n : ℂ)) := by
        linear_combination -hn
      exact mul_left_cancel₀ h2 h3
    have hval : (a : ℂ) = -(n : ℂ) * (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ^ k := by
      rw [div_eq_iff (pow_ne_zero _ hqC)] at h1; exact h1
    have hZ : a = -n * (((primesEquiv p : Nat.Primes) : ℕ) : ℤ) ^ k := by exact_mod_cast hval
    have hint : ((a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k) =
        ((-n : ℤ) : ℚ_[primesEquiv p]) := by
      have hqQ : ((((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p])) ≠ 0 :=
        Nat.cast_ne_zero.mpr hqprime.ne_zero
      rw [hZ]; push_cast; field_simp
    have hnorm : ‖adicCompletion.padicEquiv p s‖ ≤ 1 := by
      have h1 : ‖((a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k)‖ ≤ 1 := by
        rw [hint]; exact Padic.norm_int_le_one _
      calc ‖adicCompletion.padicEquiv p s‖
          = ‖(adicCompletion.padicEquiv p s -
              (a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k) +
            (a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k‖ := by
            rw [sub_add_cancel]
        _ ≤ max ‖adicCompletion.padicEquiv p s -
              (a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k‖
            ‖(a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k‖ :=
            Padic.nonarchimedean _ _
        _ ≤ 1 := max_le ha h1

    obtain ⟨s', hs', hs'x⟩ := (adicCompletion.padicEquiv_bijOn p).surjOn hnorm
    have hss' : s = s' := (adicCompletion.padicEquiv p).injective hs'x.symm
    rw [hss']
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp hs'
  · intro h
    exact NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr h)

theorem exists_ball_subset_of_mem_nhds {x₀ : F} {s : Set F} (hs : s ∈ 𝓝 x₀) :
    ∃ n : ℕ, ∀ y : F, Valued.v (y - x₀) ≤ WithZero.exp (-(n : ℤ)) → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  have key : ∀ y : F,
      Valued.v.restrict (y - x₀) < γ.1 ↔ Valued.v (y - x₀) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    fun y => Valuation.restrict_lt_iff_lt_embedding _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) :=
    (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 =
      (WithZero.exp m : WithZero (Multiplicative ℤ)) :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  refine ⟨(-m).toNat + 1, fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x₀) < γ.1
  rw [key, hm]
  refine lt_of_le_of_lt hy ?_
  rw [WithZero.exp_lt_exp]
  have : -m ≤ ((-m).toNat : ℤ) := Int.self_le_toNat (-m)
  push_cast
  omega

theorem exists_ball_subset_of_mem_nhds_units {s : Set Fˣ} (hs : s ∈ 𝓝 (1 : Fˣ)) :
    ∃ n : ℕ, ∀ u : Fˣ, Valued.v ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ)) → u ∈ s := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  rw [Units.val_one] at ht
  obtain ⟨n, hn⟩ := exists_ball_subset_of_mem_nhds p ht
  exact ⟨n, fun u hu => hts (hn u hu)⟩

theorem valued_eq_one_of_valued_sub_one_lt {x : F} (hx : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have := Valuation.map_one_add_of_lt Valued.v hx
  rwa [show (1 : F) + (x - 1) = x by ring] at this

theorem exp_neg_natCast_lt_one {n : ℕ} (hn : 1 ≤ n) : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_natCast_le_one (n : ℕ) : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

def congr1 (n : ℕ) (hn : 1 ≤ n) : Subgroup Fˣ where
  carrier := {u | Valued.v ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at ha hb ⊢
    have ha1 : Valued.v (a : F) = 1 :=
      valued_eq_one_of_valued_sub_one_lt p (lt_of_le_of_lt ha (exp_neg_natCast_lt_one hn))
    have : (a : F) * b - 1 = (a : F) * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (Valuation.map_add Valued.v _ _).trans (max_le ?_ ha)
    rw [Valuation.map_mul, ha1, one_mul]; exact hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have ha1 : Valued.v (a : F) = 1 :=
      valued_eq_one_of_valued_sub_one_lt p (lt_of_le_of_lt ha (exp_neg_natCast_lt_one hn))
    have : ((a⁻¹ : Fˣ) : F) - 1 = ((a⁻¹ : Fˣ) : F) * (1 - a) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [this, Valuation.map_mul, Valuation.map_sub_swap]
    have hinv : Valued.v ((a⁻¹ : Fˣ) : F) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ha1, inv_one]
    rw [hinv, one_mul]; exact ha

theorem mem_congr1 {n : ℕ} {hn : 1 ≤ n} {u : Fˣ} :
    u ∈ congr1 p n hn ↔ Valued.v ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := Iff.rfl

theorem valued_eq_one_of_mem_congr1 {n : ℕ} {hn : 1 ≤ n} {u : Fˣ} (hu : u ∈ congr1 p n hn) :
    Valued.v (u : F) = 1 :=
  valued_eq_one_of_valued_sub_one_lt p (lt_of_le_of_lt hu (exp_neg_natCast_lt_one hn))

theorem isOpen_ball (m : ℤ) : IsOpen {x : F | Valued.v x ≤ WithZero.exp m} := by
  have h := isOpen_setOf_valued_le p (varpi p ^ (-m)) (zpow_ne_zero _ (varpi_ne_zero p))
  rw [valued_varpi_zpow, neg_neg] at h
  exact h

theorem isClosed_ball (m : ℤ) : IsClosed {x : F | Valued.v x ≤ WithZero.exp m} := by
  have h := isClosed_setOf_valued_le p (varpi p ^ (-m)) (zpow_ne_zero _ (varpi_ne_zero p))
  rw [valued_varpi_zpow, neg_neg] at h
  exact h

theorem isCompact_ball (m : ℤ) : IsCompact {x : F | Valued.v x ≤ WithZero.exp m} := by
  have hint : IsCompact {x : F | Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))} := by
    have h1 : IsCompact ((p.adicCompletionIntegers ℚ : Set F)) :=
      isCompact_iff_compactSpace.mpr (show CompactSpace (p.adicCompletionIntegers ℚ) from inferInstance)
    have h2 : ((p.adicCompletionIntegers ℚ : Set F)) = {x : F | Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))} := by
      ext x; exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p
    rw [← h2]; exact h1
  have heq : {x : F | Valued.v x ≤ WithZero.exp m} = (fun x => varpi p ^ (-m) * x) '' {x : F | Valued.v x ≤ 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hx
      refine ⟨(varpi p ^ (-m))⁻¹ * x, ?_,
        by rw [← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (varpi_ne_zero p)), one_mul]⟩
      rw [Valuation.map_mul, map_inv₀, valued_varpi_zpow, neg_neg]
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right hx _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · rintro ⟨z, hz, rfl⟩
      rw [Valuation.map_mul, valued_varpi_zpow, neg_neg]
      calc WithZero.exp m * Valued.v z ≤ WithZero.exp m * 1 := mul_le_mul_right hz _
        _ = WithZero.exp m := mul_one _
  rw [heq]
  exact hint.image (continuous_const.mul continuous_id)

theorem isOpen_congr1 (n : ℕ) (hn : 1 ≤ n) : IsOpen (congr1 p n hn : Set Fˣ) := by
  have hc : Continuous fun u : Fˣ => (u : F) - 1 := Units.continuous_val.sub continuous_const
  exact (isOpen_ball p (-(n : ℤ))).preimage hc

theorem mem_smul_congr1_iff {n : ℕ} {hn : 1 ≤ n} (t y : Fˣ) :
    y ∈ t • (congr1 p n hn : Set Fˣ) ↔ Valued.v (((y * t⁻¹ : Fˣ) : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [mem_leftCoset_iff, SetLike.mem_coe, mem_congr1, mul_comm]

theorem smul_congr1_eq_of_mem {n : ℕ} {hn : 1 ≤ n} {t t' y : Fˣ}
    (hy : y ∈ t • (congr1 p n hn : Set Fˣ)) (hy' : y ∈ t' • (congr1 p n hn : Set Fˣ)) :
    t • (congr1 p n hn : Set Fˣ) = t' • (congr1 p n hn : Set Fˣ) := by
  rw [mem_leftCoset_iff] at hy hy'
  have h1 : t • (congr1 p n hn : Set Fˣ) = y • (congr1 p n hn : Set Fˣ) := by
    rw [eq_comm, leftCoset_eq_iff]; simpa using (congr1 p n hn).inv_mem hy
  have h2 : t' • (congr1 p n hn : Set Fˣ) = y • (congr1 p n hn : Set Fˣ) := by
    rw [eq_comm, leftCoset_eq_iff]; simpa using (congr1 p n hn).inv_mem hy'
  rw [h1, h2]

def window (n₁ n₀ : ℤ) : Set Fˣ :=
  {y | WithZero.exp (-n₀) ≤ Valued.v (y : F) ∧ Valued.v (y : F) ≤ WithZero.exp (-n₁)}

theorem isCompact_window (n₁ n₀ : ℤ) : IsCompact (window p n₁ n₀) := by
  have himg : Units.val '' window p n₁ n₀ =
      {x : F | WithZero.exp (-n₀) ≤ Valued.v x ∧ Valued.v x ≤ WithZero.exp (-n₁)} := by
    ext x
    simp only [Set.mem_image, window, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, Valuation.map_zero] at hx
        exact WithZero.exp_ne_zero (le_antisymm hx.1 zero_le')
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [Units.isEmbedding_val₀.isCompact_iff, himg]
  refine (isCompact_ball p (-n₁)).of_isClosed_subset ?_ (fun x hx => hx.2)
  have h1 : IsClosed {x : F | WithZero.exp (-n₀) ≤ Valued.v x} := by
    have : {x : F | WithZero.exp (-n₀) ≤ Valued.v x} = {x : F | Valued.v x ≤ WithZero.exp (-n₀ - 1)}ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
      constructor
      · intro h
        refine lt_of_lt_of_le ?_ h
        rw [WithZero.exp_lt_exp]; omega
      · intro h
        by_cases hx : Valued.v x = 0
        · rw [hx] at h; exact absurd h (not_lt.mpr zero_le')
        · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx).symm⟩
          rw [hm] at h ⊢
          rw [WithZero.exp_lt_exp] at h
          rw [WithZero.exp_le_exp]; omega
    rw [this, isClosed_compl_iff]
    exact isOpen_ball p _
  simpa [Set.setOf_and] using h1.inter (isClosed_ball p (-n₁))

theorem smul_congr1_subset_window {n : ℕ} {hn : 1 ≤ n} {n₁ n₀ : ℤ} {t : Fˣ} (ht : t ∈ window p n₁ n₀) :
    t • (congr1 p n hn : Set Fˣ) ⊆ window p n₁ n₀ := by
  intro y hy
  rw [mem_leftCoset_iff] at hy
  have h1 := valued_eq_one_of_mem_congr1 p hy
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Valuation.map_mul, map_inv₀] at h1
  have ht0 : Valued.v (t : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  have hy' : Valued.v (y : F) = Valued.v (t : F) := by
    have := congrArg (fun z => Valued.v (t : F) * z) h1
    simp only [mul_one] at this
    rwa [← mul_assoc, mul_inv_cancel₀ ht0, one_mul] at this
  simp only [window, Set.mem_setOf_eq] at ht ⊢
  rw [hy']; exact ht

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

section KirillovF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G₂" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "ψ" => NumberField.StandardAddChar.psiLocal ℚ p

variable (w₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
  (hlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
    w₀ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₀ g)

include hlaw in

theorem apply_diagOne_eq_zero_of_le {w : G₂ → ℂ} (hw : w ∈ cyc w₀)
    {k : ℕ} (hk : ∀ x : F, Valued.v x ≤ WithZero.exp (-(k : ℤ)) → ∀ g : G₂, w (g * unipotent x) = w g)
    (y : Fˣ) (hy : WithZero.exp ((k : ℤ) + 1) ≤ Valued.v (y : F)) : w (diagOne y) = 0 := by
  have hy0 : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v (y : F) = WithZero.exp e := ⟨_, (WithZero.exp_log hy0).symm⟩
  set x : F := ((y : F))⁻¹ * (varpi p)⁻¹ with hxdef
  have hx : Valued.v x ≤ WithZero.exp (-(k : ℤ)) := by
    rw [he, WithZero.exp_le_exp] at hy
    rw [hxdef, Valuation.map_mul, map_inv₀, map_inv₀, valued_varpi, he, ← WithZero.exp_neg, ← WithZero.exp_neg,
      ← WithZero.exp_add, WithZero.exp_le_exp]
    omega
  have h1 := hk x hx (diagOne y)
  rw [diagOne_mul_unipotent, law_of_mem_cyc w₀ unipotent ψ hlaw w hw] at h1
  have hyx : (y : F) * x = (varpi p)⁻¹ := by
    rw [hxdef, ← mul_assoc, mul_inv_cancel₀ y.ne_zero, one_mul]
  rw [hyx] at h1
  have hne : ψ (varpi p)⁻¹ ≠ 1 := by
    rw [Ne, psiLocal_eq_one_iff, map_inv₀, valued_varpi, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    omega
  have h2 : (ψ (varpi p)⁻¹ - 1) * w (diagOne y) = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

theorem exists_stabilizers (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G₂, w₀ (g * k) = w₀ g)
    {w : G₂ → ℂ} (hw : w ∈ cyc w₀) :
    (∃ k : ℕ, ∀ x : F, Valued.v x ≤ WithZero.exp (-(k : ℤ)) → ∀ g : G₂, w (g * unipotent x) = w g) ∧
    (∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∀ u : Fˣ, Valued.v ((u : F) - 1) ≤ WithZero.exp (-(m₁ : ℤ)) →
      ∀ g : G₂, w (g * diagOne u) = w g) := by
  obtain ⟨-, hKopen⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  obtain ⟨U, hUopen, hU⟩ := smooth_of_mem_cyc w₀ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKopen hK w hw
  constructor
  · have hmem : (unipotent : F → _) ⁻¹' (U : Set G₂) ∈ 𝓝 (0 : F) := by
      refine (hUopen.preimage continuous_unipotent).mem_nhds ?_
      show unipotent (0 : F) ∈ U
      rw [unipotent_zero]; exact U.one_mem
    obtain ⟨k, hk⟩ := exists_ball_subset_of_mem_nhds p hmem
    exact ⟨k, fun x hx g => hU _ (hk x (by simpa using hx)) g⟩
  · have hmem : (diagOne : Fˣ → _) ⁻¹' (U : Set G₂) ∈ 𝓝 (1 : Fˣ) := by
      refine (hUopen.preimage continuous_diagOne).mem_nhds ?_
      show diagOne (1 : Fˣ) ∈ U
      rw [map_one]; exact U.one_mem
    obtain ⟨m₁, hm₁⟩ := exists_ball_subset_of_mem_nhds_units p hmem
    refine ⟨max m₁ 1, le_max_right _ _, fun u hu g => hU _ (hm₁ u ?_) g⟩
    exact hu.trans (by rw [WithZero.exp_le_exp]; omega)

end KirillovF
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

end TorusMultOne
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

namespace D4Kit

open AutomorphicForm LanglandsTunnell.CubicInduction

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "scal" => (Matrix.GeneralLinearGroup.scalar (Fin 2) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "OO" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)

theorem coe_scal (z : Fˣ) : ((scal z : G) : Mat) = Matrix.diagonal fun _ => (z : F) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.scalar]

theorem coe_diagOne (y : Fˣ) : ((diagOne y : G) : Mat) = Matrix.diagonal ![(y : F), 1] := rfl

theorem scal_mul_comm (z : Fˣ) (g : G) : scal z * g = g * scal z := by
  refine Units.ext ?_
  change ((scal z : G) : Mat) * (g : Mat) = (g : Mat) * ((scal z : G) : Mat)
  rw [coe_scal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> ring

theorem continuous_scal : Continuous fun z : Fˣ => (scal z : G) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (fun z : Fˣ => ((scal z : G) : Mat)) = fun z : Fˣ => Matrix.diagonal fun _ : Fin 2 => (z : F) :=
      funext fun z => coe_scal p z
    show Continuous fun z : Fˣ => ((scal z : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · have h : (fun z : Fˣ => (((scal z : G)⁻¹ : G) : Mat)) = fun z : Fˣ => Matrix.diagonal fun _ : Fin 2 => ((z⁻¹ : Fˣ) : F) :=
      funext fun z => by rw [← map_inv, coe_scal]
    show Continuous fun z : Fˣ => (((scal z : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

end D4Kit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine"

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal UnramifiedWhittaker Topology Filter
open scoped NNReal ENNReal Classical Pointwise

namespace KPair

open AutomorphicForm LanglandsTunnell.CubicInduction

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (p : HeightOneSpectrum (𝓞 ℚ)) (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
  (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
  (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
    w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
  (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
  (hw₂ne : w₂base ≠ 0)
  (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
    w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
  (hcusp : ∀ v ∈ TorusMultOne.cyc w₂base,
    ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "scal" => (Matrix.GeneralLinearGroup.scalar (Fin 2) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "V" => (TorusMultOne.cyc w₂base)

def ν : Measure Fˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))

def pairFn (u u' : G → ℂ) (t : Fˣ) : ℂ := u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹

def pair (u u' : G → ℂ) : ℂ := ∫ t, pairFn p θ₀ u u' t ∂(ν p)

def rho (g : G) (u : G → ℂ) : G → ℂ := fun x => u (x * g)

theorem rho_mul (g h : G) (u : G → ℂ) : rho p (g * h) u = rho p g (rho p h u) := by
  funext x; simp [rho, mul_assoc]

theorem rho_mem {u : G → ℂ} (hu : u ∈ V) (g : G) : rho p g u ∈ V := TorusMultOne.translate_mem_cyc w₂base hu g

def Good (g : G) : Prop :=
  ∀ u ∈ V, ∀ u' ∈ V, pair p θ₀ (rho p g u) (rho p g u') =
    ((θ₀ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * pair p θ₀ u u'

scoped instance isHaar_ν : (ν p).IsHaarMeasure := by
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := TorusShellSumEngine.isAddHaarMeasure_selfDualHaarAt ℚ p
  show (TorusShellSumEngine.mulHaar p (selfDualHaarAt ℚ p)).IsHaarMeasure
  infer_instance

include hN hw₂K hw₂ne hcentral in
theorem theta_eq_one_near_one : ∃ n : ℕ, ∀ z : Fˣ, Valued.v ((z : F) - 1) ≤ WithZero.exp (-(n : ℤ)) → θ₀ z = 1 := by
  obtain ⟨-, hKopen⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  have hmem : (fun z : Fˣ => (scal z : G)) ⁻¹' (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set G) ∈ 𝓝 (1 : Fˣ) := by
    refine (hKopen.preimage (D4Kit.continuous_scal p)).mem_nhds ?_
    show scal (1 : Fˣ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N
    rw [map_one]; exact Subgroup.one_mem _
  obtain ⟨n, hn⟩ := TorusMultOne.exists_ball_subset_of_mem_nhds_units p hmem
  refine ⟨n, fun z hz => ?_⟩
  have hzK : scal z ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := hn z hz
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, w₂base g₀ ≠ 0 := Function.ne_iff.mp hw₂ne
  have h1 : w₂base (g₀ * scal z) = w₂base g₀ := hw₂K _ hzK g₀
  rw [← D4Kit.scal_mul_comm p z g₀, hcentral] at h1
  have h2 : ((θ₀ z : ℂˣ) : ℂ) = 1 := (mul_eq_right₀ hg₀).mp h1
  exact Units.val_eq_one.mp h2

include hN hw₂K hw₂ne hcentral in
theorem isLocallyConstant_theta : IsLocallyConstant (fun t : Fˣ => ((θ₀ t : ℂˣ) : ℂ)) := by
  obtain ⟨n, hn⟩ := theta_eq_one_near_one p θ₀ N hN w₂base hw₂K hw₂ne hcentral
  refine TorusShellSumEngine.isLocallyConstant_of_forall_mul p _ {u : Fˣ | Valued.v ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ))}
    (TorusShellSumEngine.isOpen_setOf_valued_sub_one_le p _) (by simp) (fun y u hu => ?_)
  show ((θ₀ (y * u) : ℂˣ) : ℂ) = ((θ₀ y : ℂˣ) : ℂ)
  rw [map_mul, hn u hu, mul_one]

include hN hw₂K in
theorem isLocallyConstant_kirillov {w : G → ℂ} (hw : w ∈ V) : IsLocallyConstant (fun t : Fˣ => w (diagOne t)) := by
  obtain ⟨-, ⟨M, -, hM⟩⟩ := TorusMultOne.exists_stabilizers p w₂base N hN hw₂K hw
  refine TorusShellSumEngine.isLocallyConstant_of_forall_mul p _ {u : Fˣ | Valued.v ((u : F) - 1) ≤ WithZero.exp (-(M : ℤ))}
    (TorusShellSumEngine.isOpen_setOf_valued_sub_one_le p _) (by simp) (fun y u hu => ?_)
  show w (diagOne (y * u)) = w (diagOne y)
  rw [map_mul]; exact hM u hu _

include hN hw₂law hw₂K hcusp in
theorem kirillov_window {w : G → ℂ} (hw : w ∈ V) :
    ∃ n₁ n₀ : ℤ, ∀ t : Fˣ, t ∉ TorusMultOne.window p n₁ n₀ → w (diagOne t) = 0 := by
  obtain ⟨⟨k, hk⟩, -⟩ := TorusMultOne.exists_stabilizers p w₂base N hN hw₂K hw
  obtain ⟨N₀, hN₀⟩ := hcusp w hw
  refine ⟨-(k : ℤ), -(N₀ + 1), fun t ht => ?_⟩
  simp only [TorusMultOne.window, Set.mem_setOf_eq, not_and_or, not_le, neg_neg] at ht
  have ht0 : Valued.v (t : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  obtain ⟨d, hd⟩ : ∃ d : ℤ, Valued.v (t : F) = WithZero.exp d := ⟨_, (WithZero.exp_log ht0).symm⟩
  rcases ht with h | h
  · exact hN₀ t (by rw [hd] at h ⊢; rw [WithZero.exp_lt_exp] at h; rw [WithZero.exp_le_exp]; omega)
  · exact TorusMultOne.apply_diagOne_eq_zero_of_le p w₂base hw₂law hw hk t
      (by rw [hd] at h ⊢; rw [WithZero.exp_lt_exp] at h; rw [WithZero.exp_le_exp]; omega)

theorem continuous_neg_units : Continuous (fun t : Fˣ => -t) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : Fˣ => ((-t : Fˣ) : F)
    simp only [Units.val_neg]
    exact Units.continuous_val.neg
  · show Continuous fun t : Fˣ => (((-t)⁻¹ : Fˣ) : F)
    simp only [Units.val_inv_eq_inv_val, Units.val_neg]
    exact Units.continuous_val.neg.inv₀ (fun t => neg_ne_zero.mpr t.ne_zero)

include hN hw₂law hw₂K hw₂ne hcentral hcusp in
theorem continuous_pairFn {u u' : G → ℂ} (hu : u ∈ V) (hu' : u' ∈ V) : Continuous (pairFn p θ₀ u u') := by
  have h1 : Continuous (fun t : Fˣ => u (diagOne t)) := (isLocallyConstant_kirillov p N hN w₂base hw₂K hu).continuous
  have h2 : Continuous (fun t : Fˣ => u' (diagOne (-t))) :=
    (isLocallyConstant_kirillov p N hN w₂base hw₂K hu').continuous.comp (continuous_neg_units p)
  have h3 : Continuous (fun t : Fˣ => (((θ₀ t : ℂˣ) : ℂ))⁻¹) :=
    ((isLocallyConstant_theta p θ₀ N hN w₂base hw₂K hw₂ne hcentral).comp (fun z : ℂ => z⁻¹)).continuous
  exact (h1.mul h2).mul h3

include hN hw₂law hw₂K hw₂ne hcentral hcusp in
theorem integrable_pairFn {u u' : G → ℂ} (hu : u ∈ V) (hu' : u' ∈ V) : Integrable (pairFn p θ₀ u u') (ν p) := by
  haveI : SecondCountableTopology Fˣ := Units.isEmbedding_val₀.secondCountableTopology
  obtain ⟨n₁, n₀, hwin⟩ := kirillov_window p N hN w₂base hw₂law hw₂K hcusp hu
  refine (continuous_pairFn p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp hu hu').integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (TorusMultOne.isCompact_window p n₁ n₀) (fun t ht => ?_)
  simp only [pairFn, hwin t ht, zero_mul]

include hN hw₂law hw₂K hw₂ne hcentral hcusp in
theorem good_mul {g h : G} (hg : Good p θ₀ w₂base g) (hh : Good p θ₀ w₂base h) : Good p θ₀ w₂base (g * h) := by
  intro u hu u' hu'
  rw [rho_mul, rho_mul, hg _ (rho_mem p w₂base hu h) _ (rho_mem p w₂base hu' h), hh u hu u' hu', map_mul, map_mul,
    Units.val_mul, mul_assoc]

include hw₂law in
theorem good_unipotent (x : F) : Good p θ₀ w₂base (unipotent x) := by
  intro u hu u' hu'
  have hdet : Matrix.GeneralLinearGroup.det (unipotent x : G) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, TorusMultOne.unipotent_val, Matrix.det_fin_two_of]
    simp
  rw [hdet, map_one, Units.val_one, one_mul]
  unfold pair
  congr 1
  funext t
  simp only [pairFn, rho]
  rw [TorusMultOne.diagOne_mul_unipotent, TorusMultOne.diagOne_mul_unipotent,
    TorusMultOne.law_of_mem_cyc w₂base unipotent _ hw₂law u hu,
    TorusMultOne.law_of_mem_cyc w₂base unipotent _ hw₂law u' hu', Units.val_neg, neg_mul]
  have hψ : NumberField.StandardAddChar.psiLocal ℚ p ((t : F) * x) *
      NumberField.StandardAddChar.psiLocal ℚ p (-((t : F) * x)) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  linear_combination (u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹) * hψ

theorem good_diagOne (b : Fˣ) : Good p θ₀ w₂base (diagOne b) := by
  intro u hu u' hu'
  have hdet : Matrix.GeneralLinearGroup.det (diagOne b : G) = b := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, TorusMultOne.diagOne_val, Matrix.det_fin_two]
    simp [Matrix.diagonal]
  rw [hdet]
  unfold pair
  have hfun : pairFn p θ₀ (rho p (diagOne b) u) (rho p (diagOne b) u') =
      fun t => ((θ₀ b : ℂˣ) : ℂ) * pairFn p θ₀ u u' (b * t) := by
    funext t
    simp only [pairFn, rho]
    rw [← map_mul, ← map_mul, mul_comm t b, show -t * b = -(b * t) by rw [mul_comm b t, neg_mul], map_mul θ₀ b t,
      Units.val_mul, mul_inv]
    field_simp
  rw [hfun, integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self (μ := ν p) (pairFn p θ₀ u u') b

include hcentral in
theorem good_scal (z : Fˣ) : Good p θ₀ w₂base (scal z) := by
  intro u hu u' hu'
  have hdet : Matrix.GeneralLinearGroup.det (scal z : G) = z * z := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, D4Kit.coe_scal, Matrix.det_fin_two]
    simp [Matrix.diagonal]
  rw [hdet]
  unfold pair
  rw [← integral_const_mul]
  congr 1
  funext t
  simp only [pairFn, rho]
  rw [← D4Kit.scal_mul_comm p z, ← D4Kit.scal_mul_comm p z,
    TorusMultOne.law_of_mem_cyc w₂base scal (fun z => ((θ₀ z : ℂˣ) : ℂ)) hcentral u hu,
    TorusMultOne.law_of_mem_cyc w₂base scal (fun z => ((θ₀ z : ℂˣ) : ℂ)) hcentral u' hu', map_mul, Units.val_mul]
  ring

theorem diagUnitGL2_eq_diagOne' :
    (LanglandsTunnell.CubicInduction.diagUnitGL2 : Fˣ → G) = diagOne := by
  funext u
  apply Units.ext
  ext i j
  rw [LanglandsTunnell.CubicInduction.coe_diagUnitGL2, NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem ν_eq : ν p = TorusShellSumEngine.mulHaar p (selfDualHaarAt ℚ p) := rfl

theorem hasCond_of_trivial (χ : Fˣ →* ℂˣ) (c : ℕ)
    (h : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c, χ u = 1) :
    ∃ c' : ℕ, HasConductorExponentAt ℚ p χ c' := by
  classical
  have hex : ∃ c' : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c', χ u = 1 := ⟨c, h⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun m hm => ?_⟩
  have := Nat.find_min hex hm
  push_neg at this
  exact this

include hN hw₂K hw₂ne hcentral in
theorem theta_trivial_higherUnits : ∃ c : ℕ, 1 ≤ c ∧ ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c, θ₀ u = 1 := by
  obtain ⟨n, hn⟩ := theta_eq_one_near_one p θ₀ N hN w₂base hw₂K hw₂ne hcentral
  refine ⟨max n 1, le_max_right _ _, fun u hu => hn u ?_⟩
  rw [LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff] at hu
  refine (hu.2.resolve_left (by omega)).trans ?_
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem rho_finset_sum_smul {ι : Type*} (g : G) (S : Finset ι) (c : ι → ℂ) (b : ι → G → ℂ) :
    rho p g (∑ i ∈ S, c i • b i) = ∑ i ∈ S, c i • rho p g (b i) := by
  funext x
  simp only [rho, Finset.sum_apply, Pi.smul_apply]

theorem pair_finset_sum_smul {ι : Type*} (a : G → ℂ) (S : Finset ι) (c : ι → ℂ) (b : ι → G → ℂ)
    (hint : ∀ i ∈ S, Integrable (pairFn p θ₀ a (b i)) (ν p)) :
    pair p θ₀ a (∑ i ∈ S, c i • b i) = ∑ i ∈ S, c i * pair p θ₀ a (b i) := by
  unfold pair
  have hfun : pairFn p θ₀ a (∑ i ∈ S, c i • b i) = fun t => ∑ i ∈ S, c i * pairFn p θ₀ a (b i) t := by
    funext t
    simp only [pairFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun, integral_finset_sum S (fun i hi => (hint i hi).const_mul (c i))]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

include hN hw₂law hw₂K hw₂ne hcentral hcusp in

theorem pair_weylJ_pure
    (hw₂irr : ∀ w ∈ V, w ≠ 0 → w₂base ∈ TorusMultOne.cyc w)
    (hw₂adm : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ B : Finset (G → ℂ),
        ∀ w ∈ V, (∀ k ∈ U, ∀ g : G, w (g * k) = w g) → w ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (wJ : G) (hwJ : (wJ : Mat) = !![0, 1; -1, 0])
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hϖu : Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ = uniformizerUnit ℚ p)
    {u : G → ℂ} (hu : u ∈ V) (m : ℤ) (η : Fˣ →* ℂˣ) (cη : ℕ) (hη : HasConductorExponentAt ℚ p η cη)
    {vi : G → ℂ} (hvi : vi ∈ V)
    (hvK : ∀ y : Fˣ, vi (diagOne y) =
      if Valued.v (y : F) = WithZero.exp (-m) then
        ((η (y * (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (-m)) : ℂˣ) : ℂ)
      else 0) :
    pair p θ₀ (rho p wJ u) (rho p wJ vi) = pair p θ₀ u vi := by
  classical
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := TorusShellSumEngine.isAddHaarMeasure_selfDualHaarAt ℚ p
  haveI hνH : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ).IsHaarMeasure := isHaar_ν p

  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℕ, HasConductorExponentAt ℚ p η⁻¹ c₁ :=
    hasCond_of_trivial p η⁻¹ cη (fun u hu => by rw [MonoidHom.inv_apply, hη.1 u hu, inv_one])
  obtain ⟨cθ, hcθ1, hcθ⟩ := theta_trivial_higherUnits p θ₀ N hN w₂base hw₂K hw₂ne hcentral
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, HasConductorExponentAt ℚ p (θ₀⁻¹ * η) c₂ := by
    refine hasCond_of_trivial p (θ₀⁻¹ * η) (max cθ cη) (fun u hu => ?_)
    have h1 : θ₀ u = 1 := hcθ u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (le_max_left _ _) hu)
    have h2 : η u = 1 := hη.1 u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (le_max_right _ _) hu)
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, one_mul]

  obtain ⟨E₁, e₁, hE₁, hKW₁⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
      p hπ hϖ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hcusp η⁻¹ c₁ hc₁
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
  obtain ⟨E₂, e₂, hE₂, hKW₂⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
      p hπ hϖ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hcusp (θ₀⁻¹ * η) c₂ hc₂
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
  have hlam₁ : ∀ u : Fˣ, Valued.v (u : F) = 1 → η⁻¹ u = (η u)⁻¹ := fun u _ => rfl
  have hlam₂ : ∀ u : Fˣ, Valued.v (u : F) = 1 → (θ₀⁻¹ * η) u = (θ₀ u)⁻¹ * η u := fun u _ => rfl

  have hKb := LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
    p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hπ hϖ η η⁻¹ hlam₁ E₁ e₁ hKW₁ m vi hvi hvK

  obtain ⟨he, hE⟩ := LanglandsTunnell.RankinSelberg.shell_constants_mul_eq_centralChar_neg_one_of_weylJ_sq
    p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hπ hϖ η cη hη η⁻¹ hlam₁ E₁ e₁ hKW₁
    (θ₀⁻¹ * η) hlam₂ E₂ e₂ hKW₂

  have hUeq : {u : Fˣ | Valued.v (u : F) = 1} = TorusShellSumEngine.USet p := rfl
  have hνeq : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ) =
      TorusShellSumEngine.mulHaar p (selfDualHaarAt ℚ p) := rfl
  simp only [hϖu, hUeq, hνeq, diagUnitGL2_eq_diagOne'] at hKW₂ hKb hvK hE

  set πu : Fˣ := uniformizerUnit ℚ p with hπu
  set μH : Measure Fˣ := TorusShellSumEngine.mulHaar p (selfDualHaarAt ℚ p) with hμH
  set θπ : ℂ := ((θ₀ πu : ℂˣ) : ℂ) with hθπ
  have hθπ0 : θπ ≠ 0 := Units.ne_zero _
  have hvπ : ∀ n : ℤ, Valued.v ((πu ^ n : Fˣ) : F) = WithZero.exp (-n) := fun n =>
    TorusShellSumEngine.valued_uniformizerUnit_zpow p n
  set n₁ : ℤ := e₁ - m with hn₁

  set J : ℂ := ∫ x in TorusShellSumEngine.USet p, u (diagOne (πu ^ m * x)) * (((θ₀⁻¹ * η) x : ℂˣ) : ℂ) ∂μH with hJ

  have hθneg : ((θ₀ (-1) : ℂˣ) : ℂ) * ((θ₀ (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
  have hηneg : ((η (-1) : ℂˣ) : ℂ) * ((η (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]

  have hLHS : pair p θ₀ (rho p wJ u) (rho p wJ vi) =
      E₁ * E₂ * θπ ^ n₁ * ((θ₀ (-1) : ℂˣ) : ℂ) * (((η (-1) : ℂˣ) : ℂ))⁻¹ * J := by

    set g₁ : Fˣ → ℂ := fun t => u (diagOne t * wJ) *
      ((((θ₀ * η⁻¹) ((-t) * πu ^ (-n₁)) : ℂˣ) : ℂ) * (((θ₀ t : ℂˣ) : ℂ))⁻¹) with hg₁
    have hfun : pairFn p θ₀ (rho p wJ u) (rho p wJ vi) =
        fun t => E₁ * θπ ^ n₁ * (TorusShellSumEngine.shell p n₁).indicator g₁ t := by
      funext t
      simp only [pairFn, rho]
      rw [hKb (-t)]
      have hvt : Valued.v (((-t : Fˣ)) : F) = Valued.v (t : F) := by rw [Units.val_neg, Valuation.map_neg]
      rw [hvt]
      by_cases ht : Valued.v (t : F) = WithZero.exp (-n₁)
      · have hmem : t ∈ TorusShellSumEngine.shell p n₁ := ht
        rw [if_pos ht, Set.indicator_of_mem hmem, hg₁]
        ring
      · have hmem : t ∉ TorusShellSumEngine.shell p n₁ := ht
        rw [if_neg ht, Set.indicator_of_notMem hmem]
        ring
    unfold pair
    rw [ν_eq, hfun, integral_const_mul, integral_indicator (TorusShellSumEngine.measurableSet_shell p n₁),
      TorusShellSumEngine.setIntegral_shell_eq p (selfDualHaarAt ℚ p) n₁ g₁]

    have hpt : ∀ x ∈ TorusShellSumEngine.USet p, g₁ (πu ^ n₁ * x) =
        ((θ₀ (-1) : ℂˣ) : ℂ) * (((η (-1) : ℂˣ) : ℂ))⁻¹ * (θπ ^ n₁)⁻¹ *
          (u (diagOne (πu ^ n₁ * x) * wJ) * (((((θ₀⁻¹ * η) x : ℂˣ) : ℂ))⁻¹ * (((θ₀ x : ℂˣ) : ℂ))⁻¹)) := by
      intro x hx
      have hxarg : -(πu ^ n₁ * x) * πu ^ (-n₁) = -1 * x := by
        rw [neg_mul, neg_one_mul, mul_comm (πu ^ n₁) x, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
      rw [hg₁]
      simp only
      rw [hxarg]
      simp only [map_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, map_zpow, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
      have h1 : ((θ₀ x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 : ((η x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h3 : ((η (-1) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h4 : θπ ^ n₁ ≠ 0 := zpow_ne_zero _ hθπ0
      rw [hθπ] at h4 ⊢
      field_simp
      try ring
    rw [setIntegral_congr_fun (TorusShellSumEngine.measurableSet_USet p) hpt, integral_const_mul,
      hKW₂ u hu n₁, show e₂ - n₁ = m by omega]
    have h4 : θπ ^ n₁ ≠ 0 := zpow_ne_zero _ hθπ0
    rw [hθπ] at h4 ⊢
    field_simp
    try ring

  have hRHS : pair p θ₀ u vi = ((η (-1) : ℂˣ) : ℂ) * (θπ ^ m)⁻¹ * J := by
    set g₂ : Fˣ → ℂ := fun t => u (diagOne t) * (((η ((-t) * πu ^ (-m)) : ℂˣ) : ℂ) * (((θ₀ t : ℂˣ) : ℂ))⁻¹)
      with hg₂
    have hfun : pairFn p θ₀ u vi = (TorusShellSumEngine.shell p m).indicator g₂ := by
      funext t
      simp only [pairFn]
      rw [hvK (-t)]
      have hvt : Valued.v (((-t : Fˣ)) : F) = Valued.v (t : F) := by rw [Units.val_neg, Valuation.map_neg]
      rw [hvt]
      by_cases ht : Valued.v (t : F) = WithZero.exp (-m)
      · have hmem : t ∈ TorusShellSumEngine.shell p m := ht
        rw [if_pos ht, Set.indicator_of_mem hmem, hg₂]
        ring
      · have hmem : t ∉ TorusShellSumEngine.shell p m := ht
        rw [if_neg ht, Set.indicator_of_notMem hmem]
        ring
    unfold pair
    rw [ν_eq, hfun, integral_indicator (TorusShellSumEngine.measurableSet_shell p m),
      TorusShellSumEngine.setIntegral_shell_eq p (selfDualHaarAt ℚ p) m g₂]
    have hpt : ∀ x ∈ TorusShellSumEngine.USet p, g₂ (πu ^ m * x) =
        ((η (-1) : ℂˣ) : ℂ) * (θπ ^ m)⁻¹ * (u (diagOne (πu ^ m * x)) * (((θ₀⁻¹ * η) x : ℂˣ) : ℂ)) := by
      intro x hx
      have hxarg : -(πu ^ m * x) * πu ^ (-m) = -1 * x := by
        rw [neg_mul, neg_one_mul, mul_comm (πu ^ m) x, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
      rw [hg₂]
      simp only
      rw [hxarg]
      simp only [map_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, map_zpow, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
      have h1 : ((θ₀ x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h4 : θπ ^ m ≠ 0 := zpow_ne_zero _ hθπ0
      rw [hθπ] at h4 ⊢
      field_simp
      try ring
    rw [setIntegral_congr_fun (TorusShellSumEngine.measurableSet_USet p) hpt, integral_const_mul]

  rw [hLHS, hRHS]
  have hE' : E₁ * E₂ * θπ ^ e₁ = ((θ₀ (-1) : ℂˣ) : ℂ) := hE
  have hsplit : θπ ^ n₁ = θπ ^ e₁ * (θπ ^ m)⁻¹ := by
    rw [hn₁, zpow_sub₀ hθπ0, div_eq_mul_inv]
  have hηinv : (((η (-1) : ℂˣ) : ℂ))⁻¹ = ((η (-1) : ℂˣ) : ℂ) :=
    (eq_inv_of_mul_eq_one_left hηneg).symm
  rw [hsplit, hηinv]
  linear_combination ((θπ ^ m)⁻¹ * ((θ₀ (-1) : ℂˣ) : ℂ) * ((η (-1) : ℂˣ) : ℂ) * J) * hE' +
    ((θπ ^ m)⁻¹ * ((η (-1) : ℂˣ) : ℂ) * J) * hθneg

include hN hw₂law hw₂K hw₂ne hcentral hcusp in
theorem good_weylJ
    (hw₂irr : ∀ w ∈ V, w ≠ 0 → w₂base ∈ TorusMultOne.cyc w)
    (hw₂adm : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ B : Finset (G → ℂ),
        ∀ w ∈ V, (∀ k ∈ U, ∀ g : G, w (g * k) = w g) → w ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (wJ : G) (hwJ : (wJ : Mat) = !![0, 1; -1, 0]) : Good p θ₀ w₂base wJ := by
  classical
  intro u hu u' hu'

  have hdet : Matrix.GeneralLinearGroup.det wJ = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hwJ, Matrix.det_fin_two_of]
    simp
  rw [hdet, map_one, Units.val_one, one_mul]

  have hint : ((uniformizerUnit ℚ p : Fˣ) : F) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_uniformizerUnit, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  obtain ⟨ϖ, hϖdef⟩ : ∃ ϖ : p.adicCompletionIntegers ℚ, ϖ = ⟨_, hint⟩ := ⟨_, rfl⟩
  have hϖval : algebraMap (p.adicCompletionIntegers ℚ) F ϖ = (uniformizerUnit ℚ p : Fˣ) := by rw [hϖdef]; rfl
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0 := by rw [hϖval]; exact Units.ne_zero _
  have hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [hϖval]; exact valued_uniformizerUnit ℚ p
  have hϖu : Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ = uniformizerUnit ℚ p := Units.ext hϖval

  obtain ⟨S, c, v, hSv, hu'eq⟩ :=
    LanglandsTunnell.RankinSelberg.exists_finset_eq_sum_smul_shell_character_kirillov_of_cuspidal
      p hπ hϖ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hcusp u' hu'
  have hvV : ∀ i ∈ S, v i ∈ V := fun i hi => (hSv i hi).1
  rw [hu'eq, rho_finset_sum_smul,
    pair_finset_sum_smul p θ₀ _ S c _ (fun i hi =>
      integrable_pairFn p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp (rho_mem p w₂base hu wJ) (rho_mem p w₂base (hvV i hi) wJ)),
    pair_finset_sum_smul p θ₀ _ S c _ (fun i hi =>
      integrable_pairFn p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp hu (hvV i hi))]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hviV, ⟨cη, hη⟩, hvK⟩ := hSv i hi
  rw [pair_weylJ_pure p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp hw₂irr hw₂adm wJ hwJ hπ hϖ hϖu hu
    i.1 i.2 cη hη hviV hvK]

include hN hw₂law hw₂K hw₂ne hcentral hcusp in
theorem good_all
    (hw₂irr : ∀ w ∈ V, w ≠ 0 → w₂base ∈ TorusMultOne.cyc w)
    (hw₂adm : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ B : Finset (G → ℂ),
        ∀ w ∈ V, (∀ k ∈ U, ∀ g : G, w (g * k) = w g) → w ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (g : G) : Good p θ₀ w₂base g := by
  classical

  obtain ⟨wJ, hwJ⟩ : ∃ wJ : G, (wJ : Mat) = !![0, 1; -1, 0] := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two_of]), rfl⟩
  have hG : ∀ {g h : G}, Good p θ₀ w₂base g → Good p θ₀ w₂base h → Good p θ₀ w₂base (g * h) :=
    fun hg hh => good_mul p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp hg hh
  have hn := good_unipotent p θ₀ w₂base hw₂law
  have hd := good_diagOne p θ₀ w₂base
  have hs := good_scal p θ₀ w₂base hcentral
  have hw := good_weylJ p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp hw₂irr hw₂adm wJ hwJ

  obtain ⟨a, ha⟩ : ∃ a : F, a = (g : Mat) 0 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : F, b = (g : Mat) 0 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : F, c = (g : Mat) 1 0 := ⟨_, rfl⟩
  obtain ⟨d, hd'⟩ : ∃ d : F, d = (g : Mat) 1 1 := ⟨_, rfl⟩
  have hgm : (g : Mat) = !![a, b; c, d] := by rw [ha, hb, hc, hd']; exact Matrix.eta_fin_two _
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : F, Δ = a * d - b * c := ⟨_, rfl⟩
  have hΔ : Δ ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgm, Matrix.det_fin_two_of] at this
    rw [hΔdef]; exact this
  have coe_scal_two : ∀ z : Fˣ, ((scal z : G) : Mat) = !![(z : F), 0; 0, (z : F)] := by
    intro z
    rw [D4Kit.coe_scal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have coe_diagOne_two : ∀ y : Fˣ, ((diagOne y : G) : Mat) = !![(y : F), 0; 0, 1] := by
    intro y
    rw [TorusMultOne.diagOne_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  by_cases hc0 : c = 0
  ·
    have hd0 : d ≠ 0 := by intro h; apply hΔ; rw [hΔdef, h, hc0]; ring
    have ha0 : a ≠ 0 := by intro h; apply hΔ; rw [hΔdef, h, hc0]; ring
    have hg' : g = unipotent (b / d) * (scal (Units.mk0 d hd0) * diagOne (Units.mk0 (a / d) (div_ne_zero ha0 hd0))) := by
      apply Units.ext
      simp only [Units.val_mul, TorusMultOne.unipotent_val, coe_scal_two, coe_diagOne_two, Units.val_mk0,
        Matrix.mul_fin_two]
      rw [hgm, hc0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp
    rw [hg']
    exact hG (hn _) (hG (hs _) (hd _))
  ·
    have h1 : -Δ / c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hΔ) hc0
    have h2 : c * c / Δ ≠ 0 := div_ne_zero (mul_ne_zero hc0 hc0) hΔ
    have hg' : g = unipotent (a / c) * (wJ * (unipotent (d * c / Δ) *
        (scal (Units.mk0 _ h1) * diagOne (Units.mk0 _ h2)))) := by
      apply Units.ext
      simp only [Units.val_mul, TorusMultOne.unipotent_val, hwJ, coe_scal_two, coe_diagOne_two, Units.val_mk0,
        Matrix.mul_fin_two]
      rw [hgm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> rw [hΔdef] <;> ring
    rw [hg']
    exact hG (hn _) (hG hw (hG (hn _) (hG (hs _) (hd _))))

end KPair
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.KPair"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.TorusShellSumEngine P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.KPair"

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction UnramifiedWhittaker
open NumberField.AdelicLevel (diagOne)
open scoped Classical

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)),
    ∀ u ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
    ∀ u' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      Integrable (fun t : (p.adicCompletion ℚ)ˣ => u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
      (∫ t : (p.adicCompletion ℚ)ˣ, (fun x : GL (Fin 2) (p.adicCompletion ℚ) => u (x * g)) (diagOne t) * (fun x : GL (Fin 2) (p.adicCompletion ℚ) => u' (x * g)) (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        ((θ₀ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (∫ t : (p.adicCompletion ℚ)ˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  intro g u hu u' hu'
  have hI := KPair.integrable_pairFn p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp hu hu'
  have hG := KPair.good_all p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral hcusp hw₂irr hw₂adm g u hu u' hu'
  exact ⟨hI, hG⟩

end S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal (solution)
