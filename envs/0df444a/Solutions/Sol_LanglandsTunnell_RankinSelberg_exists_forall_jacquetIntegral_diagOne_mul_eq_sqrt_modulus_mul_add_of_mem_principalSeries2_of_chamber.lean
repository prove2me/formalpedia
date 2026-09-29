-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6ecd7253-b3fe-5f77-b20a-c27dfefefeef

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
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Pointwise

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology
open scoped NNReal ENNReal

namespace KW47
namespace TSE

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

noncomputable abbrev mulHaar : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (mulMeasure μ)

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

section Span

variable {G : Type*} [Group G]

theorem translate_mem_span (W₀ : G → ℂ) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))) (h : G) :
    (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)) := by
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

theorem span_le_span_of_mem (W₀ W₁ : G → ℂ)
    (h : W₀ ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₁ (g * h))) :
    Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))
      ≤ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₁ (g * h)) :=
  Submodule.span_le.mpr (by rintro _ ⟨h', rfl⟩; exact translate_mem_span W₁ h h')

theorem law_of_mem_span {X : Type*} (W₀ : G → ℂ) (n : X → G) (ψ : X → ℂ)
    (hlaw : ∀ (x : X) (g : G), W₀ (n x * g) = ψ x * W₀ g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)),
      ∀ (x : X) (g : G), W (n x * g) = ψ x * W g := by
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

theorem smooth_of_mem_span (W₀ : G → ℂ) (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G))
    (hfix : ∀ k ∈ K₀, ∀ g : G, W₀ (g * k) = W₀ g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)),
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
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

end KW47.TSE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47.TSE"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47"

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace S1Q

section Main
variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem smul_set_eq_preimage {c : F} (hc : c ≠ 0) (T : Set F) :
    c • T = (fun y => c⁻¹ * y) ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

theorem map_mul_left_eq_smul [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure] (u : (F)ˣ) :
    ν.map (fun x : F => (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = ((u⁻¹ : (F)ˣ) : F) • s := by
    rw [smul_set_eq_preimage p (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul ν (u⁻¹) s
  rw [show ((u⁻¹ : (F)ˣ) • s : Set F) = ((u⁻¹ : (F)ˣ) : F) • s from rfl] at h
  rw [← h, map_inv, modulus_coe_units, ENNReal.coe_inv (distribHaarChar_pos).ne']

theorem integral_comp_units_mul [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
    (u : (F)ˣ) (h : F → ℂ) :
    ∫ x, h ((u : F) * x) ∂ν = (((modulus (u : F) : ℝ≥0) : ℝ) : ℂ)⁻¹ * ∫ x, h x ∂ν := by
  have h1 : ∫ x, h ((u : F) * x) ∂ν = ∫ y, h y ∂(ν.map fun x : F => (u : F) * x) :=
    (integral_map_equiv (Homeomorph.mulLeft₀ (u : F) u.ne_zero).toMeasurableEquiv h).symm
  rw [h1, map_mul_left_eq_smul, integral_smul_measure, ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.real_smul]
  push_cast
  rfl

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem norm_le_zpow_of_valued_le {x : F} {m : ℤ} (hx : Valued.v x ≤ WithZero.exp (-m)) :
    ‖x‖ ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-m) := by
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0, norm_zero]; positivity
  · have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v x = WithZero.exp a := ⟨_, (WithZero.exp_log hv0).symm⟩
    rw [KW47.TSE.norm_eq_zpow_of_valued p ha]
    rw [ha, WithZero.exp_le_exp] at hx
    exact zpow_le_zpow_right₀ (KW47.TSE.one_lt_absNorm p).le hx

theorem exists_nat_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-(m : ℤ)) < ε := by
  have hq : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := KW47.TSE.one_lt_absNorm p
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  refine ⟨m, ?_⟩
  rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow]

theorem diagonal2_coe' (a : Fin 2 → (F)ˣ) :
    ((diagonal2 p a : G2) : Matrix (Fin 2) (Fin 2) F) = !![(a 0 : F), 0; 0, (a 1 : F)] := by
  rw [diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_eq_diagonal2 (y : (F)ˣ) : (diagOne y : G2) = diagonal2 p ![y, 1] := by
  apply Units.ext
  rw [diagonal2_coe']
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem weyl_unip_diagOne (x : F) (y : (F)ˣ) (k : G2) :
    antidiagonal2 p * upperUnipotent2 p x * (diagOne y * k) =
      diagonal2 p ![1, y] * (antidiagonal2 p * upperUnipotent2 p (x * ((y : F))⁻¹) * k) := by
  have key : antidiagonal2 p * upperUnipotent2 p x * diagOne y =
      diagonal2 p ![1, y] * (antidiagonal2 p * upperUnipotent2 p (x * ((y : F))⁻¹)) := by
    rw [diagOne_eq_diagonal2]
    apply Units.ext
    simp only [Units.val_mul, upperUnipotent2_coe, antidiagonal2_coe, diagonal2_coe']
    have hy : (y : F) ≠ 0 := y.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy] <;> field_simp
  calc antidiagonal2 p * upperUnipotent2 p x * (diagOne y * k)
      = (antidiagonal2 p * upperUnipotent2 p x * diagOne y) * k := by simp only [mul_assoc]
    _ = _ := by rw [key, mul_assoc]

theorem weyl_unip_eq (t : (F)ˣ) :
    antidiagonal2 p * upperUnipotent2 p (t : F) =
      upperUnipotent2 p ((t : F))⁻¹ * diagonal2 p ![-t⁻¹, t] *
        (antidiagonal2 p * upperUnipotent2 p ((t : F))⁻¹ * antidiagonal2 p) := by
  apply Units.ext
  simp only [Units.val_mul, upperUnipotent2_coe, antidiagonal2_coe, diagonal2_coe', Units.val_neg,
    Units.val_inv_eq_inv_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  have ht : (t : F) ≠ 0 := t.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht] <;> field_simp

theorem antidiagonal2_mul_self : antidiagonal2 p * antidiagonal2 p = 1 := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal2_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem upperUnipotent2_zero : upperUnipotent2 p (0 : F) = 1 := by
  apply Units.ext
  simp only [upperUnipotent2_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem upperUnipotent2_eq_unipotentGL2 (x : F) : (upperUnipotent2 p x : G2) = unipotentGL2 x :=
  Units.ext rfl

theorem continuous_upperUnipotent2 : Continuous fun x : F => (upperUnipotent2 p x : G2) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2_coe] <;> fun_prop
  · have : (fun x : F => (((upperUnipotent2 p x : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F)) =
        fun x : F => !![1, -x; 0, 1] := by
      funext x; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

variable (μ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))

theorem ps_diag_one_left {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) (y : (F)ˣ) (g : G2) :
    φ (diagonal2 p ![1, y] * g) = ((μ 1 y : ℂˣ) : ℂ) * (((Real.sqrt ‖(y : F)‖ : ℝ) : ℂ))⁻¹ * φ g := by
  rw [hφ.2.2]
  congr 1
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_one, Units.val_one, one_mul, norm_one, one_div, Real.sqrt_inv]
  push_cast
  ring

theorem ps_weyl_unip {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) (t : (F)ˣ) (k : G2) :
    φ (antidiagonal2 p * upperUnipotent2 p (t : F) * k) =
      ((μ 0 (-t⁻¹) : ℂˣ) : ℂ) * ((μ 1 t : ℂˣ) : ℂ) * ((‖(t : F)‖⁻¹ : ℝ) : ℂ) *
        φ (antidiagonal2 p * upperUnipotent2 p ((t : F))⁻¹ * antidiagonal2 p * k) := by
  rw [weyl_unip_eq, mul_assoc, mul_assoc, hφ.2.1, hφ.2.2]
  congr 1
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Units.val_neg, Units.val_inv_eq_inv_val, norm_neg, norm_inv]
  have ht : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  rw [show ‖(t : F)‖⁻¹ / ‖(t : F)‖ = (‖(t : F)‖⁻¹) ^ 2 by field_simp, Real.sqrt_sq (inv_nonneg.2 ht.le)]

theorem exists_forall_apply_lowerUnipotent_mul_eq {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) :
    ∃ m : ℕ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ c : F, Valued.v c ≤ WithZero.exp (-(m : ℤ)) →
      φ (antidiagonal2 p * upperUnipotent2 p c * antidiagonal2 p * k) = φ k := by
  classical
  have hlc : IsLocallyConstant φ := hφ.1
  have hK : IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G2) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).1
  set S : Set (G2 × G2) := {q | φ (q.1 * q.2) = φ q.2} with hS
  have hSo : IsOpen S := by
    have h1 : IsLocallyConstant (fun q : G2 × G2 => φ (q.1 * q.2)) := hlc.comp_continuous continuous_mul
    have h2 : IsLocallyConstant (fun q : G2 × G2 => φ q.2) := hlc.comp_continuous continuous_snd
    have hS' : S = ⋃ c : ℂ, ((fun q : G2 × G2 => φ (q.1 * q.2)) ⁻¹' {c} ∩ (fun q : G2 × G2 => φ q.2) ⁻¹' {c}) := by
      ext q
      simp only [hS, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨φ q.2, h, rfl⟩, fun ⟨c, h1, h2⟩ => h1.trans h2.symm⟩
    rw [hS']
    exact isOpen_iUnion fun c => (h1.isOpen_fiber c).inter (h2.isOpen_fiber c)
  have hsub : ({(1 : G2)} : Set G2) ×ˢ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G2) ⊆ S := by
    rintro ⟨a, k⟩ ⟨ha, -⟩
    have ha' : a = 1 := ha
    simp [hS, ha']
  obtain ⟨U, V, hU, -, h1U, hKV, hUV⟩ := generalized_tube_lemma isCompact_singleton hK hSo hsub
  have hcont : Continuous fun c : F => (antidiagonal2 p * upperUnipotent2 p c * antidiagonal2 p : G2) :=
    (continuous_const.mul (continuous_upperUnipotent2 p)).mul continuous_const
  have h0 : (antidiagonal2 p * upperUnipotent2 p 0 * antidiagonal2 p : G2) = 1 := by
    rw [upperUnipotent2_zero, mul_one, antidiagonal2_mul_self]
  have hpre : (fun c : F => (antidiagonal2 p * upperUnipotent2 p c * antidiagonal2 p : G2)) ⁻¹' U ∈ 𝓝 (0 : F) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds (h1U (Set.mem_singleton 1)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨m, hm⟩ := exists_nat_zpow_neg_lt p hε
  refine ⟨m, fun k hk c hc => ?_⟩
  have hcU : (antidiagonal2 p * upperUnipotent2 p c * antidiagonal2 p : G2) ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_le_zpow_of_valued_le p hc) hm
  have := hUV (Set.mk_mem_prod hcU (hKV hk))
  simpa [hS] using this

theorem exists_forall_apply_weyl_unip_eq_tail {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) :
    ∃ m : ℕ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ t : F, WithZero.exp (m : ℤ) ≤ Valued.v t →
      φ (antidiagonal2 p * upperUnipotent2 p t * k) =
        ((μ 0 (-1) : ℂˣ) : ℂ) * φ k * (charExt ((μ 0)⁻¹ * μ 1) t * ((‖t‖⁻¹ : ℝ) : ℂ)) := by
  obtain ⟨m, hm⟩ := exists_forall_apply_lowerUnipotent_mul_eq p μ hφ
  refine ⟨m, fun k hk t ht => ?_⟩
  have hvt0 : Valued.v t ≠ 0 := by
    intro h0; rw [h0] at ht; exact absurd ht (not_le.2 WithZero.exp_pos)
  have ht0 : t ≠ 0 := (Valuation.ne_zero_iff _).1 hvt0
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v t = WithZero.exp a := ⟨_, (WithZero.exp_log hvt0).symm⟩
  have hma : (m : ℤ) ≤ a := by rwa [ha, WithZero.exp_le_exp] at ht
  have hinv : Valued.v t⁻¹ ≤ WithZero.exp (-(m : ℤ)) := by
    rw [map_inv₀, ha, ← WithZero.exp_neg, WithZero.exp_le_exp]; omega
  set u : (F)ˣ := Units.mk0 t ht0 with hu
  have hut : (u : F) = t := rfl
  have e1 := ps_weyl_unip p μ hφ u k
  rw [hut] at e1
  rw [e1, hm k hk _ hinv, charExt_of_ne_zero _ ht0]
  rw [show Units.mk0 t ht0 = u from rfl, show (-u⁻¹ : (F)ˣ) = -1 * u⁻¹ from (neg_one_mul _).symm]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

theorem exists_forall_higherUnitsAt_eq_one (χ : (F)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ c : ℕ, ∀ u ∈ higherUnitsAt ℚ p c, χ u = 1 := by
  have hO : IsOpen {u : (F)ˣ | χ u = 1} := hχ.isOpen_fiber 1
  obtain ⟨U, hU, hUO⟩ := (Units.isEmbedding_val₀ (G₀ := F)).isInducing.isOpen_iff.mp hO
  have h1U : U ∈ 𝓝 (1 : F) := by
    refine hU.mem_nhds ?_
    have h1 : (1 : (F)ˣ) ∈ Units.val ⁻¹' U := by
      rw [hUO]; simp
    simpa using h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h1U
  obtain ⟨m, hm⟩ := exists_nat_zpow_neg_lt p hε
  refine ⟨m + 1, fun u hu => ?_⟩
  rcases ((mem_higherUnitsAt_iff ℚ p).1 hu).2 with h0 | hle
  · omega
  have hle' : Valued.v ((u : F) - 1) ≤ WithZero.exp (-(m : ℤ)) :=
    hle.trans (WithZero.exp_le_exp.2 (by push_cast; omega))
  have hmem : u ∈ Units.val ⁻¹' U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (norm_le_zpow_of_valued_le p hle') hm
  rw [hUO] at hmem
  exact hmem

theorem norm_uniformizerUnit :
    ‖(uniformizerUnit ℚ p : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [KW47.TSE.norm_eq_zpow_of_valued p (valued_uniformizerUnit ℚ p), _root_.zpow_neg_one]

theorem hdom_of_chamber (hμ : ∀ i, IsLocallyConstant (μ i)) (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (F)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i)) (h01 : σ 1 < σ 0) :
    ‖((μ 0 (uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ < ‖((μ 1 (uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ := by
  rw [hσ, hσ, norm_uniformizerUnit]
  have hq : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by
    have h2 : 2 ≤ Ideal.absNorm p.asIdeal := by
      have hne1 : Ideal.absNorm p.asIdeal ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
      have hne0 : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
      omega
    exact_mod_cast h2
  have h0 : (0 : ℝ) < (((Ideal.absNorm p.asIdeal : ℕ) : ℝ))⁻¹ := inv_pos.2 (zero_lt_one.trans hq)
  have h1 : (((Ideal.absNorm p.asIdeal : ℕ) : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  exact (Real.rpow_lt_rpow_left_iff_of_base_lt_one h0 h1).2 h01

theorem integrable_psi_mul_weyl_unip {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (hμ : ∀ i, IsLocallyConstant (μ i)) (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (F)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i)) (h01 : σ 1 < σ 0)
    (a : F) (k : G2) :
    letI : MeasurableSpace F := localBorel ℚ p
    Integrable (fun t : F => NumberField.StandardAddChar.psiLocal ℚ p (a * t) *
      φ (antidiagonal2 p * upperUnipotent2 p t * k)) (selfDualHaarAt ℚ p) := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := KW47.TSE.isAddHaarMeasure_selfDualHaarAt ℚ p
  choose cχ hcχ using fun i => exists_forall_higherUnitsAt_eq_one p (μ i) (hμ i)
  have hθ : Continuous (AddChar.mulShift (NumberField.StandardAddChar.psiLocal ℚ p) a) := by
    show Continuous fun t : F => NumberField.StandardAddChar.psiLocal ℚ p (a * t)
    exact (NumberField.StandardAddChar.continuous_psiLocal (K := ℚ) (v := p)).comp (continuous_const.mul continuous_id)
  have h := LanglandsTunnell.CubicInduction.integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
    p μ cχ hcχ (uniformizerUnit ℚ p) (valued_uniformizerUnit ℚ p) (hdom_of_chamber p μ hμ σ hσ h01) φ hφ
    (antidiagonal2 p) (antidiagonal2_coe p) (AddChar.mulShift (NumberField.StandardAddChar.psiLocal ℚ p) a) hθ k
    (selfDualHaarAt ℚ p)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  show φ (antidiagonal2 p * unipotentGL2 t * k) * (AddChar.mulShift (NumberField.StandardAddChar.psiLocal ℚ p) a) t = _
  rw [AddChar.mulShift_apply, ← upperUnipotent2_eq_unipotentGL2, mul_comm]

theorem compl_ball_eq (m : ℤ) :
    {t : F | Valued.v t ≤ WithZero.exp (m - 1)}ᶜ = {t : F | WithZero.exp m ≤ Valued.v t} := by
  ext t
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  rcases eq_or_ne (Valued.v t) 0 with h0 | h0
  · rw [h0]
    exact ⟨fun h => absurd h (not_lt_of_ge zero_le'), fun h => absurd WithZero.exp_pos (not_lt_of_ge h)⟩
  · obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v t = WithZero.exp a := ⟨_, (WithZero.exp_log h0).symm⟩
    rw [ha, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem measurableSet_ball (m : ℤ) :
    letI : MeasurableSpace F := localBorel ℚ p
    MeasurableSet {t : F | Valued.v t ≤ WithZero.exp m} := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  exact (KW47.TSE.isClosed_ball p m).measurableSet

theorem struct {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (hμ : ∀ i, IsLocallyConstant (μ i)) (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (F)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i)) (h01 : σ 1 < σ 0) :
    letI : MeasurableSpace F := localBorel ℚ p
    ∃ m : ℕ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ y : (F)ˣ,
      Valued.v (y : F) ≤ WithZero.exp (-(m : ℤ)) →
        (∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
            φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * k)) ∂(selfDualHaarAt ℚ p)) =
          ((μ 1 y : ℂˣ) : ℂ) * ((Real.sqrt (modulus (y : F)) : ℝ) : ℂ) *
            ((∫ t in {t : F | Valued.v t ≤ WithZero.exp ((m : ℤ) - 1)},
                φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂(selfDualHaarAt ℚ p)) +
              ((μ 0 (-1) : ℂˣ) : ℂ) * φ k *
                ∫ t in {t : F | WithZero.exp (m : ℤ) ≤ Valued.v t},
                  NumberField.StandardAddChar.psiLocal ℚ p ((y : F) * t) *
                    (charExt ((μ 0)⁻¹ * μ 1) t * ((‖t‖⁻¹ : ℝ) : ℂ)) ∂(selfDualHaarAt ℚ p)) := by
  classical
  letI instMS : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := KW47.TSE.isAddHaarMeasure_selfDualHaarAt ℚ p
  obtain ⟨m, htail⟩ := exists_forall_apply_weyl_unip_eq_tail p μ hφ
  refine ⟨m, fun k hk y hy => ?_⟩
  set ψ := NumberField.StandardAddChar.psiLocal ℚ p with hψ
  set ν : Measure F := selfDualHaarAt ℚ p with hν
  have hy0 : (y : F) ≠ 0 := y.ne_zero

  have e1 : ∀ x : F, ψ x * φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * k)) =
      (((μ 1 y : ℂˣ) : ℂ) * (((Real.sqrt ‖(y : F)‖ : ℝ) : ℂ))⁻¹) *
        (ψ x * φ (antidiagonal2 p * upperUnipotent2 p (x * ((y : F))⁻¹) * k)) := by
    intro x
    rw [weyl_unip_diagOne, ps_diag_one_left p μ hφ]
    ring
  have e2 : (∫ x : F, ψ x * φ (antidiagonal2 p * upperUnipotent2 p (x * ((y : F))⁻¹) * k) ∂ν) =
      (((modulus (y : F) : ℝ≥0) : ℝ) : ℂ) *
        ∫ t : F, ψ ((y : F) * t) * φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν := by
    have h := integral_comp_units_mul p ν y (fun x => ψ x * φ (antidiagonal2 p * upperUnipotent2 p (x * ((y : F))⁻¹) * k))
    have hmod : (((modulus (y : F) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
      rw [coe_modulus_eq_norm]; exact_mod_cast (norm_pos_iff.2 hy0).ne'
    have hc : ∀ t : F, (y : F) * t * ((y : F))⁻¹ = t := fun t => by
      rw [mul_comm ((y : F)) t, mul_inv_cancel_right₀ hy0]
    simp only [hc] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hmod, one_mul]
  have hint := integrable_psi_mul_weyl_unip p μ hφ hμ σ hσ h01 (y : F) k
  have hB := measurableSet_ball p ((m : ℤ) - 1)
  have hR : MeasurableSet {t : F | WithZero.exp (m : ℤ) ≤ Valued.v t} := by
    rw [← compl_ball_eq]; exact hB.compl

  have esplit : (∫ t : F, ψ ((y : F) * t) * φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν) =
      (∫ t in {t : F | Valued.v t ≤ WithZero.exp ((m : ℤ) - 1)},
          ψ ((y : F) * t) * φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν) +
        ∫ t in {t : F | WithZero.exp (m : ℤ) ≤ Valued.v t},
          ψ ((y : F) * t) * φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν := by
    rw [← integral_add_compl hB hint, compl_ball_eq]

  have e3 : ∫ t in {t : F | Valued.v t ≤ WithZero.exp ((m : ℤ) - 1)},
        ψ ((y : F) * t) * φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν =
      ∫ t in {t : F | Valued.v t ≤ WithZero.exp ((m : ℤ) - 1)}, φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν := by
    refine setIntegral_congr_fun hB fun t ht => ?_
    have hψ1 : ψ ((y : F) * t) = 1 := by
      apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
      have ht' : Valued.v t ≤ WithZero.exp ((m : ℤ) - 1) := ht
      calc Valued.v (y : F) * Valued.v t ≤ WithZero.exp (-(m : ℤ)) * WithZero.exp ((m : ℤ) - 1) :=
            mul_le_mul' hy ht'
        _ ≤ 1 := by rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    rw [hψ1, one_mul]

  have e4 : ∫ t in {t : F | WithZero.exp (m : ℤ) ≤ Valued.v t},
        ψ ((y : F) * t) * φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν =
      ((μ 0 (-1) : ℂˣ) : ℂ) * φ k *
        ∫ t in {t : F | WithZero.exp (m : ℤ) ≤ Valued.v t},
          ψ ((y : F) * t) * (charExt ((μ 0)⁻¹ * μ 1) t * ((‖t‖⁻¹ : ℝ) : ℂ)) ∂ν := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hR fun t ht => ?_
    rw [htail k hk t ht]
    ring

  have hny : 0 < ‖(y : F)‖ := norm_pos_iff.2 hy0
  have hs : (((Real.sqrt ‖(y : F)‖ : ℝ) : ℂ))⁻¹ * (((modulus (y : F) : ℝ≥0) : ℝ) : ℂ) =
      ((Real.sqrt (modulus (y : F)) : ℝ) : ℂ) := by
    rw [coe_modulus_eq_norm, inv_mul_eq_div, ← Complex.ofReal_div, Real.div_sqrt]

  calc (∫ x : F, ψ x * φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * k)) ∂ν)
      = ∫ x : F, (((μ 1 y : ℂˣ) : ℂ) * (((Real.sqrt ‖(y : F)‖ : ℝ) : ℂ))⁻¹) *
          (ψ x * φ (antidiagonal2 p * upperUnipotent2 p (x * ((y : F))⁻¹) * k)) ∂ν := by
        simp_rw [e1]
    _ = (((μ 1 y : ℂˣ) : ℂ) * (((Real.sqrt ‖(y : F)‖ : ℝ) : ℂ))⁻¹) *
          ((((modulus (y : F) : ℝ≥0) : ℝ) : ℂ) *
            ∫ t : F, ψ ((y : F) * t) * φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν) := by
        rw [integral_const_mul, e2]
    _ = ((μ 1 y : ℂˣ) : ℂ) * ((((Real.sqrt ‖(y : F)‖ : ℝ) : ℂ))⁻¹ * (((modulus (y : F) : ℝ≥0) : ℝ) : ℂ)) *
          ((∫ t in {t : F | Valued.v t ≤ WithZero.exp ((m : ℤ) - 1)}, φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂ν) +
            ((μ 0 (-1) : ℂˣ) : ℂ) * φ k *
              ∫ t in {t : F | WithZero.exp (m : ℤ) ≤ Valued.v t},
                ψ ((y : F) * t) * (charExt ((μ 0)⁻¹ * μ 1) t * ((‖t‖⁻¹ : ℝ) : ℂ)) ∂ν) := by
        rw [esplit, e3, e4]; ring
    _ = _ := by rw [hs]

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47.TSE"
end S1Q
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47.TSE"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.KW47.TSE"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)
open scoped Classical

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ (c : ℝ) (C₀ C₁ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), 0 < c ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (y : (p.adicCompletion ℚ)ˣ), ‖(y : p.adicCompletion ℚ)‖ ≤ c →
        (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * k)) ∂(selfDualHaarAt ℚ p)) =
          ((Real.sqrt (modulus (y : p.adicCompletion ℚ)) : ℝ) : ℂ) * (C₁ k * ((μ 1 y : ℂˣ) : ℂ) + C₀ k * ((μ 0 y : ℂˣ) : ℂ)) := by
  classical
  letI instMS : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := KW47.TSE.isAddHaarMeasure_selfDualHaarAt ℚ p

  obtain ⟨m, hstruct⟩ := S1Q.struct p μ hφ hμ σ hσ h01

  have hηlc : IsLocallyConstant ((μ 0)⁻¹ * μ 1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) := by
    have : (⇑((μ 0)⁻¹ * μ 1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) : (p.adicCompletion ℚ)ˣ → ℂˣ) =
        fun a => ((μ 0) a)⁻¹ * (μ 1) a := funext fun a => rfl
    rw [this]
    exact (hμ 0).comp₂ (hμ 1) (fun a b => a⁻¹ * b)
  have hησ : ∀ a : (p.adicCompletion ℚ)ˣ,
      ‖((((μ 0)⁻¹ * μ 1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ 1 - σ 0) := by
    intro a
    have ha : 0 < ‖(a : p.adicCompletion ℚ)‖ := norm_pos_iff.2 a.ne_zero
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
      hσ, hσ, Real.rpow_sub ha]
    ring
  obtain ⟨-, c, A, B, hc, hG⟩ :=
    LanglandsTunnell.TateLocal.integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero
      p ((μ 0)⁻¹ * μ 1) hηlc (σ 1 - σ 0) hησ (by linarith) (m : ℤ) (selfDualHaarAt ℚ p)

  have hq : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := KW47.TSE.one_lt_absNorm p
  set c' : ℝ := min c ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ)) ^ (-(m : ℤ))) with hc'
  refine ⟨c', fun k => ((μ 0 (-1) : ℂˣ) : ℂ) * φ k * B,
    fun k => (∫ t in {t : p.adicCompletion ℚ | Valued.v t ≤ WithZero.exp ((m : ℤ) - 1)},
        φ (antidiagonal2 p * upperUnipotent2 p t * k) ∂(selfDualHaarAt ℚ p)) + ((μ 0 (-1) : ℂˣ) : ℂ) * φ k * A,
    lt_min hc (zpow_pos (zero_lt_one.trans hq) _), fun k hk y hy => ?_⟩
  have hy1 : ‖(y : p.adicCompletion ℚ)‖ ≤ c := hy.trans (min_le_left _ _)
  have hy2 : Valued.v (y : p.adicCompletion ℚ) ≤ WithZero.exp (-(m : ℤ)) := by
    have h := hy.trans (min_le_right _ _)
    have hvy : Valued.v (y : p.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
    obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v (y : p.adicCompletion ℚ) = WithZero.exp a := ⟨_, (WithZero.exp_log hvy).symm⟩
    rw [KW47.TSE.norm_eq_zpow_of_valued p ha] at h
    rw [ha, WithZero.exp_le_exp]
    exact (zpow_le_zpow_iff_right₀ hq).1 h
  rw [hstruct k hk y hy2, hG y hy1, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  have h0 : ((μ 0 y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h1 : ((μ 1 y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  ring

end S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber (solution)
