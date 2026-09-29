-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bd776f0c-fe7c-56ba-8197-6ac379301ee0

import Mathlib
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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta_tateFourier_mul_localLFactorAt_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_ne_zero_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)
open scoped Classical

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology
open scoped NNReal ENNReal

namespace ALLTWIST
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

private theorem _root_.ALLTWIST.TSE.isOpen_ball (k : ℤ) : IsOpen {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

p2m_export "ALLTWIST.TSE" "isOpen_ball"

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

theorem integrable_and_hasSum_shell
    (φ : (v.adicCompletion K)ˣ → ℂ) (hφ : IsLocallyConstant φ)
    (C : ℝ) (M : ℕ)
    (hC : ∀ y : (v.adicCompletion K)ˣ, ‖φ y‖ ≤ C * max 1 ((modulus (y : v.adicCompletion K)) ^ M)⁻¹)
    (c₀ : ℝ) (hc₀ : ∀ y : (v.adicCompletion K)ˣ, c₀ < modulus (y : v.adicCompletion K) → φ y = 0)
    (ν : (v.adicCompletion K)ˣ →* ℂˣ) (hν : IsLocallyConstant fun y : (v.adicCompletion K)ˣ => ((ν y : ℂˣ) : ℂ))
    (B : ℝ) (hB : ∀ u ∈ USet v, ‖((ν u : ℂˣ) : ℂ)‖ ≤ B)
    (k₂ : ℕ) (hk₂ : ‖((ν (uniformizerUnit K v) : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ k₂)
    (z : ℂ) (hz : (M : ℝ) + k₂ < z.re) :
    Integrable (fun y : (v.adicCompletion K)ˣ =>
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z) (mulHaar v μ) ∧
    HasSum (fun n : ℤ => ∫ y in shell v n,
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ))
      (∫ y, φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ)) ∧
    (∀ n : ℤ, ∫ y in shell v n,
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ)
      = (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) *
          ∫ y in shell v n, φ y * ((ν y : ℂˣ) : ℂ) ∂(mulHaar v μ)) := by

  set ϖ : (v.adicCompletion K)ˣ := uniformizerUnit K v with hϖ
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hN
  set μx : Measure (v.adicCompletion K)ˣ := mulHaar v μ with hμx
  set f : (v.adicCompletion K)ˣ → ℂ := fun y =>
    φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z with hf
  set F : (v.adicCompletion K)ˣ → ℂ := fun y => φ y * ((ν y : ℂˣ) : ℂ) with hF
  have hNpos : 0 < N := absNorm_pos v
  have hN1 : 1 < N := one_lt_absNorm v
  have hNC0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by rw [← hN]; exact hNpos.ne'
    exact_mod_cast h0
  set σ : ℝ := z.re with hσ
  set t : ℝ := ‖((ν ϖ : ℂˣ) : ℂ)‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _

  set cst : ℤ → ℂ := fun n => (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) with hcst
  have hnorm_cst : ∀ n : ℤ, ‖cst n‖ = N ^ (-(n : ℝ) * σ) := by
    intro n
    rw [hcst]
    simp only
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))]
    congr 1
    simp [hσ]

  have hmodC : ∀ (n : ℤ) (y : (v.adicCompletion K)ˣ), y ∈ shell v n →
      ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z = cst n := by
    intro n y hy
    have hm := modulus_shell v hy
    rw [hcst]
    simp only
    rw [hm, NNReal.coe_zpow, NNReal.coe_natCast]
    have hr : (0 : ℝ) < N ^ (-n) := zpow_pos hNpos _
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.cpow_def_of_ne_zero hNC0]
    congr 1
    have hlog1 : Complex.log ((N ^ (-n) : ℝ) : ℂ) = ((Real.log (N ^ (-n)) : ℝ) : ℂ) :=
      (Complex.ofReal_log hr.le).symm
    have hlog2 : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = ((Real.log N : ℝ) : ℂ) := by
      rw [show (Ideal.absNorm v.asIdeal : ℂ) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) by push_cast; rfl]
      exact (Complex.ofReal_log hNpos.le).symm
    rw [hlog1, hlog2, Real.log_zpow]
    push_cast
    ring
  have hfF : ∀ (n : ℤ) (y : (v.adicCompletion K)ˣ), y ∈ shell v n → f y = cst n * F y := by
    intro n y hy
    simp only [hf, hF]
    rw [hmodC n y hy]
    ring

  have hF_cont : Continuous F := hφ.continuous.mul hν.continuous
  have hFn_meas : ∀ n : ℤ, Measurable fun u : (v.adicCompletion K)ˣ => F (ϖ ^ n * u) := fun n =>
    (hF_cont.comp (continuous_const_mul (ϖ ^ n))).measurable

  have hνn : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ),
      ((ν (ϖ ^ n * u) : ℂˣ) : ℂ) = ((ν ϖ : ℂˣ) : ℂ) ^ n * ((ν u : ℂˣ) : ℂ) := by
    intro n u
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]

  set B' : ℝ := max B 0 with hB'
  set C' : ℝ := max C 0 with hC'
  set R : ℤ → ℝ := fun n => C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) * (t ^ n * B') with hR
  have hR_nonneg : ∀ n, 0 ≤ R n := fun n =>
    mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _))
      (mul_nonneg (zpow_nonneg ht0 _) (le_max_right _ _))
  have hmax_le : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v →
      ((max 1 ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ^ M)⁻¹ : NNReal) : ℝ)
        ≤ N ^ ((M : ℝ) * (max n 0 : ℤ)) := by
    intro n u hu
    rw [modulus_uniformizer_zpow_mul v (n := n) hu]
    push_cast
    rw [← hN, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
    refine max_le ?_ ?_
    · exact Real.one_le_rpow hN1.le (by positivity)
    · rw [← Real.rpow_intCast]
      refine Real.rpow_le_rpow_of_exponent_le hN1.le ?_
      push_cast
      have h1 : (n : ℝ) ≤ ((max n 0 : ℤ) : ℝ) := by exact_mod_cast le_max_left n 0
      have h1' : (n : ℝ) ≤ max (n : ℝ) 0 := le_max_left _ _
      have h2 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_le_mul_of_nonneg_left h1' h2]
  have hF_bound : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v → ‖F (ϖ ^ n * u)‖ ≤ R n := by
    intro n u hu
    simp only [hF, hR]
    rw [norm_mul]
    have h1 : ‖φ (ϖ ^ n * u)‖ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := by
      refine (hC _).trans ?_
      have hm := hmax_le n u hu
      have hmn : (0 : ℝ) ≤ ((max 1 ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ^ M)⁻¹
          : NNReal) : ℝ) := NNReal.coe_nonneg _
      calc C * _ ≤ C' * _ := mul_le_mul_of_nonneg_right (le_max_left C 0) hmn
        _ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := mul_le_mul_of_nonneg_left hm (le_max_right _ _)
    have h2 : ‖((ν (ϖ ^ n * u) : ℂˣ) : ℂ)‖ ≤ t ^ n * B' := by
      rw [hνn, norm_mul, norm_zpow, ← ht]
      exact mul_le_mul_of_nonneg_left ((hB u hu).trans (le_max_left _ _)) (zpow_nonneg ht0 _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _))

  have hFn_int : ∀ n : ℤ, IntegrableOn (fun u => F (ϖ ^ n * u)) (USet v) μx := fun n =>
    integrableOn_USet_of_bound v μ _ (hFn_meas n) (R n) (hF_bound n)
  have hF_shell : ∀ n : ℤ, IntegrableOn F (shell v n) μx := by
    intro n
    rw [hμx, integrableOn_shell_iff v μ n F]
    exact hFn_int n
  have hf_shell : ∀ n : ℤ, IntegrableOn f (shell v n) μx := by
    intro n
    refine IntegrableOn.congr_fun (f := fun y => cst n * F y) ?_ ?_ (measurableSet_shell v n)
    · exact (hF_shell n).const_mul (cst n)
    · intro y hy
      exact (hfF n y hy).symm

  set V : ℝ := μx.real (USet v) with hV
  have hV_nonneg : 0 ≤ V := measureReal_nonneg
  have hnorm_shell : ∀ n : ℤ, ∫ y in shell v n, ‖f y‖ ∂μx ≤ N ^ (-(n : ℝ) * σ) * (R n * V) := by
    intro n
    have h1 : ∫ y in shell v n, ‖f y‖ ∂μx = ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx := by
      rw [hμx]
      exact setIntegral_shell_eq v μ n (fun y => ‖f y‖)
    rw [h1]
    have h2 : ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx ≤ ∫ u in USet v, N ^ (-(n : ℝ) * σ) * R n ∂μx := by
      refine setIntegral_mono_on ?_ ?_ (measurableSet_USet v) ?_
      · exact ((integrableOn_shell_iff v μ n f).mp (hf_shell n)).norm
      · exact integrableOn_const ((mulHaar_USet_lt_top v μ).ne)
      · intro u hu
        rw [hfF n (ϖ ^ n * u) (mul_mem_shell v n hu), norm_mul, hnorm_cst n]
        exact mul_le_mul_of_nonneg_left (hF_bound n u hu) (Real.rpow_nonneg hNpos.le _)
    refine h2.trans ?_
    rw [setIntegral_const, smul_eq_mul, hV]
    nlinarith [hR_nonneg n, hV_nonneg, Real.rpow_nonneg hNpos.le (-(n : ℝ) * σ)]

  set K₀ : ℕ := ⌈c₀⌉₊ with hK₀
  have hfar : ∀ k : ℕ, K₀ ≤ k → ∫ y in shell v (-((k : ℤ) + 1)), ‖f y‖ ∂μx = 0 := by
    intro k hk
    refine (setIntegral_congr_fun (measurableSet_shell v _) fun y hy => ?_).trans (integral_zero _ _)
    have hm : (modulus (y : v.adicCompletion K) : ℝ) = N ^ ((k : ℤ) + 1) := by
      rw [modulus_shell v hy, neg_neg, NNReal.coe_zpow, NNReal.coe_natCast]
    have hbig : c₀ < modulus (y : v.adicCompletion K) := by
      rw [hm, zpow_add_one₀ hNpos.ne', zpow_natCast]
      have hk' : c₀ ≤ (k : ℝ) := (Nat.le_ceil c₀).trans (by exact_mod_cast hk)
      have hpow : (k : ℝ) + 1 ≤ N ^ k := by
        have h2N : (2 : ℝ) ≤ N := two_le_absNorm v
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ N - 1 by linarith) k
        rw [add_sub_cancel] at this
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [this, mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ N - 1 by linarith) hk0]
      nlinarith [hpow, pow_pos hNpos k]
    show ‖f y‖ = 0
    rw [hf]
    simp only
    rw [hc₀ y hbig, zero_mul, zero_mul, norm_zero]

  have hsumm : Summable fun n : ℤ => ∫ y in shell v n, ‖f y‖ ∂μx := by
    have hnn : ∀ n : ℤ, 0 ≤ ∫ y in shell v n, ‖f y‖ ∂μx := fun n => integral_nonneg fun _ => norm_nonneg _
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    ·
      set r : ℝ := N ^ ((M : ℝ) + k₂ - σ) with hr
      have hr0 : 0 ≤ r := Real.rpow_nonneg hNpos.le _
      have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by rw [hσ] at hz; linarith)
      refine Summable.of_nonneg_of_le (fun n => hnn n) (fun n => ?_)
        ((summable_geometric_of_lt_one hr0 hr1).mul_left (C' * B' * V))
      refine (hnorm_shell n).trans ?_
      simp only [hR]
      rw [show ((max (n : ℤ) 0 : ℤ) : ℝ) = n by simp, zpow_natCast]

      have htn : t ^ n ≤ N ^ ((k₂ : ℝ) * n) := by
        calc t ^ n ≤ (N ^ k₂) ^ n := pow_le_pow_left₀ ht0 hk₂ n
          _ = N ^ ((k₂ : ℝ) * n) := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      have hrn : r ^ n = N ^ (((M : ℝ) + k₂ - σ) * n) := by
        rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      have hpos1 : 0 ≤ N ^ (-((n : ℤ) : ℝ) * σ) := Real.rpow_nonneg hNpos.le _
      have hpos2 : 0 ≤ N ^ ((M : ℝ) * n) := Real.rpow_nonneg hNpos.le _
      have hC'0 : 0 ≤ C' := le_max_right _ _
      have hB'0 : 0 ≤ B' := le_max_right _ _
      calc N ^ (-((n : ℤ) : ℝ) * σ) * (C' * N ^ ((M : ℝ) * n) * (t ^ n * B') * V)
          = C' * B' * V * (N ^ (-((n : ℤ) : ℝ) * σ) * N ^ ((M : ℝ) * n)) * t ^ n := by ring
        _ ≤ C' * B' * V * (N ^ (-((n : ℤ) : ℝ) * σ) * N ^ ((M : ℝ) * n)) * N ^ ((k₂ : ℝ) * n) := by
            refine mul_le_mul_of_nonneg_left htn ?_
            exact mul_nonneg (mul_nonneg (mul_nonneg hC'0 hB'0) hV_nonneg) (mul_nonneg hpos1 hpos2)
        _ = C' * B' * V * r ^ n := by
            rw [hrn, ← Real.rpow_add hNpos, mul_assoc (C' * B' * V), ← Real.rpow_add hNpos]
            congr 2
            push_cast
            ring
    ·
      refine summable_of_ne_finset_zero (s := Finset.range K₀) fun k hk => ?_
      rw [Finset.mem_range, not_lt] at hk
      exact hfar k hk

  have hint : Integrable f μx := by
    have := integrableOn_iUnion_of_summable_integral_norm hf_shell hsumm
    rwa [iUnion_shell, integrableOn_univ] at this
  refine ⟨hint, ?_, ?_⟩
  ·
    have hsum := hasSum_integral_iUnion (measurableSet_shell v) (pairwise_disjoint_shell v)
      (by rw [iUnion_shell]; exact hint.integrableOn)
    rwa [iUnion_shell, Measure.restrict_univ] at hsum
  ·
    intro n
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_shell v n) fun y hy => hfF n y hy

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

end ALLTWIST.TSE
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST.TSE"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST.TSE"

noncomputable section
namespace Ws28T0

open Topology Filter

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem modulus_coe_pos (y : Fˣ) : 0 < (modulus (y : F) : ℝ) := by
  exact_mod_cast modulus_pos (Units.ne_zero y)

theorem modulus_coe_ne_zero (y : Fˣ) : ((modulus (y : F) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (modulus_coe_pos p y).ne'

theorem modulus_eq_norm (x : F) : (modulus x : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]

def modPow (t : ℝ) : Fˣ →* ℂˣ where
  toFun y := Units.mk0 (((modulus (y : F) : ℝ) : ℂ) ^ (t : ℂ))
    (by rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl (modulus_coe_ne_zero p y))
  map_one' := by
    ext
    simp [modulus_one]
  map_mul' y y' := by
    ext
    simp only [Units.val_mul, Units.val_mk0, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem modPow_apply (t : ℝ) (y : Fˣ) :
    ((modPow p t y : ℂˣ) : ℂ) = ((modulus (y : F) : ℝ) : ℂ) ^ (t : ℂ) := rfl

theorem isLocallyConstant_modulus_coe : IsLocallyConstant fun y : Fˣ => (modulus (y : F) : ℝ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y₀
  have h0 : 0 < ‖(y₀ : F)‖ := norm_pos_iff.mpr (Units.ne_zero y₀)
  have hopen : IsOpen (Metric.ball (y₀ : F) ‖(y₀ : F)‖) := Metric.isOpen_ball
  have hmem : (fun y : Fˣ => (y : F)) ⁻¹' Metric.ball (y₀ : F) ‖(y₀ : F)‖ ∈ 𝓝 y₀ := by
    refine (hopen.preimage Units.continuous_val).mem_nhds ?_
    show (y₀ : F) ∈ Metric.ball (y₀ : F) ‖(y₀ : F)‖
    exact Metric.mem_ball_self h0
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy' : ‖(y : F) - (y₀ : F)‖ < ‖(y₀ : F)‖ := by
    have : dist (y : F) (y₀ : F) < ‖(y₀ : F)‖ := hy
    rwa [dist_eq_norm] at this
  show (modulus (y : F) : ℝ) = (modulus (y₀ : F) : ℝ)
  rw [modulus_eq_norm p, modulus_eq_norm p]
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max ((y : F) - (y₀ : F)) (y₀ : F)
    rw [sub_add_cancel] at h1
    exact h1.trans (max_le hy'.le le_rfl)
  · have h2 := IsUltrametricDist.norm_add_le_max ((y₀ : F) - (y : F)) (y : F)
    rw [sub_add_cancel] at h2
    rcases le_max_iff.mp h2 with h | h
    · rw [norm_sub_rev] at h
      exact absurd (lt_of_le_of_lt h hy') (lt_irrefl _)
    · exact h

end Ws28T0
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST.TSE"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST.TSE"

noncomputable section
namespace T0FE

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem measurableEmbedding_unitsVal : MeasurableEmbedding (Units.val : Fˣ → F) := by
  have hms : (inferInstance : MeasurableSpace Fˣ) = MeasurableSpace.comap Units.val inferInstance := rfl
  refine ⟨fun a b h => Units.ext h, ?_, ?_⟩
  · exact measurable_iff_comap_le.2 le_rfl
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := (id hs : ∃ t : Set F, MeasurableSet t ∧ Units.val ⁻¹' t = s)
    have : Units.val '' (Units.val ⁻¹' t : Set Fˣ) = t ∩ {x : F | x ≠ 0} := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hx, hx0⟩; exact ⟨Units.mk0 x hx0, by simpa using hx, by simp⟩
    rw [this]
    exact ht.inter (isClosed_singleton.measurableSet.compl)

theorem integral_comap_unitsVal (μF : Measure F) (G : F → ℂ) :
    (∫ a : Fˣ, G (a : F) ∂(Measure.comap Units.val (mulMeasure μF))) = ∫ x, G x ∂(mulMeasure μF) := by
  have hemb := measurableEmbedding_unitsVal p
  rw [← hemb.integral_map G, hemb.map_comap]
  congr 1
  apply Measure.restrict_eq_self_of_ae_mem
  have h0 : mulMeasure μF {(0 : F)} = 0 := by
    rw [mulMeasure, withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict (measurableSet_singleton 0)]
    simp
  rw [ae_iff, ← nonpos_iff_eq_zero, ← h0]
  refine le_of_eq (congrArg _ ?_)
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_range, not_exists, Set.mem_singleton_iff]
  constructor
  · intro h; by_contra hx; exact h (Units.mk0 x hx) (by simp)
  · rintro rfl u hu; exact u.ne_zero hu

theorem localZeta_eq_integral_units (μF : Measure F) (f : F → ℂ) (χ χ' : Fˣ →* ℂˣ) (τ : ℝ) (z : ℂ)
    (hχ' : ∀ a : Fˣ, ((χ' a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (τ : ℂ)) :
    localZeta μF f χ' z =
      ∫ a : Fˣ, f (a : F) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (z + τ)
        ∂(Measure.comap Units.val (mulMeasure μF)) := by
  rw [localZeta, ← integral_comap_unitsVal p μF]
  congr 1; funext a
  rw [charExt_of_ne_zero χ' a.ne_zero, Units.mk0_val, hχ', Complex.cpow_add _ _ (Ws28T0.modulus_coe_ne_zero p a)]
  ring

theorem exists_hasConductorExponentAt_of_isLocallyConstant (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ a : ℕ, HasConductorExponentAt ℚ p χ a := by
  classical

  have hopen : IsOpen {y : Fˣ | χ y = χ 1} := hχ.isOpen_fiber (χ 1)
  obtain ⟨V, hV, hVeq⟩ := (Units.isEmbedding_val₀ (G₀ := F)).isInducing.isOpen_iff.1 hopen
  have h1V : (1 : F) ∈ V := by
    have : (1 : Fˣ) ∈ Units.val ⁻¹' V := by rw [hVeq]; simp
    simpa using this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV 1 h1V
  have hq1 : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := ALLTWIST.TSE.one_lt_absNorm p
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ε⁻¹ hq1
  have hP : ∃ n : ℕ, ∀ u ∈ higherUnitsAt ℚ p n, χ u = 1 := by
    refine ⟨m + 1, fun u hu => ?_⟩
    rw [mem_higherUnitsAt_iff] at hu
    obtain ⟨hu1, hu2⟩ := hu
    rcases hu2 with h0 | hle
    · omega
    · have hnorm : ‖(u : F) - 1‖ < ε := by
        by_cases hz : (u : F) - 1 = 0
        · rw [hz, norm_zero]; exact hε
        · obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v ((u : F) - 1) = WithZero.exp k :=
            ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hz)).symm⟩
          rw [ALLTWIST.TSE.norm_eq_zpow_of_valued p hk]
          rw [hk, WithZero.exp_le_exp] at hle
          have hqpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by linarith
          calc (Ideal.absNorm p.asIdeal : ℝ) ^ k ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-((m : ℕ) : ℤ)) :=
                zpow_le_zpow_right₀ hq1.le (by push_cast; omega)
            _ = ((Ideal.absNorm p.asIdeal : ℝ) ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
            _ < ε := by
                rw [inv_lt_comm₀ (pow_pos hqpos m) hε]; exact hm
      have hmem : (u : F) ∈ V := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hnorm)
      have : u ∈ Units.val ⁻¹' V := hmem
      rw [hVeq] at this
      simpa using this
  refine ⟨Nat.find hP, Nat.find_spec hP, fun m' hm' => ?_⟩
  have := Nat.find_min hP hm'
  push_neg at this
  exact this

end T0FE
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST.TSE"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.ALLTWIST.TSE"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsLocallyConstant μ) :
    letI := localBorel ℚ p
    ∃ (Γn Γd : Polynomial ℂ) (eΓ : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ (φ : p.adicCompletion ℚ → ℂ), IsSchwartzBruhat φ → ∀ s : ℂ,
        -1 - Real.logb (Ideal.absNorm p.asIdeal : ℝ) ‖((μ (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ < s.re →
        s.re < -Real.logb (Ideal.absNorm p.asIdeal : ℝ) ‖((μ (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ →
          (∫ a : (p.adicCompletion ℚ)ˣ,
              tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ (a : p.adicCompletion ℚ) *
                ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((eΓ : ℂ) * s) *
              (∫ a : (p.adicCompletion ℚ)ˣ,
                φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  classical
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p

  have hq1 : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := ALLTWIST.TSE.one_lt_absNorm p
  have hq0 : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by linarith
  have hqne1 : (Ideal.absNorm p.asIdeal : ℝ) ≠ 1 := by linarith
  have hqC : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqRC : ((Ideal.absNorm p.asIdeal : ℝ) : ℂ) = (Ideal.absNorm p.asIdeal : ℂ) := by push_cast; rfl
  have hnormq : ∀ z : ℂ, ‖(Ideal.absNorm p.asIdeal : ℂ) ^ z‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ z.re := by
    intro z; rw [← hqRC, Complex.norm_cpow_eq_rpow_re_of_pos hq0]

  set ϖ : (p.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖ
  set r : ℝ := ‖((μ ϖ : ℂˣ) : ℂ)‖ with hr
  have hr0 : 0 < r := by rw [hr]; exact norm_pos_iff.2 (Units.ne_zero _)
  set t₀ : ℝ := Real.logb (Ideal.absNorm p.asIdeal : ℝ) r with ht₀
  set η : (p.adicCompletion ℚ)ˣ →* ℂˣ := μ * Ws28T0.modPow p t₀ with hη
  have hηapply : ∀ a : (p.adicCompletion ℚ)ˣ, ((η a : ℂˣ) : ℂ) =
      ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (t₀ : ℂ) := by
    intro a; rw [hη, MonoidHom.mul_apply, Units.val_mul, Ws28T0.modPow_apply]
  have hηinv : ∀ a : (p.adicCompletion ℚ)ˣ, ((η⁻¹ a : ℂˣ) : ℂ) =
      ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((-t₀ : ℝ) : ℂ) := by
    intro a
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hηapply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, mul_inv,
      Complex.ofReal_neg, Complex.cpow_neg]

  have hmodϖ : (modulus (ϖ : p.adicCompletion ℚ) : ℝ) = (Ideal.absNorm p.asIdeal : ℝ)⁻¹ := by
    rw [ALLTWIST.TSE.coe_modulus_of_valued p (NumberField.AdelicLevel.valued_uniformizerUnit ℚ p), zpow_neg, zpow_one]
  have hη1 : ‖((η ϖ : ℂˣ) : ℂ)‖ = 1 := by
    rw [hηapply, norm_mul, hmodϖ, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.2 hq0), Complex.ofReal_re,
      Real.inv_rpow hq0.le, ht₀, Real.rpow_logb hq0 hqne1 hr0, ← hr]
    exact mul_inv_cancel₀ hr0.ne'

  have hmodlc : IsLocallyConstant (fun y : (p.adicCompletion ℚ)ˣ => (Ws28T0.modPow p t₀ y : ℂˣ)) := by
    refine IsLocallyConstant.desc _ (Units.val : ℂˣ → ℂ) ?_ (fun a b h => Units.ext h)
    have : (Units.val ∘ fun y : (p.adicCompletion ℚ)ˣ => (Ws28T0.modPow p t₀ y : ℂˣ)) =
        (fun x : ℝ => ((x : ℂ)) ^ (t₀ : ℂ)) ∘ fun y : (p.adicCompletion ℚ)ˣ => (modulus (y : p.adicCompletion ℚ) : ℝ) := by
      funext y; simp [Function.comp, Ws28T0.modPow_apply]
    rw [this]
    exact (Ws28T0.isLocallyConstant_modulus_coe p).comp _
  have hηlc : IsLocallyConstant η := by
    have h1 := hμ.prodMk hmodlc
    have : (η : (p.adicCompletion ℚ)ˣ → ℂˣ) = (fun z : ℂˣ × ℂˣ => z.1 * z.2) ∘ fun y => (μ y, Ws28T0.modPow p t₀ y) := by
      funext y; rw [hη]; rfl
    rw [this]; exact h1.comp _

  obtain ⟨a, ha⟩ := T0FE.exists_hasConductorExponentAt_of_isLocallyConstant p η hηlc
  have hε : stdRootNumberAt ℚ p η ≠ 0 := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0] at ha
      rw [LanglandsTunnell.TateLocal.stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero ℚ p η ha hη1
        (LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p) (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)]
      exact one_ne_zero
    · exact LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ p η a hpos ha hη1

  have hZ : ∀ (φ : p.adicCompletion ℚ → ℂ) (s : ℂ),
      localZeta (selfDualHaarAt ℚ p) φ η (-s - (t₀ : ℂ)) =
        ∫ a : (p.adicCompletion ℚ)ˣ, φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) *
          ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    intro φ s
    rw [T0FE.localZeta_eq_integral_units p _ φ μ η t₀ _ hηapply, show -s - (t₀ : ℂ) + (t₀ : ℂ) = -s by ring]
  have hZd : ∀ (φ : p.adicCompletion ℚ → ℂ) (s : ℂ),
      localZeta (selfDualHaarAt ℚ p) (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ) η⁻¹
          (1 - (-s - (t₀ : ℂ))) =
        ∫ a : (p.adicCompletion ℚ)ˣ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ
            (a : p.adicCompletion ℚ) * ((μ⁻¹ a : ℂˣ) : ℂ) *
          ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    intro φ s
    rw [T0FE.localZeta_eq_integral_units p _ _ μ⁻¹ η⁻¹ (-t₀) _ hηinv,
      show (1 - (-s - (t₀ : ℂ))) + ((-t₀ : ℝ) : ℂ) = 1 + s by push_cast; ring]

  have hstrip : ∀ s : ℂ, -1 - t₀ < s.re → s.re < -t₀ → 0 < (-s - (t₀ : ℂ)).re ∧ (-s - (t₀ : ℂ)).re < 1 := by
    intro s h1 h2
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
    constructor <;> linarith

  set cη : ℂ := ((η ϖ : ℂˣ) : ℂ) with hcη
  have hcηnorm : ‖cη‖ = 1 := hη1
  have hcη0 : cη ≠ 0 := Units.ne_zero _
  set E : ℂ := stdRootNumberAt ℚ p η * (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 + (t₀ : ℂ))) with hE
  have hE0 : E ≠ 0 := mul_ne_zero hε (by rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqC)
  have hpowsplit : ∀ s : ℂ, (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - (-s - (t₀ : ℂ)))) =
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 + (t₀ : ℂ))) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * s) := by
    intro s; rw [← Complex.cpow_add _ _ hqC]; congr 1; ring
  have hηinv0 : HasConductorExponentAt ℚ p η 0 → HasConductorExponentAt ℚ p η⁻¹ 0 := by
    intro h; rw [hasConductorExponentAt_zero_iff] at h ⊢; intro u hu; rw [MonoidHom.inv_apply, h u hu, inv_one]
  have hηinv0' : ¬ HasConductorExponentAt ℚ p η 0 → ¬ HasConductorExponentAt ℚ p η⁻¹ 0 := by
    intro h h'; apply h; rw [hasConductorExponentAt_zero_iff] at h' ⊢; intro u hu
    have := h' u hu; rwa [MonoidHom.inv_apply, inv_eq_one] at this
  by_cases hun : HasConductorExponentAt ℚ p η 0
  ·
    set c : ℂ := cη * (Ideal.absNorm p.asIdeal : ℂ) ^ (t₀ : ℂ) with hc
    set d : ℂ := cη⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(t₀ : ℂ) - 1) with hd
    refine ⟨Polynomial.C E * (Polynomial.X - Polynomial.C c), Polynomial.X - Polynomial.C d * Polynomial.X ^ 2, a,
      mul_ne_zero (Polynomial.C_ne_zero.2 hE0) (Polynomial.X_sub_C_ne_zero c), ?_, fun φ hφ s hs1 hs2 => ?_⟩
    · intro h
      have := congrArg (fun P : Polynomial ℂ => P.coeff 1) h
      simp [Polynomial.coeff_X, Polynomial.coeff_C_mul] at this
    · obtain ⟨ht0, ht1⟩ := hstrip s hs1 hs2
      have FE := LanglandsTunnell.CubicInduction.localZeta_tateFourier_mul_localLFactorAt_eq p η hηlc hη1 a ha φ hφ
        (-s - (t₀ : ℂ)) ht0 ht1
      rw [hZ, hZd, hpowsplit, localLFactorAt_of_hasConductorExponentAt_zero ℚ p hun,
        localLFactorAt_of_hasConductorExponentAt_zero ℚ p (hηinv0 hun)] at FE

      set A := ∫ a : (p.adicCompletion ℚ)ˣ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ
            (a : p.adicCompletion ℚ) * ((μ⁻¹ a : ℂˣ) : ℂ) *
          ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) with hA
      set B := ∫ a : (p.adicCompletion ℚ)ˣ, φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) *
          ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) with hB
      set X' : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ (-s) with hX
      set Y' : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ s with hY
      set W : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * s) with hW
      have hXY : X' * Y' = 1 := by rw [hX, hY, ← Complex.cpow_add _ _ hqC, neg_add_cancel, Complex.cpow_zero]

      have e1 : ((η (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(-s - (t₀ : ℂ))) =
          c * Y' := by
        rw [hc, hY, hcη, hϖ, show -(-s - (t₀ : ℂ)) = (t₀ : ℂ) + s by ring, Complex.cpow_add _ _ hqC]; ring
      have e2 : ((η⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - (-s - (t₀ : ℂ)))) =
          d * X' := by
        rw [hd, hX, hcη, hϖ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
          show -(1 - (-s - (t₀ : ℂ))) = (-(t₀ : ℂ) - 1) + -s by ring, Complex.cpow_add _ _ hqC]; ring
      rw [e1, e2] at FE

      have hn1 : ‖c * Y'‖ < 1 := by
        rw [hc, hY, norm_mul, norm_mul, hcηnorm, one_mul, hnormq, hnormq, Complex.ofReal_re, ← Real.rpow_add hq0]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
      have hn2 : ‖d * X'‖ < 1 := by
        rw [hd, hX, norm_mul, norm_mul, norm_inv, hcηnorm, inv_one, one_mul, hnormq, hnormq, ← Real.rpow_add hq0]
        simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
      have h1 : (1 - c * Y') ≠ 0 := by
        intro h; have : c * Y' = 1 := by linear_combination -h
        rw [this, norm_one] at hn1; exact lt_irrefl _ hn1
      have h2 : (1 - d * X') ≠ 0 := by
        intro h; have : d * X' = 1 := by linear_combination -h
        rw [this, norm_one] at hn2; exact lt_irrefl _ hn2
      have h3 : (1 - d * X')⁻¹ * (1 - d * X') = 1 := inv_mul_cancel₀ h2
      have key : A * (1 - d * X') = E * W * B * (1 - c * Y') := by
        calc A * (1 - d * X') = A * (1 - c * Y')⁻¹ * (1 - c * Y') * (1 - d * X') := by rw [inv_mul_cancel_right₀ h1]
          _ = stdRootNumberAt ℚ p η * ((Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 + (t₀ : ℂ))) * W) *
                ((1 - d * X')⁻¹ * B) * (1 - c * Y') * (1 - d * X') := by rw [FE]
          _ = E * W * B * (1 - c * Y') := by
              rw [hE]
              linear_combination (stdRootNumberAt ℚ p η * (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 + (t₀ : ℂ))) *
                W * B * (1 - c * Y')) * h3
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow]
      linear_combination X' * key - (E * W * B * c) * hXY
  ·
    refine ⟨Polynomial.C E, 1, a, Polynomial.C_ne_zero.2 hE0, one_ne_zero, fun φ hφ s hs1 hs2 => ?_⟩
    obtain ⟨ht0, ht1⟩ := hstrip s hs1 hs2
    have FE := LanglandsTunnell.CubicInduction.localZeta_tateFourier_mul_localLFactorAt_eq p η hηlc hη1 a ha φ hφ
      (-s - (t₀ : ℂ)) ht0 ht1
    rw [hZ, hZd, hpowsplit, localLFactorAt_of_not_hasConductorExponentAt_zero ℚ p hun,
      localLFactorAt_of_not_hasConductorExponentAt_zero ℚ p (hηinv0' hun)] at FE
    simp only [Polynomial.eval_C, Polynomial.eval_one]
    linear_combination FE

#print axioms solution

end S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip (solution)
