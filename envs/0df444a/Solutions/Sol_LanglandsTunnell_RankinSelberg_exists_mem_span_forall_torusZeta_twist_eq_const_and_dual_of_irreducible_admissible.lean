-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9cbb160e-6527-52ce-9e81-b0e303ec4ec5

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible.TorusShellSumEngine"

namespace KSE

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible.TorusShellSumEngine"

section LocalNhds

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

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

end LocalNhds
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible.TorusShellSumEngine"

end KSE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible.TorusShellSumEngine"

section MainLemmas

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G₂" => GL (Fin 2) (p.adicCompletion ℚ)

theorem continuous_glScalar :
    Continuous fun u : Fˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) u : G₂) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous (fun u : Fˣ => ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G₂) : Matrix (Fin 2) (Fin 2) F))
    have h : (fun u : Fˣ => ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G₂) : Matrix (Fin 2) (Fin 2) F)) =
        fun u : Fˣ => Matrix.diagonal (fun _ : Fin 2 => (u : F)) := by
      funext u
      rfl
    rw [h]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous (fun u : Fˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G₂)⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F))
    have h : (fun u : Fˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G₂)⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F)) =
        fun u : Fˣ => Matrix.diagonal (fun _ : Fin 2 => ((u⁻¹ : Fˣ) : F)) := by
      funext u
      rw [← map_inv]
      rfl
    rw [h]
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

theorem glScalar_mul_comm (u : Fˣ) (g : G₂) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u : G₂) * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (u : F) (fun r' => mul_comm _ r') (g : Matrix (Fin 2) (Fin 2) F)).eq

end MainLemmas
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible.TorusShellSumEngine"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible.TorusShellSumEngine"

open IsDedekindDomain NumberField NumberField.AdelicLevel UnramifiedWhittaker Topology Filter
open MeasureTheory LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

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
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    letI := localBorel ℚ p
    ∃ (c cd : ℂ), c ≠ 0 ∧ cd ≠ 0 ∧
      (∃ w₁ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ s : ℂ,
          Integrable (fun y : (p.adicCompletion ℚ)ˣ => w₁ (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ, w₁ (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = c) ∧
      (∃ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ s : ℂ,
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
              w₂ (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ,
                w₂ (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = cd) := by
  classical
  letI hms : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := TorusShellSumEngine.isAddHaarMeasure_selfDualHaarAt ℚ p

  have hμx : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ) =
      TorusShellSumEngine.mulHaar p (selfDualHaarAt ℚ p) := rfl
  haveI hHaar : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure := by
    rw [hμx]; infer_instance
  set U : Set (p.adicCompletion ℚ)ˣ := TorusShellSumEngine.USet p with hU
  have hUmem : ∀ y : (p.adicCompletion ℚ)ˣ, y ∈ U ↔ Valued.v (y : p.adicCompletion ℚ) = 1 := fun y => Iff.rfl
  have hUopen : IsOpen U := TorusShellSumEngine.isOpen_USet p
  have hUmeas : MeasurableSet U := TorusShellSumEngine.measurableSet_USet p
  have hUfin : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) U < ⊤ := by
    rw [hμx]; exact TorusShellSumEngine.mulHaar_USet_lt_top p _
  have hUpos : 0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) U :=
    hUopen.measure_pos _ ⟨1, by rw [hUmem]; simp⟩
  set c : ℂ := (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) U).toReal : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact_mod_cast (ENNReal.toReal_pos hUpos.ne' hUfin.ne).ne'

  have hind_int : Integrable (U.indicator fun _ => (1 : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    refine IntegrableOn.integrable_indicator ?_ hUmeas
    exact integrableOn_const (hs := hUfin.ne)
  have hind_val : (∫ y, U.indicator (fun _ => (1 : ℂ)) y ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = c := by
    rw [integral_indicator_const (1 : ℂ) hUmeas, hc, Complex.real_smul, mul_one]
    rfl

  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ ∀ u : (p.adicCompletion ℚ)ˣ,
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m : ℤ)) → η u = 1 := by
    have hopen : IsOpen {u : (p.adicCompletion ℚ)ˣ | η u = η 1} := hη.isOpen_fiber (η 1)
    obtain ⟨m₀, hm₀⟩ := KSE.exists_ball_subset_of_mem_nhds_units p (hopen.mem_nhds (by simp))
    refine ⟨max m₀ 1, le_max_right _ _, fun u hu => ?_⟩
    have := hm₀ u (hu.trans (by rw [WithZero.exp_le_exp]; omega))
    simpa using this

  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, ∀ u : (p.adicCompletion ℚ)ˣ,
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m' : ℤ)) → θ₀ u = 1 := by
    obtain ⟨-, hKopen⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
    have hmem : (fun u : (p.adicCompletion ℚ)ˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (p.adicCompletion ℚ))) ⁻¹'
        (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∈ 𝓝 (1 : (p.adicCompletion ℚ)ˣ) := by
      refine (hKopen.preimage (continuous_glScalar p)).mem_nhds ?_
      show Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (p.adicCompletion ℚ)ˣ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N
      rw [map_one]; exact Subgroup.one_mem _
    obtain ⟨m', hm'⟩ := KSE.exists_ball_subset_of_mem_nhds_units p hmem
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, w₂base g₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw₂ne (funext hcon)
    refine ⟨m', fun u hu => ?_⟩
    have hk := hw₂K _ (hm' u hu) g₀
    rw [← glScalar_mul_comm p u g₀, hcentral u g₀] at hk
    have h1 : ((θ₀ u : ℂˣ) : ℂ) = 1 := (mul_eq_right₀ hg₀).mp hk
    exact Units.ext h1

  set M : ℕ := max m m' with hM
  let f₁ : (p.adicCompletion ℚ)ˣ → ℂ := fun y =>
    if Valued.v (y : p.adicCompletion ℚ) = 1 then (((η y : ℂˣ) : ℂ))⁻¹ else 0
  let f₂ : (p.adicCompletion ℚ)ˣ → ℂ := fun y =>
    if Valued.v (y : p.adicCompletion ℚ) = 1 then ((η y : ℂˣ) : ℂ) * ((θ₀ y : ℂˣ) : ℂ) else 0
  have hwin : ∀ y : (p.adicCompletion ℚ)ˣ,
      WithZero.exp (-(0 : ℤ)) < Valued.v (y : p.adicCompletion ℚ) ∨ Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-(0 : ℤ)) →
        Valued.v (y : p.adicCompletion ℚ) ≠ 1 := by
    intro y hy
    rw [neg_zero, WithZero.exp_zero] at hy
    rcases hy with h | h
    · exact ne_of_gt h
    · exact ne_of_lt h
  have hunit : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(M : ℤ)) →
        (Valued.v (((y * u : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = 1 ↔ Valued.v (y : p.adicCompletion ℚ) = 1) ∧
        η u = 1 ∧ θ₀ u = 1 := by
    intro y u hu1 hu
    refine ⟨by rw [Units.val_mul, map_mul, hu1, mul_one], hm u (hu.trans ?_), hm' u (hu.trans ?_)⟩
    · rw [WithZero.exp_le_exp]; omega
    · rw [WithZero.exp_le_exp]; omega
  have hf₁₀ : ∀ y : (p.adicCompletion ℚ)ˣ,
      WithZero.exp (-(0 : ℤ)) < Valued.v (y : p.adicCompletion ℚ) ∨ Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-(0 : ℤ)) →
        f₁ y = 0 := fun y hy => by simp only [f₁, if_neg (hwin y hy)]
  have hf₂₀ : ∀ y : (p.adicCompletion ℚ)ˣ,
      WithZero.exp (-(0 : ℤ)) < Valued.v (y : p.adicCompletion ℚ) ∨ Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-(0 : ℤ)) →
        f₂ y = 0 := fun y hy => by simp only [f₂, if_neg (hwin y hy)]
  have hf₁₁ : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(M : ℤ)) → f₁ (y * u) = f₁ y := by
    intro y u hu1 hu
    obtain ⟨hiff, hηu, -⟩ := hunit y u hu1 hu
    simp only [f₁, map_mul, hηu, mul_one]
    by_cases hy : Valued.v (y : p.adicCompletion ℚ) = 1
    · rw [if_pos (hiff.mpr hy), if_pos hy]
    · rw [if_neg (fun h => hy (hiff.mp h)), if_neg hy]
  have hf₂₁ : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(M : ℤ)) → f₂ (y * u) = f₂ y := by
    intro y u hu1 hu
    obtain ⟨hiff, hηu, hθu⟩ := hunit y u hu1 hu
    simp only [f₂, map_mul, hηu, hθu, mul_one]
    by_cases hy : Valued.v (y : p.adicCompletion ℚ) = 1
    · rw [if_pos (hiff.mpr hy), if_pos hy]
    · rw [if_neg (fun h => hy (hiff.mp h)), if_neg hy]
  obtain ⟨b₁, hb₁V, hb₁K⟩ :=
    AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
      p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr f₁ 0 0 M hf₁₀ hf₁₁
  obtain ⟨b₂, hb₂V, hb₂K⟩ :=
    AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
      p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr f₂ 0 0 M hf₂₀ hf₂₁

  have hmodU : ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : p.adicCompletion ℚ) = 1 →
      ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) = 1 := by
    intro y hy
    have h := TorusShellSumEngine.modulus_of_valued p (x := (y : p.adicCompletion ℚ)) (m := 0) (by rw [hy, WithZero.exp_zero])
    rw [zpow_zero] at h
    rw [h]; simp

  have hI₁ : ∀ s : ℂ, (fun y : (p.adicCompletion ℚ)ˣ => b₁ (diagOne y) * ((η y : ℂˣ) : ℂ) *
      ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) = U.indicator fun _ => (1 : ℂ) := by
    intro s
    funext y
    rw [hb₁K]
    by_cases hy : Valued.v (y : p.adicCompletion ℚ) = 1
    · rw [Set.indicator_of_mem ((hUmem y).mpr hy)]
      simp only [f₁, if_pos hy]
      rw [hmodU y hy, Complex.one_cpow, mul_one, inv_mul_cancel₀ (Units.ne_zero _)]
    · rw [Set.indicator_of_notMem (fun h => hy ((hUmem y).mp h))]
      simp only [f₁, if_neg hy, zero_mul]

  let w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => b₂ (g * wJ⁻¹)
  have hw₂V : w₂ ∈ KSE.cyc w₂base := KSE.translate_mem_cyc w₂base hb₂V wJ⁻¹
  have hI₂ : ∀ s : ℂ, (fun y : (p.adicCompletion ℚ)ˣ =>
      w₂ (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
        ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) = U.indicator fun _ => (1 : ℂ) := by
    intro s
    funext y
    have hw₂y : w₂ (diagOne y * wJ) = b₂ (diagOne y) := by
      show b₂ (diagOne y * wJ * wJ⁻¹) = b₂ (diagOne y)
      rw [mul_inv_cancel_right]
    rw [hw₂y, hb₂K]
    by_cases hy : Valued.v (y : p.adicCompletion ℚ) = 1
    · rw [Set.indicator_of_mem ((hUmem y).mpr hy)]
      simp only [f₂, if_pos hy]
      rw [hmodU y hy, Complex.one_cpow, mul_one]
      field_simp [Units.ne_zero (η y), Units.ne_zero (θ₀ y)]
    · rw [Set.indicator_of_notMem (fun h => hy ((hUmem y).mp h))]
      simp only [f₂, if_neg hy, zero_mul]
  refine ⟨c, c, hc0, hc0, ⟨b₁, hb₁V, fun s => ?_⟩, ⟨w₂, hw₂V, fun s => ?_⟩⟩
  · rw [hI₁ s]; exact ⟨hind_int, hind_val⟩
  · rw [hI₂ s]; exact ⟨hind_int, hind_val⟩

end S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible (solution)
