-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_godementDatum_primitive_of_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0840fcb7-7e84-5fdb-8bf7-ed1f5a1ab86d

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47.TSE"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47"

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Classical

noncomputable section

namespace SIGQ

section Main
variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem diagonal2_coe' (a : Fin 2 → (F)ˣ) :
    ((diagonal2 p a : G2) : Matrix (Fin 2) (Fin 2) F) = !![(a 0 : F), 0; 0, (a 1 : F)] := by
  rw [diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

def secL (a : F) (b : (F)ˣ) : G2 where
  val := !![((b : F))⁻¹, 0; a, (b : F)]
  inv := !![(b : F), 0; -a, ((b : F))⁻¹]
  val_inv := by
    have hb : (b : F) ≠ 0 := b.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb] <;> ring
  inv_val := by
    have hb : (b : F) ≠ 0 := b.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb] <;> ring

def secS (a : (F)ˣ) (b : F) : G2 where
  val := !![0, -((a : F))⁻¹; (a : F), b]
  inv := !![b, ((a : F))⁻¹; -(a : F), 0]
  val_inv := by
    have ha : (a : F) ≠ 0 := a.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha] <;> ring
  inv_val := by
    have ha : (a : F) ≠ 0 := a.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha] <;> ring

@[scoped simp] theorem secL_coe (a : F) (b : (F)ˣ) :
    ((secL p a b : G2) : Matrix (Fin 2) (Fin 2) F) = !![((b : F))⁻¹, 0; a, (b : F)] := rfl

@[scoped simp] theorem secS_coe (a : (F)ˣ) (b : F) :
    ((secS p a b : G2) : Matrix (Fin 2) (Fin 2) F) = !![0, -((a : F))⁻¹; (a : F), b] := rfl

theorem det_secL (a : F) (b : (F)ˣ) : Matrix.GeneralLinearGroup.det (secL p a b) = 1 := by
  apply Units.ext
  have hb : (b : F) ≠ 0 := b.ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, secL_coe, Matrix.det_fin_two_of, Units.val_one]
  field_simp
  ring

theorem det_secS (a : (F)ˣ) (b : F) : Matrix.GeneralLinearGroup.det (secS p a b) = 1 := by
  apply Units.ext
  have ha : (a : F) ≠ 0 := a.ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, secS_coe, Matrix.det_fin_two_of, Units.val_one]
  field_simp
  ring

def secL' (v : Fin 2 → F) : G2 := if h : v 1 ≠ 0 then secL p (v 0) (Units.mk0 (v 1) h) else 1
def secS' (v : Fin 2 → F) : G2 := if h : v 0 ≠ 0 then secS p (Units.mk0 (v 0) h) (v 1) else 1

theorem secL'_row {v : Fin 2 → F} (h : v 1 ≠ 0) (j : Fin 2) :
    ((secL' p v : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = v j := by
  simp only [secL', dif_pos h, secL_coe]
  fin_cases j <;> simp

theorem secS'_row {v : Fin 2 → F} (h : v 0 ≠ 0) (j : Fin 2) :
    ((secS' p v : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = v j := by
  simp only [secS', dif_pos h, secS_coe]
  fin_cases j <;> simp

theorem det_secL' {v : Fin 2 → F} (h : v 1 ≠ 0) : Matrix.GeneralLinearGroup.det (secL' p v) = 1 := by
  simp only [secL', dif_pos h, det_secL]

theorem det_secS' {v : Fin 2 → F} (h : v 0 ≠ 0) : Matrix.GeneralLinearGroup.det (secS' p v) = 1 := by
  simp only [secS', dif_pos h, det_secS]

theorem continuous_secL_subtype :
    Continuous fun w : {v : Fin 2 → F // v 1 ≠ 0} => (secL p (w.1 0) (Units.mk0 (w.1 1) w.2) : G2) := by
  have h0 : Continuous fun w : {v : Fin 2 → F // v 1 ≠ 0} => w.1 0 := (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun w : {v : Fin 2 → F // v 1 ≠ 0} => w.1 1 := (continuous_apply 1).comp continuous_subtype_val
  have h1i : Continuous fun w : {v : Fin 2 → F // v 1 ≠ 0} => (w.1 1)⁻¹ := h1.inv₀ fun w => w.2
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [secL_coe] <;> first | exact h1i | exact continuous_const | exact h0 | exact h1
  · have : (fun w : {v : Fin 2 → F // v 1 ≠ 0} => (((secL p (w.1 0) (Units.mk0 (w.1 1) w.2) : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F))
        = fun w => !![w.1 1, 0; -(w.1 0), (w.1 1)⁻¹] := by
      funext w; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact h1 | exact continuous_const | exact h0.neg | exact h1i

theorem continuous_secS_subtype :
    Continuous fun w : {v : Fin 2 → F // v 0 ≠ 0} => (secS p (Units.mk0 (w.1 0) w.2) (w.1 1) : G2) := by
  have h0 : Continuous fun w : {v : Fin 2 → F // v 0 ≠ 0} => w.1 0 := (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun w : {v : Fin 2 → F // v 0 ≠ 0} => w.1 1 := (continuous_apply 1).comp continuous_subtype_val
  have h0i : Continuous fun w : {v : Fin 2 → F // v 0 ≠ 0} => (w.1 0)⁻¹ := h0.inv₀ fun w => w.2
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [secS_coe] <;> first | exact continuous_const | exact h0i.neg | exact h0 | exact h1
  · have : (fun w : {v : Fin 2 → F // v 0 ≠ 0} => (((secS p (Units.mk0 (w.1 0) w.2) (w.1 1) : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F))
        = fun w => !![w.1 1, (w.1 0)⁻¹; -(w.1 0), 0] := by
      funext w; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact h1 | exact h0i | exact h0.neg | exact continuous_const

theorem eventually_secL'_eq {φ : G2 → ℂ} (hφ : IsLocallyConstant φ) {v : Fin 2 → F} (hv : v 1 ≠ 0) :
    ∀ᶠ v' in 𝓝 v, φ (secL' p v') = φ (secL' p v) := by
  have hlc : IsLocallyConstant (fun w : {v : Fin 2 → F // v 1 ≠ 0} => φ (secL p (w.1 0) (Units.mk0 (w.1 1) w.2))) :=
    hφ.comp_continuous (continuous_secL_subtype p)
  have hO : IsOpen {w : {v : Fin 2 → F // v 1 ≠ 0} | φ (secL p (w.1 0) (Units.mk0 (w.1 1) w.2)) = φ (secL' p v)} :=
    hlc.isOpen_fiber _
  have hDo : IsOpen {v : Fin 2 → F | v 1 ≠ 0} := isOpen_ne.preimage (continuous_apply 1)
  have hO' : IsOpen ((Subtype.val : {v : Fin 2 → F // v 1 ≠ 0} → (Fin 2 → F)) ''
      {w : {v : Fin 2 → F // v 1 ≠ 0} | φ (secL p (w.1 0) (Units.mk0 (w.1 1) w.2)) = φ (secL' p v)}) :=
    hDo.isOpenMap_subtype_val _ hO
  have hmem : v ∈ (Subtype.val : {v : Fin 2 → F // v 1 ≠ 0} → (Fin 2 → F)) ''
      {w : {v : Fin 2 → F // v 1 ≠ 0} | φ (secL p (w.1 0) (Units.mk0 (w.1 1) w.2)) = φ (secL' p v)} := by
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    show φ (secL p (v 0) (Units.mk0 (v 1) hv)) = φ (secL' p v)
    simp only [secL', dif_pos hv]
  filter_upwards [hO'.mem_nhds hmem] with v' hv'
  obtain ⟨w, hw, rfl⟩ := hv'
  have : secL' p w.1 = secL p (w.1 0) (Units.mk0 (w.1 1) w.2) := by simp only [secL', dif_pos w.2]
  rw [this]; exact hw

theorem eventually_secS'_eq {φ : G2 → ℂ} (hφ : IsLocallyConstant φ) {v : Fin 2 → F} (hv : v 0 ≠ 0) :
    ∀ᶠ v' in 𝓝 v, φ (secS' p v') = φ (secS' p v) := by
  have hlc : IsLocallyConstant (fun w : {v : Fin 2 → F // v 0 ≠ 0} => φ (secS p (Units.mk0 (w.1 0) w.2) (w.1 1))) :=
    hφ.comp_continuous (continuous_secS_subtype p)
  have hO : IsOpen {w : {v : Fin 2 → F // v 0 ≠ 0} | φ (secS p (Units.mk0 (w.1 0) w.2) (w.1 1)) = φ (secS' p v)} :=
    hlc.isOpen_fiber _
  have hDo : IsOpen {v : Fin 2 → F | v 0 ≠ 0} := isOpen_ne.preimage (continuous_apply 0)
  have hO' : IsOpen ((Subtype.val : {v : Fin 2 → F // v 0 ≠ 0} → (Fin 2 → F)) ''
      {w : {v : Fin 2 → F // v 0 ≠ 0} | φ (secS p (Units.mk0 (w.1 0) w.2) (w.1 1)) = φ (secS' p v)}) :=
    hDo.isOpenMap_subtype_val _ hO
  have hmem : v ∈ (Subtype.val : {v : Fin 2 → F // v 0 ≠ 0} → (Fin 2 → F)) ''
      {w : {v : Fin 2 → F // v 0 ≠ 0} | φ (secS p (Units.mk0 (w.1 0) w.2) (w.1 1)) = φ (secS' p v)} := by
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    show φ (secS p (Units.mk0 (v 0) hv) (v 1)) = φ (secS' p v)
    simp only [secS', dif_pos hv]
  filter_upwards [hO'.mem_nhds hmem] with v' hv'
  obtain ⟨w, hw, rfl⟩ := hv'
  have : secS' p w.1 = secS p (Units.mk0 (w.1 0) w.2) (w.1 1) := by simp only [secS', dif_pos w.2]
  rw [this]; exact hw

def S₁ : Set (Fin 2 → F) := {v | Valued.v (v 1) = 1 ∧ Valued.v (v 0) ≤ 1}
def S₂ : Set (Fin 2 → F) := {v | Valued.v (v 0) = 1 ∧ Valued.v (v 1) ≤ WithZero.exp (-1 : ℤ)}

theorem isClopen_sphereF : IsClopen {x : F | Valued.v x = 1} := by
  have h1 := KW47.TSE.isClosed_sphere p 0
  have h2 := KW47.TSE.isOpen_sphere p 0
  rw [WithZero.exp_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem isClopen_ballF (k : ℤ) : IsClopen {x : F | Valued.v x ≤ WithZero.exp k} :=
  ⟨KW47.TSE.isClosed_ball p k, KW47.TSE.isOpen_ball p k⟩

theorem isClopen_S₁ : IsClopen (S₁ p) := by
  have hA : IsClopen ((fun v : Fin 2 → F => v 1) ⁻¹' {x : F | Valued.v x = 1}) :=
    (isClopen_sphereF p).preimage (continuous_apply 1)
  have hB : IsClopen ((fun v : Fin 2 → F => v 0) ⁻¹' {x : F | Valued.v x ≤ WithZero.exp 0}) :=
    (isClopen_ballF p 0).preimage (continuous_apply 0)
  have : S₁ p = ((fun v : Fin 2 → F => v 1) ⁻¹' {x : F | Valued.v x = 1}) ∩
      ((fun v : Fin 2 → F => v 0) ⁻¹' {x : F | Valued.v x ≤ WithZero.exp 0}) := by
    ext v; simp [S₁, WithZero.exp_zero]
  rw [this]; exact hA.inter hB

theorem isClopen_S₂ : IsClopen (S₂ p) := by
  have hA : IsClopen ((fun v : Fin 2 → F => v 0) ⁻¹' {x : F | Valued.v x = 1}) :=
    (isClopen_sphereF p).preimage (continuous_apply 0)
  have hB : IsClopen ((fun v : Fin 2 → F => v 1) ⁻¹' {x : F | Valued.v x ≤ WithZero.exp (-1 : ℤ)}) :=
    (isClopen_ballF p (-1)).preimage (continuous_apply 1)
  have : S₂ p = ((fun v : Fin 2 → F => v 0) ⁻¹' {x : F | Valued.v x = 1}) ∩
      ((fun v : Fin 2 → F => v 1) ⁻¹' {x : F | Valued.v x ≤ WithZero.exp (-1 : ℤ)}) := by
    ext v; simp [S₂]
  rw [this]; exact hA.inter hB

theorem disjoint_S₁_S₂ : Disjoint (S₁ p) (S₂ p) := by
  rw [Set.disjoint_left]
  rintro v ⟨h1, -⟩ ⟨-, h2⟩
  rw [h1] at h2
  exact absurd h2 (not_le.2 (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num))

theorem ne_zero_of_mem_S₁ {v : Fin 2 → F} (hv : v ∈ S₁ p) : v 1 ≠ 0 := by
  intro h; have := hv.1; rw [h, map_zero] at this; exact zero_ne_one this

theorem ne_zero_of_mem_S₂ {v : Fin 2 → F} (hv : v ∈ S₂ p) : v 0 ≠ 0 := by
  intro h; have := hv.1; rw [h, map_zero] at this; exact zero_ne_one this

theorem isLocallyConstant_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) {A : X → ℂ}
    (hA : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, A y = A x) : IsLocallyConstant (S.indicator A) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ S
  · filter_upwards [hS.isOpen.mem_nhds hx, hA x hx] with y hy hAy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hAy]
  · have : ∀ᶠ y in 𝓝 x, y ∉ S := hS.isClosed.isOpen_compl.mem_nhds hx
    filter_upwards [this] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

variable (μ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))

theorem ps_apply_eq_of_row_eq {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) (g g' : G2)
    (hrow : ∀ j : Fin 2, (g' : Matrix (Fin 2) (Fin 2) F) 1 j = (g : Matrix (Fin 2) (Fin 2) F) 1 j) :
    φ g' = ((μ 0 (Matrix.GeneralLinearGroup.det g' * (Matrix.GeneralLinearGroup.det g)⁻¹) : ℂˣ) : ℂ) *
      ((Real.sqrt (‖((Matrix.GeneralLinearGroup.det g' : (F)ˣ) : F)‖ / ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖) : ℝ) : ℂ) *
        φ g := by
  set m : G2 := g' * g⁻¹ with hm
  have hm1 : ∀ j : Fin 2, ((m : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = (1 : Matrix (Fin 2) (Fin 2) F) 1 j := by
    intro j
    have h1 : ((g * g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [mul_inv_cancel]; rfl
    have e1 : ((m : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = ∑ k : Fin 2, (g' : Matrix (Fin 2) (Fin 2) F) 1 k * ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) k j := by
      rw [hm, Units.val_mul, Matrix.mul_apply]
    have e2 : (1 : Matrix (Fin 2) (Fin 2) F) 1 j = ∑ k : Fin 2, (g : Matrix (Fin 2) (Fin 2) F) 1 k * ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) k j := by
      rw [← h1, Units.val_mul, Matrix.mul_apply]
    rw [e1, e2]
    simp only [hrow]
  have hm10 : ((m : G2) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [hm1]; simp
  have hm11 : ((m : G2) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by rw [hm1]; simp
  have hdet : ((Matrix.GeneralLinearGroup.det m : (F)ˣ) : F) = ((m : G2) : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hm10, hm11]; ring
  set α : (F)ˣ := Matrix.GeneralLinearGroup.det m with hα
  have hαeq : α = Matrix.GeneralLinearGroup.det g' * (Matrix.GeneralLinearGroup.det g)⁻¹ := by
    rw [hα, hm, map_mul, map_inv]
  have hfac : m = upperUnipotent2 p (((m : G2) : Matrix (Fin 2) (Fin 2) F) 0 1) * diagonal2 p ![α, 1] := by
    apply Units.ext
    simp only [Units.val_mul, upperUnipotent2_coe, diagonal2_coe', Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hm10, hm11, ← hdet, hα]
  have hg' : g' = m * g := by rw [hm, inv_mul_cancel_right]
  conv_lhs => rw [hg', hfac, mul_assoc, hφ.2.1, hφ.2.2]
  congr 1
  rw [hαeq]
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_one,
    Units.val_one, mul_one, norm_one, div_one, Units.val_mul, Units.val_inv_eq_inv_val,
    norm_mul, norm_inv, div_eq_mul_inv, inv_one, mul_one]

theorem ps_diag_one_left {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) (y : (F)ˣ) (g : G2) :
    φ (diagonal2 p ![1, y] * g) = ((μ 1 y : ℂˣ) : ℂ) * (((Real.sqrt ‖(y : F)‖ : ℝ) : ℂ))⁻¹ * φ g := by
  rw [hφ.2.2]
  congr 1
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_one, Units.val_one, one_mul, norm_one, one_div, Real.sqrt_inv]
  push_cast
  ring

theorem row_diag_one_mul (y : (F)ˣ) (g : G2) (j : Fin 2) :
    ((diagonal2 p ![1, y] * g : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = (y : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Units.val_mul, diagonal2_coe', Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem key_value {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) (g s : G2) (t : (F)ˣ)
    (hs : Matrix.GeneralLinearGroup.det s = 1)
    (hrow : ∀ j : Fin 2, (s : Matrix (Fin 2) (Fin 2) F) 1 j = (t : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 j) :
    φ s * ((μ 0 t : ℂˣ) : ℂ) * (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : F) : ℝ) : ℂ) =
      (((μ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))⁻¹ *
        (((Real.sqrt ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℝ) : ℂ))⁻¹ * φ g := by
  have hdet : Matrix.GeneralLinearGroup.det (diagonal2 p ![1, t]) = t := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagonal2_coe', Matrix.det_fin_two_of]
    simp
  have h1 := ps_apply_eq_of_row_eq p μ hφ (diagonal2 p ![1, t] * g) s (fun j => by rw [hrow, row_diag_one_mul])
  rw [ps_diag_one_left p μ hφ, hs,
    show Matrix.GeneralLinearGroup.det (diagonal2 p ![1, t] * g) = t * Matrix.GeneralLinearGroup.det g by
      rw [map_mul, hdet]] at h1
  rw [h1, coe_modulus_eq_norm]
  have ht : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  have hd : 0 < ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ := norm_pos_iff.2 (Units.ne_zero _)
  simp only [one_mul, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one, norm_one, norm_mul, one_div, mul_inv]
  rw [Real.sqrt_mul (inv_nonneg.2 ht.le), Real.sqrt_inv, Real.sqrt_inv]
  have hst : (Real.sqrt ‖(t : F)‖ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  have hsd : (Real.sqrt ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hd).ne'
  have hμ0 : ((μ 0 t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hμ1 : ((μ 1 t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hsq : (Real.sqrt ‖(t : F)‖ : ℂ) * (Real.sqrt ‖(t : F)‖ : ℂ) = (‖(t : F)‖ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  push_cast
  field_simp
  linear_combination (-(φ g)) * hsq

theorem valued_le_exp_neg_one_of_lt_one {x : F} (hx : Valued.v x < 1) : Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]; exact zero_le'
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
    rw [hm] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]; omega

theorem exists_row_max (g : G2) : ∃ n : ℤ,
    (∀ j : Fin 2, Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 j) ≤ WithZero.exp n) ∧
    ∃ j : Fin 2, Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 j) = WithZero.exp n := by
  set a := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hb
  have hrow : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨ha0, hb0⟩
    have hdet : ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) = 0 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, ← ha, ← hb, ha0, hb0]; ring
    exact (Units.ne_zero _) hdet
  rcases le_total (Valued.v a) (Valued.v b) with hab | hba
  · have hb0 : b ≠ 0 := by
      intro hb0
      apply hrow
      refine ⟨?_, hb0⟩
      rw [hb0, map_zero] at hab
      exact (Valuation.zero_iff _).1 (le_antisymm hab zero_le')
    have hvb : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb0
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v b = WithZero.exp n := ⟨_, (WithZero.exp_log hvb).symm⟩
    refine ⟨n, fun j => ?_, 1, hn⟩
    fin_cases j
    · exact hab.trans hn.le
    · exact hn.le
  · have ha0 : a ≠ 0 := by
      intro ha0
      apply hrow
      refine ⟨ha0, ?_⟩
      rw [ha0, map_zero] at hba
      exact (Valuation.zero_iff _).1 (le_antisymm hba zero_le')
    have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v a = WithZero.exp n := ⟨_, (WithZero.exp_log hva).symm⟩
    refine ⟨n, fun j => ?_, 0, hn⟩
    fin_cases j
    · exact hn.le
    · exact hba.trans hn.le

theorem main {φ : G2 → ℂ} (hφ : φ ∈ principalSeries2 p μ) :
    letI : MeasurableSpace F := localBorel ℚ p
    ∃ Φ₁ : (Fin 2 → F) → ℂ, IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁ ∧
      (∀ v : Fin 2 → F, Φ₁ v ≠ 0 →
        (∀ j : Fin 2, Valued.v (v j) ≤ 1) ∧ ∃ j : Fin 2, Valued.v (v j) = 1) ∧
      ∀ g : G2,
        Integrable (fun t : (F)ˣ => Φ₁ (fun j : Fin 2 => (t : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 j) * ((μ 0 t : ℂˣ) : ℂ) * (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : F) : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        φ g = ((μ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (F)ˣ, Φ₁ (fun j : Fin 2 => (t : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 j) * ((μ 0 t : ℂˣ) : ℂ) * (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : F) : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  classical
  letI instMS : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  set μx : Measure (F)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hμx
  obtain ⟨hmeas, -, hshell, -, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p

  set vol : ℝ := (μx {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-((0 : ℤ)))}).toReal with hvol
  have hvol0 : 0 < vol := by
    rw [hvol]
    exact ENNReal.toReal_pos (hshell 0).2.1.ne' (hshell 0).2.2.ne
  set c : ℂ := ((vol : ℝ) : ℂ)⁻¹ with hc

  set Φ₁ : (Fin 2 → F) → ℂ := fun v =>
    c * ((S₁ p).indicator (fun v => φ (secL' p v)) v + (S₂ p).indicator (fun v => φ (secS' p v)) v) with hΦ₁
  have hΦ₁S₁ : ∀ v ∈ S₁ p, Φ₁ v = c * φ (secL' p v) := by
    intro v hv
    simp only [hΦ₁, Set.indicator_of_mem hv, Set.indicator_of_notMem (Set.disjoint_left.1 (disjoint_S₁_S₂ p) hv), add_zero]
  have hΦ₁S₂ : ∀ v ∈ S₂ p, Φ₁ v = c * φ (secS' p v) := by
    intro v hv
    simp only [hΦ₁, Set.indicator_of_mem hv, Set.indicator_of_notMem (Set.disjoint_right.1 (disjoint_S₁_S₂ p) hv), zero_add]
  have hΦ₁0 : ∀ v, v ∉ S₁ p → v ∉ S₂ p → Φ₁ v = 0 := by
    intro v h1 h2
    simp only [hΦ₁, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero, mul_zero]
  refine ⟨Φ₁, ?_, ?_, ?_, fun g => ?_⟩
  ·
    have h1 : IsLocallyConstant ((S₁ p).indicator (fun v => φ (secL' p v))) :=
      isLocallyConstant_indicator (isClopen_S₁ p) (fun v hv => eventually_secL'_eq p hφ.1 (ne_zero_of_mem_S₁ p hv))
    have h2 : IsLocallyConstant ((S₂ p).indicator (fun v => φ (secS' p v))) :=
      isLocallyConstant_indicator (isClopen_S₂ p) (fun v hv => eventually_secS'_eq p hφ.1 (ne_zero_of_mem_S₂ p hv))
    exact h1.comp₂ h2 (fun a b => c * (a + b))
  ·
    refine HasCompactSupport.intro (isCompact_univ_pi fun _ : Fin 2 => KW47.TSE.isCompact_ball_zero p) ?_
    intro v hv
    rw [Set.mem_univ_pi] at hv
    push Not at hv
    obtain ⟨j, hj⟩ := hv
    have hj' : ¬ Valued.v (v j) ≤ 1 := by simpa [WithZero.exp_zero] using hj
    refine hΦ₁0 v ?_ ?_
    · intro h; fin_cases j; exacts [hj' h.2, hj' h.1.le]
    · intro h; fin_cases j
      · exact hj' h.1.le
      · exact hj' (h.2.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num))
  ·
    intro v hv
    by_cases h1 : v ∈ S₁ p
    · refine ⟨fun j => ?_, 1, h1.1⟩
      fin_cases j; exacts [h1.2, h1.1.le]
    by_cases h2 : v ∈ S₂ p
    · refine ⟨fun j => ?_, 0, h2.1⟩
      fin_cases j
      · exact h2.1.le
      · exact h2.2.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    exact absurd (hΦ₁0 v h1 h2) hv

  obtain ⟨n, hle, j₀, hj₀⟩ := exists_row_max p g
  set T : Set (F)ˣ := {t : (F)ˣ | Valued.v (t : F) = WithZero.exp (-(n))} with hT
  set Kc : ℂ := c * ((((μ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))⁻¹ *
    (((Real.sqrt ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℝ) : ℂ))⁻¹ * φ g) with hKc

  have hfun : (fun t : (F)ˣ => Φ₁ (fun j : Fin 2 => (t : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 j) * ((μ 0 t : ℂˣ) : ℂ) *
      (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : F) : ℝ) : ℂ)) = T.indicator (fun _ => Kc) := by
    funext t
    set w : Fin 2 → F := fun j : Fin 2 => (t : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 j with hw
    have hvt0 : Valued.v (t : F) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (t : F) = WithZero.exp m := ⟨_, (WithZero.exp_log hvt0).symm⟩
    have hwj : ∀ j : Fin 2, Valued.v (w j) = WithZero.exp m * Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 j) := by
      intro j; simp only [hw, map_mul, hm]
    by_cases ht : t ∈ T
    ·
      have hmn : m = -n := by
        have : Valued.v (t : F) = WithZero.exp (-n) := ht
        rw [hm] at this; exact WithZero.exp_injective this
      have hwle : ∀ j : Fin 2, Valued.v (w j) ≤ 1 := by
        intro j
        rw [hwj, hmn]
        calc WithZero.exp (-n) * Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 j)
            ≤ WithZero.exp (-n) * WithZero.exp n := mul_le_mul_right (hle j) _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      have hwj₀ : Valued.v (w j₀) = 1 := by
        rw [hwj, hmn, hj₀, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      rw [Set.indicator_of_mem ht]
      by_cases h1 : Valued.v (w 1) = 1
      · have hS : w ∈ S₁ p := ⟨h1, hwle 0⟩
        have hne : w 1 ≠ 0 := ne_zero_of_mem_S₁ p hS
        rw [hΦ₁S₁ w hS, hKc]
        have := key_value p μ hφ g (secL' p w) t (det_secL' p hne) (fun j => by rw [secL'_row p hne])
        linear_combination c * this
      · have h1' : Valued.v (w 1) ≤ WithZero.exp (-1 : ℤ) :=
          valued_le_exp_neg_one_of_lt_one p (lt_of_le_of_ne (hwle 1) h1)
        have h0 : Valued.v (w 0) = 1 := by
          fin_cases j₀
          · exact hwj₀
          · exact absurd hwj₀ h1
        have hS : w ∈ S₂ p := ⟨h0, h1'⟩
        have hne : w 0 ≠ 0 := ne_zero_of_mem_S₂ p hS
        rw [hΦ₁S₂ w hS, hKc]
        have := key_value p μ hφ g (secS' p w) t (det_secS' p hne) (fun j => by rw [secS'_row p hne])
        linear_combination c * this
    ·
      rw [Set.indicator_of_notMem ht]
      have hnot : ¬ ((∀ j : Fin 2, Valued.v (w j) ≤ 1) ∧ ∃ j : Fin 2, Valued.v (w j) = 1) := by
        rintro ⟨hall, j, hj⟩
        apply ht
        show Valued.v (t : F) = WithZero.exp (-n)
        rw [hm, WithZero.exp_inj]

        have h1 : WithZero.exp m * WithZero.exp n ≤ 1 := by rw [← hj₀, ← hwj]; exact hall j₀
        have hvj0 : Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 j) ≠ 0 := by
          intro h0; rw [hwj, h0, mul_zero] at hj; exact zero_ne_one hj
        obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 j) = WithZero.exp k :=
          ⟨_, (WithZero.exp_log hvj0).symm⟩
        have h2 : WithZero.exp m * WithZero.exp k = 1 := by rw [← hk, ← hwj]; exact hj
        have h3 : WithZero.exp k ≤ WithZero.exp n := by rw [← hk]; exact hle j
        rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
        rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h2
        rw [WithZero.exp_le_exp] at h3
        omega
      have hS1 : w ∉ S₁ p := fun h => hnot ⟨fun j => by fin_cases j; exacts [h.2, h.1.le], 1, h.1⟩
      have hS2 : w ∉ S₂ p := fun h => hnot ⟨fun j => by
        fin_cases j
        · exact h.1.le
        · exact h.2.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num), 0, h.1⟩
      rw [hΦ₁0 w hS1 hS2]
      simp
  have hTm : MeasurableSet T := hmeas n
  have hTfin : μx T < ⊤ := (hshell n).2.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (integrable_indicator_iff hTm).2 (integrableOn_const (hs := hTfin.ne))
  · rw [hfun, integral_indicator_const Kc hTm]
    have hTvol : (μx T).toReal = vol := by rw [hvol, (hshell n).1]
    rw [Measure.real, hTvol, hKc, Complex.real_smul]
    have hvolc : ((vol : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvol0.ne'
    have hd : 0 < ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have hsd : (Real.sqrt ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hd).ne'
    have hμ0 : ((μ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hmod : ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
        (Real.sqrt ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℂ) := by
      rw [coe_modulus_eq_norm, Real.sqrt_eq_rpow, Complex.ofReal_cpow (norm_nonneg _)]
      norm_num
    rw [hmod, hc]
    field_simp

theorem solution'
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ) : True := trivial

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47.TSE"
end SIGQ
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47.TSE P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.SIGQ"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.KW47.TSE P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.SIGQ"

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
open NumberField.AdelicLevel (diagOne)

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ) :
    letI := localBorel ℚ p
    ∃ Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁ ∧
      (∀ v : Fin 2 → p.adicCompletion ℚ, Φ₁ v ≠ 0 →
        (∀ j : Fin 2, Valued.v (v j) ≤ 1) ∧ ∃ j : Fin 2, Valued.v (v j) = 1) ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        Integrable (fun t : (p.adicCompletion ℚ)ˣ => Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μ 0 t : ℂˣ) : ℂ) * (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        φ g = ((μ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μ 0 t : ℂˣ) : ℂ) * (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  exact SIGQ.main p μ hφ

end S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2 (solution)
