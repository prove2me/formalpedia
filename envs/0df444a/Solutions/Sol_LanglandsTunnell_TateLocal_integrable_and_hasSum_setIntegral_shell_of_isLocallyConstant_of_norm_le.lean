-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b58eec3f-b271-5f45-b73e-6bee9a427a12

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell.TateLocal Topology"
open scoped NNReal ENNReal

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "modulus mulMeasure isHaarMeasure_comap_val_mulMeasure modulus_adicCompletion_eq_nnnorm"
namespace ShellCalculus
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

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
      = {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp k} \ {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp (k - 1)} := by
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

theorem coe_integers_eq : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
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

def shell (n : ℤ) : Set (v.adicCompletion K)ˣ := {y : (v.adicCompletion K)ˣ | Valued.v (y : (v.adicCompletion K)) = WithZero.exp (-n)}

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
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
  exact ⟨-m, by rw [hm, neg_neg]⟩

theorem preimage_shell (n : ℤ) :
    (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) ⁻¹' shell v n = USet v := by
  ext u
  simp only [Set.mem_preimage, shell, USet, Set.mem_setOf_eq, Units.val_mul, map_mul,
    valued_uniformizerUnit_zpow]
  constructor
  · intro h
    have hne : (WithZero.exp (-n) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
    calc Valued.v (u : (v.adicCompletion K)) = (WithZero.exp (-n))⁻¹ * (WithZero.exp (-n) * Valued.v (u : (v.adicCompletion K))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = 1 := by rw [h, inv_mul_cancel₀ hne]
  · intro h
    rw [h, mul_one]

theorem modulus_shell {n : ℤ} {y : (v.adicCompletion K)ˣ} (hy : y ∈ shell v n) :
    modulus (y : (v.adicCompletion K)) = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
  modulus_of_valued v hy

theorem modulus_uniformizer_zpow_mul {n : ℤ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    modulus ((uniformizerUnit K v ^ n * u : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) := by
  refine modulus_shell v (n := n) ?_
  have := preimage_shell v n
  rw [Set.ext_iff] at this
  exact (this u).mpr hu

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
    ∫ y in shell v n, f y ∂(mulHaar v μ) = ∫ u in USet v, f (uniformizerUnit K v ^ n * u) ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) :=
    (MeasurableEquiv.mulLeft (uniformizerUnit K v ^ n)).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_shell]

theorem integrableOn_shell_iff {E : Type*} [NormedAddCommGroup E] (n : ℤ) (f : (v.adicCompletion K)ˣ → E) :
    IntegrableOn f (shell v n) (mulHaar v μ) ↔
      IntegrableOn (fun u => f (uniformizerUnit K v ^ n * u)) (USet v) (mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) (mulHaar v μ) (mulHaar v μ) :=
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

end LanglandsTunnell.TateLocal.ShellCalculus
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell.TateLocal.ShellCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell.TateLocal"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell.TateLocal.ShellCalculus"

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.LanglandsTunnell.TateLocal LanglandsTunnell.TateLocal.ShellCalculus in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (φ : (v.adicCompletion K)ˣ → ℂ) (hφ : IsLocallyConstant φ)
    (C : ℝ) (M : ℕ)
    (hC : ∀ y : (v.adicCompletion K)ˣ, ‖φ y‖ ≤ C * max 1 ((modulus (y : v.adicCompletion K)) ^ M)⁻¹)
    (c₀ : ℝ) (hc₀ : ∀ y : (v.adicCompletion K)ˣ, c₀ < modulus (y : v.adicCompletion K) → φ y = 0)
    (ν : (v.adicCompletion K)ˣ →* ℂˣ) (hν : IsLocallyConstant fun y : (v.adicCompletion K)ˣ => ((ν y : ℂˣ) : ℂ))
    (B : ℝ) (hB : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → ‖((ν u : ℂˣ) : ℂ)‖ ≤ B)
    (hνϖ : ‖((ν (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (z : ℂ) (hz : (M : ℝ) < z.re) :
    Integrable (fun y : (v.adicCompletion K)ˣ =>
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z)
      (Measure.comap Units.val (mulMeasure μ)) ∧
    (∀ n : ℤ, IntegrableOn
      (fun u : (v.adicCompletion K)ˣ => φ (uniformizerUnit K v ^ n * u) * ((ν u : ℂˣ) : ℂ))
      {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1}
      (Measure.comap Units.val (mulMeasure μ))) ∧
    HasSum (fun n : ℤ =>
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) * ((ν (uniformizerUnit K v) : ℂˣ) : ℂ) ^ n *
          ∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
            φ (uniformizerUnit K v ^ n * u) * ((ν u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure μ)))
      (∫ y, φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z
        ∂(Measure.comap Units.val (mulMeasure μ))) := by

  set ϖ : (v.adicCompletion K)ˣ := uniformizerUnit K v with hϖ
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hN
  set μx : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (mulMeasure μ) with hμx
  have hμx' : μx = mulHaar v μ := rfl
  set f : (v.adicCompletion K)ˣ → ℂ := fun y =>
    φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z with hf
  set g : ℤ → (v.adicCompletion K)ˣ → ℂ := fun n u => φ (ϖ ^ n * u) * ((ν u : ℂˣ) : ℂ) with hg
  have hNpos : 0 < N := absNorm_pos v
  have hN1 : 1 < N := one_lt_absNorm v
  have hNC0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by rw [← hN]; exact hNpos.ne'
    exact_mod_cast h0
  set σ : ℝ := z.re with hσ

  set cst : ℤ → ℂ := fun n => (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) * ((ν ϖ : ℂˣ) : ℂ) ^ n
    with hcst
  have hnorm_cst : ∀ n : ℤ, ‖cst n‖ = N ^ (-(n : ℝ) * σ) := by
    intro n
    rw [hcst]
    simp only
    rw [norm_mul, norm_zpow, hνϖ, one_zpow, mul_one,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))]
    congr 1
    simp [hσ]

  have hmodC : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v →
      ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ) : ℂ) ^ z
        = (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) := by
    intro n u hu
    have hm := modulus_uniformizer_zpow_mul v (n := n) hu
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
  have hfg : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v → f (ϖ ^ n * u) = cst n * g n u := by
    intro n u hu
    simp only [hf, hg, hcst]
    rw [hmodC n u hu, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
    ring

  have hg_meas : ∀ n : ℤ, Measurable (g n) := by
    intro n
    have h1 : IsLocallyConstant fun u : (v.adicCompletion K)ˣ => φ (ϖ ^ n * u) :=
      hφ.comp_continuous (continuous_mul_left (ϖ ^ n))
    exact (h1.continuous.mul hν.continuous).measurable

  set B' : ℝ := max B 0 with hB'
  set C' : ℝ := max C 0 with hC'
  set R : ℤ → ℝ := fun n => C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) * B' with hR
  have hR_nonneg : ∀ n, 0 ≤ R n := fun n =>
    mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _)) (le_max_right _ _)
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
      have hz' : (((-(-n * (M : ℤ))) : ℤ) : ℝ) = (M : ℝ) * (n : ℝ) := by push_cast; ring
      rw [hz']
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast le_max_left n 0) (Nat.cast_nonneg M)
  have hg_bound : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v → ‖g n u‖ ≤ R n := by
    intro n u hu
    simp only [hg, hR]
    rw [norm_mul]
    have h1 : ‖φ (ϖ ^ n * u)‖ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := by
      refine (hC _).trans ?_
      have hm := hmax_le n u hu
      have hmn : (0 : ℝ) ≤ ((max 1 ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ^ M)⁻¹
          : NNReal) : ℝ) := NNReal.coe_nonneg _
      calc C * _ ≤ C' * _ := mul_le_mul_of_nonneg_right (le_max_left C 0) hmn
        _ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := mul_le_mul_of_nonneg_left hm (le_max_right _ _)
    have h2 : ‖((ν u : ℂˣ) : ℂ)‖ ≤ B' := (hB u hu).trans (le_max_left _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _))

  have hg_int : ∀ n : ℤ, IntegrableOn (g n) (USet v) μx := fun n =>
    integrableOn_USet_of_bound v μ (g n) (hg_meas n) (R n) (hg_bound n)

  have hf_shell : ∀ n : ℤ, IntegrableOn f (shell v n) μx := by
    intro n
    rw [hμx', integrableOn_shell_iff v μ n f]
    refine IntegrableOn.congr_fun (f := fun u => cst n * g n u) ?_ ?_ (measurableSet_USet v)
    · exact (hg_int n).const_mul (cst n)
    · intro u hu
      exact (hfg n u hu).symm

  set V : ℝ := μx.real (USet v) with hV
  have hV_nonneg : 0 ≤ V := measureReal_nonneg
  have hnorm_shell : ∀ n : ℤ, ∫ y in shell v n, ‖f y‖ ∂μx ≤ N ^ (-(n : ℝ) * σ) * (R n * V) := by
    intro n
    have h1 : ∫ y in shell v n, ‖f y‖ ∂μx = ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx := by
      rw [hμx']
      exact setIntegral_shell_eq v μ n (fun y => ‖f y‖)
    rw [h1]
    have h2 : ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx ≤ ∫ u in USet v, N ^ (-(n : ℝ) * σ) * R n ∂μx := by
      refine setIntegral_mono_on ?_ ?_ (measurableSet_USet v) ?_
      · have := ((integrableOn_shell_iff v μ n f).mp (hf_shell n)).norm
        exact this
      · exact integrableOn_const ((mulHaar_USet_lt_top v μ).ne)
      · intro u hu
        rw [hfg n u hu, norm_mul, hnorm_cst n]
        exact mul_le_mul_of_nonneg_left (hg_bound n u hu) (Real.rpow_nonneg hNpos.le _)
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
      show (c₀ : ℝ) < (modulus (y : v.adicCompletion K) : ℝ)
      rw [hm, zpow_add_one₀ hNpos.ne', zpow_natCast]
      have hk' : c₀ ≤ (k : ℝ) := (Nat.le_ceil c₀).trans (by exact_mod_cast hk)
      have hN2 : (2 : ℝ) ≤ N := two_le_absNorm v
      have hpow : (k : ℝ) + 1 ≤ N ^ k := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ N - 1 by linarith) k
        rw [show (1 : ℝ) + (N - 1) = N by ring] at this
        nlinarith [this, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      nlinarith [hpow, pow_pos hNpos k]
    show ‖f y‖ = 0
    rw [hf]
    simp only
    rw [hc₀ y hbig, zero_mul, zero_mul, norm_zero]

  have hsumm : Summable fun n : ℤ => ∫ y in shell v n, ‖f y‖ ∂μx := by
    have hnn : ∀ n : ℤ, 0 ≤ ∫ y in shell v n, ‖f y‖ ∂μx := fun n => integral_nonneg fun _ => norm_nonneg _
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    ·
      set r : ℝ := N ^ ((M : ℝ) - σ) with hr
      have hr0 : 0 ≤ r := Real.rpow_nonneg hNpos.le _
      have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by rw [hσ] at hz; linarith)
      refine Summable.of_nonneg_of_le (fun n => hnn n) (fun n => ?_) ((summable_geometric_of_lt_one hr0 hr1).mul_left
        (C' * B' * V))
      refine (hnorm_shell n).trans (le_of_eq ?_)
      simp only [hR]
      rw [show ((max (n : ℤ) 0 : ℤ) : ℝ) = n by simp, hr, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      rw [show N ^ (-((n : ℤ) : ℝ) * σ) * (C' * N ^ ((M : ℝ) * n) * B' * V)
          = C' * B' * V * (N ^ (-((n : ℤ) : ℝ) * σ) * N ^ ((M : ℝ) * n)) by ring,
        ← Real.rpow_add hNpos]
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
  refine ⟨hint, fun n => hg_int n, ?_⟩

  have hsum := hasSum_integral_iUnion (measurableSet_shell v) (pairwise_disjoint_shell v)
    (by rw [iUnion_shell]; exact hint.integrableOn)
  rw [iUnion_shell, Measure.restrict_univ] at hsum
  refine hsum.congr_fun ?_
  intro n
  show cst n * ∫ u in USet v, g n u ∂μx = ∫ y in shell v n, f y ∂μx
  rw [hμx', setIntegral_shell_eq v μ n f, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_USet v) fun u hu => ?_
  exact (hfg n u hu).symm

end S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le (solution)
