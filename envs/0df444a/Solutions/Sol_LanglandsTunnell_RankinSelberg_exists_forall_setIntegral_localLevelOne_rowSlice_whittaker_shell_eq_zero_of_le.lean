-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/12959662-4327-52d9-9ba3-1d60d541cb98

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
import Theorems.Thm_LanglandsTunnell_RankinSelberg_apply_scalar_mul_eq_mul_of_mem_span_translate
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical
open scoped NNReal ENNReal Topology

noncomputable section

namespace SVDGlue

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem diagZ_mul_diagUnitGL2 (x : F) (hx : x ≠ 0) (n : ℤ) (u : Fˣ) :
    diagZ x hx n * diagUnitGL2 u = diagUnitGL2 ((Units.mk0 x hx) ^ n * u) := by
  apply Units.ext
  change (!![x ^ n, 0; 0, 1] : M2) * !![(u : F), 0; 0, 1] = !![(((Units.mk0 x hx) ^ n * u : Fˣ) : F), 0; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_zpow_eq_zpow_val]

theorem scalarPi_eq_scalar (x : F) (hx : x ≠ 0) :
    scalarPi x hx = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 x hx) := by
  apply Units.ext
  change (!![x, 0; 0, x] : M2) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar]

theorem det_diagUnitGL2 (u : Fˣ) : Matrix.GeneralLinearGroup.det (diagUnitGL2 u : G₂) = u := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnitGL2, Matrix.det_fin_two_of]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

theorem measurableSet_units : MeasurableSet {u : Fˣ | Valued.v (u : F) = 1} := by
  haveI : BorelSpace Fˣ := borelSpace_units
  have hopen : IsOpen {x : F | Valued.v x = 1} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : Valued.v x = 1 := hx
    have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx']; exact one_ne_zero)
    exact (eventually_valued_eq p hx0).mono fun y hy => by
      show Valued.v y = 1
      rw [hy, hx']
  have : {u : Fˣ | Valued.v (u : F) = 1} = Units.val ⁻¹' {x : F | Valued.v x = 1} := rfl
  rw [this]
  exact (hopen.preimage Units.continuous_val).measurableSet

theorem modulus_eq_one_of_valued (u : F) (hu : Valued.v u = 1) : modulus u = 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p u]
  ext
  rw [coe_nnnorm, NumberField.FinitePlace.norm_def, hu, map_one]

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem continuous_val_det : Continuous fun h : G₂ => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.continuous_val.matrix_det

theorem continuous_det : Continuous fun h : G₂ => (Matrix.GeneralLinearGroup.det h : Fˣ) := by
  refine Units.continuous_iff.mpr ⟨continuous_val_det p, ?_⟩
  have : (fun h : G₂ => (((Matrix.GeneralLinearGroup.det h)⁻¹ : Fˣ) : F)) = fun h => (((h⁻¹ : G₂) : M2)).det := by
    funext h
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Units.continuous_coe_inv.matrix_det

theorem isLocallyConstant_chi_det (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    IsLocallyConstant fun g : G₂ => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
  (hχ.comp_continuous (continuous_det p)).comp Units.val

theorem isLocallyConstant_modulus_det :
    IsLocallyConstant fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) := by
  have h : IsLocallyConstant fun g : G₂ => ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro h₀
    exact ((continuous_val_det p).tendsto h₀).eventually
      (eventually_norm_eq p (Matrix.GeneralLinearGroup.det h₀).ne_zero)
  have heq : (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ))
      = fun g => (((‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ : ℝ) : ℂ)) := by
    funext g
    rw [coe_modulus_eq_norm]
  rw [heq]
  exact h.comp (fun r : ℝ => ((r : ℝ) : ℂ))

theorem isLocallyConstant_of_rightSmooth {X : Type*} (A : G₂ → X)
    (hA : ∃ U : Subgroup G₂, IsOpen (U : Set G₂) ∧ ∀ k ∈ U, ∀ g : G₂, A (g * k) = A g) :
    IsLocallyConstant A := by
  obtain ⟨U, hUo, hU⟩ := hA
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hopen : IsOpen ((fun u => g * u) '' (U : Set G₂)) := isOpenMap_mul_left g _ hUo
  have hmem : g ∈ (fun u => g * u) '' (U : Set G₂) := ⟨1, U.one_mem, mul_one g⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact hU u hu g

theorem smooth_of_mem_span {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (W₀ : G → ℂ) (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G))
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

end SVDGlue

open SVDGlue in

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

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (htorus : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ),
        ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∃ nstar c : ℤ, ∀ (n₁ n₂ : ℤ), nstar ≤ n₁ → c ≤ n₁ + n₂ → ∀ s : ℂ,
            ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
              (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
                ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k)) : ℂˣ) : ℂ) *
                w (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k) *
                ((modulus ((Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s ∂μ₂ = 0 := by
  letI := localBorel ℚ p
  haveI := borelSpace_localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _ w hw Φ hΦ hΦc

  obtain ⟨-, ⟨U, hUo, hBU⟩, c, M, C, hprof⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport p hπ hϖ Φ hΦ hΦc
  obtain ⟨nstar, hb⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ χ hχ htorus hπ hϖ w hw
  have hcw := LanglandsTunnell.RankinSelberg.apply_scalar_mul_eq_mul_of_mem_span_translate p θ₀ w₂base hcentral w hw
  obtain ⟨-, hKNo⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  obtain ⟨Uw, hUwo, hUw⟩ := smooth_of_mem_span w₂base _ hKNo hw₂K w hw
  refine ⟨nstar, c, fun n₁ n₂ hn₁ hn₁₂ s => ?_⟩

  set π : p.adicCompletion ℚ := algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ with hπdef
  set ϖ₁ : (p.adicCompletion ℚ)ˣ := Units.mk0 π hπ with hϖ₁
  set a : GL (Fin 2) (p.adicCompletion ℚ) := scalarPi π hπ ^ n₂ * diagZ π hπ n₁ with ha
  set Fk : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun k =>
    (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
        Φ ((unipotent x * (a * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
        ∂(selfDualHaarAt ℚ p)) *
      ((χ (Matrix.GeneralLinearGroup.det (a * k)) : ℂˣ) : ℂ) *
      w (a * k) *
      ((modulus ((Matrix.GeneralLinearGroup.det (a * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
    with hF
  show ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fk k ∂μ₂ = 0

  have hFlc : IsLocallyConstant Fk := by
    have h1 : IsLocallyConstant fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
        ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          Φ ((unipotent x * (a * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
          ∂(selfDualHaarAt ℚ p) :=
      (isLocallyConstant_of_rightSmooth p
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
          ∂(selfDualHaarAt ℚ p)) ⟨U, hUo, hBU⟩).comp_continuous (continuous_const_mul a)
    have h2 : IsLocallyConstant fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((χ (Matrix.GeneralLinearGroup.det (a * k)) : ℂˣ) : ℂ) :=
      (isLocallyConstant_chi_det p χ hχ).comp_continuous (continuous_const_mul a)
    have h3 : IsLocallyConstant fun k : GL (Fin 2) (p.adicCompletion ℚ) => w (a * k) :=
      (isLocallyConstant_of_rightSmooth p w ⟨Uw, hUwo, hUw⟩).comp_continuous (continuous_const_mul a)
    have h4 : IsLocallyConstant fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((modulus ((Matrix.GeneralLinearGroup.det (a * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s :=
      ((isLocallyConstant_modulus_det p).comp_continuous (continuous_const_mul a)).comp (fun z : ℂ => z ^ s)
    exact ((h1.comp₂ h2 (· * ·)).comp₂ h3 (· * ·)).comp₂ h4 (· * ·)

  obtain ⟨hν0, hνtop, -, -, hid⟩ :=
    LanglandsTunnell.RankinSelberg.setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant
      p μ₂ Fk hFlc

  have hinner : ∀ k ∈ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
      (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}, Fk (diagUnitGL2 u * k)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 := by
    intro k hk

    set Cst : ℂ :=
      (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          Φ ((unipotent x * (scalarPi π hπ ^ n₂ * diagZ π hπ (c - n₂) * k) : GL (Fin 2) (p.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
        ((χ (Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂) * ϖ₁ ^ n₁ * Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        ((θ₀ (ϖ₁ ^ n₂) : ℂˣ) : ℂ) *
        ((modulus (((Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂) * ϖ₁ ^ n₁ * Matrix.GeneralLinearGroup.det k :
            (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s with hCst
    have hptw : Set.EqOn (fun u : (p.adicCompletion ℚ)ˣ => Fk (diagUnitGL2 u * k))
        (fun u => Cst * (((χ u : ℂˣ) : ℂ) * w (diagUnitGL2 (ϖ₁ ^ n₁ * u) * k)))
        {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
      intro u hu
      have hu1 : Valued.v (u : p.adicCompletion ℚ) = 1 := hu
      have hX : a * (diagUnitGL2 u * k) = scalarPi π hπ ^ n₂ * diagUnitGL2 (ϖ₁ ^ n₁ * u) * k := by
        rw [ha, hϖ₁, ← diagZ_mul_diagUnitGL2 p π hπ n₁ u]
        simp only [mul_assoc]
      have hB := (hprof k hk n₁ n₂ u hu1).2.2.2.1 hn₁₂
      have hdet : Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂ * diagUnitGL2 (ϖ₁ ^ n₁ * u) * k)
          = Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂) * ϖ₁ ^ n₁ * Matrix.GeneralLinearGroup.det k * u := by
        rw [map_mul, map_mul, det_diagUnitGL2, ← mul_assoc, mul_right_comm _ u]
      have hw' : w (scalarPi π hπ ^ n₂ * diagUnitGL2 (ϖ₁ ^ n₁ * u) * k)
          = ((θ₀ (ϖ₁ ^ n₂) : ℂˣ) : ℂ) * w (diagUnitGL2 (ϖ₁ ^ n₁ * u) * k) := by
        rw [scalarPi_eq_scalar p π hπ, ← hϖ₁, ← map_zpow, mul_assoc, hcw]
      have hM : modulus ((Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂ * diagUnitGL2 (ϖ₁ ^ n₁ * u) * k) :
            (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)
          = modulus ((Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂) * ϖ₁ ^ n₁ * Matrix.GeneralLinearGroup.det k :
            (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) := by
        rw [hdet, Units.val_mul, modulus_mul, modulus_eq_one_of_valued p _ hu1, mul_one]
      have hχ' : ((χ (Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂ * diagUnitGL2 (ϖ₁ ^ n₁ * u) * k)) : ℂˣ) : ℂ)
          = ((χ (Matrix.GeneralLinearGroup.det (scalarPi π hπ ^ n₂) * ϖ₁ ^ n₁ * Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
            * ((χ u : ℂˣ) : ℂ) := by
        rw [hdet, map_mul, Units.val_mul]
      show Fk (diagUnitGL2 u * k) = Cst * (((χ u : ℂˣ) : ℂ) * w (diagUnitGL2 (ϖ₁ ^ n₁ * u) * k))
      simp only [hF]
      rw [hX, hB, hχ', hw', hM, hCst]
      ring
    rw [setIntegral_congr_fun (measurableSet_units p) hptw, integral_const_mul, hb k hk n₁ hn₁, mul_zero]
  have hvol : (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
      {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro h0
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
    · exact hν0 h
    · exact hνtop h
  exact (mul_eq_zero.mp (hid.trans (setIntegral_eq_zero_of_forall_eq_zero hinner))).resolve_left hvol

end
end S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le (solution)
