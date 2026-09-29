-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a13c64f7-5eb9-527e-a1c5-ac11176285ce

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

import Theorems.Thm_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace SVDb

variable (p : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem diagUnitGL2_eq_diagOne (x : (p.adicCompletion ℚ)ˣ) :
    (diagUnitGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) = diagOne x := by
  refine Units.ext ?_
  show !![(x : p.adicCompletion ℚ), 0; 0, 1] = Matrix.diagonal ![(x : p.adicCompletion ℚ), 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem diagOne_mul_unipotent (y : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    (diagOne y : GL (Fin 2) (p.adicCompletion ℚ)) * unipotent x = unipotent ((y : p.adicCompletion ℚ) * x) * diagOne y := by
  refine Units.ext ?_
  simp only [Units.val_mul]
  show Matrix.diagonal ![(y : p.adicCompletion ℚ), 1] * !![1, x; 0, 1] =
    !![1, (y : p.adicCompletion ℚ) * x; 0, 1] * Matrix.diagonal ![(y : p.adicCompletion ℚ), 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem continuous_unipotent : Continuous (fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ))) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : p.adicCompletion ℚ => (!![(1 : p.adicCompletion ℚ), x; 0, 1] : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ x : p.adicCompletion ℚ, (((unipotent x : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, -x; 0, 1] := by
      intro x
      have hinv : (unipotent x : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ = unipotent (-x) := by
        refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
        simp only [Units.val_mul, Units.val_one]
        show !![(1 : p.adicCompletion ℚ), x; 0, 1] * !![1, -x; 0, 1] = 1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [hinv]; rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem isLocallyConstant_of_stab (v : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ u ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), v (g * u) = v g) : IsLocallyConstant v := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have ho : IsOpen {g' : GL (Fin 2) (p.adicCompletion ℚ) | g⁻¹ * g' ∈ U} := hUo.preimage (continuous_const.mul continuous_id)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ U by rw [inv_mul_cancel]; exact U.one_mem)] with g' hg'
  rw [show g' = g * (g⁻¹ * g') by rw [mul_inv_cancel_left], hU _ hg']

theorem exists_forall_apply_diagOne_eq_zero (v : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hvlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      v (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * v g)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ u ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), v (g * u) = v g) :
    ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : p.adicCompletion ℚ)‖ → v (diagOne y) = 0 := by

  have h0 : {x : p.adicCompletion ℚ | (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U} ∈ nhds (0 : p.adicCompletion ℚ) := by
    refine (hUo.preimage (continuous_unipotent p)).mem_nhds ?_
    show (unipotent (0 : p.adicCompletion ℚ) : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U
    have : (unipotent (0 : p.adicCompletion ℚ) : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
      refine Units.ext ?_
      show !![(1 : p.adicCompletion ℚ), 0; 0, 1] = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [this]; exact U.one_mem
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h0

  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  refine ⟨‖t‖ / δ, fun y hy => ?_⟩
  have hy0 : 0 < ‖(y : p.adicCompletion ℚ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  set x : p.adicCompletion ℚ := (y : p.adicCompletion ℚ)⁻¹ * t with hx
  have hxU : (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, hx, norm_mul, norm_inv]
    rw [div_lt_iff₀ hδ] at hy
    rw [inv_mul_lt_iff₀ hy0]
    linarith [mul_comm δ ‖(y : p.adicCompletion ℚ)‖]
  have h1 := hU _ hxU (diagOne y)
  rw [diagOne_mul_unipotent, hvlaw] at h1
  have hyx : (y : p.adicCompletion ℚ) * x = t := by rw [hx, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  rw [hyx] at h1

  have : (NumberField.StandardAddChar.psiLocal ℚ p t - 1) * v (diagOne y) = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) ht
  · exact h

theorem translate_mem_span (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    {w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ}
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)))
    (k : GL (Fin 2) (p.adicCompletion ℚ)) :
    (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * k)) ∈
      Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine Submodule.subset_span ⟨k * h, ?_⟩
    funext g
    simp only [mul_assoc]
  | zero =>
    have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (g * k)) = 0 := by
      funext g; rfl
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (x + y) (g * k)) =
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => x (g * k)) + (fun g => y (g * k)) := by
      funext g; rfl
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (a • x) (g * k)) =
        a • (fun g : GL (Fin 2) (p.adicCompletion ℚ) => x (g * k)) := by
      funext g; rfl
    rw [this]; exact Submodule.smul_mem _ a hx

theorem whittaker_law_of_mem_span (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    {w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ}
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) :
    ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro x g
    simp only [mul_assoc, hw₂law]
  | zero => intro x g; simp
  | add u v _ _ hu hv => intro x g; simp only [Pi.add_apply, hu, hv]; ring
  | smul a u _ hu => intro x g; simp only [Pi.smul_apply, smul_eq_mul, hu]; ring

theorem exists_stab_of_mem_span (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    {w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ}
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) :
    ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ u ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * u) = w g := by
  have hKo := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx

    refine ⟨(AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N).map (MulAut.conj h).toMonoidHom, ?_, ?_⟩
    · show IsOpen ((MulAut.conj h).toMonoidHom '' (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))))
      have : ((MulAut.conj h).toMonoidHom '' (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ)))) =
          (Homeomorph.mulLeft h |>.trans (Homeomorph.mulRight h⁻¹)) '' (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set _) := by
        ext g
        simp [MulAut.conj_apply, Homeomorph.mulLeft, Homeomorph.mulRight]
      rw [this]
      exact (Homeomorph.isOpenMap _) _ hKo
    · rintro u ⟨k, hk, rfl⟩ g
      show w₂base (g * ((MulAut.conj h) k) * h) = w₂base (g * h)
      rw [MulAut.conj_apply, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc, hw₂K k hk]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add u v _ _ hu hv =>
    obtain ⟨U₁, hU₁, h₁⟩ := hu
    obtain ⟨U₂, hU₂, h₂⟩ := hv
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply, h₁ k hk.1, h₂ k hk.2]
  | smul a u _ hu =>
    obtain ⟨U₁, hU₁, h₁⟩ := hu
    exact ⟨U₁, hU₁, fun k hk g => by simp only [Pi.smul_apply, h₁ k hk]⟩

theorem continuous_diagOne : Continuous (fun a : (p.adicCompletion ℚ)ˣ => (diagOne a : GL (Fin 2) (p.adicCompletion ℚ))) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun a : (p.adicCompletion ℚ)ˣ => Matrix.diagonal ![(a : p.adicCompletion ℚ), 1]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> fun_prop
  · have h1 : Continuous fun a : (p.adicCompletion ℚ)ˣ => Matrix.diagonal ![(a : p.adicCompletion ℚ), 1] := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> fun_prop
    have : (fun a : (p.adicCompletion ℚ)ˣ => (((diagOne a : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) =
        (fun a : (p.adicCompletion ℚ)ˣ => Matrix.diagonal ![(a : p.adicCompletion ℚ), 1]) ∘ (fun a => a⁻¹) := by
      funext a
      simp only [Function.comp_apply, ← map_inv]
      rfl
    rw [this]
    exact h1.comp continuous_inv

theorem deep_shells_one (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (v : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hvlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      v (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * v g)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ u ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), v (g * u) = v g)
    (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
        v (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
      (∫ y : (p.adicCompletion ℚ)ˣ,
          v (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :
    ∀ n : ℤ, (P.natDegree : ℤ) + 1 - m ≤ n →
      ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          ((χ u : ℂˣ) : ℂ) * v (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0 := by
  intro n hn
  set f : (p.adicCompletion ℚ)ˣ → ℂ := fun y => v (diagOne y) * ((χ y : ℂˣ) : ℂ) with hf
  have hflc : IsLocallyConstant f :=
    ((isLocallyConstant_of_stab p v U hUo hU).comp_continuous (continuous_diagOne p)).mul
      (hχ.comp (fun c : ℂˣ => (c : ℂ)))
  obtain ⟨C, hC⟩ := exists_forall_apply_diagOne_eq_zero p v hvlaw U hUo hU
  have hfsupp : ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : p.adicCompletion ℚ)‖ → f y = 0 :=
    ⟨C, fun y hy => by simp only [hf, hC y hy, zero_mul]⟩
  have hmellin : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun y : (p.adicCompletion ℚ)ˣ => f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
      (∫ y : (p.adicCompletion ℚ)ˣ, f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * (1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hmel s hs
    refine ⟨h1, ?_⟩
    rw [Polynomial.eval_one, mul_one]
    exact h2
  have hrow := LanglandsTunnell.TateLocal.forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval
    p hπ hϖ f hflc hfsupp P 1 m σ₀ hmellin n
  simp only [Polynomial.natDegree_one, zero_add, Finset.sum_range_one, Polynomial.coeff_one_zero, one_mul, Nat.cast_zero,
    sub_zero] at hrow
  have hnm : 0 ≤ n + m := by omega
  rw [if_pos hnm, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at hrow

  have hq : ((Real.sqrt (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ) ^ n ≠ 0 := by
    apply zpow_ne_zero
    have : 0 < Real.sqrt (Ideal.absNorm p.asIdeal : ℝ) := Real.sqrt_pos.mpr (by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm p; exact_mod_cast (lt_trans zero_lt_one this))
    exact_mod_cast this.ne'
  have hI := (mul_eq_zero.mp hrow).resolve_left hq
  have hcχ : (((χ ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n) : ℂˣ)) : ℂ) ≠ 0 :=
    Units.ne_zero _
  have hrewrite : ∀ u : (p.adicCompletion ℚ)ˣ,
      f ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) =
        (((χ ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n) : ℂˣ)) : ℂ) *
          (((χ u : ℂˣ) : ℂ) * v (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u))) := by
    intro u
    simp only [hf, map_mul, Units.val_mul, diagUnitGL2_eq_diagOne]
    ring
  simp_rw [hrewrite] at hI
  rw [integral_const_mul] at hI
  exact (mul_eq_zero.mp hI).resolve_left hcχ

end SVDb

open SVDb in
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
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ nstar : ℤ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ, nstar ≤ n →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            ((χ u : ℂˣ) : ℂ) *
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * k)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0 := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  classical
  intro w hw

  obtain ⟨Uw, hUwo, hUw⟩ := exists_stab_of_mem_span p N hN w₂base hw₂K hw

  have hper : ∀ k : GL (Fin 2) (p.adicCompletion ℚ), ∃ n0 : ℤ, ∀ n : ℤ, n0 ≤ n →
      ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          ((χ u : ℂˣ) : ℂ) *
            w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * k)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0 := by
    intro k
    have hvk := translate_mem_span p w₂base hw k
    obtain ⟨P, m, σ₀, hmel⟩ := htorus _ hvk
    obtain ⟨Uk, hUko, hUk⟩ := exists_stab_of_mem_span p N hN w₂base hw₂K hvk
    refine ⟨(P.natDegree : ℤ) + 1 - m, fun n hn => ?_⟩
    exact deep_shells_one p χ hχ hπ hϖ (fun g => w (g * k)) (whittaker_law_of_mem_span p w₂base hw₂law hvk)
      Uk hUko (fun u hu g => hUk u hu g) P m σ₀ hmel n hn
  choose nfun hnfun using hper

  have hK0c := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) top_ne_bot).1
  obtain ⟨t, -, hcover⟩ := hK0c.elim_nhds_subcover
    (fun k₀ : GL (Fin 2) (p.adicCompletion ℚ) => {k : GL (Fin 2) (p.adicCompletion ℚ) | k₀⁻¹ * k ∈ Uw})
    (fun k₀ _ => (hUwo.preimage (continuous_const.mul continuous_id)).mem_nhds
      (show k₀⁻¹ * k₀ ∈ Uw by rw [inv_mul_cancel]; exact Uw.one_mem))
  refine ⟨((t.sup fun k₀ => (nfun k₀).toNat : ℕ) : ℤ), fun k hk n hn => ?_⟩
  obtain ⟨k₀, hk₀t, hk₀⟩ : ∃ k₀ ∈ t, k₀⁻¹ * k ∈ Uw := by
    have := hcover hk
    simpa only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using this
  have hwk : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w (g * k₀) := fun g => by
    rw [show g * k = g * k₀ * (k₀⁻¹ * k) by rw [mul_assoc, mul_inv_cancel_left], hUw _ hk₀]
  simp_rw [hwk]
  refine hnfun k₀ n (le_trans ?_ hn)
  refine le_trans (Int.self_le_toNat (nfun k₀)) ?_
  exact_mod_cast Finset.le_sup (f := fun k₀ => (nfun k₀).toNat) hk₀t

end

end S_LanglandsTunnell_RankinSelberg_exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent (solution)
