-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ffe8f79b-502f-5e16-89e9-b322ff278b20

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

namespace JSPrimal

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem unipotentGL2_eq_unipotent (x : F) : (unipotentGL2 x : GL (Fin 2) F) = unipotent x := by
  apply Units.ext
  simp [unipotentGL2_coe, unipotent, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem iotaGL_unipotent (x : F) : iotaGL (unipotent x) = upperUnipotent3 x 0 0 := by
  rw [← unipotentGL2_eq_unipotent]
  apply Units.ext
  rw [coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, upperUnipotent3, unipotentGL2_coe]

theorem whittaker_of_mem_gl3CyclicSubspace (ψ : AddChar F ℂ) (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    {W' : LocalGL3 p → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ W' := by
  induction hW' using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨h, rfl⟩ := hf
      intro x y z g
      simp only [gl3AmbientRightTranslate_apply]
      rw [mul_assoc]; exact hW x y z (g * h)
  | zero => intro x y z g; simp
  | add f g _ _ hf hg => intro x y z h; simp only [Pi.add_apply, hf x y z h, hg x y z h]; ring
  | smul a f _ hf => intro x y z h; simp only [Pi.smul_apply, smul_eq_mul, hf x y z h]; ring

theorem v_det_le_one (M : Matrix (Fin 2) (Fin 2) F) (hM : ∀ i j, M i j ∈ p.adicCompletionIntegers ℚ) :
    Valued.v M.det ≤ 1 := by
  have h : ∀ i j, Valued.v (M i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ p).mp (hM i j)
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
  · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one_of_mem_localLevelOne (N : Ideal (𝓞 ℚ)) {k : GL (Fin 2) F}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  have h1 : Valued.v ((k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≤ 1 := v_det_le_one p _ hk.1.integral
  have h2 : Valued.v ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≤ 1 := v_det_le_one p _ hk.2.integral
  have hprod : Valued.v ((k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
      Valued.v ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
        Valued.v ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det := hprod.symm
    _ ≤ Valued.v ((k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

end JSPrimal

open JSPrimal in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∃ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
    ∃ W₃ ∈ gl3CyclicSubspace W₃base,
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ c : ℂ, c ≠ 0 ∧
        ∀ s : ℂ,
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => W₃ (iotaGL g)) w₂ = c := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p

  obtain ⟨g₀, hg₀⟩ : ∃ g₀, w₂base g₀ ≠ 0 := by
    by_contra h; push Not at h; exact hw₂ne (funext h)
  set W₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => w₂base (g * g₀) with hW₂
  have hW₂V : W₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) :=
    Submodule.subset_span ⟨g₀, rfl⟩
  have hW₂1 : W₂ 1 = w₂base g₀ := by simp [hW₂]

  obtain ⟨hKc, hKo⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N _hN
  set U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)) :=
    AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N ⊓
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N).comap (MulAut.conj g₀⁻¹).toMonoidHom with hU
  have hmemU : ∀ k : GL (Fin 2) (p.adicCompletion ℚ), k ∈ U ↔
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N ∧ g₀⁻¹ * k * g₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
    intro k
    rw [hU, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hcont : Continuous fun k : GL (Fin 2) (p.adicCompletion ℚ) => g₀⁻¹ * k * g₀⁻¹⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hUset : (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∩
        (fun k : GL (Fin 2) (p.adicCompletion ℚ) => g₀⁻¹ * k * g₀⁻¹⁻¹) ⁻¹'
          (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    ext k
    simp only [hU, Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_comap,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Set.mem_preimage]
  have hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    rw [hUset]; exact hKo.inter (hKo.preimage hcont)
  have hUc : IsCompact (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    rw [hUset]; exact hKc.inter_right (hKc.isClosed.preimage hcont)

  have hψU : ∀ x : p.adicCompletion ℚ, (1 : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ * unipotentGL2 x * 1 ∈ U →
      (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x = 1 := by
    intro x hx
    rw [inv_one, one_mul, mul_one, hmemU] at hx
    have hx1 := hx.1
    rw [AdelicDock.mem_localLevelOne_iff] at hx1
    have hint := hx1.1.integral 0 1
    rw [unipotentGL2_coe] at hint
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val'] at hint
    rw [AddChar.inv_apply]
    exact LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p (-x) (neg_mem hint)

  have hψne : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one]; exact LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p
  obtain ⟨W', hW'mem, hinv, hsupp, hone⟩ :=
    LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen p
      (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ hψne W₃base hW₃law hW₃sm hW₃ne 1 U hUc hUo hψU
  have hW'law := whittaker_of_mem_gl3CyclicSubspace p _ W₃base hW₃law hW'mem
  refine ⟨W₂, hW₂V, W', hW'mem, ?_⟩
  intro μ₂ _ μN₂ _

  have hUdet : ∀ u ∈ U,
      modulus ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
    intro u hu
    have hv := v_det_eq_one_of_mem_localLevelOne p N ((hmemU u).mp hu).1
    have h4 := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
      p).2.2.2.1 0 (Matrix.GeneralLinearGroup.det u) (by
        rw [Set.mem_setOf_eq, hv]; simp)
    have : ((modulus ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : NNReal) : ℝ) =
        1 := by
      rw [h4]; simp
    exact_mod_cast this
  obtain ⟨c, hcpos, hc⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul p μ₂ μN₂
      U hUc hUo hUdet
  refine ⟨(c : ℂ) * (W' (iotaGL 1) * W₂ 1), ?_, fun s => hc s (fun g => W' (iotaGL g)) W₂ ?_ ?_ ?_⟩
  · rw [hone, hW₂1, one_mul]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hcpos.ne') hg₀
  ·
    intro x g
    show W' (iotaGL (unipotent x * g)) * w₂base (unipotent x * g * g₀) = W' (iotaGL g) * w₂base (g * g₀)
    rw [map_mul, iotaGL_unipotent, hW'law x 0 0, mul_assoc (unipotent x), hw₂law, add_zero, AddChar.inv_apply]
    calc (NumberField.StandardAddChar.psiLocal ℚ p) (-x) * W' (iotaGL g) *
          ((NumberField.StandardAddChar.psiLocal ℚ p) x * w₂base (g * g₀))
        = ((NumberField.StandardAddChar.psiLocal ℚ p) (-x) * (NumberField.StandardAddChar.psiLocal ℚ p) x) *
            (W' (iotaGL g) * w₂base (g * g₀)) := by ring
      _ = W' (iotaGL g) * w₂base (g * g₀) := by
          rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  ·
    intro g hg
    obtain ⟨x, k, hk, hgk⟩ := hsupp g (left_ne_zero_of_mul hg)
    refine ⟨x, k, hk, ?_⟩
    rw [hgk, mul_one, unipotentGL2_eq_unipotent]
  ·
    intro u hu
    have h1 : W' (iotaGL u) = W' (iotaGL 1) := by
      have := hinv u hu 1; rwa [one_mul] at this
    have h2 : W₂ u = W₂ 1 := by
      show w₂base (u * g₀) = w₂base (1 * g₀)
      rw [one_mul, show u * g₀ = g₀ * (g₀⁻¹ * u * g₀) by group]
      exact hw₂K _ ((hmemU u).mp hu).2 g₀
    show W' (iotaGL u) * W₂ u = W' (iotaGL 1) * W₂ 1
    rw [h1, h2]

end S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn (solution)
