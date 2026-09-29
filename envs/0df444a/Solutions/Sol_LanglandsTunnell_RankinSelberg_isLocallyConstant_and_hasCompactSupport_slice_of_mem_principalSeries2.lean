-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/87b0b9c8-0f0d-57f0-be3d-db95e2e73968

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace LanglandsTunnell
namespace RankinSelberg
namespace SliceSB
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open scoped Matrix Topology

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F𝔽" => p.adicCompletion ℚ
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem exists_nhds_forall_add_eq {X : Type*} [AddCommGroup X] [UniformSpace X] [IsUniformAddGroup X] {Y : Type*} [Zero Y]
    (f : X → Y) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ V ∈ 𝓝 (0 : X), ∀ x e, e ∈ V → f (x + e) = f x := by
  obtain ⟨W, hWu, hWK⟩ := lebesgue_number_lemma hfc.isCompact (fun m : X => hf {f m})
    (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩)
  have hW' := hWu
  rw [uniformity_eq_comap_nhds_zero X, Filter.mem_comap] at hW'
  obtain ⟨V₀, hV₀, hV₀W⟩ := hW'
  have hnegV : (fun e : X => -e) ⁻¹' V₀ ∈ 𝓝 (0 : X) := by
    have : Filter.Tendsto (fun e : X => -e) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact this hV₀
  refine ⟨V₀ ∩ (fun e : X => -e) ⁻¹' V₀, Filter.inter_mem hV₀ hnegV, ?_⟩
  have key : ∀ x ∈ tsupport f, ∀ e ∈ V₀, f (x + e) = f x := by
    intro x hx e he
    obtain ⟨m, hm⟩ := hWK x hx
    have h1 : x + e ∈ UniformSpace.ball x W := hV₀W (by simpa using he)
    have h2 : x ∈ UniformSpace.ball x W := UniformSpace.mem_ball_self x hWu
    have e1 : f (x + e) = f m := hm h1
    have e2 : f x = f m := hm h2
    rw [e1, e2]
  intro x e he
  by_cases hx : x ∈ tsupport f
  · exact key x hx e he.1
  by_cases hxe : x + e ∈ tsupport f
  · have := key (x + e) hxe (-e) (by simpa using he.2)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxe]

theorem exists_entry_bound (Φ : Mat → ℂ) (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, ∀ m ∈ tsupport Φ, ∀ i j : Fin 2, ‖m i j‖ ≤ B := by
  have hc : ∀ i j : Fin 2, Continuous fun m : Mat => ‖m i j‖ := fun i j =>
    (continuous_id.matrix_elem i j).norm
  choose B hB using fun i j => hΦc.isCompact.exists_bound_of_continuousOn ((hc i j).continuousOn)
  refine ⟨max (max (B 0 0) (B 0 1)) (max (B 1 0) (B 1 1)), fun m hm i j => ?_⟩
  have h := hB i j m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  fin_cases i <;> fin_cases j
  · exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem norm_inv_entry_le_one {k : G2} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (i j : Fin 2) :
    ‖((k⁻¹ : G2) : Mat) i j‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 (((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p k).1 hk).2.integral i j))

theorem upper_mul_mul_inv (a x d : F𝔽) (k : G2) :
    !![a, x; 0, d] * (k : Mat) * ((k⁻¹ : G2) : Mat) = !![a, x; 0, d] := by
  rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem norm_fst_le (a x d : F𝔽) (k : G2) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (B : ℝ)
    (hB : ∀ i j : Fin 2, ‖(!![a, x; 0, d] * (k : Mat)) i j‖ ≤ B) : ‖a‖ ≤ B ∧ ‖d‖ ≤ B := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 0)
  have hki := norm_inv_entry_le_one p hk
  have bnd : ∀ i j i' j', ‖(!![a, x; 0, d] * (k : Mat)) i j * ((k⁻¹ : G2) : Mat) i' j'‖ ≤ B := fun i j i' j' => by
    rw [norm_mul]; exact (mul_le_mul (hB i j) (hki i' j') (norm_nonneg _) hB0).trans (by rw [mul_one])
  have ha : a = (!![a, x; 0, d] * (k : Mat) * ((k⁻¹ : G2) : Mat)) 0 0 := by
    rw [upper_mul_mul_inv]; simp
  have hd : d = (!![a, x; 0, d] * (k : Mat) * ((k⁻¹ : G2) : Mat)) 1 1 := by
    rw [upper_mul_mul_inv]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at ha hd
  constructor
  · rw [ha]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (bnd 0 0 0 0) (bnd 0 1 1 0))
  · rw [hd]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (bnd 1 0 0 1) (bnd 1 1 1 1))

theorem main
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hF : F ∈ principalSeries2 p lam)
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let ϕ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun ad =>
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
              (∫ x : (p.adicCompletion ℚ), Φ (!![ad.1, x; 0, ad.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂
        IsLocallyConstant ϕ ∧ HasCompactSupport ϕ := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ ϕ
  set Kset : Set G2 := (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G2) with hKset
  obtain ⟨hK0c, hK0o⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot
  have hKmeas : MeasurableSet Kset := hK0o.measurableSet
  constructor
  ·
    rw [IsLocallyConstant.iff_eventually_eq]
    intro ad
    obtain ⟨V, hV, hVeq⟩ := exists_nhds_forall_add_eq Φ hΦ hΦc
    set E : (F𝔽 × F𝔽) × G2 → Mat := fun z => !![z.1.1 - ad.1, 0; 0, z.1.2 - ad.2] * (z.2 : Mat) with hE
    have hEc : Continuous E := by
      refine Continuous.mul ?_ (Units.continuous_val.comp continuous_snd)
      refine continuous_matrix ?_
      intro i j
      fin_cases i <;> fin_cases j
      · exact (continuous_fst.comp continuous_fst).sub continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact (continuous_snd.comp continuous_fst).sub continuous_const
    have hE0 : ∀ k : G2, E (ad, k) = 0 := fun k => by
      simp only [hE, sub_self]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hev : ∀ᶠ ad' in 𝓝 ad, ∀ k ∈ Kset, E (ad', k) ∈ V := by
      refine hK0c.eventually_forall_of_forall_eventually (fun k _ => ?_)
      have : V ∈ 𝓝 (E (ad, k)) := by rw [hE0 k]; exact hV
      exact hEc.continuousAt.preimage_mem_nhds this
    filter_upwards [hev] with ad' had'
    show (∫ k in Kset, F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ x : F𝔽, Φ (!![ad'.1, x; 0, ad'.2] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) ∂μ₂) =
      ∫ k in Kset, F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ x : F𝔽, Φ (!![ad.1, x; 0, ad.2] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) ∂μ₂
    refine setIntegral_congr_fun hKmeas (fun k hk => ?_)
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hsplit : !![ad'.1, x; 0, ad'.2] * (k : Mat) = !![ad.1, x; 0, ad.2] * (k : Mat) + E (ad', k) := by
      simp only [hE]
      rw [← Matrix.add_mul]
      congr 1
      ext i j; fin_cases i <;> fin_cases j <;> simp
    show Φ (!![ad'.1, x; 0, ad'.2] * (k : Mat)) = Φ (!![ad.1, x; 0, ad.2] * (k : Mat))
    rw [hsplit]
    exact hVeq _ _ (had' k hk)
  ·
    obtain ⟨B, hB⟩ := exists_entry_bound p Φ hΦc
    refine HasCompactSupport.intro ((isCompact_closedBall (0 : F𝔽) B).prod (isCompact_closedBall (0 : F𝔽) B)) ?_
    intro ad had
    have hzero : ∀ k ∈ Kset, ∀ x : F𝔽, Φ (!![ad.1, x; 0, ad.2] * (k : Mat)) = 0 := by
      intro k hk x
      by_contra hne
      have hmem : !![ad.1, x; 0, ad.2] * (k : Mat) ∈ tsupport Φ := subset_tsupport _ hne
      obtain ⟨ha, hd⟩ := norm_fst_le p ad.1 x ad.2 k hk B (hB _ hmem)
      exact had ⟨mem_closedBall_zero_iff.2 ha, mem_closedBall_zero_iff.2 hd⟩
    show (∫ k in Kset, F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ x : F𝔽, Φ (!![ad.1, x; 0, ad.2] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) ∂μ₂) = 0
    rw [setIntegral_congr_fun hKmeas (fun k hk => by
      show F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
          (∫ x : F𝔽, Φ (!![ad.1, x; 0, ad.2] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) = 0
      rw [integral_congr_ae (ae_of_all _ fun x => hzero k hk x)]
      simp)]
    simp

end LanglandsTunnell.RankinSelberg.SliceSB

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hF : F ∈ principalSeries2 p lam)
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let ϕ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun ad =>
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
              (∫ x : (p.adicCompletion ℚ), Φ (!![ad.1, x; 0, ad.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂
        IsLocallyConstant ϕ ∧ HasCompactSupport ϕ :=
  LanglandsTunnell.RankinSelberg.SliceSB.main p lam hlam χ hχ F hF Φ hΦ hΦc

end S_LanglandsTunnell_RankinSelberg_isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2 (solution)
