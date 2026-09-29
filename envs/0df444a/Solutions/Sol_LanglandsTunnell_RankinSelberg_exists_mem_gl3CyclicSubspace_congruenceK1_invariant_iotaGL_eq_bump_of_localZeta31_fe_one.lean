-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6de1caf3-7db9-5b9c-af21-d82c3511ec03

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

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_spherical_of_eulerPoly_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_zero_of_isGL3PsiWhittakerFn_of_congruenceK1
import Theorems.Thm_LanglandsTunnell_RankinSelberg_localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

namespace Ws1
namespace EssNorm

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem translate_mem (W : LocalGL3 p → ℂ) (g₀ : LocalGL3 p) :
    (fun g => W (g * g₀)) ∈ gl3CyclicSubspace W :=
  Submodule.subset_span ⟨g₀, by funext g; simp⟩

theorem cyc_le_of_mem (W F : LocalGL3 p → ℂ) (hF : F ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace F ≤ gl3CyclicSubspace W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨h, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hF

noncomputable def normalise (W : LocalGL3 p → ℂ) (g₀ : LocalGL3 p) : LocalGL3 p → ℂ :=
  fun g => (W g₀)⁻¹ * W (g * g₀)

theorem normalise_mem (W : LocalGL3 p → ℂ) (g₀ : LocalGL3 p) : normalise W g₀ ∈ gl3CyclicSubspace W := by
  have : normalise W g₀ = (W g₀)⁻¹ • (fun g => W (g * g₀)) := by
    funext g; simp [normalise, Pi.smul_apply, smul_eq_mul]
  rw [this]; exact Submodule.smul_mem _ _ (translate_mem W g₀)

theorem normalise_one (W : LocalGL3 p → ℂ) (g₀ : LocalGL3 p) (h : W g₀ ≠ 0) : normalise W g₀ 1 = 1 := by
  simp [normalise, h]

theorem normalise_ne_zero (W : LocalGL3 p → ℂ) (g₀ : LocalGL3 p) (h : W g₀ ≠ 0) : normalise W g₀ ≠ 0 := by
  intro h0; have := congrFun h0 1; rw [normalise_one W g₀ h] at this; simp at this

theorem normalise_law (ψ : AddChar (p.adicCompletion ℚ) ℂ) (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ W) (g₀ : LocalGL3 p) :
    IsGL3PsiWhittakerFn ψ (normalise W g₀) := by
  intro x y z g
  simp only [normalise, mul_assoc]
  rw [hW x y z (g * g₀)]
  ring

theorem normalise_smooth (W : LocalGL3 p → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (g₀ : LocalGL3 p) :
    ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, normalise W g₀ (g * k) = normalise W g₀ g := by
  obtain ⟨Uv, hUo, hU⟩ := hsm
  let φ : LocalGL3 p →* LocalGL3 p := (MulAut.conj g₀⁻¹).toMonoidHom
  have hφ : ∀ x, φ x = g₀⁻¹ * x * g₀ := by
    intro x; simp [φ]
  refine ⟨Uv.comap φ, ?_, ?_⟩
  · have hcont : Continuous (fun x : LocalGL3 p => g₀⁻¹ * x * g₀) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hset : ((Uv.comap φ : Subgroup (LocalGL3 p)) : Set (LocalGL3 p)) =
        (fun x : LocalGL3 p => g₀⁻¹ * x * g₀) ⁻¹' (Uv : Set (LocalGL3 p)) := by
      ext x; simp [Subgroup.coe_comap, hφ]
    rw [hset]; exact hUo.preimage hcont
  · intro k hk g
    have hk' : g₀⁻¹ * k * g₀ ∈ Uv := by simpa [Subgroup.mem_comap, hφ] using hk
    simp only [normalise]
    congr 1
    have : g * k * g₀ = g * g₀ * (g₀⁻¹ * k * g₀) := by group
    rw [this, hU _ hk']

theorem normalise_irr (W : LocalGL3 p → ℂ) (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (g₀ : LocalGL3 p) (h : W g₀ ≠ 0) :
    ∀ F ∈ gl3CyclicSubspace (normalise W g₀), F ≠ 0 → normalise W g₀ ∈ gl3CyclicSubspace F := by
  intro F hF hF0
  have hF' : F ∈ gl3CyclicSubspace W := cyc_le_of_mem W _ (normalise_mem W g₀) hF
  have hW : W ∈ gl3CyclicSubspace F := hirr F hF' hF0
  exact cyc_le_of_mem F W hW (normalise_mem W g₀)

theorem normalise_adm (W : LocalGL3 p → ℂ)
    (hadm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))
    (g₀ : LocalGL3 p) :
    ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ F ∈ gl3CyclicSubspace (normalise W g₀),
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)) := by
  intro Uv hUo
  obtain ⟨B, hB⟩ := hadm Uv hUo
  exact ⟨B, fun F hF hFk => hB F (cyc_le_of_mem W _ (normalise_mem W g₀) hF) hFk⟩

theorem exists_apply_ne_zero (W : LocalGL3 p → ℂ) (hne : W ≠ 0) : ∃ g₀, W g₀ ≠ 0 := by
  by_contra h; simp only [not_exists, not_not] at h; exact hne (funext h)

theorem isLocalWhittakerDatum_normalise (W : LocalGL3 p → ℂ)
    (hlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hadm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))
    (g₀ : LocalGL3 p) (h : W g₀ ≠ 0) :
    IsLocalWhittakerDatum p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (normalise W g₀) := by
  have hψ : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ ≠ 1 := by
    intro h1; apply LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p
    rw [← inv_inv (NumberField.StandardAddChar.psiLocal ℚ p), h1, inv_one]
  refine ⟨normalise_law _ W hlaw g₀, normalise_one W g₀ h, ?_, normalise_irr W hirr g₀ h, normalise_smooth W hsm g₀,
    normalise_adm W hadm g₀⟩
  exact LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace p _ hψ _
    (normalise_ne_zero W g₀ h) (normalise_irr W hirr g₀ h) (normalise_smooth W hsm g₀) (normalise_adm W hadm g₀)

end Ws1.EssNorm

namespace Ws1
namespace EssL
variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem scalar_mul_comm (g g₀ : LocalGL3 p) (dd : (p.adicCompletion ℚ)ˣ) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 3) dd * g₀ = Matrix.GeneralLinearGroup.scalar (Fin 3) dd * (g * g₀) := by
  have hc : ∀ x : LocalGL3 p, x * Matrix.GeneralLinearGroup.scalar (Fin 3) dd = Matrix.GeneralLinearGroup.scalar (Fin 3) dd * x := by
    intro x
    apply Units.ext
    change (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) * Matrix.scalar (Fin 3) (dd : p.adicCompletion ℚ) =
      Matrix.scalar (Fin 3) (dd : p.adicCompletion ℚ) * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
    exact ((Matrix.scalar_commute (dd : p.adicCompletion ℚ) (fun r => Commute.all _ r) _).eq).symm
  rw [hc, mul_assoc]

theorem law_of_mem_cyc (ψ : AddChar (p.adicCompletion ℚ) ℂ) (W F : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hF : F ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ F := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace (p.adicCompletion ℚ) ℂ ψ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ F).mp (hle hF)

end Ws1.EssL

open scoped Classical in
theorem Ws1.EssBump.bump_of_spherical_pairing
    (p : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (E : Polynomial ℂ) (hE1 : E = 1)
    (W : LocalGL3 p → ℂ)
    (hWlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W)
    (hK : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p ℓ, ∀ g : LocalGL3 p, W (g * k) = W g)
    (hW1 : W 1 = 1)
    (hpair : (∀ {ϖ : p.adicCompletionIntegers ℚ}
        (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0),
        Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
        ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
        (W₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
        (hW₂ψ : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W₂ g)
        (hW₂K : ∀ (k g : GL (Fin 2) (p.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → W₂ (g * k) = W₂ g)
        (hW₂1 : W₂ 1 = 1)
        (hW₂Z : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          W₂ (g * scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) =
            a₁ * a₂ / (Ideal.absNorm p.asIdeal : ℂ) * W₂ g)
        (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m) =
          torusFactor (Ideal.absNorm p.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm p.asIdeal : ℂ)) m),
        letI := localGLBorel ℚ p
        haveI := borelSpace_localGLBorel ℚ p
        ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
        ∃ σ₂ : ℝ,
          (∀ s : ℂ, σ₂ < s.re →
            Integrable
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W (iotaGL g) * W₂ g) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                      p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W (iotaGL g)) W₂ *
                (E).eval (a₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + 1 /
                    2))) *
                (E).eval (a₂ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + 1 /
                    2))) =
              (((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN))
                  {g : GL (Fin 2) (p.adicCompletion ℚ) |
                    ∃ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, g = n * k}).toReal : ℂ)))) :
    (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      W (iotaGL (h * k)) = W (iotaGL h)) ∧
    (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
    W (iotaGL 1) = 1 := by
  classical

  have iotaGL_mem : ∀ (c : ℕ) (k : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      (iotaGL k : LocalGL3 p) ∈ congruenceK1 (𝓞 ℚ) ℚ p c := by
    intro c k hk
    rw [AdelicDock.mem_localLevelOne_iff] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hint : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ≤ 1 :=
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk1.integral i j)
    have hint' : ∀ i j, Valued.v (((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ≤ 1 :=
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk2.integral i j)
    have hemb : ∀ (M : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), (∀ i j, Valued.v (M i j) ≤ 1) →
        ∀ i j, Valued.v (embedMat2 M i j) ≤ 1 := by
      intro M hM i j
      fin_cases i <;> fin_cases j <;> simp [embedMat2, hM]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_localMaximalCompact3_iff]
      refine ⟨?_, ?_⟩
      · intro i j; rw [coe_iotaGL]; exact hemb _ hint i j
      · intro i j; rw [← map_inv, coe_iotaGL]; exact hemb _ hint' i j
    · simp [embedMat2]
    · simp [embedMat2]
    · simp [embedMat2]
  have hunip : ∀ x : p.adicCompletion ℚ, (iotaGL (unipotent x) : LocalGL3 p) = upperUnipotent3 x 0 0 := by
    intro x
    have : (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) = AutomorphicForm.unipotentGL2 x := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unipotent, AutomorphicForm.unipotentGL2, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    rw [this, iotaGL_unipotentGL2]

  obtain ⟨ϖ, hϖ0⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer ℚ p
  have hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := hϖ0
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ

  set f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun h => W (iotaGL h) with hf
  have hfψ : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      f (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x * f g := by
    intro x g
    simp only [hf, map_mul, hunip]
    have := hWlaw x 0 0 (iotaGL g)
    rw [add_zero] at this
    exact this
  have hfK : ∀ (k g : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → f (g * k) = f g := by
    intro k g hk
    simp only [hf, map_mul]
    exact hK _ (iotaGL_mem ℓ k hk) _

  have hsupp := LanglandsTunnell.RankinSelberg.forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_zero_of_isGL3PsiWhittakerFn_of_congruenceK1
    p ϖ hπ hϖ W hWlaw ℓ hK
  subst hE1
  have hid := hpair hπ hϖ
  simp only [Polynomial.eval_one, mul_one] at hid

  have htorus := LanglandsTunnell.RankinSelberg.forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
    p ϖ hπ hϖ f hfψ hfK (fun m n hmn => by simp only [hf]; exact hsupp m n hmn) hid
  exact LanglandsTunnell.RankinSelberg.localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite
    p ϖ hπ hϖ f hfψ hfK htorus

open scoped Classical in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (hWgauge : ∃ (Bg : ℝ) (tg : ℕ) (Cg : ℝ), ∀ h : LocalGL3 p,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg) → W₃base h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg →
        ‖W₃base h‖ ≤ Cg / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ tg))
    (hω₃u : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((ω₃ z : ℂˣ) : ℂ)‖ = 1)
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (hE1 : E = 1) (hEd1 : Ed = 1) (hε : ε ≠ 0) (hℓ1 : 1 ≤ ℓ)
    (hω₃ℓ : ∀ d : (p.adicCompletion ℚ)ˣ, Valued.v (d : p.adicCompletion ℚ) = 1 →
      Valued.v ((d : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(ℓ : ℤ)) → ω₃ d = 1)
    (h31 : ∀ g : LocalGL3 p,
      (letI := localBorel ℚ p
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base 1 s g =
            (E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∃ W₀ ∈ gl3CyclicSubspace W₃base,
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p ℓ, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
        ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
      W₀ (iotaGL 1) = 1 := by
  classical
  have hψ : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ ≠ 1 := by
    intro h1; apply LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p
    rw [← inv_inv (NumberField.StandardAddChar.psiLocal ℚ p), h1, inv_one]
  have hmult : HasWhittakerMultOne (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base :=
    LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace p _ hψ W₃base
      hW₃ne hW₃irr hW₃sm hW₃adm
  obtain ⟨g₀, hg₀⟩ := Ws1.EssNorm.exists_apply_ne_zero W₃base hW₃ne
  have h₀ := Ws1.EssNorm.isLocalWhittakerDatum_normalise W₃base hW₃law hW₃sm hW₃irr hW₃adm g₀ hg₀
  have hZ : ∀ (g : LocalGL3 p) (dd : (p.adicCompletion ℚ)ˣ), Valued.v (dd : p.adicCompletion ℚ) = 1 →
      Valued.v ((dd : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(ℓ : ℤ)) →
      Ws1.EssNorm.normalise W₃base g₀ (g * Matrix.GeneralLinearGroup.scalar (Fin 3) dd) =
        Ws1.EssNorm.normalise W₃base g₀ g := by
    intro g dd h1 h2
    show (W₃base g₀)⁻¹ * W₃base (g * Matrix.GeneralLinearGroup.scalar (Fin 3) dd * g₀) = (W₃base g₀)⁻¹ * W₃base (g * g₀)
    rw [Ws1.EssL.scalar_mul_comm, hω₃, hω₃ℓ dd h1 h2]
    simp

  have hle := Ws1.EssNorm.cyc_le_of_mem W₃base _ (Ws1.EssNorm.normalise_mem W₃base g₀)
  obtain ⟨W, hWmem, hK, hW1, hpair⟩ :=
    LanglandsTunnell.RankinSelberg.exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_spherical_of_eulerPoly_eq_one
      p ℓ hℓ1 (Ws1.EssNorm.normalise W₃base g₀) h₀ hZ ε hε E Ed hE1 hEd1
      (by
        intro ϖ hπ hϖ a₁ a₂ ha W₂ h1 h2 h3 h4 h5 W₂d h6 h7 h8 h9 h10 μ₂ i1 μN i2 W hW
        exact LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
          p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ rfl W₃base hW₃law hmult hW₃irr hW₃sm hW₃adm hWgauge ω₃ hω₃u hω₃
          hπ hϖ E Ed ε ℓ h31 a₁ a₂ ha W₂ h1 h2 h3 h4 h5 W₂d h6 h7 h8 h9 h10 μ₂ μN W (hle hW))
  have hWmem' : W ∈ gl3CyclicSubspace W₃base := hle hWmem
  have hWlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W :=
    Ws1.EssL.law_of_mem_cyc _ W₃base W hW₃law hWmem'
  obtain ⟨hι, hsupp, hone⟩ := Ws1.EssBump.bump_of_spherical_pairing p ℓ E hE1 W hWlaw hK hW1 hpair
  exact ⟨W, hWmem', hK, hι, hsupp, hone⟩

end S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one (solution)
