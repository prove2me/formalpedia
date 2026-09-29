-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_mem_span_schwartzBruhat_fourier_unitShell_pairing_ne_zero_of_deepTwist_of_conductor_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/db45f0c8-84d0-5484-b3e7-8a8d38b46019

import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le
import Theorems.Thm_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_schwartzBruhat_fourier_unitShell_pairing_ne_zero_of_deepTwist_of_conductor_le
p2m_attr_erase "instance" "LocalGL2.Kirillov.fintype_Qm LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply LocalGL2.Kirillov.rT_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

noncomputable section

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ξ x : ℂˣ) : ℂ)‖ = 1)
    (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B)

    (f : ℕ)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω x : ℂˣ) : ℂ)‖ = 1)
    (hωf : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p f, ω u = 1)

    (hωB : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p B, ω u = 1)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hθu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((θ₀ z : ℂˣ) : ℂ)‖ = 1)
    (b : ℕ) (hcθ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, θ₀ u = 1)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
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
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (hBk : B < kp) (hfk : f ≤ kp) (hbk : 2 * b + 1 ≤ kp) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    ∃ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
    ∃ φ φ₁ : p.adicCompletion ℚ → ℂ,
      IsSchwartzBruhat φ ∧ IsSchwartzBruhat φ₁ ∧

      (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 →
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ (t : p.adicCompletion ℚ) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) t : ℂˣ) : ℂ)) ∧
      (∀ y : p.adicCompletion ℚ, Valued.v y ≠ 1 →
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ y = 0) ∧

      (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → ∀ y : p.adicCompletion ℚ,
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ ((t : p.adicCompletion ℚ) * y) =
          ((ω t : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y) ∧
      (∀ y : p.adicCompletion ℚ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y ≠ 0 →
        Valued.v y ≤ WithZero.exp (-(f : ℤ))) ∧

      (∀ u y : p.adicCompletion ℚ, φ u ≠ 0 → φ₁ y ≠ 0 →
        y ≠ 0 ∧ Valued.v y⁻¹ ≤ WithZero.exp (-(f : ℤ)) ∧ Valued.v (y⁻¹ * u) ≤ WithZero.exp (-(f : ℤ))) ∧

      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (unipotent x * g) =
          NumberField.StandardAddChar.psiLocal ℚ p x *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) z : ℂˣ) : ℂ) *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (g * k) =
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧

      (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1},
          ((ω t : ℂˣ) : ℂ) *
            (∫ x : p.adicCompletion ℚ,
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                    ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (w₀p * diagUnitGL2 t * unipotent x) *
                  tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) ∂(selfDualHaarAt ℚ p))
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ≠ 0 := by
  classical
  obtain ⟨w', hw'V, ⟨c₀, hc₀, hK⟩, hlaw, hθ, hsm⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne p χ kp hkp ξ B hξB hBk θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral
  letI : MeasurableSpace (p.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ p
  refine ⟨w', hw'V, (fun u : p.adicCompletion ℚ =>
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p)
          (fun x : p.adicCompletion ℚ => if Valued.v x = 1 then charExt (θ₀ * (χ * ξ⁻¹) ^ 2) x else 0) (-u)), (fun y : p.adicCompletion ℚ =>
        if Valued.v y = WithZero.exp (((2 * kp : ℕ)) : ℤ) then
          charExt ω⁻¹ (y * ((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ (2 * kp) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ))
        else 0), ?_⟩
  obtain ⟨hφ, hφ₁, h6a, h6b, h7, h8, hcut⟩ :=
    LanglandsTunnell.RankinSelberg.isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le p χ kp hkp ξ B hξB f ω hωf θ₀ b hcθ hBk hfk hbk _ _ rfl rfl
  have hnz := LanglandsTunnell.RankinSelberg.setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le p χ hχu kp hkp ξ hξu B hξB f ω hωu hωf hωB θ₀ hθu b hcθ N hN hNb w₂base hw₂law hw₂K hw₂ne
    hw₂irr hw₂adm hcentral w₀p hw₀p hBk hfk hbk w' hw'V c₀ hc₀ hK ⟨hlaw, hθ, hsm⟩ _ rfl
  exact ⟨hφ, hφ₁, h6a, h6b, h7, h8, hcut, hlaw, hθ, hsm, hnz⟩

end

end S_LanglandsTunnell_RankinSelberg_exists_mem_span_schwartzBruhat_fourier_unitShell_pairing_ne_zero_of_deepTwist_of_conductor_le
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_schwartzBruhat_fourier_unitShell_pairing_ne_zero_of_deepTwist_of_conductor_le (solution)
