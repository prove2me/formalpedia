-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/8060a64e-4df7-5bc4-8bcd-a7fe150438d2

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (A : Type) [CommRing A]
    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (φ₀ : P₀.B₀ →ₐ[A] Ω)

    (hy : ∃ y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt (DualNumber Ω),
      (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A) y = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ₀ P₀.univ ∧
      y ≠ (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A) ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ₀ P₀.univ)) :
    ∃ φ : P₀.B₀ →ₐ[A] DualNumber Ω,
      (∀ b : P₀.B₀, (φ b).fst = φ₀ b) ∧ ∃ b : P₀.B₀, (φ b).snd ≠ 0 := by
  obtain ⟨y, hy1, hy2⟩ := hy

  have hcl : ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A).comp (P₀.classify y) = φ₀ := by
    have e1 : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A).comp (P₀.classify y)) P₀.univ = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ₀ P₀.univ := by
      rw [(rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map_comp, P₀.map_classify]; exact hy1
    exact (P₀.classify_unique _ _ e1).trans (P₀.classify_unique _ φ₀ rfl).symm
  refine ⟨P₀.classify y, fun b => ?_, ?_⟩
  · exact congrArg (fun f : P₀.B₀ →ₐ[A] Ω => f b) hcl
  · by_contra hall
    push_neg at hall
    apply hy2
    have h2 : P₀.classify y = ((TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A).comp (((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A).comp (P₀.classify y)) := by
      apply AlgHom.ext
      intro b
      apply TrivSqZeroExt.ext
      · rfl
      · show (P₀.classify y b).snd = 0
        exact hall b
    calc y = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (P₀.classify y) P₀.univ := (P₀.map_classify y).symm
      _ = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (((TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A).comp (((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A).comp (P₀.classify y))) P₀.univ := by rw [← h2]
      _ = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A) ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A).comp (P₀.classify y)) P₀.univ) := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map_comp _ _ _
      _ = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A) ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ₀ P₀.univ) := by rw [hcl]

end S_ModularCurve_FullLevel_exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow (solution)
