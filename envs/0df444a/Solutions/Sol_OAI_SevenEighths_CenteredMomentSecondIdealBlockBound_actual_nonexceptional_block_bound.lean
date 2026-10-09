-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSecondIdealBlockBound.actual_nonexceptional_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:58:12.315042+00:00
-- url     : https://prove2.me/submissions/aa536bfe-066e-4bb6-b43f-efaa8a317021

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondCanonicalScalar_actual_retained_scalar_norm
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondNonexceptional_whole_kernel_nonexceptional_second_bound

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LogDyadic
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

theorem logAnnulus_norm (x : ℝ) : ‖logAnnulus x‖≤1 := by
  rw [logAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annulus_bounds _).1]
  exact (annulus_bounds _).2

end SevenEighths.CenteredMomentLogDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sectorElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Ideal.span {sectorElement C hC S a}=a :=
  primary_span_supported a (sectorPool_supported C hC S a)

theorem sectorElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (Ideal.span {sectorElement C hC S a}) := by
  rw [sectorElement_span]
  exact sectorPool_supported C hC S a

theorem sectorElement_primary (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : ConcretePrimeRowBridge.goodLambda^2∣sectorElement C hC S a-1 :=
  (primaryGenerator_spec a (supported_primaryGenerator_ne_zero a (sectorPool_supported C hC S a))).2

theorem coprime_of_same_support (C D a : Ideal O) (hC : C≠0) (hD : D≠0) (ha : a≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    IsCoprime C a ↔ IsCoprime D a := by
  change IdealMobiusDivisorSum.primeSupport C=IdealMobiusDivisorSum.primeSupport D at hCD
  rw [←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha,
    ←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hD ha,hCD]

theorem sectorElement_coprime (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (a : sectorPool C hC.1 S) :
    IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement C hC.1 S a) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [←Ideal.span_singleton_mul_span_singleton,primary_span_supported C hC,
    primary_span_supported D hD,sectorElement_span]
  have hc := (Finset.mem_filter.mp a.property).2
  exact hc.mul_left ((coprime_of_same_support C D a hC.1 hD.1
    (sectorPool_supported C hC.1 S a).1 hCD).mp hc)

end SevenEighths.CenteredMomentSecondSectorColumns

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondIdealBlockBound
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondIdealBlockBound
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem logAnnulus_enclosure (x : ℝ) (hx : logAnnulus x≠0) : |x|≤Real.log 4 := by
  have hh := logAnnulus_support hx
  exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩

theorem actual_nonexceptional_block_bound_oai (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ r : ℝ,0< r →
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
        (C D : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C=primeSupport D →
      ∀ (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
        (ρ x : O→ℝ) (u : sectorPool C hC.1 S→ℝ) (v : sectorPool D hD.1 S→ℝ)
        (Q : Ideal O) (m : O) (χ₀ : RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
      (∀ z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (H : ℝ),0<H →
      (∀ z : O,0≤(Φ (normValue z/H)).re) →
      (∀ z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀ E₁ E₂ : Ideal O→ℝ,
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₁ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₂ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement C hC.1 S)
          (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) Φ H≤
              (E₁ L*(1+‖w‖)^J₁)^2) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement D hD.1 S)
          (fun J=>divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient A (sectorElement D hD.1 S) d) χ J*star (columnPhase logAnnulus (v J) w)) Φ H≤
              (E₂ L*(1+‖w‖)^J₂)^2) →
      (1+r)^decay*‖∑ z∈rows,retainedScalar C D U R z*
        ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤
        B*∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(E₁ L*E₂ L) := by
  obtain ⟨B,hB,hbound⟩ := whole_kernel_nonexceptional_second_bound W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num)) (fun _ x hx=>logAnnulus_enclosure x hx)
    decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v Q m χ₀ hQ hmLam hm2
  dsimp only
  intro hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcopD (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := hbound r hr rows Finset.univ Finset.univ (primaryGenerator C) (primaryGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun J=>β (D*J)*heightCoeff η t J) u v ρ x η χ₀ Q m hQ hmLam hm2 hrows
    (fun z _=>actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _)
    Φ H hH (by simpa only [normValue_eq_embedding] using hΦ)
    (by simpa only [normValue_eq_embedding] using hmajor) E₁ E₂
    (by simpa only [sectorElement_span] using hE₁) (by simpa only [sectorElement_span] using hE₂)
    (by simpa only [sectorElement_span] using hleft) (by simpa only [sectorElement_span] using hright)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.CenteredMomentSecondIdealBlockBound

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentSecondIdealBlockBound.actual_nonexceptional_block_bound_oai := @OAI.SevenEighths.CenteredMomentSecondIdealBlockBound.actual_nonexceptional_block_bound_oai
