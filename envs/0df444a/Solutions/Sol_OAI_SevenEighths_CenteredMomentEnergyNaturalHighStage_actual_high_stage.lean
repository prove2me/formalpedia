-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyNaturalHighStage.actual_high_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:32:34.778543+00:00
-- url     : https://prove2.me/submissions/21a44d0d-5770-4931-b286-6aa890778f6c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalHighPhysical_actual_high_physical
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyPositiveHighBound_actual_high_from_physical

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem frequencyLoss_nonneg (Z Csec ξ : ℝ) (hZ : 1 < Z) (hC : 1 ≤ Csec) (hξ : 0 ≤ ξ) :
    0 ≤ frequencyLoss Z Csec ξ := by
  have hlog := Real.logb_nonneg hZ (show 1 ≤ 4*Csec by linarith)
  unfold frequencyLoss
  linarith

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.State
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

namespace NaturalState
variable {Z Bmask bΦ:ℝ}
lemma width_nonneg (s:NaturalState Z Bmask bΦ):0≤ s.width :=
  add_nonneg s.row_nonneg s.character_nonneg

end NaturalState

end SevenEighths.CenteredMomentEnergyState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dirichlet
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

variable [NeZero q]

end SevenEighths.HeckeDirichlet

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.Bands
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentEnergyBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O"=>HeckeFamily.O

lemma length_nonneg (Z X:ℝ)(hZ:1<Z):0≤length Z X:=
  Real.logb_nonneg hZ (le_max_left _ _)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyBands

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

lemma profile_control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(hst:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SuccessorPaidParameters
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤kappa) (hr : 0≤ reserve) :
    kappa*(reserve/(kappa+1))≤ reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<kappa+1)).mpr
  nlinarith

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.WidthSchedule
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

theorem bounds (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<amplification ε ∧ amplification ε≤1 ∧ amplification ε≤ε/16000 ∧
    0< reserve M B ε ∧ 0< mesh M B κ ε ∧ mesh M B κ ε≤ reserve M B ε ∧
    κ*mesh M B κ ε≤ reserve M B ε ∧
    20*reserve M B ε≤amplification ε/2 ∧
    M<width M B ε (count M ε) ∧
    loss M B ε (count M ε)≤ε/1000 :=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hs1:amplification ε≤1:=min_le_left _ _
  have hse:amplification ε≤ε/16000:=min_le_right _ _
  have hn:0≤(count M ε:ℝ):=Nat.cast_nonneg _
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL:(count M ε:ℝ)≤ scale M B ε:=by unfold scale;linarith
  have h1L:1≤ scale M B ε:=by unfold scale;linarith
  have hnR:(count M ε:ℝ)*reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR:reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm:0< mesh M B κ ε:=by unfold mesh;positivity
  have hmr:mesh M B κ ε≤ reserve M B ε:=by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm:κ*mesh M B κ ε≤ reserve M B ε:=mesh_cost κ _ hκ hr.le
  have hw:M<width M B ε (count M ε):=by
    have hd:=depth_covers M (amplification ε) hs
    change M<(count M ε:ℝ)*amplification ε/2 at hd
    unfold width
    linarith
  refine ⟨hs,hs1,hse,hr,hm,hmr,hkm,by linarith,hw,?_⟩
  unfold loss
  linarith

lemma reserve_cost (M B ε c:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)
    (hc:c≤ scale M B ε):c*reserve M B ε≤ε/1000000:=by
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hh:=mul_le_mul_of_nonneg_right hc hr.le
  nlinarith

theorem one_time_losses (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (df es d theta other A:ℝ)(hdf:df≤ reserve M B ε)(hes:es≤ reserve M B ε)
    (hd:d≤ reserve M B ε)(ht:theta≤ reserve M B ε)(ho:other≤ reserve M B ε)
    (he0:0≤es)(hA:A≤M):
    exceptional (amplification ε) df es d B theta≤ε/1000 ∧
      diagonal (amplification ε) d other es A≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hs:=hb.2.2.1
  have hr:=hb.2.2.2.1
  have hx:=reserve_cost M B ε (10*B+7) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have hy:=reserve_cost M B ε (M+2) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have htheta:=mul_le_mul_of_nonneg_left ht (show 0≤2*(5*B+1) by positivity)
  have hmul:es*A≤ reserve M B ε*M:=
    (mul_le_mul_of_nonneg_left hA he0).trans (mul_le_mul_of_nonneg_right hes hM)
  constructor
  · unfold exceptional
    nlinarith
  · unfold diagonal
    nlinarith

lemma loss_succ (M B ε:ℝ)(k:ℕ):
    loss M B ε (k+1)=loss M B ε k+64*reserve M B ε:=by
  simp only [loss,Nat.cast_add,Nat.cast_one]
  ring

lemma next_paid_loss (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other:ℝ)
    (her:er≤ reserve M B ε)(hd:d≤ reserve M B ε)(he:e≤ reserve M B ε)
    (hd1:d1≤ reserve M B ε)(hd2:d2≤ reserve M B ε)(ht:theta≤ reserve M B ε)
    (ho:other≤50*reserve M B ε):
    loss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+other≤
      loss M B ε (k+1):=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hm:=hb.2.2.2.2.2.2.1
  rw [loss_succ]
  unfold edge
  linarith

end SevenEighths.CenteredMomentEnergyWidthSchedule

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.StageReserveSchedule
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

lemma stageLoss_pos (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<stageLoss M B ε k:=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  unfold stageLoss loss
  positivity

lemma successor_with_references (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other highReflection zeroReflection:ℝ)
    (her:er≤ reserve M B ε)(hd:d≤ reserve M B ε)(he:e≤ reserve M B ε)
    (hd1:d1≤ reserve M B ε)(hd2:d2≤ reserve M B ε)(ht:theta≤ reserve M B ε)
    (ho:other≤48*reserve M B ε)
    (hhigh:highReflection≤ reserve M B ε)(hzero:zeroReflection≤ reserve M B ε):
    stageLoss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+
      other+highReflection+zeroReflection≤ stageLoss M B ε (k+1):=by
  have hh:=next_paid_loss M B κ ε hM hB hκ hε k er d e d1 d2 theta
    (other+highReflection+zeroReflection) her hd he hd1 hd2 ht (by linarith)
  unfold stageLoss
  linarith

lemma one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(sourceLoss extra:ℝ)(hsource:sourceLoss≤ε/1000)
    (hextra:extra≤50*reserve M B ε):
    sourceLoss+extra≤ stageLoss M B ε (k+1):=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have hk:0≤(k:ℝ):=Nat.cast_nonneg _
  simp only [stageLoss,loss,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma actual_one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(df es d theta other A extra:ℝ)
    (hdf:df≤ reserve M B ε)(hes:es≤ reserve M B ε)(hd:d≤ reserve M B ε)
    (ht:theta≤ reserve M B ε)(ho:other≤ reserve M B ε)(he0:0≤es)(hA:A≤M)
    (hextra:extra≤50*reserve M B ε):
    CenteredMomentSuccessorPaidParameters.exceptional (amplification ε) df es d B theta+extra≤
      stageLoss M B ε (k+1) ∧
    CenteredMomentSuccessorPaidParameters.diagonal (amplification ε) d other es A+extra≤
      stageLoss M B ε (k+1):=by
  have hh:=one_time_losses M B κ ε hM hB hκ hε df es d theta other A hdf hes hd ht ho he0 hA
  exact ⟨one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.1 hextra,
    one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.2 hextra⟩

end SevenEighths.CenteredMomentEnergyStageReserveSchedule

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstStageLossBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentSuccessorPaidParameters
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

theorem literal_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(ell epsSrc epsMask deltaSrc thetaSrc deltaAmp reserveAmp thetaSource thetaClip
      er primeLoss physicalLoss highReflection zeroReflection saving:ℝ)
    (hell:ell≤ stageLoss M Bcap ε k)
    (he0:0≤epsSrc)(he:epsSrc≤ reserve M Bcap ε)
    (hemask:(Bcap+Bcap)*epsMask≤ reserve M Bcap ε)
    (hdsrc:deltaSrc≤ reserve M Bcap ε)(htsrc:thetaSrc≤ reserve M Bcap ε)
    (hda:0≤deltaAmp)(hra:0≤ reserveAmp)(hts:0≤thetaSource)(htc:0≤thetaClip)
    (hsmall:deltaAmp+reserveAmp+thetaSource≤ reserve M Bcap ε)
    (hclip:thetaClip≤ reserve M Bcap ε)(her:er≤ reserve M Bcap ε)
    (hcommon:epsSrc*Bcommon≤ reserve M Bcap ε)
    (hprime:primeLoss≤ reserve M Bcap ε)(hphysical:physicalLoss≤ reserve M Bcap ε)
    (hhigh:highReflection≤ reserve M Bcap ε)(hzero:zeroReflection≤ reserve M Bcap ε)
    (hsaving:2*amplification ε+deltaAmp+reserveAmp≤ saving):
    ∀j:Fin 4,
      losses epsSrc deltaSrc thetaSrc Bcap j+
        lossVector (amplification ε) deltaAmp reserveAmp
          (sourcePaid Bcap epsMask ell er deltaAmp reserveAmp thetaSource thetaClip κ (mesh M Bcap κ ε))
          epsSrc M saving j+
        epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      stageLoss M Bcap ε (k+1):=by
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< reserve M Bcap ε:=hb.2.2.2.1
  have hs:0≤amplification ε:=hb.1.le
  have hother:epsSrc*Bcommon+primeLoss+physicalLoss≤48*reserve M Bcap ε:=by linarith
  have hextra:epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      50*reserve M Bcap ε:=by linarith
  have hdf:deltaAmp+reserveAmp≤ reserve M Bcap ε:=by linarith
  have hdelta:deltaAmp≤ reserve M Bcap ε:=by linarith
  have hres:reserveAmp≤ reserve M Bcap ε:=by linarith
  have hmain:=successor_with_references M Bcap κ ε hM hB hκ hε k
    er deltaSrc epsSrc (deltaAmp+reserveAmp+thetaSource) ((Bcap+Bcap)*epsMask) thetaClip
    (epsSrc*Bcommon+primeLoss+physicalLoss) highReflection zeroReflection
    her hdsrc he hsmall hemask hclip hother hhigh hzero
  have hone:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaSrc thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdsrc htsrc hres he0 le_rfl hextra
  have hdiag:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaAmp thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdelta htsrc hres he0 le_rfl hextra
  have htail:=one_time_with_new_cost M Bcap κ ε hM hB hκ hε k 0
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection) (by positivity) hextra
  intro j
  fin_cases j <;> simp only [losses,lossVector,Matrix.cons_val,Fin.reduceFinMk]
  · dsimp [sourcePaid,edge] at hmain ⊢
    linarith
  · dsimp [exceptional] at hone
    linarith [hone.1]
  · dsimp [diagonal] at hdiag
    linarith [hdiag.2]
  · linarith

end SevenEighths.CenteredMomentEnergyFirstStageLossBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstDeclaredCapacityLossBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

lemma lossVector_cap (sigma delta reserveAmp paid es M A saving:ℝ)
    (he:0≤es)(hM:0≤M)(hA:0≤A)(j:Fin 4):
    lossVector sigma delta reserveAmp paid es A saving j≤
      lossVector sigma delta reserveAmp paid es M saving j+es*A:=by
  fin_cases j <;> simp only [lossVector,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg he hM,mul_nonneg he hA]

theorem chosen_declared_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ es*A≤ r/4 ∧ es*Bcommon≤ r/4 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
      highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es A (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< r:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:r≤amplification ε/100:=min_le_left _ _
  have hr1:r≤1:=by linarith [hb.2.1]
  have hden:0<4*(Bcommon+A+1):=by positivity
  have hes:0<es:=by dsimp [es];positivity
  have hesle:es≤ r/4:=by
    dsimp [es]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc,mul_nonneg hr.le hA]
  have hescap:es*A≤ r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc]
  have hescommon:es*Bcommon≤ r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hA]
  have hemscale:(Bcap+Bcap)*(r/(Bcap+Bcap+1))≤ r:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,by linarith,by positivity,hescap,hescommon,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hh:=literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    es (r/(Bcap+Bcap+1)) (r/4) (r/4) (r/4) (r/4) (r/4) (r/4)
    (r/4) (r/4) (r/4+es*A) highReflection zeroReflection (2*amplification ε+1)
    hell hes.le (by dsimp [r] at *;linarith) hemscale
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    hhigh hzero (by linarith)
  have hc:=lossVector_cap (amplification ε) (r/4) (r/4)
    (sourcePaid Bcap (r/(Bcap+Bcap+1)) ell (r/4) (r/4) (r/4) (r/4) (r/4)
      κ (mesh M Bcap κ ε)) es M A (2*amplification ε+1) hes.le hM hA j
  have hj:=hh j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_
  linarith only [hj,hc]

end SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstActualFrequencyBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSectorLocalization

theorem eventually_frequency_loss (r:ℝ)(hr:0< r):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤ r/4:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by positivity:0< r/8))) 128,
    eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  have hlog:=Real.logb_le_logb_of_le hZ (by norm_num:(0:ℝ)<128) hpow
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hlog
  refine ⟨hZ,frequencyLoss_nonneg Z 32 (r/4) hZ (by norm_num) (by positivity),?_⟩
  unfold frequencyLoss
  norm_num only [show (4:ℝ)*32=128 by norm_num]
  linarith only [hlog]

lemma paid_frequency_mono
    (sigma delta delta' reserveAmp Bcap emask ell er thetaSource thetaClip κ mesh
      es A saving:ℝ)(hd:delta≤delta')(j:Fin 4):
    lossVector sigma delta reserveAmp
      (sourcePaid Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh)
      es A saving j≤
    lossVector sigma delta' reserveAmp
      (sourcePaid Bcap emask ell er delta' reserveAmp thetaSource thetaClip κ mesh)
      es A saving j:=by
  fin_cases j <;>
    simp only [lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    linarith only [hd]

theorem actual_frequency_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ 0< r/4 ∧ r/4≤amplification ε/4 ∧
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤ r/4 ∧
      ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
        highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
        losses es (r/4) (r/4) Bcap j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            (sourcePaid Bcap em ell (r/4) (frequencyLoss Z 32 (r/4))
              (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
            es A (2*amplification ε+1) j+
          es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  let em:=r/(Bcap+Bcap+1)
  obtain ⟨hes,hes1,hem,_,_,hbudget⟩:=chosen_declared_four_budget M A Bcap Bcommon κ ε
    hM hA hB hBc hκ hε
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< r:=hb.2.2.2.1
  have hrs:r≤amplification ε/100:=min_le_left _ _
  refine ⟨hes,hes1,hem,by positivity,by linarith [hb.1],?_⟩
  filter_upwards [eventually_frequency_loss r hr] with Z hZ
  refine ⟨hZ.1,hZ.2.1,hZ.2.2,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hfixed:=hbudget k ell highReflection zeroReflection hell hhigh hzero j
  have hmono:=paid_frequency_mono (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
    (r/4) Bcap em ell (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε) es A
    (2*amplification ε+1) hZ.2.2 j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_ at hfixed ⊢
  linarith only [hfixed,hmono]

end SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.Reindex
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyReindex
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

variable {α β:Type*}[Fintype α][Fintype β]

lemma positive_reindex (e:α≃β)(η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (pool∘e) (coeff∘e) (P∘e) t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ pool coeff P t X₁ X₂:=by
  unfold positiveSlotRow
  simp only [Function.comp_apply,e.prod_comp P,
    e.prod_comp (fun i=>CenteredMomentHeckeSlots.rowSlot η m A z (pool i) (coeff i) t)]

theorem energy_reindex (e:α≃β)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (pool∘e) (coeff∘e) (P∘e) X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_reindex]

end SevenEighths.CenteredMomentEnergyReindex

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyInputParentCapacity
open CenteredMomentEnergyBands CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
variable {ι:Type*} [Fintype ι]

lemma raw_log_le_length (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    Real.logb Z X≤length Z X :=
  Real.logb_le_logb_of_le hZ hX (le_max_right _ _)

end SevenEighths.CenteredMomentEnergyInputParentCapacity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondInputCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonHeightEnvelope
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.instDecidableEq_definitions
lemma lowerFactor_pos (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower):
    0<lowerFactor N slotLower plainLower:=by unfold lowerFactor;positivity

end SevenEighths.CenteredMomentSecondInputCapacitySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.StageMargins
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageMargins
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule

lemma physicalLoss_eq (M B ε:ℝ)(k:ℕ):
    physicalLoss M B ε k=stageLoss M B ε k+62*reserve M B ε:=by
  unfold physicalLoss stageLoss
  rw [loss_succ]
  ring
lemma reflected_then_zero (M B ε:ℝ)(k:ℕ):
    reflectedLoss M B ε k+reserve M B ε=stageLoss M B ε (k+1):=by
  unfold reflectedLoss physicalLoss
  ring
lemma margins (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<physicalLoss M B ε k ∧
    stageLoss M B ε k≤physicalLoss M B ε k ∧
    reserve M B ε/4≤physicalLoss M B ε k ∧
    physicalLoss M B ε k≤ reflectedLoss M B ε k ∧
    reflectedLoss M B ε k≤ stageLoss M B ε (k+1):=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have he:=stageLoss_pos M B κ ε hM hB hκ hε k
  have hp:=physicalLoss_eq M B ε k
  have hf:=reflected_then_zero M B ε k
  unfold reflectedLoss at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyStageMargins

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstSourceParameters
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤Bschedule)(ht:0≤ts)(hem:0≤em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤M)(hA:0≤A)(hB:0≤B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0<sigma ∧ sigma≤1 ∧ 0< r/4 ∧ r/4≤ sigma/4 ∧ r/4≤1 ∧
      0<sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0< maskEpsilon M B ε ∧ 0< mesh M B κ ε ∧
      mesh M B κ ε≤ sigma/12 ∧ 0≤ sigma/12 ∧ sigma/12<sigma/6 ∧
      0<2*sigma+1 ∧ 0≤A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0<sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤ reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(_hP:0≤P)(hB:0≤B)(hready:readyBudget A P≤B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤ stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤ columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤_ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

end SevenEighths.CenteredMomentEnergyFirstSourceParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.LowBandSubtype
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLowBandSubtype
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentEnergyReferenceLowBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentEnergyReindex
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [Fintype β] in
theorem positiveLowAt_embedding (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=β) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  let E : T≃T.map e := Finset.equivMap e T
  let θ' : T.map e→RayQuotient.Characters M H := θ∘E.symm
  let w' : T.map e→ℝ := w∘E.symm
  let σ' : T.map e→ℝ := σ∘E.symm
  let v' : T.map e→ℝ := v∘E.symm
  have hsum : (∑i:T.map e,w' i)=∑i:T,w i := E.symm.sum_comp w
  have hh := h (T.map e) θ' w' σ' v' t height
    (fun i=>hw (E.symm i)) (fun i=>hwL (E.symm i))
    (fun i=>hσlo (E.symm i)) (fun i=>hσhi (E.symm i))
    hheight (fun i=>hv (E.symm i)) s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
    (by rw [hsum];exact hcapacity) (by rw [hsum];exact hlow)
  have he := energy_reindex E s.character s.mask 1 (p.profile 0) (p.profile 1)
    (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
    (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
    (fun i:T.map e=>Z^(w' i)) t X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have he' : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>primePool M H bslot (Z^(w i)))
      (fun (i:T) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:T=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
      (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
      (fun i:T.map e=>Z^(w' i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
    simpa only [Function.comp_def,θ',w',σ',v',Equiv.symm_apply_apply] using he
  exact he'.le.trans hh

omit [Fintype α] in
theorem positiveLowAt_subtype (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=T) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveLowAt_embedding M H hH ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h

end SevenEighths.CenteredMomentEnergyLowBandSubtype

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceInputTailUniform CenteredMomentFirstReferenceEnergy
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
lemma lower_product (s:Input ι)(N:ℕ)(a:ℝ)(ha:0<a)
    (hN:Fintype.card ι≤N)(hlo:∀i,a≤ s.lo i):
    (min 1 a)^N≤∏i,s.lo i := by
  have hm:0≤ min 1 a:=le_min zero_le_one ha.le
  calc
    _≤(min 1 a)^(Fintype.card ι):=pow_le_pow_of_le_one hm (min_le_left _ _) hN
    _=∏_i:ι,min 1 a:=by simp
    _≤∏i,s.lo i:=Finset.prod_le_prod (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlo i))

local notation "O"=>HeckeFamily.O
end SevenEighths.CenteredMomentEnergyOriginalProfileControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalSourceAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyInputParentCapacity CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSourceRow CenteredMomentRetainedEnergy
open CenteredMomentSourceInputTailUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_1 : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum
theorem radial_admission {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) :
    1 ≤ state.radial.scale ∧ state.radial.scale⁻¹ ≤ 1 ∧
    state.radial.scale⁻¹ ≤ Z^state.width := by
  have hs : 1 ≤ state.radial.scale := by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  have hi := inv_le_one_of_one_le₀ hs
  exact ⟨hs,hi,hi.trans (Real.one_le_rpow state.base_ge_one state.width_nonneg)⟩

theorem original_scale_caps {Z X₁ X₂ M L κ : ℝ} (w : ι → ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hw : ∀ i, 0 ≤ w i) (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ M)
    (hM : M ≤ L) : X₁ ≤ Z^L ∧ X₂ ≤ Z^L := by
  have hn : 0 ≤ 6*κ*(∑ i, w i) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun i _ => hw i))
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor
  · apply (Real.logb_le_iff_le_rpow hZ hX₁).mp
    linarith [length_nonneg Z X₂ hZ]
  · apply (Real.logb_le_iff_le_rpow hZ hX₂).mp
    linarith [length_nonneg Z X₁ hZ]

end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PositiveHighSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource"=>balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_2 : DecidableEq (α⊕Fin 2):=Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPositiveHighSource.instFiniteQuotientOIdeal_solutions
omit [DecidableEq α] in
lemma balanced_matches:
    CenteredMomentAllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

omit [DecidableEq α] in
lemma balanced_volume:
    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hx (X:ℝ):X≤Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=>Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

end SevenEighths.CenteredMomentEnergyPositiveHighSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveHighParameters
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_3 : DecidableEq (α⊕Fin 2):=Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters.instFiniteQuotientOIdeal
lemma actual_width_le (hZ:1<Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

end SevenEighths.CenteredMomentEnergyPositiveHighParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PositiveBalancedAdmission
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_4 : DecidableEq (α⊕Fin 2):=Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission.instFiniteQuotientOIdeal
theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=>le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩

theorem four_upper_scales (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤L) :
    (balancedSource).X₁≤Z^L ∧ (balancedSource).X₂≤Z^L ∧
    (balancedSource).Y₁≤Z^L ∧ (balancedSource).Y₂≤Z^L := by
  have hp:0<Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=>hw i))
  have hxy:X₁*X₂≤volume balancedSource:=by
    change X₁*X₂≤X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤ comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssembly
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_5 : DecidableEq (α⊕Fin 2):=Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPositiveHighAssembly.instFiniteQuotientOIdeal
omit [Fintype α] [DecidableEq α] in
lemma low_restrict (W:ℝ→ℂ)(bslot a b bΦ Bmask L L' Lslot lo hi Mcap d d' κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hZ:1≤Z)(hL:L'≤L)(hd:d≤d')(hC:0≤C)
    (h:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap d κ Z η₀ Q degree S C):
    PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L' Lslot lo hi
      Mcap d' κ Z η₀ Q degree S C:=by
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
  have hscale:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale) hcap hlow
  apply hh.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (by have hh:=diagonalControl_nonneg s.radial.profile;positivity)

end SevenEighths.CenteredMomentEnergyPositiveHighAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyPositiveHighBound CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_6 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPositiveHighSourceBound.instFiniteQuotientOIdeal_solutions
theorem actual_high_stage_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hrho:0< rho)(hε:0<ε)(hMcap:0≤Mcap)(hBmask:0≤Bmask)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(L Lslot κ e emass efinal:ℝ)(η₀:Character)(Q:Ideal O)(K Cphysical:ℝ),
      3/4≤κ→0≤e→0≤K→0≤Cphysical→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
        Lslot lo hi Mcap e κ Z η₀ Q degree S K→
      PhysicalHighAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ emass Z ha Ψ η₀ Q Smass Jmass Cphysical→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap efinal κ Z η₀ Q
        Jout U (Cfixed*(K+Cphysical+1)):=by
  have hfixed (T:Finset α):=actual_high_from_physical (α:=T) M H hH W aslot bslot lo hi
    haslot hWs hW a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε
    hMcap hBmask hbslot hεdiag hξ
  choose Lj hLj hLjcap Ψ hΨs hΨn hj using hfixed
  refine ⟨Ψ,hΨs,hΨn,?_⟩
  intro degree S Jmass Smass
  have hall (T:Finset α):=hj T degree S Jmass Smass
  choose Jj Uj Cj hCj hbound using hall
  let Jout:ℕ:=∑T:Finset α,Jj T
  let U:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  have hJJ (T:Finset α):Jj T≤Jout:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hUU (T:Finset α):Uj T⊆U:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ T,hx⟩
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  have hevent:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro L Lslot κ e emass efinal η₀ Q K Cphysical hκ he hK hCphysical hefinal hmassFinal
    hdiagFinal htailFinal hlow hmass
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hlowT:=CenteredMomentEnergyLowBandSubtype.positiveLowAt_subtype (α:=α) M H hH T
    W bslot a b bΦ Bmask (Mcap+Bmask+rho/100) Lslot lo hi Mcap e κ Z η₀ Q degree S K hlow
  have hlowLj:=low_restrict (α:=T) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
    (Lj T) Lslot lo hi Mcap e e κ Z η₀ Q degree S K hZ1.le (hLjcap T) le_rfl hK hlowT
  have hphys:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo
    hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hh:=(hZ T).2 e emass efinal Lslot κ η₀ Q K Cphysical he hK hCphysical
    hefinal hmassFinal hdiagFinal htailFinal hlowLj θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ state hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcapacity hphys
  have hc:=hCC T
  have hp:=profile_control_mono p (hUU T)
  have hp0:=p.control_nonneg (Uj T)
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  have hpow:=pow_le_pow_right₀ hbase (hJJ T)
  have hd:=diagonalControl_nonneg state.radial.profile
  have hz:0≤Z:=zero_le_one.trans hZ1.le
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PositiveHighPhysical
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyPositiveHighSourceBound
open CenteredMomentEnergyPositiveHighParameters CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_7 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions_r03d442_1 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_positive_high_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (_hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalHighAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0<a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0<lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLphys:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (max Lgoal Mparent) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=>aslot) (fun _=>bslot) (fun _=>hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b)]
    with Z hZZ hfit hclipPow
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlarge
  dsimp only
  intro hfour
  let inp:=balancedInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤N:=Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
  have hm:=balanced_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hu:=four_upper_scales M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ κ (max Lgoal Mparent)
    hZ hw hκ hcapacity (hstate.trans (le_max_right _ _))
  have hp:=fixed_lower_product M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=>le_rfl) (fun _=>le_rfl) (fun _=>rfl) (fun _=>rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl le_rfl hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  rw [ht] at hh
  dsimp only [inp,r] at hh
  have hN1:((1:Ideal O).absNorm:ℝ)=1:=by norm_num
  simpa only [hN1,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyPositiveHighPhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.NaturalHighStage
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalHighStage
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyPositiveHighSourceBound
open CenteredMomentEnergyPositiveHighParameters CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instDecidableEqSumFinOfNatNat_solutions_r03d442_8 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions_r03d442_2 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_high_stage_oai
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hrho:0< rho)(hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(lowDegree:ℕ)(Slow:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤C₀→0≤C₁→0≤Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      CenteredMomentEnergyReferenceLowBands.PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask
        (Mparent+Bmask+rho/100) Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z η₀ Q
        lowDegree Slow Clow→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi rho Mparent
        (reflectedLoss Mglobal B ε k) κ Z η₀ Q J U (C*(C₀+C₁+Clow+1)) := by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hb:0≤b:=zero_le_one.trans hhi
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hr4:0< r/4:=by positivity
  have hs:0<amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
  obtain ⟨Ψ,hΨs,hΨn,hstage⟩:=actual_high_stage_from_physical (α:=α) M H hH
    W hW.continuous aslot bslot lo hi a b bΦ rho r Mparent Bmask (r/4) (r/4)
    (2*amplification ε+1) haslot hWs hbslot ha hlo hhi hbΦ hrho hr hMp hBm hr4 hr4
  obtain ⟨Up,Jp,hphysical⟩:=CenteredMomentEnergyPositiveHighPhysical.actual_positive_high_physical
    (α:=α) M H hH W hW aslot bslot lo hi a b bΦ haslot hWs hbslot ha hb
    Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε k hMg hA hB hBm hMp hMc hL hLs
    hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  obtain ⟨J,U,Cf,hCf,hstageZ⟩:=hstage lowDegree Slow Jp Up
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphysZ⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cf*(Cp+1),by positivity,?_⟩
  filter_upwards [hstageZ,hphysZ] with Z hstageNow hphysicalNow
  refine ⟨hphysicalNow.1,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hzero hpos hlow
  have hp:=hphysicalNow.2 εchild C₀ C₁ hchild hC₀ hC₁ hzero hpos
  have hm:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hmass:0≤Cp*(C₀+C₁+1):=by positivity
  have hh:=hstageNow.2 Lgoal Lslot κ (physicalLoss Mglobal B ε k)
    (physicalLoss Mglobal B ε k) (reflectedLoss Mglobal B ε k) η₀ Q
    Clow (Cp*(C₀+C₁+1)) hκ hm.1.le hClow hmass
    (by exact le_rfl) hm.2.2.2.1 (hm.2.2.1.trans hm.2.2.2.1)
    (by have hpos:=hm.1.le.trans hm.2.2.2.1;linarith only [hpos,hs]) hlow hp
  have hconst:Cf*(Clow+Cp*(C₀+C₁+1)+1)≤(Cf*(Cp+1))*(C₀+C₁+Clow+1):=by
    have hh:0≤Cp*Clow:=mul_nonneg hCp.le hClow
    nlinarith only [mul_nonneg hCf.le hh,mul_nonneg hCf.le hC₀,mul_nonneg hCf.le hC₁]
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge
  apply (hh T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge).trans
  have hd:=diagonalControl_nonneg state.radial.profile
  have hp0:=p.control_nonneg U
  have hz:0≤Z:=zero_le_one.trans hphysicalNow.1.le
  gcongr

end SevenEighths.CenteredMomentEnergyNaturalHighStage

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyNaturalHighStage.actual_high_stage_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyNaturalHighStage.actual_high_stage_oai.{u_1}
