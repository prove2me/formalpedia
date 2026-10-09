-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyCappedLowStage.actual_capped_low
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:36:56.841629+00:00
-- url     : https://prove2.me/submissions/de17f2b8-3e47-4e7c-8dca-ad903c2f171c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalLowPhysical_actual_low_physical
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyPositiveLowSourceControlled_actual_low_stages_from_physical

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

theorem zeroAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b radial mask L Mcap eps Z J S C):
    ZeroAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_rdfbb09_1 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
omit [Fintype α] [DecidableEq α] in
theorem positiveAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

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

lemma width_succ (M B ε:ℝ)(k:ℕ):
    width M B ε (k+1)-amplification ε/2=width M B ε k:=by
  simp only [width,Nat.cast_add,Nat.cast_one]
  ring
lemma loss_succ (M B ε:ℝ)(k:ℕ):
    loss M B ε (k+1)=loss M B ε k+64*reserve M B ε:=by
  simp only [loss,Nat.cast_add,Nat.cast_one]
  ring

lemma child_band (M B ε parent child:ℝ)(k:ℕ)
    (hp:parent≤width M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤width M B ε k:=by
  rw [←width_succ M B ε k]
  linarith

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.Profiles
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

lemma lower_pos (a b:ℝ)(ha:0<a)(n:ℕ):0<lower a b n:=by
  induction n with
  | zero=>exact ha
  | succ n ih=>exact div_pos ih (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.WidthRanges
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

lemma range_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ range M B L n:=by
  induction n with
  | zero=>exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=>simp only [range,step];positivity

lemma range_mono (M B L:ℝ)(hM:0≤M)(hB:0≤B):Monotone (range M B L):=by
  apply monotone_nat_of_le_succ
  intro n
  have hh:=range_nonneg M B L hM hB n
  simp only [range,step]
  linarith

lemma sourceCap_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold sourceCap
  positivity

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.WidthInduction
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

lemma lowerAt_pos (a b M ε:ℝ)(ha:0<a)(k:ℕ):0<lowerAt a b M ε k:=
  CenteredMomentEnergyProfiles.lower_pos a b ha _

lemma child_support (a b M ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lowerAt a b M ε k=lowerAt a b M ε (k+1)/max 1 b:=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lowerAt,he,CenteredMomentEnergyProfiles.lower]

lemma child_length (M B L ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lengthAt M B L ε k=step M B (lengthAt M B L ε (k+1)):=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lengthAt,he,range]

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyWidthInduction

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)

lemma bandWidth_le (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤M:=min_le_left _ _
lemma bandWidth_le_schedule (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤width M B ε k:=min_le_right _ _
lemma bandWidth_nonneg (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)(k:ℕ):
    0≤bandWidth M B ε k:=by
  have hr:0< reserve M B ε:=(bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.1
  have hs:0<amplification ε:=(bounds M B 0 ε hM hB (by norm_num) hε).1
  unfold bandWidth width
  positivity
lemma actual_child_band (M B ε parent child:ℝ)(hε:0<ε)(k:ℕ)
    (hp:parent≤bandWidth M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤bandWidth M B ε k:=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  apply le_min
  · have hh:=hp.trans (bandWidth_le M B ε (k+1));linarith
  · exact child_band M B ε parent child k (hp.trans (bandWidth_le_schedule M B ε (k+1))) hc

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyCappedWidthInduction

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

theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.SourceCapSchedule
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergySourceCapSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyFirstLiveAdmission

lemma count_pos (M ε:ℝ):0<count M ε:=by
  unfold count CenteredMomentFirstSecondLossParameters.depth
  omega
lemma final_range_large (M B L ε:ℝ)(hM:0≤M)(hB:0≤B):
    20≤ range M B L (count M ε):=by
  have hh:=range_mono M B L hM hB (show 1≤ count M ε from count_pos M ε)
  have hm:1≤ max 1 L:=le_max_left _ _
  simp only [range,step] at hh
  linarith
lemma readyBudget_le_schedule (M B L ε A P:ℝ)(hM:0≤M)(hB:0≤B)
    (hA:A≤2*range M B L (count M ε)+M+1)(hP:P≤B):
    readyBudget A P≤finalSourceCap M B L ε:=by
  have hr:=final_range_large M B L ε hM hB
  unfold readyBudget finalSourceCap sourceCap
  linarith

end SevenEighths.CenteredMomentEnergySourceCapSchedule

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CappedRequests
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyCappedRequests
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergySourceCapSchedule

lemma request_bounds (M B L:ℝ)(hM:0≤M)(hB:0≤B)(_hL:0≤L):
    0≤ requestLength M B L ∧ L≤ requestLength M B L ∧ M≤ requestLength M B L:=by
  have hh:=le_max_left L (2*M+B+2)
  have hg:=le_max_right L (2*M+B+2)
  unfold requestLength
  constructor
  · linarith
  constructor <;> linarith

lemma doubled_request (M B L e:ℝ)(hM:0≤M)(hB:0≤B)(hL:0≤L)(he:e≤1):
    2*requestLength M B L+e≤ step M B L:=by
  have hh:max L (2*M+B+2)≤L+2*M+B+2:=by
    apply max_le <;> linarith
  unfold requestLength step
  linarith

lemma previous_admits (M B L ε parent e:ℝ)(hM:0≤M)(hB:0≤B)
    (hp:parent≤M)(he:e≤1)(k:ℕ)(hk:k<count M ε):
    2*max (requestLength M B (lengthAt M B L ε (k+1))) parent+e≤lengthAt M B L ε k:=by
  have hL:=range_nonneg M B L hM hB (remaining M ε (k+1))
  change 0≤lengthAt M B L ε (k+1) at hL
  have hreq:=request_bounds M B (lengthAt M B L ε (k+1)) hM hB hL
  rw [max_eq_left (hp.trans hreq.2.2),child_length M B L ε k hk]
  exact doubled_request M B _ e hM hB hL he

lemma parent_drop (M B ε:ℝ)(hε:0<ε)(k:ℕ):
    bandWidth M B ε (k+1)-amplification ε/2≤bandWidth M B ε k:=
  actual_child_band M B ε _ _ hε k le_rfl le_rfl

end SevenEighths.CenteredMomentEnergyCappedRequests

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroComparison
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroComparison
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentHeckeExpansion CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentSourceRow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentHeckeHeight CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_rdfbb09_1 : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum
lemma smallScale_le_one (b:ℝ):smallScale b≤1:=by
  unfold smallScale
  apply (div_le_iff₀ (by positivity:0<(2:ℝ)*max 1 b)).mpr
  linarith [le_max_left (1:ℝ) b]

end SevenEighths.CenteredMomentEnergyZeroComparison

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

local instance instDecidableEqSumFinOfNatNat_solutions_rdfbb09_2 : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum
lemma lowerProduct_pos (N : ℕ) {aslot a : ℝ} (hs : 0 < aslot) (ha : 0 < a) :
    0 < lowerProduct N aslot a := by unfold lowerProduct; positivity

section Source
variable (Q : Ideal O) [NeZero Q]
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ)
variable (p : Profiles a b) (ha : 0 < a) (t X₁ X₂ : ℝ)
variable (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "s" => sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
local notation "s₀" => zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂

local instance instDecidableEqSumFinOfNatNat_solutions_rdfbb09_3 : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum
theorem both_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s η₀ θ w σ freq W bslot Z ∧
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s₀ η₀ θ w σ freq W bslot Z := by
  constructor <;> constructor <;> intros <;> rfl

lemma volume_log (hZ : 1 < Z) :
    Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i ∧
    Real.logb Z (volume s₀) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i := by
  have hh := input_volume_log s Z
  change Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ +
    ∑ i, Real.logb Z (Z^(w i)) at hh
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  exact ⟨hh,hh⟩

theorem low_admission (hZ : 1 < Z)
    (hlow : length Z X₁ + length Z X₂ + ∑ i, w i ≤ 5*state.width/6) :
    Real.logb Z (volume s) ≤ 5*state.width/6 ∧
    Real.logb Z (volume s₀) ≤ 5*state.width/6 := by
  have hv := volume_log Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂ hZ
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor <;> linarith [hv.1,hv.2]

theorem lower_product_admission (N : ℕ) (hN : Fintype.card ι ≤ N) :
    0 < lowerProduct N aslot a ∧
    lowerProduct N aslot a ≤ (∏ i, (s).lo i)*a*a ∧
    lowerProduct N aslot a ≤ (∏ i, (s₀).lo i)*a*a := by
  have hh := lower_product s N aslot haslot hN (fun _ => le_rfl)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le
  exact ⟨lowerProduct_pos N haslot ha,hb,hb⟩

end Source

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

theorem eventually_scale_admission (b L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    ∀ (Q : Ideal O) [NeZero Q] (H : Subgroup (O ⧸ Q)ˣ)
      (hH : RayOrthogonality.globalUnits Q ≤ H) (η₀ : Character)
      (θ : ι → RayQuotient.Characters Q H),
    ∀ (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
      (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot),
    ∀ (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi),
    ∀ (Bmask bΦ a : ℝ) (state : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (ha : 0 < a) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (κ : ℝ),
    (∀ i, 0 ≤ w i) → 1/6 ≤ κ → state.width ≤ L →
    length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width →
    let s := sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    let s₀ := zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    (s).X₁ ≤ Z^L ∧ (s).X₂ ≤ Z^L ∧ (s).Y₁ ≤ Z^L ∧ (s).Y₂ ≤ Z^L ∧
    (s₀).X₁ ≤ Z^L ∧ (s₀).X₂ ≤ Z^L ∧
    (s₀).Y₁ ≤ Z^(2*L+ε) ∧ (s₀).Y₂ ≤ Z^(2*L+ε) := by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1 : ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ Q _ H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ hw hκ hM hcap
  dsimp only
  have hx := original_scale_caps w hZ hX₁ hX₂ hw hκ hcap hM
  refine ⟨hx.1,hx.2,hx.1,hx.2,hx.1,hx.2,?_,?_⟩
  · exact (smallScale_le_one b).trans (Real.one_le_rpow hZ.le (by positivity))
  · change X₁*X₂/smallScale b ≤ _
    have hp : X₁*X₂ ≤ Z^(2*L) := by
      have hh := mul_le_mul hx.1 hx.2 hX₂.le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) L).le
      rw [←Real.rpow_add (zero_lt_one.trans hZ)] at hh
      simpa only [two_mul] using hh
    unfold smallScale
    rw [div_div_eq_mul_div,div_one]
    exact (mul_le_mul hp hc (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le).trans_eq
        (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

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

local instance instDecidableEqSumFinOfNatNat_solutions_rdfbb09_4 : DecidableEq (α⊕Fin 2):=Classical.decEq _
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.NaturalLowPhysical
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParameters CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instDecidableEqSumFinOfNatNat_solutions_rdfbb09_5 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions_rdfbb09_2 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_natural_low_physical
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
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
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
  have hLbase:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0≤2*max Lgoal Mparent+r/4:=by positivity
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalLowPhysical.actual_low_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (2*max Lgoal Mparent+r/4) hLphys degree S haslot hWs hW hMc hLs hr
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
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlow
  let inp:=zeroSourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤N:=Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
  have hm:=(both_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂).2
  have hu:=hscale.2 T M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ
    hw hκsmall (hstate.trans (le_max_right _ _)) hcapacity
  have hg:max Lgoal Mparent≤2*max Lgoal Mparent+r/4:=by linarith
  have hu1:inp.X₁≤Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hu2:inp.X₂≤Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hp:=lower_product_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hlowV:Real.logb Z (volume inp)≤5*state.width/6:=
    (low_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ hZ hlow).2
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=>le_rfl) (fun _=>le_rfl) (fun _=>rfl) (fun _=>rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu1 hu2 hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl hlowV (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  have hv0:volume inp = volume (sourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂):=rfl
  rw [ht,hv0] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyNaturalLowPhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.StageMonotonicity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyStageMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceBound CenteredMomentEnergyZeroGrowth
local notation "O"=>HeckeFamily.O

theorem zeroLowAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroLowAt Q a b radial mask L Mcap eps Z J S C):
    ZeroLowAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hlow
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hlow
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_rdfbb09_3 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
omit [Fintype α] [DecidableEq α] in
theorem positiveLowAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveLowAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveLowAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity hlow
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyStageMonotonicity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.NaturalLowStage
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowStage
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParameters CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyNaturalLowPhysical CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyBandMonotonicity

local instance instDecidableEqSumFinOfNatNat_solutions_rdfbb09_6 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions_rdfbb09_4 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_low_from_bands
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hΦ:2≤bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot κ ε:ℝ)(k:ℕ)
    (hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uout:Finset (ℕ×ℕ),∃Jout:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi Mparent
        (physicalLoss Mglobal B ε k) κ Z η₀ Q Jout Uout (C*(C₀+C₁+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (physicalLoss Mglobal B ε k) Z Jout Uout (C*(C₀+C₁+1)) :=by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hmarg:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hbΦ:0<bΦ:=by linarith
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hentry⟩:=
    CenteredMomentEnergyPositiveLowSourceControlled.actual_low_stages_from_physical (α:=α)
      M H hH W hW.continuous aslot bslot lo hi a b bΦ Mparent (r/4) (r/4)
      (2*amplification ε+1) haslot hWs hbslot ha hb hbΦ hMp (by positivity) (by positivity)
  obtain ⟨U,J,hphysical⟩:=actual_natural_low_physical (α:=α) M H hH W hW aslot bslot lo hi a b bΦ
    haslot hWs hbslot ha hb Mglobal A B Bmask Mparent Mchild Lgoal Lslot Mchild κ ε k
    hMg hA hB hBm hMp hMc hL hLs hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  let Umerge:=S∪U
  let Jmerge:=degree+J
  have hS:S⊆Umerge:=Finset.subset_union_left
  have hU:U⊆Umerge:=Finset.subset_union_right
  have hdeg:degree≤Jmerge:=Nat.le_add_right _ _
  have hJ:J≤Jmerge:=Nat.le_add_left _ _
  have halower:a/max 1 b≤a:=by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    nlinarith [le_max_left (1:ℝ) b]
  have hlen:Lgoal≤2*max Lgoal Mparent+r/4:=by
    have hh:=le_max_left Lgoal Mparent
    linarith
  refine ⟨insert (0,0) Umerge,Jmerge,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphys⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let Cout:=Cfixed*(Cp+1)+1
  have hCout:0<Cout:=by dsimp [Cout];positivity
  refine ⟨Cout,hCout,?_⟩
  filter_upwards [hentry,hphys] with Z he hp
  refine ⟨hp.1,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
  have hzsmall:=zeroAt_transport (internalQ Q η₀)
    (a/max 1 b) b bΦ Bmask _ Mchild εchild Z
    (a/max 1 b) b 2 0 _ Mchild εchild degree degree S S C₀ C₀ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₀ le_rfl hzero
  have hpsmall:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    (a/max 1 b) b 2 0 _ Mchild εchild η₀ Q degree degree S S C₁ C₁ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hpos
  have hold:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    a b bΦ Bmask Lgoal Mchild (physicalLoss Mglobal B ε k) η₀ Q
    degree Jmerge S Umerge C₁ C₁ hp.1.le halower le_rfl le_rfl le_rfl hlen le_rfl
    (hell.trans hmarg.2.1) hdeg hS hC₁ le_rfl hpos
  have hm:=hp.2 εchild C₀ C₁ hell hC₀ hC₁ hzsmall hpsmall
  have hm':PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
      a b bΦ Bmask Lgoal Lslot Mchild Mparent κ (r/4) (physicalLoss Mglobal B ε k)
      Z ha Ψ η₀ Q Umerge Jmerge (Cp*(C₀+C₁+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hm T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤Z:=zero_le_one.trans hp.1.le
    have hcontrol:=profile_control_mono p hU
    have hc0:=p.control_nonneg U
    have hheight1:1≤1+|t|+height:=by linarith [abs_nonneg t]
    apply hh.trans
    gcongr
  have hsave:-(2*amplification ε+1)≤physicalLoss Mglobal B ε k:=by
    have hs:0<amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
    linarith [hmarg.1]
  have hout:=he.2 Bmask Lgoal Lslot Mchild κ (physicalLoss Mglobal B ε k) η₀ Q Umerge Jmerge
    (Cp*(C₀+C₁+1)) C₁ hκsmall (by positivity) hC₁ hmarg.2.2.1 hsave hold hm'
  have hC:Cfixed*(Cp*(C₀+C₁+1)+1)+C₁≤Cout*(C₀+C₁+1):=by
    dsimp [Cout]
    nlinarith [mul_nonneg hCfixed.le hC₀,mul_nonneg hCfixed.le hC₁]
  constructor
  · exact CenteredMomentEnergyStageMonotonicity.positiveLowAt_transport (α:=α) M H hH W bslot
      a b bΦ Bmask Lgoal Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) η₀ Q Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.1
  · exact CenteredMomentEnergyStageMonotonicity.zeroLowAt_transport (internalQ Q η₀)
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.2

end SevenEighths.CenteredMomentEnergyNaturalLowStage

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CappedLowStage
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedLowStage
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyCappedRequests CenteredMomentEnergySourceCapSchedule
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_rdfbb09_5 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_capped_low_oai
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hW:ContDiff ℝ ∞ W)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hbslot:0≤bslot)
    (ha:0<a)(hb:0≤b)(hrad:2≤ radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(k:ℕ)(hk:k<count Mcap ε)
    (hold:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q J U C ∧
        ZeroLowAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z J U C :=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Ag:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let Lreq:=requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1))
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hRange:=range_nonneg Mcap Bmask L hMcap hmask (count Mcap ε)
  have hAg:0≤Ag:=by dsimp [Ag];positivity
  have hMp:0≤Mp:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε (k+1)
  have hMc:0≤Mc:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε k
  have hMpCap:Mp≤Mcap:=bandWidth_le Mcap Bs ε (k+1)
  have hMpAg:Mp≤Ag:=by dsimp [Ag];linarith
  have hLnext:0≤lengthAt Mcap Bmask L ε (k+1):=
    range_nonneg Mcap Bmask L hMcap hmask _
  have hLreq:0≤Lreq:=(request_bounds Mcap Bmask _ hMcap hmask hLnext).1
  have hκ0:0≤κ:=by linarith
  have hbounds:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have hmesh:0≤fineMesh Mcap Bmask L κ ε:=hbounds.2.2.2.2.1.le
  have hr:0< reserve Mcap Bs ε:=hbounds.2.2.2.1
  have hr4:reserve Mcap Bs ε/4≤1:=by
    have hh:reserve Mcap Bs ε≤amplification ε/100:=min_le_left _ _
    have hs:=hbounds.2.1
    linarith
  have hready:CenteredMomentEnergyFirstLiveAdmission.readyBudget Ag Bmask≤Bs:=
    readyBudget_le_schedule Mcap Bmask L ε Ag Bmask hMcap hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤Mc:=parent_drop Mcap Bs ε hε k
  have hlength:2*max Lreq Mp+reserve Mcap Bs ε/4≤lengthAt Mcap Bmask L ε k:=
    previous_admits Mcap Bmask L ε Mp (reserve Mcap Bs ε/4) hMcap hmask hMpCap hr4 k hk
  have hsupport:=child_support a b Mcap ε k hk
  obtain ⟨degree,S,hold⟩:=hold
  obtain ⟨U,J,hstage⟩:=CenteredMomentEnergyNaturalLowStage.actual_low_from_bands
    (α:=α) M H hH W hW aslot bslot lo hi (lowerAt a b Mcap ε (k+1)) b radial
    haslot hWs hbslot (lowerAt_pos a b Mcap ε ha (k+1)) hb hrad
    Mcap Ag Bs Bmask Mp Mc Lreq (fineMesh Mcap Bmask L κ ε) κ ε k
    hMcap hAg hBs hmask hMp hMc hLreq hmesh hMpAg hready hκ hbeta hκbeta hε
    le_rfl hdrop degree S
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,Cp,hCz,hCp,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cs,hCs,hstage⟩:=hstage η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cs*(Cz+Cp+1),by positivity,?_⟩
  filter_upwards [hold,hstage] with Z hold hs
  have hz:=hold.2.1
  have hp:=hold.2.2
  rw [hsupport] at hz hp
  have hz':ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) Mc (stageLoss Mcap Bs ε k) Z degree S Cz:=
    zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl
      le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz
  have hp':PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀ Q degree S Cp:=
    positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cp Cp hold.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hp
  exact ⟨hs.1,hs.2 (stageLoss Mcap Bs ε k) Cz Cp le_rfl hCz.le hCp.le hz' hp'⟩

end SevenEighths.CenteredMomentEnergyCappedLowStage

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyCappedLowStage.actual_capped_low_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyCappedLowStage.actual_capped_low_oai.{u_1}
