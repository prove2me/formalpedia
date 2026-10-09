-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyNaturalZeroStage.actual_zero_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:33:14.294512+00:00
-- url     : https://prove2.me/submissions/7bb78fad-ec3f-4a4e-a1a4-ed1785d2511f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalHighPhysical_actual_high_physical
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroGrowthContourBounded_zero_from_growth_additional_loss_bounded
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroGrowthHighBound_actual_high_from_physical

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

local instance instFiniteQuotientOIdeal_solutions_r1a5a6d_1 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputReindex
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalChildEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]

local instance instDecidableEq_solutions_r1a5a6d_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance instDecidableEqSumFinOfNatNat_solutions_r1a5a6d_1 : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputReindex.instDecidableEqSumFinOfNatNat_solutions_1
omit [Fintype α] [Fintype β] in
lemma tupleMap_apply (e : α≃β) (v : Tuple α) (j : β⊕Fin 2) :
    tupleMap e v j = v ((e.sumCongr (Equiv.refl (Fin 2))).symm j) := rfl

lemma tupleMap_product (e : α≃β) (v : Tuple α) :
    finiteTupleProduct (tupleMap e v)=finiteTupleProduct v :=
  (e.sumCongr (Equiv.refl (Fin 2))).symm.prod_comp v

lemma pools_map (e : α≃β) (s : Input α) :
    (Fintype.piFinset s.pools).image (tupleMap e) = Fintype.piFinset (reindex e s).pools := by
  ext v
  simp only [Finset.mem_image,Fintype.mem_piFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩ j
    cases j with
    | inl i => exact hw (Sum.inl (e.symm i))
    | inr i => exact hw (Sum.inr i)
  · intro hv
    refine ⟨(tupleMap e).symm v,?_,(tupleMap e).apply_symm_apply v⟩
    intro j
    cases j with
    | inl i => simpa [tupleMap,Input.pools,reindex] using hv (Sum.inl (e i))
    | inr i => exact hv (Sum.inr i)

lemma profile_map (e : α≃β) (s : Input α) (R seed : Ideal O) (v : Tuple α) :
    (original (reindex e s) R seed).profile (tupleMap e v) =
      (original s R seed).profile v := by
  simp only [OriginalData.profile,original,reindex,profileCoefficient,tupleMap_product,
    tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.refl_symm,
    Equiv.refl_apply,Sum.map_inl,Sum.map_inr]
  congr 3
  exact e.symm.prod_comp (fun i=>s.ν i (v (Sum.inl i))*
    s.W i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/s.P i))

lemma coefficient_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).beta=(original s R seed).beta := by
  funext I
  unfold OriginalData.beta finiteColumnCoefficient
  change (∑v∈(Fintype.piFinset (reindex e s).pools).filter (fun v=>finiteTupleProduct v=I),
    (original (reindex e s) R seed).profile v)=_
  rw [←pools_map,Finset.filter_image]
  rw [Finset.sum_image (fun v _ w _ h => (tupleMap e).injective h)]
  simp only [tupleMap_product,profile_map]
  rfl

lemma volume_map (e : α≃β) (s : Input α) : volume (reindex e s)=volume s := by
  simp only [volume,reindex,e.symm.prod_comp]

lemma sourceRadius_map (e : α≃β) (s : Input α) :
    CenteredMomentOriginalCommonHarmonic.sourceRadius (reindex e s)=
      CenteredMomentOriginalCommonHarmonic.sourceRadius s := by
  simp only [CenteredMomentOriginalCommonHarmonic.sourceRadius,reindex,e.symm.prod_comp]

end SevenEighths.CenteredMomentSourceInputReindex

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
open CenteredMomentEnergyOriginalSource
open CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSourceRow CenteredMomentRetainedEnergy
open CenteredMomentSourceInputTailUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEqSumFinOfNatNat_solutions_r1a5a6d_2 : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum
theorem radial_admission {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) :
    1 ≤ state.radial.scale ∧ state.radial.scale⁻¹ ≤ 1 ∧
    state.radial.scale⁻¹ ≤ Z^state.width := by
  have hs : 1 ≤ state.radial.scale := by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  have hi := inv_le_one_of_one_le₀ hs
  exact ⟨hs,hi,hi.trans (Real.one_le_rpow state.base_ge_one state.width_nonneg)⟩

end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
local notation "O"=>HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry

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
open CenteredMomentEnergyPositiveHighSource
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

local instance instDecidableEqSumFinOfNatNat_solutions_r1a5a6d_3 : DecidableEq (α⊕Fin 2):=Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters.instFiniteQuotientOIdeal
lemma actual_width_le (hZ:1<Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

lemma actual_conductor_scale (hZ:1<Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

end SevenEighths.CenteredMomentEnergyPositiveHighParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowth
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowth
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands QuadraticInitialBound
local notation "O" => HeckeFamily.O

lemma zeroGrowth_of_zeroAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (h : ZeroAt Q a b bΦ Bmask L M ε Z degree S C) :
    ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C := by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  apply (h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂).trans
  have he : s.width + ε ≤ max s.width (length Z X₁ + length Z X₂) + ε := by
    linarith [le_max_left s.width (length Z X₁ + length Z X₂)]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one he)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC
    (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _)

end SevenEighths.CenteredMomentEnergyZeroGrowth

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

end SevenEighths.CenteredMomentEnergyStageMonotonicity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysical
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalSource
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r1a5a6d_4 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
lemma balanced_volume {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    CenteredMomentAmplificationChildInput.volume (balancedInput s p ha t X₁ X₂ hX₁ hX₂)=X₁*X₂:=by
  simp only [CenteredMomentAmplificationChildInput.volume,
    balancedInput,naturalInput,completeInput,naturalData,Finset.univ_eq_empty,Finset.prod_empty,mul_one]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroBalancedDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedDictionary
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyNaturalInputMatches
open CenteredMomentAmplificationChildInput CenteredMomentFirstSourceReduction
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "zeroInput"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

variable (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)(w σ freq:Fin 0→ℝ)

local notation "positiveInput"=>positiveEmptyInput M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyZeroBalancedDictionary.instFiniteQuotientOIdeal_solutions
theorem declared_capacity (hZ:1<Z):
    let Mdecl:=max s.width (length Z X₁+length Z X₂);
    Real.logb Z (volume zeroInput)≤Mdecl ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width ∧
    volume zeroInput≤Z^Mdecl:=by
  have hlog (X:ℝ)(hX:0<X):Real.logb Z X≤length Z X:=by
    rw [CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX]
    exact le_max_right _ _
  have hV:Real.logb Z (volume zeroInput)≤length Z X₁+length Z X₂:=by
    rw [CenteredMomentEnergyZeroReferencePhysical.balanced_volume,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact add_le_add (hlog X₁ hX₁) (hlog X₂ hX₂)
  have hdecl:=hV.trans (le_max_right s.width (length Z X₁+length Z X₂))
  refine ⟨hdecl,CenteredMomentEnergyPositiveHighParameters.actual_width_le s hZ,
    CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos zeroInput)).mp hdecl

lemma declared_capacity_upper (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal):
    max s.width (length Z X₁+length Z X₂)≤ max Mcap (2*Lgoal):=by
  have hlen (X:ℝ)(hcap:X≤Z^Lgoal):length Z X≤Lgoal:=by
    unfold length
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mpr
      (max_le (Real.one_le_rpow hZ.le hL) hcap)
  exact max_le_max hs (by linarith [hlen X₁ hc₁,hlen X₂ hc₂])

end SevenEighths.CenteredMomentEnergyZeroBalancedDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroBalancedAdmission
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedAdmission
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyReferenceState CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceInputTailUniform
open CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "inp"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

theorem four_upper_scales (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    (inp).X₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).X₂≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₂≤Z^(max Mcap (2*Lgoal)) := by
  have hLg:Lgoal≤ max Mcap (2*Lgoal):=by linarith [le_max_right Mcap (2*Lgoal)]
  have hp:0<Z:=zero_lt_one.trans hZ
  have hquarter:0≤ s.width/4:=div_nonneg s.width_nonneg (by norm_num)
  have hY₁:1≤ comparisonFirst Z s.width:=Real.one_le_rpow hZ.le hquarter
  refine ⟨hc₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),
    hc₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),?_,?_⟩
  · change Z^(s.width/4)≤_
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [s.width_nonneg,le_max_left Mcap (2*Lgoal)]
  · change X₁*X₂/comparisonFirst Z s.width≤_
    calc
      _≤X₁*X₂:=div_le_self (mul_pos hX₁ hX₂).le hY₁
      _≤Z^Lgoal*Z^Lgoal:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_pos_of_pos hp _).le
      _=Z^(2*Lgoal):=by rw [←Real.rpow_add hp];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (le_max_right _ _)

end SevenEighths.CenteredMomentEnergyZeroBalancedAdmission

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysicalReindex
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentSourceInputReindex
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstRetainedNorm CenteredMomentAmplificationChildInput
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α β:Type*}[Fintype α][Fintype β]

local instance instDecidableEq_solutions_r1a5a6d_2 {κ:Type*}:DecidableEq κ:=Classical.decEq _
local instance instDecidableEqSumFinOfNatNat_solutions_r1a5a6d_5 : DecidableEq (α⊕Fin 2):=Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex.instDecidableEqSumFinOfNatNat_solutions_1
lemma physical_mass_map (e:α≃β)(s:Input α)(R seed:Ideal O)(m A:O)
    (Ψ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass (reindex e s) R seed m A Ψ K Z ξ=physicalMass s R seed m A Ψ K Z ξ:=by
  have hc:coefficient (reindex e s) R seed=coefficient s R seed:=by
    simpa only [CenteredMomentFirstAmplificationChoice.OriginalData.beta,
      CenteredMomentFirstAmplificationChoice.OriginalData.profile,original,coefficient]
      using coefficient_map e s R seed
  have hp:CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools)=
      CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools):=by
    rw [←pools_map e s,CenteredMomentSourceMass.finiteColumns,Finset.image_image]
    congr 1
    funext v
    exact tupleMap_product e v
  have hv:CenteredMomentExceptionalAmplitudePair.volume (reindex e s).toData=
      CenteredMomentExceptionalAmplitudePair.volume s.toData:=volume_map e s
  have hs (T:Finset (Ideal O))(C D:Ideal O)
      (hC:CanonicalQuadraticSieve.Supported C)(hD:CanonicalQuadraticSieve.Supported D)
      (t X:ℝ):
      sectorMass (reindex e s) R seed m A t T C D hC hD Ψ K X Z ξ=
      sectorMass s R seed m A t T C D hC hD Ψ K X Z ξ:=by
    unfold sectorMass
    rw [sourceRadius_map e s]
    simp only [hc, show (reindex e s).η=s.η from rfl]
  let sumAt (T:Finset (Ideal O))(t X:ℝ):ℝ:=
    ∑p:CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns T) (CenteredMomentSourceRow.supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).1
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).2 Ψ K X Z ξ
  have hl:physicalMass (reindex e s) R seed m A Ψ K Z ξ=
      sumAt (CenteredMomentActiveSource.activeSource
        (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools))
        (coefficient (reindex e s) R seed)) s.t
        (CenteredMomentExceptionalAmplitudePair.volume (reindex e s).toData):=by
    unfold physicalMass
    dsimp only
    exact Finset.sum_congr rfl (fun p _=>hs _ _ _ _ _ _ _)
  rw [hl]
  rw [hc,hp,hv]
  rfl

variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

lemma empty_balanced_mass (R seed:Ideal O)(m A:O)(Ψ:𝓢(ℝ,ℂ))(K Z₀ ξ:ℝ):
    physicalMass (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α) R seed m A Ψ K Z₀ ξ=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        R seed m A Ψ K Z₀ ξ:=
  physical_mass_map (emptyEquiv α) _ R seed m A Ψ K Z₀ ξ

lemma empty_balanced_volume : volume (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α)=X₁*X₂:=by
  rw [emptyBalanced,volume_map,CenteredMomentEnergyZeroReferencePhysical.balanced_volume]

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthHighBound
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyBandMonotonicity
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r1a5a6d_6 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
lemma low_restrict (Q:Ideal O)(a b bΦ Bmask L L' Mcap e Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(K:ℝ)(hZ:1≤Z)(hL:L'≤L)
    (h:ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K):
    ZeroLowAt Q a b bΦ Bmask L' Mcap e Z degree S K:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hL
  exact h s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hp) (hc₂.trans hp) hl

end SevenEighths.CenteredMomentEnergyZeroGrowthHighBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysical
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSecondHeightFamily
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyZeroGrowthPhysicalReindex CenteredMomentSourceInputReindex
open CenteredMomentEnergyZeroBalancedAdmission CenteredMomentEnergyZeroBalancedDictionary
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstSourceParameters CenteredMomentEnergyFirstLiveAdmission
open CenteredMomentEnergyCanonicalHighPhysical CenteredMomentEnergyZeroGrowthSource
open CenteredMomentEnergyStageMargins CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceReduction
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_growth_physical
    (Wslot:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Lchild Mparent Mchild
      Mschedule Bschedule ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hLs:0≤Lslot)(hκ:(3/4:ℝ)≤κ)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0<a)(hb:0≤b)(hBmask:0≤Bmask)(hLgoal:0≤Lgoal)(hLchild:0≤Lchild)
    (hMparent:0≤Mparent)(hMchild:0≤Mchild)(hMschedule:0≤Mschedule)(hBschedule:0≤Bschedule)
    (hε:0<ε)(hcap: max Mparent (2*Lgoal)≤Lchild)
    (hready:readyBudget (max Mparent (2*Lgoal)) Bmask≤Bschedule)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(k:ℕ)(εchild C₀ C₁ rho:ℝ),εchild≤ stageLoss Mschedule Bschedule ε k→
      0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalGrowthAt (internalQ Q η₀) a b bΦ Bmask Lgoal rho Mparent
        (reserve Mschedule Bschedule ε/4) (physicalLoss Mschedule Bschedule ε k)
        Z ha Ψ Uprofile Jheight (C*(C₀+C₁+1)):=by
  let A:=max Mparent (2*Lgoal)
  let r:=reserve Mschedule Bschedule ε
  have hA:0≤A:=hMparent.trans (le_max_left _ _)
  obtain ⟨hsigma,hsigma1,hr,hxiSigma,hxi1,hes,hes1,hem,hmesh,hmeshEta,heta0,heta,hSaving,hSeed⟩:=
    parameter_gates Mschedule A Bschedule κ ε hMschedule hA hBschedule hκ hε
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have ha2:0<a^2:=sq_pos_of_pos ha
  obtain ⟨U,J,hphysical⟩:=actual_high_physical (α:=α) M H hH
    Wslot aslot bslot Mchild Lslot (r/4) lo hi κ a b 1
    (maskEpsilon Mschedule Bschedule ε) (by norm_num) hem ha hb
    Lchild hLchild degree S haslot hWs hW hMchild hLs hr hκsmall hbeta hκbeta
    0 1 1 (a^2) (r/4) (by norm_num) (by norm_num) ha2 hr
    (fun _=>1) (fun _=>1) (fun _=>by norm_num)
    (sourceEpsilon Mschedule A Bschedule ε) (r/4) (r/4) (A+1) (r/4)
    (2*amplification ε+1) hes hr hr hr
    (amplification ε) hsigma hxiSigma A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBmask heta hr hsigma1 hxi1 hr hes1 le_rfl (fun _=>Ψ) (r/4) (a*a)
    hr (mul_pos ha ha)
  have hfit:=eventually_actual_four_fit Mschedule A Bmask Bschedule κ ε
    hMschedule hA hBmask hBschedule hready hκ hε
  have hclip:∀ᶠZ:ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<2*(r/4) by linarith)))
        (max 1 b*max 1 b)] with Z hZ hz
    exact ⟨hZ,(Real.logb_le_iff_le_rpow hZ (mul_pos
      (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hz⟩
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Zbase,hZbase,hphysical⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Znum,hZnum⟩:=Filter.eventually_atTop.mp (hfit.and hclip)
  refine ⟨C,hC,max Zbase Znum,hZbase.trans_le (le_max_left _ _),?_⟩
  intro Z hZZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpos
  have hZbaseLe:Zbase≤Z:=(le_max_left _ _).trans hZZ
  have hn:=hZnum Z ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hn.1.1
  intro s hQ hsLower hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hlarge
  dsimp only
  intro hfour
  let src:=emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α
  let θ:(∅:Finset α)→RayQuotient.Characters M H:=fun i=>isEmptyElim i
  have hmatch:CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ
      (fun _=>0) (fun _=>0) (fun _=>0) Wslot bslot Z:=by
    constructor <;> intro i <;> exact isEmptyElim i
  have hupper:=four_upper_scales s p ha t X₁ X₂ hX₁ hX₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hu:Z^A≤Z^Lchild:=Real.rpow_le_rpow_of_exponent_le hZ.le hcap
  have hgate:=declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hdecl:=declared_capacity_upper s X₁ X₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hK:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  have hbound:=hphysical ∅ θ Z hZbaseLe εchild C₀ C₁ hC₀ hC₁ hzero hpos
    (fun _=>0) (fun _=>0) (fun _=>0) 0 (mesh Mschedule Bschedule κ ε) hmesh.le
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by norm_num)
    (fun i=>isEmptyElim i) src hmatch
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by simp) le_rfl le_rfl
    hb hb (le_max_right _ _) (le_max_right _ _) (by simp)
    s.puncture 1 s.puncture_ne_zero s.puncture_bound squarefree_one one_ne_zero
    s.radial.scale hK.1 p rfl rfl
    (hupper.1.trans hu) (hupper.2.1.trans hu) (hupper.2.2.1.trans hu) (hupper.2.2.2.trans hu)
    (max s.width (length Z X₁+length Z X₂)) s.width (r/4)
    (columnLoss Mschedule Bschedule ε k) hr.le hdecl
    (by
      change length Z X₁+length Z X₂+6*κ*(∑i:(∅:Finset α),(0:ℝ))≤_
      simpa only [Finset.sum_const_zero,mul_zero,add_zero] using
        le_max_right s.width (length Z X₁+length Z X₂))
    (hgate.2.1.trans (le_max_left _ _)) hgate.2.1 (by linarith)
    hn.2.2 (by simp [lowerFactor]) (le_max_left _ _)
    hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hn.1.2 k εchild hchild)
  rw [show physicalMass src s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4)=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4) from
        empty_balanced_mass s p ha t X₁ X₂ hX₁ hX₂ _ _ _ _ _ _ _ _] at hbound
  rw [show volume src=X₁*X₂ from empty_balanced_volume s p ha t X₁ X₂ hX₁ hX₂] at hbound
  have heq:max s.width (length Z X₁+length Z X₂)+columnLoss Mschedule Bschedule ε k+r/4=
      max s.width (length Z X₁+length Z X₂)+physicalLoss Mschedule Bschedule ε k:=by
    dsimp only [r]
    rw [add_assoc,columnLoss_physical]
  simpa only [map_one,Nat.cast_one,div_one,add_zero,
    show (src).t=t from rfl,heq] using hbound

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthSourceControlled
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSourceControlled
open HeckeFamily QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroGrowthHighBound
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyZeroGrowthSource (PhysicalGrowthAt)

local instance instDecidableEqSumFinOfNatNat_solutions_r1a5a6d_7 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
theorem actual_growth_from_physical
    (a b bΦ rho ε Mcap Bmask B L εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hLB:2*L≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass Cprevious:ℝ),
      0≤e→0≤K→0≤Cmass→0≤Cprevious→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroAt Q a b bΦ Bmask L rho efinal Z degree S Cprevious→
      ZeroLowAt Q a b bΦ Bmask (max L (Mcap+Bmask+rho/100)) Mcap e Z degree S K→
      PhysicalGrowthAt Q a b bΦ Bmask L rho Mcap ξ emass Z ha Ψ Smass Jmass Cmass→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap efinal Z Jout U (Cfixed*(K+Cmass+Cprevious+1)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,hstage⟩:=actual_high_from_physical a b bΦ rho ε Mcap Bmask B εdiag ξ saving
    ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Jh,Uh,Ch,hCh,hbound⟩:=hstage degree S Jmass Smass
  let Jout:=degree+Jh
  let U:=S∪Uh
  let Cfixed:=Ch+1
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];linarith
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass Cprevious he hK hCm hCp hef hmf hdf htf hold hlow hmass
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hCout:0≤Cfixed*(K+Cmass+Cprevious+1):=by positivity
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hbase:1≤1+|t|:=by linarith [abs_nonneg t]
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hS:S⊆U:=Finset.subset_union_left
  have hUh:Uh⊆U:=Finset.subset_union_right
  by_cases hsmall:s.width≤ rho
  · have hh:=zeroGrowth_of_zeroAt Q a b bΦ Bmask L rho efinal Z degree S
      Cprevious hCp hold s hQ hsmall p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ (show 1≤1+‖t‖ by linarith [norm_nonneg t]) hj
    have hcoeff:Cprevious≤Cfixed*(K+Cmass+Cprevious+1):=by
      dsimp [Cfixed]
      nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    gcongr
  have hlowL:=low_restrict Q a b bΦ Bmask _ L Mcap e Z degree S K hZ.1.le (le_max_left _ _) hlow
  by_cases hl:length Z X₁+length Z X₂≤5*s.width/6
  · have hh:=hlowL s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ hbase hj
    have hloss:s.width+e≤ max s.width (length Z X₁+length Z X₂)+efinal:=by
      linarith [le_max_left s.width (length Z X₁+length Z X₂)]
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hloss
    have hcoeff:K≤Cfixed*(K+Cmass+Cprevious+1):=by dsimp [Cfixed];nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
  have hlowR:=low_restrict Q a b bΦ Bmask _ (Mcap+Bmask+rho/100) Mcap e Z degree S K
    hZ.1.le (le_max_right _ _) hlow
  have hvolume:X₁*X₂≤Z^B:=by
    calc
      _≤Z^L*Z^L:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLB
  have hp:=hmass s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (le_of_not_ge hl)
  have hh:=hZ.2 e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hlowR
    s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hvolume (le_of_not_ge hl) hp
  have hcontrol:=profile_control_mono p hUh
  have hp0:=p.control_nonneg Uh
  have hj:Jh≤Jout:=Nat.le_add_left _ _
  have hpow:=pow_le_pow_right₀ hbase hj
  have hcoeff:Ch≤Cfixed:=by dsimp [Cfixed];linarith
  have hcoefFull:Ch*(K+Cmass+1)≤Cfixed*(K+Cmass+Cprevious+1):=
    mul_le_mul hcoeff (by linarith) (by positivity) hCfixed.le
  have hfront:=mul_le_mul_of_nonneg_right hcoefFull
    (show 0≤diagonalControl s.radial.profile*(p.control Uh)^2*(1+|t|)^Jh*
      Z^(max s.width (length Z X₁+length Z X₂)+efinal) by positivity)
  have hmid:s.plainEnergy p t X₁ X₂≤
      Cfixed*(K+Cmass+Cprevious+1)*diagonalControl s.radial.profile*(p.control Uh)^2*
        (1+|t|)^Jh*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
    apply hh.trans
    convert (preTransparency := .instances) hfront using 1 <;> ring
  apply hmid.trans
  rw [Real.norm_eq_abs]
  gcongr

end SevenEighths.CenteredMomentEnergyZeroGrowthSourceControlled

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.NaturalZeroStage
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalZeroStage
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r1a5a6d_2 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_zero_stage_oai
    (W:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Mparent Mchild
      Mschedule Bschedule ε rho:ℝ)(k:ℕ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hLs:0≤Lslot)(hκ:(3/4:ℝ)≤κ)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:2≤bΦ)(hBmask:0≤Bmask)(_hLgoal:0≤Lgoal)
    (hMparent:0≤Mparent)(hMchild:0≤Mchild)(hMschedule:0≤Mschedule)(hBschedule:0≤Bschedule)
    (hε:0<ε)(hrho:0< rho)(hrhoChild:rho≤Mchild)
    (hdrop:Mparent-amplification ε/2≤Mchild):
    ∃d Lgrow Llow:ℝ,0<d ∧ d≤1 ∧ 0<Lgrow ∧ Lgoal≤Lgrow ∧
      Lgrow=max Lgoal (Mparent+Bmask+2*d)+1 ∧
      Llow=max Lgrow (Mparent+Bmask+rho/100) ∧
      Llow≤ max Lgoal (Mparent+Bmask+rho/100+2)+1 ∧
    ∀Lchild:ℝ,0≤Lchild→max Mparent (2*Lgrow)≤Lchild→
      readyBudget (max Mparent (2*Lgrow)) Bmask≤Bschedule→
    ∀degree degreeLow:ℕ,∀S Slow:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤ stageLoss Mschedule Bschedule ε k→
      0≤C₀→0≤C₁→0≤Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Llow Mparent
        (physicalLoss Mschedule Bschedule ε k) Z degreeLow Slow Clow→
      ZeroAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (stageLoss Mschedule Bschedule ε (k+1)) Z J U (C*(Clow+C₀+C₁+1)):=by
  let r:=reserve Mschedule Bschedule ε
  have hκ0:0≤κ:=by linarith
  have hr:0< r:=(bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).2.2.2.1
  have hb:0≤b:=by linarith
  have hrad:0<bΦ:=by linarith
  obtain ⟨d,Lgrow,hd,hd1,hLg,hgoal,hLexact,hLupper,hsharp⟩:=
    CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
      a b bΦ r Mparent Bmask Lgoal ha hlo hhi hrad hr hMparent hBmask
  let Llow:=max Lgrow (Mparent+Bmask+rho/100)
  refine ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,rfl,?_,?_⟩
  · apply max_le
    · apply hLupper.trans
      exact add_le_add (max_le_max (le_refl Lgoal)
        (show Mparent+Bmask+2≤Mparent+Bmask+rho/100+2 by linarith only [hrho])) (le_refl (1:ℝ))
    · have hh:=le_max_right Lgoal (Mparent+Bmask+rho/100+2)
      linarith
  intro Lchild hLc hcap hready degree degreeLow S Slow
  obtain ⟨Ψ,hsΨ,hnΨ,hgrowth⟩:=
    CenteredMomentEnergyZeroGrowthSourceControlled.actual_growth_from_physical
      a b bΦ rho r Mparent Bmask (2*Lgrow) Lgrow (r/4) (r/4) (2*amplification ε+1)
      ha hlo hhi hrad hrho hr hMparent hBmask (by positivity) le_rfl (by positivity) (by positivity)
  obtain ⟨Smass,Jmass,hphysical⟩:=
    CenteredMomentEnergyZeroGrowthPhysical.actual_growth_physical (α:=α) M H hH
      W aslot bslot Lslot lo hi κ a b bΦ Bmask Lgrow Lchild Mparent Mchild Mschedule Bschedule ε
      haslot hWs hW hLs hκ hbeta hκbeta ha hb hBmask hLg.le hLc hMparent hMchild
      hMschedule hBschedule hε hcap hready hdrop Ψ degree S
  obtain ⟨Jgrowth,Ugrowth,Cgrowth,hCg,hgrowth⟩:=hgrowth (degree+degreeLow) (S∪Slow) Jmass Smass
  obtain ⟨J,U,Csharp,hCs,hsharp⟩:=hsharp Ugrowth
  refine ⟨J,U,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cmass,hCm,Zmass,hZm,hmass⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let C:=Csharp*(Cgrowth*(Cmass+2)+1)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_ge_atTop Zmass,hgrowth,hsharp] with Z hZmZ hg hs
  have hZ:1<Z:=hZm.trans_le hZmZ
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hz hp hl
  have hmarg:=margins Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε k
  have hpLoss:0≤physicalLoss Mschedule Bschedule ε k:=hmarg.1.le
  have hrLoss:0≤ reflectedLoss Mschedule Bschedule ε k:=hpLoss.trans hmarg.2.2.2.1
  have hlength:Lgrow≤Lchild:=by linarith [le_max_right Mparent (2*Lgrow)]
  have hap:a/max 1 b≤a:=div_le_self ha.le (le_max_left _ _)
  have hzero:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ 2 0 _ _ _
    degree degree S S C₀ C₀ hZ.le le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) hC₀ le_rfl hz
  have hpositive:=positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
    _ _ 2 0 _ _ _ η₀ Q degree degree S S C₁ C₁ hZ.le
    le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hp
  have hmassNow:=hmass Z hZmZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpositive
  have hprevious:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z a b bΦ Bmask Lgrow rho
    (reflectedLoss Mschedule Bschedule ε k) degree (degree+degreeLow) S (S∪Slow) C₀ C₀
    hZ.le hap le_rfl le_rfl le_rfl hlength hrhoChild
    (hchild.trans (hmarg.2.1.trans hmarg.2.2.2.1)) (Nat.le_add_right _ _)
    Finset.subset_union_left hC₀ le_rfl hz
  have hlow:=zeroLowAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    degreeLow (degree+degreeLow) Slow (S∪Slow) Clow Clow hZ.le
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_add_left _ _)
    Finset.subset_union_right hClow le_rfl hl
  have hgrowthNow:=hg.2 (physicalLoss Mschedule Bschedule ε k)
    (physicalLoss Mschedule Bschedule ε k) (reflectedLoss Mschedule Bschedule ε k)
    (internalQ Q η₀) Clow (Cmass*(C₀+C₁+1)) C₀ hpLoss hClow (by positivity) hC₀
    (by unfold reflectedLoss;exact le_rfl) hmarg.2.2.2.1
    (hmarg.2.2.1.trans hmarg.2.2.2.1)
    (by have hh:= (bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).1
        linarith only [hrLoss,hh]) hprevious hlow hmassNow
  have hfinal:=hs.2 (reflectedLoss Mschedule Bschedule ε k) (internalQ Q η₀) Jgrowth
    (Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)) hrLoss (by positivity) hgrowthNow
  rw [reflected_then_zero] at hfinal
  have hfront:Csharp*(Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)+1)≤C*(Clow+C₀+C₁+1):=by
    have hinner:Clow+Cmass*(C₀+C₁+1)+C₀+1≤(Cmass+2)*(Clow+C₀+C₁+1):=by
      nlinarith [mul_nonneg hCm.le hClow]
    calc
      _≤Csharp*(Cgrowth*((Cmass+2)*(Clow+C₀+C₁+1))+(Clow+C₀+C₁+1)):=by
        gcongr
        linarith
      _=_:=by dsimp [C];ring
  exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    J J U U _ _ hZ.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) (by positivity) hfront hfinal

end SevenEighths.CenteredMomentEnergyNaturalZeroStage

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyNaturalZeroStage.actual_zero_stage_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyNaturalZeroStage.actual_zero_stage_oai.{u_1}
