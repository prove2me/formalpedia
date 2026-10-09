-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn.actual_admitted_subsets_low_column
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:14:41.758997+00:00
-- url     : https://prove2.me/submissions/cf02a01f-817e-4366-9e93-6608b378daa3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalAnnularPower_actual_original_subsets_annular_power
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyFirstLowHomogeneousPowers_actual_low_homogeneous_four_powers
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstCommonSourceBudget_common_energy_live_allocations

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllocationSum
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSupport
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem actualAllocations_card (S : ι → Finset (Ideal O)) (C : Ideal O) (hC : C≠0) :
    (actualAllocations S C).card≤(idealDivisors C).card^(Fintype.card ι) := by
  let f (B : actualAllocations S C) : ι → idealDivisors C := fun i => ⟨B.val i,by
    apply (mem_idealDivisors hC).mpr
    have hh := Finset.dvd_prod_of_mem B.val (Finset.mem_univ i)
    rw [(Finset.mem_filter.mp B.property).2] at hh
    exact hh⟩
  have hf : Function.Injective f := by
    intro B D he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective f hf

end SevenEighths.CenteredMomentCommonAllocationSum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocationCost
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O

 theorem actualAllocations_uniform_small_power (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ D : ℝ,0<D ∧ ∀ {ι : Type*} [Fintype ι],Fintype.card ι≤N →
      ∀ (S : ι → Finset (Ideal O)) (C : Ideal O),C≠0 →
        ((actualAllocations S C).card:ℝ)≤D*(Ideal.absNorm C:ℝ)^ε := by
  let δ := ε/(N+1:ℕ)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(1+D)^(N+1),by positivity,?_⟩
  intro ι _ hn S C hC
  have hNC : (1:ℝ)≤Ideal.absNorm C := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hb : 1≤(1+D)*(Ideal.absNorm C:ℝ)^δ := by
    nlinarith [Real.one_le_rpow hNC hδ.le]
  have hd : δ*(N+1:ℕ)=ε := by
    dsimp only [δ]
    field_simp
  calc
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors C).card:ℝ)^Fintype.card ι := by
      exact_mod_cast actualAllocations_card S C hC
    _ ≤ ((1+D)*(Ideal.absNorm C:ℝ)^δ)^Fintype.card ι := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ _
      exact (hdiv C hC).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ ≤ ((1+D)*(Ideal.absNorm C:ℝ)^δ)^(N+1) := pow_le_pow_right₀ hb (by omega)
    _ = _ := by rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),hd]

end SevenEighths.CenteredMomentAllocationCost

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRawScale
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem plainNorm_pos (B : Tuple ι) (hB : ∀ i,B i≠0) : 0<plainNorm B := by
  unfold plainNorm
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB _))

omit [Fintype ι] in
theorem frozenScale_pos (B : Tuple ι) (P : ι → ℝ) (hP : ∀ i,0<P i) (i : ι) :
    0<frozenScale B P i := by
  unfold frozenScale
  split_ifs
  · exact zero_lt_one
  · exact hP i

theorem rawReduction_pos (B : Tuple ι) (hB : ∀ i,B i≠0) (P : ι → ℝ) (hP : ∀ i,0<P i) :
    0< rawReduction B P := mul_pos (plainNorm_pos B hB) (Finset.prod_pos (fun i _ => frozenScale_pos B P hP i))

theorem slot_scale_split (B : Tuple ι) (P : ι → ℝ) :
    (∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)=∏ i,P i := by
  rw [Finset.prod_coe_sort (liveIndices B) P]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1) P]
  unfold frozenScale liveIndices
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  ring

theorem raw_scale_identity (B : Tuple ι) (hB : ∀ i,B i≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B T P*rawReduction B P=T*∏ i,P i := by
  unfold remainingRaw rawReduction
  have h := slot_scale_split B P
  calc
    _ = T*((∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)) := by
      field_simp [(plainNorm_pos B hB).ne']
    _ = _ := by rw [h]

theorem product_norm (B : Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct B):ℝ)=plainNorm B*∏ i,(Ideal.absNorm (B (Sum.inl i)):ℝ) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,map_mul,map_prod,
    Nat.cast_mul,Nat.cast_prod,plainNorm]
  ring

theorem frozen_window_ne_zero (B : Tuple ι) (C R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (hne : frozenCoefficient B C R ν Wslot P≠0) (i : ι) (hi : B (Sum.inl i)≠1) :
    Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i)≠0 := by
  have hp := (mul_ne_zero_iff.mp hne).1
  have hx := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  exact (mul_ne_zero_iff.mp hx).2

theorem actual_reduction_norm (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (hP : ∀ i,0<P i)
    (a b : ℝ) (ha : 0<a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (hne : frozenCoefficient B C R ν Wslot P≠0) :
    (min 1 a)^Fintype.card ι*rawReduction B P≤(Ideal.absNorm C:ℝ) ∧
      (Ideal.absNorm C:ℝ)≤(max 1 b)^Fintype.card ι*rawReduction B P := by
  have hi (i : ι) : min 1 a*frozenScale B P i≤(Ideal.absNorm (B (Sum.inl i)):ℝ) ∧
      (Ideal.absNorm (B (Sum.inl i)):ℝ)≤ max 1 b*frozenScale B P i := by
    by_cases h : B (Sum.inl i)=1
    · simp only [frozenScale,h,ite_true,map_one,Nat.cast_one,mul_one]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    · have hs := hW i (frozen_window_ne_zero B C R ν Wslot P hne i h)
      rw [frozenScale,if_neg h]
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (hP i).le)
          ((le_div_iff₀ (hP i)).mp hs.1),
        le_trans ((div_le_iff₀ (hP i)).mp hs.2)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (hP i).le)⟩
  rw [←hprod,product_norm]
  constructor
  · have hh := Finset.prod_le_prod (s:=Finset.univ)
      (fun i _ => mul_nonneg (le_of_lt (lt_min zero_lt_one ha)) (frozenScale_pos B P hP i).le)
      (fun i _ => (hi i).1)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'
  · have hh := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Ideal.absNorm (B (Sum.inl i))))
      (fun i _ => (hi i).2)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'

end SevenEighths.CenteredMomentCommonRawScale

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

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRadialData
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma Input.slot_support (s:Input ι) (i:ι) : Function.support (s.W i)⊆Set.Icc s.lower s.upper :=
  fun _x hx=>⟨(s.lower_le i).trans (s.support i hx).1,((s.support i hx).2).trans (s.upper_ge i)⟩

end SevenEighths.CenteredMomentCommonRadialData

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

lemma weight_bounds (x:ℝ):0≤weight x ∧ weight x≤1:=by
  have h₁:=cutoff_bounds (x/2)
  have h₂:=cutoff_bounds (4*x)
  unfold weight
  constructor
  · exact mul_nonneg h₁.1 (sub_nonneg.mpr h₂.2)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ h₂.1) h₁.1).trans
      (by simpa only [mul_one] using h₁.2)

lemma profile_nonneg (x:ℝ):0≤(profile x).re:=(weight_bounds x).1

end SevenEighths.CenteredMomentFirstAnnularMajorant

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplificationChildSourceCaps
open ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEq_solutions_r5c5aa2_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
lemma norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma allocation_product (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2

lemma allocation_ne (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←allocation_product s C B]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

theorem common_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)=
      CenteredMomentAmplificationChildInput.volume s/rawReduction B.val s.P := by
  have hh:=raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  change _ = CenteredMomentAmplificationChildInput.volume s at hh
  rw [←hh]
  congr 1
  unfold CenteredMomentAmplificationChildInput.volume child commonData remainingRaw plainNorm
  dsimp only
  ring

theorem common_volume_le (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)≤
      b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ) := by
  have hc:=norm_ge_one C (allocation_ne s C B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx=>⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn':(C.absNorm:ℝ)≤b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  rw [common_volume]
  apply (div_le_div_iff₀ hr (zero_lt_one.trans_le hc)).mpr
  nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤ mass s :=
  Finset.one_le_prod (fun i _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤ mass s := zero_le_one.trans (mass_one s)

end SevenEighths.CenteredMomentFirstChildProfileControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocationControl
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma frozen_live_control (B : Tuple ι) (M : ι→ℝ) :
    frozenControl B M * (∏i : liveIndices B,M i.val) = ∏i,M i := by
  rw [Finset.prod_coe_sort (liveIndices B) M]
  unfold frozenControl liveIndices
  rw [mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=>B (Sum.inl i)=1) M

lemma frozen_child_control (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t : ℝ) :
    (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2 = (∏i,s.M i)^2 := by
  rw [←mul_pow]
  exact congrArg (fun x:ℝ=>x^2) (frozen_live_control B.val s.M)

lemma allocated_control_sum (s : Input ι) (C R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) :
    (∑B : actualAllocations s.pools C,
      (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) =
      ((actualAllocations s.pools C).card:ℝ) * (∏i,s.M i)^2 := by
  simp only [frozen_child_control,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    nsmul_eq_mul]

theorem allocated_control_mass (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{κ : Type*}[Fintype κ],Fintype.card κ≤N →
      ∀(s : Input κ)(C R : Ideal O),C≠0 →
      ∀(τ : HeckeFamily.Character)(t : ℝ),
        ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          (∑B : actualAllocations s.pools C,
            (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) ≤
          D*(Ideal.absNorm C:ℝ)^(ε-1)*(∏i,s.M i)^2 := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro κ _ hn s C R hC τ t
  have hN : (0:ℝ)<Ideal.absNorm C := CenteredMomentFirstScale.norm_pos C hC
  have hh := hcard (ι:=κ⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega)
    s.pools C hC
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hh 2
  rw [mul_pow,←Real.rpow_mul_natCast hN.le,show ε/2*(2:ℕ)=ε by norm_num] at hs
  rw [allocated_control_sum]
  calc
    _ = (((actualAllocations s.pools C).card:ℝ)^2/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 := by ring
    _ ≤ (D^2*(Ideal.absNorm C:ℝ)^ε/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hN.le) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub hN,Real.rpow_one];ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstCommonSourceBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourceBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

local instance instDecidableEq_solutions_r5c5aa2_2 {κ:Type*}:DecidableEq κ:=Classical.decEq _
theorem common_energy_from_live_children (N:ℕ)(a b ε:ℝ)(ha:0<a)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{κ:Type*}[Fintype κ],∀s:Input κ,
    Fintype.card κ≤N → a≤ s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0<K → 0≤E →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤E*(∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*E*(∏i,s.M i)^2:=by
  obtain ⟨D,hD,hmass⟩:=allocated_control_mass N ε hε
  refine ⟨(max 1 b)^N*D,mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hD,?_⟩
  intro κ _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hh:=common_energy_live_allocations N a b ha s hcard haS hbS C R seed hC hseed τ t L W K hK hW
  apply hh.trans
  have hc:0≤(max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ):=by positivity
  have hs:(∑B:actualAllocations s.pools C,
      if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
        (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K else 0)≤
      E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B hB
    split_ifs with hb
    · convert (preTransparency := .instances) mul_le_mul_of_nonneg_left (hchild B hb) (sq_nonneg (frozenControl B.val s.M)) using 1 ; ring
    · positivity
  have hm:=hmass hcard s C R hC.1 τ t
  calc
    _≤((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ))*
        (E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=
      mul_le_mul_of_nonneg_left hs hc
    _=((max 1 b)^N*E)*(((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
        ∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=by ring
    _≤((max 1 b)^N*E)*(D*(C.absNorm:ℝ)^(ε-1)*(∏i,s.M i)^2):=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) hE)
    _=_:=by ring

end SevenEighths.CenteredMomentFirstCommonSourceBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstCommonSourcePowerBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourcePowerBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
local notation "O"=>ActualEisensteinCubic.O

local instance instDecidableEq_solutions_r5c5aa2_3 {κ:Type*}:DecidableEq κ:=Classical.decEq _
theorem common_energy_power_budget (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤ s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ),0<K →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(CenteredMomentAmplificationChildInput.volume (child s C R B τ t))^(α j))*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*
          (∑j,E j*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))^(α j))*
            (∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound,hCbound,?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  apply hbound s hcard haS hbS C R seed hC hseed τ t L W K _ hK
    (Finset.sum_nonneg (fun j _=>mul_nonneg (hE j) (Real.rpow_nonneg (by positivity) _))) hW
  intro B hB
  apply (hchild B hB).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hE j)
  exact Real.rpow_le_rpow (CenteredMomentAmplificationChildInput.volume_pos _).le
    (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) (hα j)

end SevenEighths.CenteredMomentFirstCommonSourcePowerBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstCommonReferencePower
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonReferencePower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
open CenteredMomentFirstCommonSourcePowerBudget
local notation "O"=>HeckeFamily.O

local instance instDecidableEq_solutions_r5c5aa2_4 {κ:Type*}:DecidableEq κ:=Classical.decEq _
lemma reference_power_identity (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0<b)(hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    (q*(V/C)^2*Z^allowance)*normalizedPower b V C q Z allowance ε E N α=
      C ^(ε-1)*V*E*(b^N*V/C)^α:=by
  have hx:0<V/C:=div_pos hV hC
  have hbN:0<b^N:=pow_pos hb N
  have hprod:Z^allowance*Z^(-allowance)=1:=by
    rw [←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero]
  unfold normalizedPower
  rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_sub hC,Real.rpow_one,
    show b^N*V/C=b^N*(V/C) by ring,Real.mul_rpow hbN.le hx.le]
  field_simp
  calc
    _ = E*(Z^allowance*Z^(-allowance)):=by ring
    _ = E:=by rw [hprod,mul_one]

theorem common_energy_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤ s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K Z allowance:ℝ),0<K→0<Z→
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(volume (child s C R B τ t))^(α j))*(∏i,(child s C R B τ t).M i)^2)→
    (commonEnergy (original s R seed) C hC τ t L W K).re≤
      ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
        (Cb*(∏i,s.M i)^2*∑j,normalizedPower b (volume s) (C.absNorm:ℝ)
          (τ.modulus.absNorm:ℝ) Z allowance ε (E j) N (α j)):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_power_budget N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L W K Z allowance hK hZ hW n E α hE hα hchild
  have hV:=volume_pos s
  have hNC:=CenteredMomentFirstScale.norm_pos C hC.1
  have hq:=CenteredMomentFirstScale.norm_pos τ.modulus τ.modulus_ne_bot
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hh':=(div_le_iff₀ hV).mp hh
  apply hh'.trans_eq
  calc
    _ = Cb*(∏i,s.M i)^2*∑j,(C.absNorm:ℝ)^(ε-1)*volume s*E j*
        (b^N*volume s/(C.absNorm:ℝ))^(α j):=by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Cb*(∏i,s.M i)^2*∑j,
        ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
          normalizedPower b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
            Z allowance ε (E j) N (α j):=by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (reference_power_identity b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
        Z allowance ε (E j) N (α j) (zero_lt_one.trans_le hb) hV hNC hq hZ).symm
    _ = _:=by rw [←Finset.mul_sum];ring

end SevenEighths.CenteredMomentFirstCommonReferencePower

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondChildPowerBudget
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentFirstChildProfileControl CenteredMomentCommonRadialPointwise
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma powers_nonneg (ε : ℝ) (hε : 0≤ε) : ∀j,0≤powers ε j := by
  intro j
  fin_cases j <;> simp [powers,hε]

end SevenEighths.CenteredMomentSecondChildPowerBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSuccessorPaidParameters
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

lemma source_coefficients_nonneg (P:Finset (Ideal O))(mainFactor:ℝ)(hmain:0≤ mainFactor)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ)
    (ha:∀j,0≤amain j)(he:∀p i χ j,0≤aerror p i χ j):
    ∀j,0≤ sourceCoefficients P mainFactor amain aerror alpha j := by
  intro j
  have hc:∀p:O,∀n:ℕ,0≤localErrorCost p n:=by
    intro p n
    have hn:0≤normValue p:=by unfold normValue;positivity
    unfold localErrorCost
    split <;> positivity
  unfold sourceCoefficients
  apply mul_nonneg (by positivity)
  apply add_nonneg (mul_nonneg hmain (ha j))
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (by positivity) (hc p (errorIndex i)))
  apply Finset.sum_nonneg
  intro χ _
  exact mul_nonneg (he p i χ j) (Real.rpow_nonneg (by unfold normValue;positivity) _)

end SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedColumn
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget
open CenteredMomentSourceLiveColumn
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

local instance instDecidableEqSumFinOfNatNat_solutions_r5c5aa2_1 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
lemma main_coefficients_nonneg (q Z K ell deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤ mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

lemma error_coefficients_nonneg (p:O)(k:ℕ)(q Z K deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalLowColumn
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowColumn
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission
open CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers

local instance instDecidableEqSumFinOfNatNat_solutions_r5c5aa2_2 {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn.instFiniteQuotientOIdeal
lemma source_mass_cap {ι:Type*}[Fintype ι](s:Input ι)(N:ℕ)(Mslot:ℝ)
    (hc:Fintype.card ι≤N)(hM:∀i,s.M i≤Mslot):mass s≤(max 1 Mslot)^N:=by
  calc
    _≤∏i:ι,max 1 Mslot:=by
      apply Finset.prod_le_prod
      · intro i _;exact zero_le_one.trans (s.M_ge_one i)
      · intro i _;exact (hM i).trans (le_max_right _ _)
    _=(max 1 Mslot)^Fintype.card ι:=by simp
    _≤_:=pow_le_pow_right₀ (le_max_left _ _) hc

lemma inherited_height_split (t height:ℝ)(J:ℕ)(hh:0≤height):
    (1+|t|+height)^J≤(1+height)^J*(1+|t|)^(2*J):=by
  have hbase:1+|t|+height≤(1+height)*(1+|t|):=by
    nlinarith [abs_nonneg t,mul_nonneg hh (abs_nonneg t)]
  calc
    _≤((1+height)*(1+|t|))^J:=pow_le_pow_left₀ (by positivity) hbase J
    _=(1+height)^J*(1+|t|)^J:=mul_pow _ _ _
    _≤_:=mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega:J≤2*J)) (by positivity)

theorem actual_admitted_subsets_low_column_oai
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)(heps1:εsrc≤1):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(t:ℝ)(seed0:Ideal O),seed0∣C →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → 0≤Mdecl → Mdecl≤A →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    (∀B:actualAllocations src.pools C,
      frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) ∧
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap))) →
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile H0).re≤
      (ref/(seed.absNorm:ℝ))*(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hann⟩:=actual_original_subsets_annular_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve
  obtain ⟨Cb,hCb,hcommon⟩:=common_energy_reference_powers N lower upper εsrc hlower hupper hεsrc
  let Mamp:=amplifierCap A 0 ξ
  let avg:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card RayCharacter:ℝ))
  have hMamp:0≤Mamp:=by dsimp [Mamp,amplifierCap];positivity
  have havg:0<avg:=by dsimp [avg];positivity
  have hmcap:0<(max 1 Mslot)^(2*N):=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ca,hCa,Z₀,hZ₀,hannZ⟩:=hann η₀ Q hQM hQ0 hQt hQ72
  let Ccolumn:=Cb*upper^N*avg*Ca*(max 1 Mslot)^(2*N)
  have hCcolumn:0<Ccolumn:=by dsimp [Ccolumn];positivity
  refine ⟨Ccolumn,hCcolumn,Z₀,hZ₀,?_⟩
  intro Z hZZ
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hZpos:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hPne,hPcard,hfamily⟩:=hannZ Z hZZ
  dsimp only at hPne hPcard hfamily ⊢
  refine ⟨hPne,hPcard,?_⟩
  intro τ
  obtain ⟨υ,hυ,henergy⟩:=hfamily τ
  refine ⟨υ,hυ,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K H0 hK hH0 houter hHcap t seed0 hseed0 seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower hpackets
  let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))
  let delta:=frequencyLoss Z 32 ξ
  let Bcap:=readyBudget A Pcap
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Kerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1)
  let rerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    rmain-errorRemoval prime Z (errorIndex i+1)
  let front:=Ca*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J
  let Hcoef:=fun j:Fin 4=>front*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool P)(i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>
    Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror prime i χ) deficit paid saving (rerror prime i χ) j
  let coeff:=sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror (powers εsrc)
  have hNseed:0<(seed.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hseedne
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hfront:0≤front:=by dsimp [front];positivity
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have hKmain:0≤Kmain:=by unfold Kmain mainRadius mainCommonRadius;positivity
  have hKerror:∀prime i χ,0≤Kerror prime i χ:=by
    intro prime i χ;unfold Kerror errorRadius errorCommonRadius;positivity
  have hcoeff:∀j,0≤ coeff j:=source_coefficients_nonneg P _ (by positivity)
    amain aerror (powers εsrc)
    (fun j=>mul_nonneg (hHcoef j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZpos.le hKmain j))
    (fun prime i χ j=>mul_nonneg (hHcoef j)
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j))
  have hchildren (B:actualAllocations src.pools C)
      (hB:frozenCoefficient B.val C R0 src.ν src.W src.P≠0):
      childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,coeff j*(volume (child src C R0 B τ t))^(powers εsrc j))*mass (child src C R0 B τ t)^2:=by
    exact henergy Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
      K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (hpackets B hB).1 (hpackets B hB).2
  have hcommonBound:=hcommon src hcard hlowerSrc hupperSrc C R0 seed0 hC hseed0 τ t seed
    CenteredMomentFirstAnnularMajorant.profile H0 Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
    hH0 hZpos (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 coeff (powers εsrc)
    hcoeff (powers_nonneg εsrc hεsrc.le) hchildren
  have hscalar:=actual_low_homogeneous_four_powers M H fixedBadPrimes (Finset.Subset.refl _)
    src.η τ C D hC hD hCD E K (volume src) Z sigma delta reserve paid εsrc saving Mdecl A Mamp primeLoss
    hK (volume_pos src) hZ hsigma hεsrc.le hMdecl0 hMA hMdecl hlow hPrimeLoss.le hMamp hPcard hmod
    upper N hupper Hcoef hHcoef front (seed.absNorm:ℝ) (A+1)
    (CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap)
    hfront hNseed heps1 hNC (fun j=>le_rfl) rmain rerror
  dsimp only at hscalar
  have hmass:=source_mass_cap src N Mslot hcard hMs
  have hmass2:mass src^2≤(max 1 Mslot)^(2*N):=by
    calc
      _≤((max 1 Mslot)^N)^2:=pow_le_pow_left₀ (mass_nonneg src) hmass 2
      _=_:=by rw [←pow_mul];congr 1;omega
  have hheightSplit:=inherited_height_split t height J hheight
  let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*
    Z^(CenteredMomentFirstMixedAllowance.allowance C D Z)
  have href:0≤ ref:=by dsimp [ref];positivity
  have hsum:0≤∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
      lossVector sigma delta reserve paid εsrc A saving j):=Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg hZpos.le _)
  calc
    _≤ ref*(Cb*mass src^2*∑j,normalizedPower upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) N (powers εsrc j)):=hcommonBound
    _≤ ref*(Cb*mass src^2*((upper^N*avg*front/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul_of_nonneg_left hscalar
      exact mul_nonneg hCb.le (sq_nonneg _)
    _≤ ref*(Cb*(max 1 Mslot)^(2*N)*((upper^N*avg*
        (Ca*(C₀+C₁+1)*(p.control U)^2*((1+height)^J*(1+|t|)^(2*J)))/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      have hfrontBound:front≤Ca*(C₀+C₁+1)*(p.control U)^2*
          ((1+height)^J*(1+|t|)^(2*J)):=
        mul_le_mul_of_nonneg_left hheightSplit
          (mul_nonneg (mul_nonneg hCa.le
            (add_nonneg (add_nonneg hC₀ hC₁) zero_le_one)) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmass2 hCb.le
      · apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        apply div_le_div_of_nonneg_right _ hNseed.le
        exact mul_le_mul_of_nonneg_left hfrontBound
          (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le)
      · exact mul_nonneg (mul_nonneg
          (div_nonneg (mul_nonneg
            (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le) hfront) hNseed.le)
          (Real.rpow_nonneg hZpos.le _)) hsum
      · exact mul_nonneg hCb.le hmcap.le
    _=_:=by dsimp only [Ccolumn,ref,deficit,paid,Bcap,delta];ring

end SevenEighths.CenteredMomentEnergyCanonicalLowColumn

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn.actual_admitted_subsets_low_column_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn.actual_admitted_subsets_low_column_oai.{u_1}
