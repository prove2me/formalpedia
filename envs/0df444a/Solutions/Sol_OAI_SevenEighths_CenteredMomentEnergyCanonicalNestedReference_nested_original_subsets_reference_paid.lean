-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyCanonicalNestedReference.nested_original_subsets_reference_paid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:11:23.602313+00:00
-- url     : https://prove2.me/submissions/50e87981-3063-43d0-9707-216a2a48fa04

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyAllocatedChildren_actual_common_from_energy
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalLiveBound_actual_live_canonical_child_bands

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRaw
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDivisorRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem split_slot_product {M : Type*} [CommMonoid M] (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (f : ι → M) :
    (∏ i∈frozenIndices D a,f i)*(∏ i∈liveIndices D a,f i)=∏ i,f i :=
  Finset.prod_filter_mul_prod_filter_not _ _ _

theorem selectedNorm_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    0 < selectedNorm D a := by
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a _))

theorem raw_scale_identity (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) :
    rawRemaining D a T P*formalReductionFactor D a P=T*∏ i,P i := by
  unfold rawRemaining formalReductionFactor
  rw [← split_slot_product D a P]
  field_simp [(selectedNorm_pos D a).ne']

end SevenEighths.CenteredMomentDivisorRaw

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RetainedProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem clippedScale_ge_one (S : ℝ) : 1 ≤ clippedScale S := le_max_left _ _

end SevenEighths.CenteredMomentRetainedProfile

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.BandSubtypeTransport
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandSubtypeTransport
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentEnergyReindex
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [Fintype β] in
theorem positiveAt_embedding (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveAt (α:=β) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity
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
    (by rw [hsum];exact hcapacity)
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
theorem positiveAt_subtype (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveAt (α:=T) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveAt_embedding M H hH ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h

end SevenEighths.CenteredMomentEnergyBandSubtypeTransport

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

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X) := by
  by_cases hx:1≤X
  · rw [length,max_eq_right hx,max_eq_right (Real.logb_nonneg hZ hx)]
  · have hh:X≤1:=le_of_not_ge hx
    have hl:Real.logb Z X≤0 := by
      simpa using Real.logb_le_logb_of_le hZ hX hh
    rw [length,max_eq_left hh,Real.logb_one,max_eq_left hl]

theorem postmask_length (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)=length Z X-min (Real.logb Z D) (length Z X) := by
  have hp:0< max 1 X:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd:0<D:=zero_lt_one.trans_le hD
  rw [length_eq_max_log Z _ hZ (div_pos hp hd),Real.logb_div hp.ne' hd.ne']
  change max 0 (length Z X-Real.logb Z D)=_
  by_cases h:Real.logb Z D≤length Z X
  · rw [min_eq_left h,max_eq_right (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),sub_self]

lemma postmask_length_le (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)≤length Z X := by
  rw [postmask_length Z X D hZ hD]
  have hm:0≤ min (Real.logb Z D) (length Z X):=
    le_min (Real.logb_nonneg hZ hD) (length_nonneg Z X hZ)
  linarith

end SevenEighths.CenteredMomentEnergyInputParentCapacity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

lemma clipped_log (Z U : ℝ) (hZ : 1<Z) (hU : 0<U) :
    Real.logb Z (clippedScale U)=Real.logb Z U+max (-Real.logb Z U) 0 := by
  by_cases h : 1≤U
  · rw [clippedScale,max_eq_right h,max_eq_right (neg_nonpos.mpr (Real.logb_nonneg hZ h))]
    ring
  · have hu : U≤1 := (lt_of_not_ge h).le
    have hl : Real.logb Z U≤0 := Real.logb_nonpos hZ hU.le hu
    rw [clippedScale,max_eq_left hu,max_eq_left (neg_nonneg.mpr hl),Real.logb_one]
    ring

lemma clipped_pair_log (Z U₁ U₂ : ℝ) (hZ : 1<Z) (h₁ : 0<U₁) (h₂ : 0<U₂) :
    Real.logb Z (clippedScale U₁)+Real.logb Z (clippedScale U₂)=
      Real.logb Z U₁+Real.logb Z U₂+clippingLoss Z U₁ U₂ := by
  rw [clipped_log Z U₁ hZ h₁,clipped_log Z U₂ hZ h₂]
  unfold clippingLoss
  ring

lemma clipping_loss_bound (Z U₁ U₂ b₁ b₂ : ℝ) (hZ : 1<Z)
    (h₁ : 0<U₁) (h₂ : 0<U₂) (hs₁ : 1≤U₁*b₁) (hs₂ : 1≤U₂*b₂) :
    0≤ clippingLoss Z U₁ U₂ ∧
      clippingLoss Z U₁ U₂≤Real.logb Z (max 1 b₁*max 1 b₂) := by
  have one (U b : ℝ) (hU : 0<U) (hs : 1≤U*b) :
      max (-Real.logb Z U) 0≤Real.logb Z (max 1 b) := by
    have hb : 0< max 1 b := zero_lt_one.trans_le (le_max_left _ _)
    have hc : clippedScale U≤ max 1 b*U := by
      apply max_le
      · exact hs.trans (by nlinarith [le_max_right (1:ℝ) b])
      · nlinarith [le_max_left (1:ℝ) b]
    have hl := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one U)) hc
    rw [clipped_log Z U hZ hU,Real.logb_mul hb.ne' hU.ne'] at hl
    linarith
  refine ⟨add_nonneg (le_max_right _ _) (le_max_right _ _),?_⟩
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₁)))
    (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₂)))]
  exact add_le_add (one U₁ b₁ h₁ hs₁) (one U₂ b₂ h₂ hs₂)

lemma profile_polynomial_survives (χ : Character) (V : Plain) (U : ℝ) (hU : 0<U)
    (t X σ v : ℝ) (hn : HeckeDyadic.polynomial χ false (V.profile U hU t) X σ v≠0) :
    1≤U*V.b := by
  by_contra hs
  rw [V.profile_zero U hU t (lt_of_not_ge hs)] at hn
  exact hn (by simp [HeckeDyadic.polynomial,HeckeDyadic.summand])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma selectedNorm_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) :
    1≤ selectedNorm D a := by
  have hn (j : Fin 2) : (1:ℝ)≤Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (hn 0) (hn 1)

lemma remainingLogs_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (hZ : 1<Z) (P : ι→ℝ) (hP : ∀i,1≤P i) :
    remainingLogs D a Z P≤∑i,Real.logb Z (P i) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

lemma raw_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (X₁ X₂ : ℝ) (P : ι→ℝ) (hP : ∀i,0<P i) :
    rawScale D a X₁ 0*rawScale D a X₂ 1*(∏i∈liveIndices D a,P i)=
      (X₁*X₂*∏i,P i)/formalReductionFactor D a P := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  apply (eq_div_iff hr.ne').mpr
  simpa only [rawScale,div_mul_div_comm,rawRemaining,selectedNorm] using
    CenteredMomentDivisorRaw.raw_scale_identity D a (X₁*X₂) P

lemma raw_log_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (P : ι→ℝ) (hP : ∀i,0<P i) :
    Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+remainingLogs D a Z P=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P) := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  have hh := congrArg (Real.logb Z) (raw_volume D a X₁ X₂ P hP)
  rw [Real.logb_div (mul_pos (mul_pos h₁ h₂) (Finset.prod_pos (fun i _=>hP i))).ne' hr.ne',
    Real.logb_mul (mul_pos (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)).ne'
      (Finset.prod_pos (fun i _=>hP i)).ne',
    Real.logb_mul (rawScale_pos D a X₁ h₁ 0).ne' (rawScale_pos D a X₂ h₂ 1).ne',
    Real.logb_prod _ _ (fun i _=>(hP i).ne')] at hh
  exact hh

theorem affine_exact (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i) :
    plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+
        clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) := by
  have hv := raw_log_volume D a Z X₁ X₂ h₁ h₂ P hP
  rw [plainLogs,clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)]
  nlinarith

theorem excess_le_remaining (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i)
    (hs₁ : 1≤ rawScale D a X₁ 0*b₁) (hs₂ : 1≤ rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P hP]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  exact max_le_max (by linarith) le_rfl

end SevenEighths.CenteredMomentAllocatedChildCapacity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityLedger
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem formal_reduction_pays_slots (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z:ℝ)(hZ:1<Z)(P:ι→ℝ)(hP:∀i,1≤P i):
    (∑i,Real.logb Z (P i))-remainingLogs D a Z P≤
      Real.logb Z (formalReductionFactor D a P) := by
  have hp:∀i,0<P i:=fun i=>zero_lt_one.trans_le (hP i)
  have hs:=congrArg (Real.logb Z) (split_slot_product D a P)
  rw [Real.logb_mul (Finset.prod_pos (fun i _=>hp i)).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne')] at hs
  rw [formalReductionFactor,Real.logb_mul (selectedNorm_pos D a).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne')]
  have hn:=Real.logb_nonneg hZ (selectedNorm_ge_one D a)
  dsimp only [remainingLogs]
  linarith

theorem affine_reduction_le_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z κ:ℝ)(hZ:1<Z)(hκ:0≤κ)(P:ι→ℝ)(hP:∀i,1≤P i):
    -Real.logb Z (formalReductionFactor D a P)+(6*κ-1)*remainingLogs D a Z P≤
      (6*κ-1)*(∑i,Real.logb Z (P i)) := by
  have hred:=formal_reduction_pays_slots D a Z hZ P hP
  have hrem:=remainingLogs_le D a Z hZ P hP
  nlinarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityDefect
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma width_defect_cost (x B δ:ℝ)(hB:0≤B)(hδ:0≤δ)(hx:x≤δ):
    x+max (B-x) 0/6≤δ+B/6 := by
  by_cases h:0≤B-x
  · rw [max_eq_left h];linarith
  · rw [max_eq_right (le_of_not_ge h)];linarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.DeletedChildCapacity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyDeletedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedChildCapacity
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSecondCapacityLedger CenteredMomentLiveCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hF))

lemma postmaskLength_le (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F≤Real.logb Z (clippedScale U) :=
  postmask_length_le Z U _ hZ (deletion_norm F hF)

theorem child_survives (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0) :
    1≤ rawScale D a X₁ 0*V₁.b ∧ 1≤ rawScale D a X₂ 1*V₂.b := by
  unfold child at hne
  have hp:=left_ne_zero_of_mul hne
  exact ⟨profile_polynomial_survives χ V₁ _ (rawScale_pos D a X₁ h₁ 0) t _ 0 0
    (left_ne_zero_of_mul hp),
    profile_polynomial_survives χ V₂ _ (rawScale_pos D a X₂ h₂ 1) t _ 0 0
      (right_ne_zero_of_mul hp)⟩

lemma deletedExcess_le (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0) :
    deletedExcess D a Z X₁ X₂ κ M P F₁ F₂ J≤
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := by
  have h₁:=postmaskLength_le Z (rawScale D a X₁ 0) F₁ hZ hF₁
  have h₂:=postmaskLength_le Z (rawScale D a X₂ 1) F₂ hZ hF₂
  have hsum:(∑i∈liveIndices D a\J,Real.logb Z (P i))≤ remainingLogs D a Z P :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _=>Real.logb_nonneg hZ (hP i))
  have hh:=mul_le_mul_of_nonneg_left hsum (by positivity : 0≤6*κ)
  unfold deletedExcess excess plainLogs
  exact max_le_max (by linarith) le_rfl

theorem child_excess_from_parent (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 := by
  obtain ⟨hs₁,hs₂⟩:=child_survives χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J hne
  apply (deletedExcess_le D a Z X₁ X₂ κ Mactual P F₁ F₂ J hZ hκ hP hF₁ hF₂).trans
  apply (excess_le_remaining D a Z X₁ X₂ V₁.b V₂.b κ Mactual hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
  linarith

theorem child_paid_width (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    Mactual+deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6≤
      Mnom+δ₂+w+ell+δ₁/6+θ/3 := by
  have he:=child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne hparent hshift hclip
  have hh:=width_defect_cost (Mactual-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mactual-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mactual by ring] at hh
  linarith

end SevenEighths.CenteredMomentEnergyDeletedChildCapacity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalLiveCapacity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentRetainedProfile
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyBands
open CenteredMomentEnergyDeletedChildCapacity CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

lemma original_deleted_excess (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset
      (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (τ:Character)(v Z X₁ X₂ κ Mactual:ℝ)(w:α→ℝ)
    (hZ:1<Z)(hscale:∀i,src.P i=Z^(w i))(F₁ F₂:Finset (Ideal O)):
    deletedExcess D alloc Z X₁ X₂ κ Mactual
      (commonData (withHeight src τ v) C R B).P F₁ F₂ J =
    CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) Mactual κ:=by
  unfold deletedExcess CenteredMomentLiveCapacity.excess originalImage
  simp only [Finset.sum_map,originalEmbedding,Function.Embedding.coeFn_mk]
  congr 3
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change Real.logb Z (src.P i.val)=w i.val
  rw [hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem live_source_paid_cost (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset
      (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (τ:Character)(rad:Radial)(V₁ V₂:Plain)(v Z X₁ X₂ κ A M Mnom Mactual u ell δ₁ δ₂ θ:ℝ)
    (w:α→ℝ)(h₁:0<X₁)(h₂:0<X₂)(F₁ F₂:Finset (Ideal O))
    (hZ:1<Z)(hκ:0≤κ)(hw:∀i,0≤w i)(hscale:∀i,src.P i=Z^(w i))
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hparent:A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-M+6*(u+ell)+δ₁)
    (hwidth:Mactual-Mnom≤δ₂)(hu:0≤u)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ)
    (hlive:LiveChild τ rad D alloc V₁ V₂
      (commonData (withHeight src τ v) C R B).slots
      (commonData (withHeight src τ v) C R B).coefficient
      (commonData (withHeight src τ v) C R B).P v X₁ X₂ h₁ h₂ F₁ F₂ J):
    Mactual-Mnom+CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) Mactual κ/6≤
      δ₂+u+ell+δ₁/6+θ/3:=by
  obtain ⟨z,hz,hφ,hchild⟩:=hlive
  let d:=commonData (withHeight src τ v) C R B
  have hP:∀i,1≤d.P i:=by
    intro i
    change 1≤ src.P i.val
    rw [hscale]
    exact Real.one_le_rpow hZ.le (hw i.val)
  have hp:A+(6*κ-1)*(∑i,Real.logb Z (d.P i))≤M:=by
    simpa only [d,commonData,withHeight,hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hparent
  have hb:=child_paid_width (naturalCharacter τ z) D alloc V₁ V₂ d.slots d.coefficient d.P
    v Z X₁ X₂ κ A M Mnom Mactual u ell δ₁ δ₂ θ h₁ h₂ F₁ F₂ J
    hZ hκ hP hF₁ hF₂ hchild hp hshift hwidth hu hell hδ₁ hδ₂ hθ hclip
  rw [original_deleted_excess src C R B D alloc J τ v Z X₁ X₂ κ Mactual w hZ hscale F₁ F₂] at hb
  linarith

end SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalPaidSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalPaidSource
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
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

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource.instFiniteQuotientOIdeal
theorem actual_canonical_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_live_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    Mnom (δ₂+u+ell+δ₁/6+θclip/3)
  intro hlive
  exact live_source_paid_cost src C R B D alloc J τ (canonicalRadial τ (internalQ Q η₀) dyad)
    (sourcePlain a b haPlain (p.profile 0) (p.support 0))
    (sourcePlain a b haPlain (p.profile 1) (p.support 1))
    v Z X₁ X₂ κ A Mparent Mnom
    (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))
    u ell δ₁ δ₂ θclip w hX₁ hX₂ F₁ F₂ (hZ₀.trans_le hZ)
    (by linarith) hw hmatch.scale hF₁ hF₂ hparent hshift hdefect hu hell hδ₁ hδ₂ hθclip hclip hlive

end SevenEighths.CenteredMomentEnergyCanonicalPaidSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalCommonPaid
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalCommonPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
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

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid.instFiniteQuotientOIdeal
theorem actual_common_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  obtain ⟨Cm,hCm,hcommon⟩:=actual_common_from_energy (α:=α) (fun _=>bslot) (fun _=>Mslot)
    (fun _=>hMslot) εmask hεmask
  refine ⟨n,T,dc,2*Cm*Cc,by positivity,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent Mnom u ell δ₁ δ₂ θclip
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  let E:=Cc*(C₀+C₁)*diagonalControl rad.profile*(p.control T)^2*
    (1+(|v|+height))^(dc+degree+4*n)*
    Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh)
  have hz:1<Z:=hZ₀.trans_le hZ
  have he:0≤E:=by
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hz0:0<Z:=zero_lt_one.trans hz
    dsimp [E]
    positivity
  have hleft:∀X₁ X₂:ℝ,∀h₁:0<X₁,∀h₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
      X₁*X₂=d.X₁*d.X₂ → ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
      ∀J,allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
        v X₁ X₂ h₁ h₂ F₁ F₂ J≤E:=by
    intro X₁ X₂ h₁ h₂ hc₁ hc₂ hprod F₁ F₂ hF₁ hF₂ J
    apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ h₁ h₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
      A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent _ hdefect hclip
    simpa only [hprod] using hshift
  have hh:=hcommon src hhi hMs τ v C R hR B D alloc V₁ V₂ hp₁ hp₂ rad
    (fun z hz=>hz.1) E E he he (by
      intro left F₁ hF₁ F₂ hF₂ J hJ
      have hf₁:∀I∈F₁,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₁) hi)).ne_zero
      have hf₂:∀I∈F₂,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₂) hi)).ne_zero
      cases left
      · exact hleft d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos hY₁ hY₂ d.same_product F₁ F₂ hf₁ hf₂ J
      · exact hleft d.X₁ d.X₂ d.X₁_pos d.X₂_pos hX₁ hX₂ rfl F₁ F₂ hf₁ hf₂ J)
  apply hh.trans_eq
  dsimp [E]
  ring

end SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalReferencePaid
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalReferencePaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
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

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid.instFiniteQuotientOIdeal
theorem actual_reference_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0< reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_common_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hz:1<Z:=hZ₀.trans_le hZ
  have hz0:0<Z:=zero_lt_one.trans hz
  have hr:1≤ ratioPenalty dyad:=le_max_left _ _
  have hr0:0< ratioPenalty dyad:=zero_lt_one.trans_le hr
  have hlog:0≤Real.logb Z (ratioPenalty dyad):=Real.logb_nonneg hz hr
  have hh:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent (Real.logb Z reference) u ell
    (δ₁+Real.logb Z (ratioPenalty dyad)) δ₂ θclip hu hell (by linarith) hδ₂ hθclip
    hparent (by linarith) hdefect hclip
  have hpow:Z^(Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh)=
      reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh):=by
    rw [show Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh=
      Real.logb Z reference+Real.logb Z (ratioPenalty dyad)*((1:ℝ)/6)+
        (εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) by ring]
    rw [Real.rpow_add hz0,Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' href,
      Real.rpow_mul hz0.le,Real.rpow_logb hz0 hz.ne' hr0]
  rw [hpow] at hh
  convert (preTransparency := .instances) hh using 1 ; ring

end SevenEighths.CenteredMomentEnergyCanonicalReferencePaid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalNestedReference
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalNestedReference
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
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

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalNestedReference.instFiniteQuotientOIdeal
theorem nested_original_subsets_reference_paid_oai (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀Jparent:Finset α,∀Jorig:Finset Jparent,∀θ:Jorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Jorig→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Jorig,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0< reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  let Pairs:=ΣJparent:Finset α,Finset Jparent
  have hex (J:Pairs):=actual_reference_paid_source (α:=J.2) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  choose n T dc Cc hCc hbound using hex
  let n₀:=∑J:Pairs,n J
  let dc₀:=∑J:Pairs,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let Ctot:ℝ:=1+∑J:Pairs,Cc J
  have hCt:0<Ctot:=by
    have hh:=Finset.sum_nonneg (fun J (_:J∈(Finset.univ:Finset Pairs))=>(hCc J).le)
    dsimp [Ctot];linarith
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=ΣJ:Pairs,J.2→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1<Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  let Z₀:ℝ:=1+∑c:Choices,Zchoice c
  have hZ₀:1<Z₀:=by
    have hn:Nonempty Choices:=⟨⟨⟨∅,∅⟩,fun i=>False.elim (Finset.notMem_empty _ i.property)⟩⟩
    let:Nonempty Choices:=hn
    have hh:=Finset.sum_pos (s:=Finset.univ) (fun c _=>(zero_lt_one.trans (hZchoice c)))
      Finset.univ_nonempty
    dsimp [Z₀];linarith
  refine ⟨Z₀,hZ₀,?_⟩
  intro Jparent Jorig θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi:Zchoice ⟨⟨Jparent,Jorig⟩,θ⟩≤Z:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (fun c _=>(zero_lt_one.trans (hZchoice c)).le) (Finset.mem_univ (⟨⟨Jparent,Jorig⟩,θ⟩:Choices))
    dsimp [Z₀] at hZ
    linarith
  have hp₀:=positiveAt_subtype M H hH Jparent W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hp:=positiveAt_subtype M H hH Jorig W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hp₀
  have hh:=hb ⟨⟨Jparent,Jorig⟩,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hc:Cc ⟨Jparent,Jorig⟩≤Ctot:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (fun J _=>(hCc J).le) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
    dsimp [Ctot];linarith
  have ht:T ⟨Jparent,Jorig⟩⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨⟨Jparent,Jorig⟩,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T ⟨Jparent,Jorig⟩)≤p.control T₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hn₀:n ⟨Jparent,Jorig⟩≤n₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdc₀:dc ⟨Jparent,Jorig⟩≤dc₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdeg:dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩≤dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T ⟨Jparent,Jorig⟩)
  have hd:0≤diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hz0:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hr:0< ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyCanonicalNestedReference

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyCanonicalNestedReference.nested_original_subsets_reference_paid_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyCanonicalNestedReference.nested_original_subsets_reference_paid_oai.{u_1}
