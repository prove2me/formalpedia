-- Prove2me | solution 1 for OAI.SevenEighths.ProbeFinalAssembly.chosen_input_of_fine
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:09:56.742842+00:00
-- url     : https://prove2.me/submissions/2219dbda-ad90-49d8-8163-d02fa5c48675

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_HeckeInverseAmplification_no_slot_rowwise_endpoint
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_balanced_adaptive_count_from_raw_moments

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Sobolev
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace CS

variable {f : CS n E} {R x v : ℝ}

theorem bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalProduct
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection
local notation "O" => ActualEisensteinCubic.O

lemma mem_smallPrimeSet (N : ℕ) (P : PrimeIdeal) :
    P.val ∈ smallPrimeSet N ↔ Ideal.absNorm P.val ≤ N := by
  simp [smallPrimeSet, P.property]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem exists_uniform_global_cutoff :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N → P.val∈S) → CorrectionTail S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero globalPrimeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  constructor
  · intro P hP
    have hn : ¬Ideal.absNorm P.val≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>globalPrimeDefectBound_nonneg P.val) (fun _=>le_rfl)
      (globalPrimeDefectBound_summable.subtype _) (globalPrimeDefectBound_summable.subtype _)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.FirstTail
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
local notation "O" => HeckeFamily.O

theorem firstPrimeDefectBound_nonneg (eps : ℝ) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    0≤firstPrimeDefectBound eps P := by unfold firstPrimeDefectBound; positivity

theorem firstPrimeDefectBound_summable (eps : ℝ) (heps : 0<eps) :
    Summable (firstPrimeDefectBound eps) := by
  have ht : 1<(1+min eps (1/50:ℝ) : ℂ).re := by
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
    have hm : 0< min eps (1/50:ℝ) := lt_min heps (by norm_num)
    linarith
  have h := (CubicEisenstein.fullIdealWeight_summable_norm
    (1+min eps (1/50:ℝ) : ℂ) ht).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight (1+min eps (1/50:ℝ) : ℂ) P.val‖=_
  unfold firstPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp only [Complex.neg_re,Complex.add_re,Complex.one_re,Complex.ofReal_re]
  congr 2
  ring

theorem exists_first_cutoff (eps : ℝ) (heps : 0<eps) :
    ∃N : ℕ,4≤N ∧ ∀S : Finset (Ideal O),
      (∀P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,P.val.absNorm≤N → P.val∈S) → FirstTail eps S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (firstPrimeDefectBound eps))).2
    (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>P.val.absNorm))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal=>P.val.absNorm) hm).trans
      (le_max_right _ _)))
  let inc : T→{P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P∉F}=>P.val) h)
  refine ⟨heps,?_,?_⟩
  · intro P hP
    have hn : ¬P.val.absNorm≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>firstPrimeDefectBound_nonneg eps P.val) (fun _=>le_rfl)
      ((firstPrimeDefectBound_summable eps heps).subtype _)
      ((firstPrimeDefectBound_summable eps heps).subtype _)

theorem exists_both_source_exclusions (eps : ℝ) (heps : 0<eps)
    (S₀ : Finset (Ideal O)) (hp : ∀P∈S₀,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S₀) :
    ∃S : Finset (Ideal O),S₀⊆S ∧ SourceExclusions S ∧ FirstTail eps S := by
  obtain ⟨N₁,hN₁,hcut₁⟩ := exists_uniform_global_cutoff
  obtain ⟨N₂,hN₂,hcut₂⟩ := exists_first_cutoff eps heps
  let N := max N₁ N₂
  let S := S₀∪smallPrimeSet N
  have hpS : ∀P∈S,Prime P := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  have hcut : ∀P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,P.val.absNorm≤N → P.val∈S := by
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
  refine ⟨S,Finset.subset_union_left,⟨hpS,hbad.trans Finset.subset_union_left,?_⟩,?_⟩
  · exact hcut₁ S (fun P hP=>hcut P (hP.trans (le_max_left _ _)))
  · exact hcut₂ S (fun P hP=>hcut P (hP.trans (le_max_right _ _)))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicActual
namespace OAI

noncomputable section

open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicActual
open HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles HeckeDetectorProfiles

lemma inverse_profile_smooth (Dstar D : ℝ) :
    ContDiff ℝ ∞ (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D) := by
  unfold HeckeDetectorDyadicBridge.inverseProfile
  have hv : ContDiff ℝ ∞ (fun x : ℝ => cutoff (D*x/Dstar)) := (cutoff.smooth ⊤).comp (by fun_prop)
  exact hv.mul positiveAnnular_smooth

lemma inverse_profile_support (Dstar D : ℝ) :
    Function.support (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)⊆Icc (1/4) (9/4) := by
  intro x hx
  exact positiveAnnular_support ((mul_ne_zero_iff.mp hx).2)

end SevenEighths.HeckeDetectorDyadicActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

theorem high_bin_count {B C U δ r ε γ : ℝ}
    (hC : 0≤C) (hU : 1≤U) (hδ : 5/6≤δ) (hδ' : δ≤1)
    (hγ : 0≤γ) (hr : 1-γ≤ r)
    (hI : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε)) :
    B≤C*U^(1-δ+ε+γ) := by
  apply hI.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  by_cases hr1 : 1≤ r
  · rw [max_eq_right (show 1≤(1+5*r)/6 by linarith)]
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδ) (sub_nonneg.mpr hr1)
    nlinarith
  · rw [max_eq_left (show (1+5*r)/6≤1 by linarith)]
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤δ by linarith)
    have hh' := mul_le_mul_of_nonneg_right hδ' hγ
    nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem Witness.frequency_bound {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) :
    |w.frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T := by
  have hnu : |w.nu|≤allowance := by simpa only [Real.norm_eq_abs] using w.nu_bound
  have hh := abs_sub_le (2*Real.pi*w.nu) 0 w.zero.im
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,
    abs_of_pos (show 0<2*Real.pi by positivity)] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hnu (by positivity)) w.zero_height)

theorem Witness.real_part_upper {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : w.zero.re≤1 := by
  by_contra hn
  exact LFunction_ne_zero_of_one_lt_re (χ w.label) (lt_of_not_ge hn) w.zero_eq

theorem Witness.left_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.r=Real.logb U ((2 : ℝ)^w.left.val) := by
  rw [←w.left_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem Witness.right_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.m=Real.logb U ((2 : ℝ)^w.right.val) := by
  rw [←w.right_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

theorem fiber_lengths {Row Label : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (χ : Row→Label→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (J K : Fin (dyadicLength U))
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    tstar-r-ε≤ m ∧ r≤tstar+ε ∧ m≤1/2+75*ε ∧ tstar-1/2-76*ε≤ r ∧ 0≤ m := by
  obtain ⟨u,hu⟩ := hne
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by
    rw [(w u).toWitness.left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by
    rw [(w u).toWitness.right_exponent hU,hK u hu]
  exact hr ▸ hm ▸ ⟨(w u).product_length_lower,(w u).inverse_length_upper,
    (w u).plain_length_upper,(w u).inverse_length_lower,(w u).plain_length_lower⟩

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorAdaptiveCutoff
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorAdaptiveCutoff
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorRowCount

theorem cutoff_eq_high (δ q : ℝ) (hδ : 5/6<δ) : cutoff δ q=3/2 := by
  simp only [cutoff,if_neg (not_le_of_gt hδ)]

end SevenEighths.HeckeDetectorAdaptiveCutoff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (_root_.OAI.SevenEighths.HeckeDyadic.shift σ freq)=_root_.OAI.SevenEighths.HeckeDyadic.shift σ (-freq) := by
  simp only [HeckeDyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

theorem orientedFrequency_abs (reverse : Bool) (freq : ℝ) :
    |orientedFrequency reverse freq|=|freq| := by cases reverse <;> simp [orientedFrequency]

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberSpikes
namespace OAI

noncomputable section
open scoped Classical
open Set
namespace SevenEighths.HeckeDetectorFiberSpikes
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem fiber_spikes {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(w u).label=label)
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    ∀ u∈rows,
      (w u).zero.re∈Icc (0 : ℝ) 1 ∧
      |(w u).frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T ∧
      U^((2*a-1)*r-2*ε)≤
        ‖polynomial (χ u label) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
          (U^r) (w u).zero.re (w u).frequency‖^2 ∧
      U^((2*a-1)*m-2*ε)≤
        ‖polynomial (χ u label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2 := by
  dsimp only
  intro u hu
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by rw [(w u).left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by rw [(w u).right_exponent hU,hK u hu]
  refine ⟨⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩,(w u).frequency_bound,?_,?_⟩
  · simpa only [hr,hlabel u hu,Witness.frequency] using (w u).inverse_spike
  · simpa only [hm,hlabel u hu,Witness.frequency] using (w u).plain_spike

end SevenEighths.HeckeDetectorFiberSpikes

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotInverseCount
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.HeckeDetectorNoSlotInverseCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount

theorem no_slot_inverse_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (R εm : ℝ) (hR : 0≤R) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ {Label : Type*} (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
        (a ε tstar T allowance : ℝ) (i : ℕ), 1<U → 1/2≤a →
      ∀ (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
        (label : Label) (J K : Fin (dyadicLength U)),
      (∀ u∈rows,(witness u).label=label) →
      (∀ u∈rows,(witness u).left=J) → (∀ u∈rows,(witness u).right=K) →
      0≤Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val)≤R →
      ∀ (data : RowData) (reverse : Bool) (C height : ℝ),0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      (∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows,∀ I : Ideal O,idealCoeff (χ u label) I=
        if reverse then starRingEnd ℂ (idealCoeff (data.character ⟨u.val,u.property.1⟩) I)
        else idealCoeff (data.character ⟨u.val,u.property.1⟩) I) →
      (∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
        let W := twistProfile (logTest
          (orientedProfile reverse (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val)))) n) s t
        RawMoment data W c κ C ∧ RawMoment data (scaleProfile W) c κ C) →
      (rows.card : ℝ)≤(12*(1+height)*(C*K₀))*
        U^(sourceExponent (Real.logb U ((2 : ℝ)^J.val))-
          (2*a-1)*Real.logb U ((2 : ℝ)^J.val)+2*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,he⟩ := no_slot_rowwise_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB R εm hR hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he] with U he
  intro Label rows χ a ε tstar T allowance i hU ha witness label J K hlabel hJ hK hr hrR
    data reverse C height hC hheight hfreq hrows hcoeff hraw
  let r := Real.logb U ((2 : ℝ)^J.val)
  let V := orientedProfile reverse (inverseTest U tstar r)
  have hUp : 0<U := zero_lt_one.trans hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hbase := HeckeDetectorDyadicActual.inverse_profile_support (U^tstar) (U^r)
  have hs : Function.support V⊆Icc (1/4 : ℝ) (9/4) := by
    cases reverse
    · exact hbase
    · simpa only [V,orientedProfile,Bool.true_eq,ite_true,conjugate_profile_support,inverseTest] using hbase
  have hb := HeckeDetectorDyadicActual.inverse_profile_smooth (U^tstar) (U^r)
  have hV : ContDiff ℝ ∞ V := by
    cases reverse
    · exact hb
    · exact conjugate_profile_smooth _ hb
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hσ (u : FreeRow) (hu : u∈rows) : (witness u).zero.re∈Icc (0 : ℝ) 1 := (hsp u hu).1
  have hf (u : FreeRow) (hu : u∈rows) :
      orientedFrequency reverse (witness u).frequency∈Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact (hsp u hu).2.1.trans hfreq
  have hen := he r data rows V (1/4) (9/4) C height (fun u => (witness u).zero.re)
    (fun u => orientedFrequency reverse (witness u).frequency)
    hr hrR hC hheight (by norm_num) (by norm_num) hs hV hrows hσ hf hraw
  have hspike (u : FreeRow) (hu : u∈rows) : U^((2*a-1)*r-2*ε)≤
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2 := by
    have hh := (hsp u hu).2.2.1
    rw [norm_of_oriented_coefficients (χ u label) (data.character ⟨u.val,u.property.1⟩)
      reverse (hcoeff u hu) true _ _ _ _ hD] at hh
    exact hh
  have hen' : ∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2≤
      (12*(1+height)*(C*K₀))*U^(sourceExponent r+εm) := by
    convert (preTransparency := .instances) hen using 1; ring
  have hc' := HeckeDetectorRowCount.card_of_energy rows _ U ((2*a-1)*r-2*ε)
    (sourceExponent r+εm) (12*(1+height)*(C*K₀)) hUp hspike hen'
  convert (preTransparency := .instances) hc' using 1; congr 2; ring

end SevenEighths.HeckeDetectorNoSlotInverseCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

theorem card_eq_sum_fibers {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots ((2*a-1)/2) mesh, ∑ label : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        (fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => (amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u,
      (w u).label,(w u).left,(w u).right)) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

end SevenEighths.HeckeDetectorFiberPartition

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorBatch
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorFiberPartition
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Batch.card_eq_sum_fibers [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i) :
    B.rows.card=∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows bin j J K).card :=
  HeckeDetectorFiberPartition.card_eq_sum_fibers B.rows B.family U a ε tstar T allowance i B.witness
    B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U)

theorem Batch.card_bound [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i)
    (C : ℝ) (exponent : B.Bin→ℝ) (hC : 0≤C) (hU : 0<U)
    (hfiber : ∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
      ((B.fiber bin j J K hne).rows.card : ℝ)≤C*U^(exponent bin)) :
    (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2*C*
      ∑ bin : B.Bin,U^(exponent bin) := by
  have he : (B.rows.card : ℝ)=∑ bin : B.Bin, ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows bin j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C*U^(exponent bin) := by
      apply Finset.sum_le_sum
      intro bin _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows bin j J K).Nonempty
      · exact hfiber bin j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty,Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←mul_assoc]
      rw [←Finset.mul_sum]
      ring

end SevenEighths.HeckeDetectorBatch

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.lengths (F : Fiber M H Label Slot U a ε tstar T allowance i) (hU : 1<U) :
    tstar-F.r-ε≤F.m ∧ F.r≤tstar+ε ∧ F.m≤1/2+75*ε ∧ tstar-1/2-76*ε≤F.r ∧ 0≤F.m :=
  fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hU F.witness
    F.left F.right F.fixed_left F.fixed_right

theorem fiberConstant_bounds (C height K : ℝ) (hC : 0≤C) (hh : 0≤height) (hK : 0≤K) :
    0≤fiberConstant C height K ∧ 192*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*(C*K)≤fiberConstant C height K := by
  have h1 : 0≤192*(1+height)*C := by positivity
  have h2 : 12*(1+height)*C≤192*(1+height)*C := by nlinarith
  have hbig : 192*(1+height)*C≤fiberConstant C height K :=
    le_mul_of_one_le_right h1 (le_max_left _ _)
  refine ⟨h1.trans hbig,hbig,h2.trans hbig,?_⟩
  calc
    _ = (12*(1+height)*C)*K := by ring
    _ ≤ (192*(1+height)*C)*max 1 K := mul_le_mul h2 (le_max_right _ _) hK h1

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorHighCount
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorHighCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1<U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε (3/2) T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance Δ C height i hU ha ha' hε hεsmall hC hh hf Label Slot F moments
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  obtain ⟨hconst,_,_,hconstI⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have hi := hamp F.rows F.family a ε (3/2) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hb : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+(2*ε+εm)) := by
    apply hi.trans
    convert (preTransparency := .instances) mul_le_mul_of_nonneg_right hconstI
      (Real.rpow_nonneg (zero_lt_one.trans hU).le
        (max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+2*ε+εm)) using 1 <;> congr 2; ring
  have hout := high_bin_count hconst hU.le ha (show 2*a-1≤1 by linarith)
    (show 0≤76*ε by positivity) (show 1-76*ε≤F.r by linarith [hgeom.2.2.2.1]) hb
  convert (preTransparency := .instances) hout using 1; congr 2; ring

end SevenEighths.HeckeDetectorHighCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorHighBatchCount
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorHighBatchCount
open HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_batch_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1<U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (3/2) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorHighCount.high_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf Label Slot _ B moments
  have hb := B.card_bound (fiberConstant C height K₀) (fun _=>1-(2*a-1)+78*ε+εm)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      exact hcount a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.HeckeDetectorHighBatchCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCount
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem high_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorHighBatchCount.high_batch_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height q i hU ha ha' hε hε' hC hh hf
  rw [cutoff_eq_high (2*a-1) q ha]
  exact hcount a ε T allowance Δ C height i hU ha.le ha' hε hε' hC hh hf

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (CountParameters M H εm) := by
  obtain ⟨cB,kB,KB,hcB,hcB1,hkB,hKB,hbalanced⟩ := balanced_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH,kH,KH,hcH,hcH1,hkH,hKH,hhigh⟩ := high_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB,kB,cH,kH,hcB,hcB1,hkB,hcH,hcH1,hkH,⟨KB,hKB,hbalanced⟩,⟨KH,hKH,hhigh⟩⟩⟩

end SevenEighths.ProbeFinalAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ParametersSlotLengths
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0<L) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<L) ∧ (∑j,ell j)=1/6 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/(3*L)))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hNL : 1/(3*L)<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  refine ⟨N,hNnat,ell,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤dmax) (hm : 0< mesh) (hR : 0<R) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0< rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=1/6 ∧
      (∀j,0<ell j ∧ dmax*rmin≤ell j ∧ ell j≤dmin*mesh ∧ ell j≤dmin*R) ∧
      (∀d : ℝ,dmin≤d → d≤dmax → ∀j,rmin≤ell j/d ∧ ell j/d≤ mesh ∧ ell j/d≤R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0< rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end SevenEighths.Parameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ParametersDetectorScales
namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_detector_scales (R rmin mesh dmin loss ellMin allowance J : ℝ)
    (hR : 0≤R) (hr : 0< rmin) (hm : 0< mesh) (hd : 0<dmin)
    (hl : 0<loss) (hell : 0<ellMin) (ha : 0<allowance) (hJ : 0≤J) :
    ∃ε e κ cost τ : ℝ,
      0<ε ∧ ε≤1/1000 ∧ ε< rmin*mesh ∧ ε≤allowance ∧
      0<e ∧ e<1/1000 ∧ e≤ellMin/4 ∧ e≤allowance ∧
      0<κ ∧ κ≤1 ∧ 0<cost ∧
      12*e*(22+2)+8*κ+2*cost≤ε/2 ∧
      8*e*R+κ≤ε ∧
      0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*cost ∧
      2*τ*(1+J)≤loss ∧ ∀eps : ℝ,0≤eps → eps≤1 → τ*(2+4*eps)<loss := by
  let ε := min (allowance/2) (min (rmin*mesh/2) (1/2000))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεa : ε≤allowance/2 := min_le_left _ _
  have hεr : ε≤ rmin*mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε≤1/2000 := (min_le_right _ _).trans (min_le_right _ _)
  let e := min (ε/(10000*(1+R))) (min (ellMin/4) (allowance/2))
  have he : 0<e := lt_min (div_pos hε (by positivity)) (lt_min (by positivity) (by positivity))
  have heb : e≤ε/(10000*(1+R)) := min_le_left _ _
  have hep : e*(10000*(1+R))≤ε := (le_div_iff₀ (by positivity)).mp heb
  have heR : 0≤e*R := mul_nonneg he.le hR
  have hel : e≤ellMin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hea : e≤allowance/2 := (min_le_right _ _).trans (min_le_right _ _)
  let κ := ε/1000
  let cost := ε/1000
  have hk : 0<κ := by dsimp [κ]; positivity
  have hc : 0<cost := by dsimp [cost]; positivity
  let τ := min (dmin*cost/16) (min (dmin/4) (loss/(4*(1+J+6))))
  have ht : 0<τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htc : τ≤dmin*cost/16 := min_le_left _ _
  have htd : τ≤dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have htl : τ≤loss/(4*(1+J+6)) := (min_le_right _ _).trans (min_le_right _ _)
  have htJ : τ*(4*(1+J+6))≤loss := (le_div_iff₀ (by positivity)).mp htl
  have hprod : 0≤τ*J := mul_nonneg ht.le hJ
  refine ⟨ε,e,κ,cost,τ,hε,by linarith,by nlinarith [mul_pos hr hm],by linarith,
    he,by nlinarith,hel,by linarith,hk,?_,hc,?_,?_,ht,by linarith,?_,?_,?_⟩
  · dsimp [κ];linarith
  · dsimp [κ,cost];nlinarith
  · dsimp [κ];nlinarith
  · have hp := mul_pos hd hc;linarith
  · nlinarith
  · intro eps heps heps1
    have hp := mul_le_mul_of_nonneg_left heps1 ht.le
    nlinarith
end SevenEighths.Parameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ParametersCentralBudget
namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_central_budget (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by
  let t := min (Δ/8) (1/100000000)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have htΔ : t≤Δ/8 := min_le_left _ _
  have ht1 : t≤1/100000000 := min_le_right _ _
  refine ⟨t,ht,by linarith,ht1,by norm_num,by norm_num,by linarith,
    by norm_num,by linarith,by linarith,by linarith,by linarith,?_⟩
  intro N
  let allowance := t/((N:ℝ)+2000)
  have hden : 0<(N:ℝ)+2000 := by positivity
  have ha : 0<allowance := div_pos ht hden
  have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
  refine ⟨allowance,ha,?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000*ε≤t := by linarith
  have het : 2000*e≤t := by linarith
  have hepsN : ((N:ℝ)+2000)*eps≤t := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
  constructor <;> nlinarith
end SevenEighths.Parameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ParametersProbeWindows
namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.Parameters

theorem exists_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w ⊆ Set.Ioo 1 2 ∧ (∀ x,0≤w x ∧ w x≤1) ∧
    w (3/2)=1 ∧ w≠0 ∧ (∀ x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W ⊆ Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,hs,hc,hw,hr,hval⟩ := exists_contDiff_tsupport_subset
    (n:=⊤) (E:=ℝ) (s:=Set.Ioo 1 2) (x:=3/2)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
  let f : ℝ→ℂ := fun x=>(w x:ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hw
  have hfc : HasCompactSupport f := hc.comp_left (show (fun x:ℝ=>(x:ℂ)) 0=0 by simp)
  let W : SchwartzMap ℝ ℂ := hfc.toSchwartzMap hf
  have hne : w≠0 := by intro hz;have := congrFun hz (3/2);simp [hval] at this
  refine ⟨w,W,hw,hc,(subset_tsupport w).trans hs,fun x=>hr ⟨x,rfl⟩,hval,hne,
    fun _=>rfl,?_,?_,fun _=>rfl,?_⟩
  · intro hz
    apply hne
    funext x
    have h := congrArg (fun F : SchwartzMap ℝ ℂ => (F x).re) hz
    change w x=0 at h
    exact h
  · intro x hx
    have hwx : w x≠0 := by intro h;apply hx;change (w x:ℂ)=0;rw [h];rfl
    exact Set.Ioo_subset_Icc_self (hs (subset_tsupport w hwx))
  · intro x
    exact (hr ⟨x,rfl⟩).1
end SevenEighths.Parameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ParametersFixedSource
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.Parameters
open ProbePhysical ProbeHighRowFamily CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma fixed_bad_primes_prime : ∀ P∈fixedBadPrimes,Prime P := by
  intro P hP
  rcases Finset.mem_insert.mp hP with hP|hP
  · subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      lambdaIdeal_maximal.isPrime
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:O)≠0))
      twoIdeal_maximal.isPrime

theorem exists_fixed_source (e : ℝ) (he : 0<e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀P∈S₀,Prime P) :
    ∃ S : Finset (Ideal O), S₀⊆S ∧ SourceExclusions S ∧
      FirstTail (4*e) S ∧ (∀P∈S,P.IsMaximal) := by
  obtain ⟨S,hsub,hS,hfirst⟩ := exists_both_source_exclusions (4*e) (by positivity)
    (S₀∪fixedBadPrimes)
    (fun P hP => (Finset.mem_union.mp hP).elim (hS₀ P) (fixed_bad_primes_prime P))
    Finset.subset_union_right
  refine ⟨S,Finset.subset_union_left.trans hsub,hS,hfirst,?_⟩
  intro P hP
  exact (Ideal.isPrime_of_prime (hS.prime P hP)).isMaximal (hS.prime P hP).ne_zero

theorem exists_fixed_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w⊆Set.Ioo 1 2 ∧ tsupport w⊆Set.Ioi 0 ∧
    (∀x,0≤w x ∧ w x≤1) ∧ w≠0 ∧ (∀x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W⊆Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,W,hw,hc,hs,hb,hv,hn,he,hWn,hWs,hr,hp⟩ := exists_probe_window
  refine ⟨w,W,hw,hc,hs,?_,hb,hn,he,hWn,hWs,hr,hp⟩
  have hcl : tsupport w⊆Set.Icc 1 2 :=
    closure_minimal (hs.trans Set.Ioo_subset_Icc_self) isClosed_Icc
  intro x hx
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hcl hx).1
end SevenEighths.Parameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

theorem exists_source_data {Δ : ℝ} (D : HighData Δ) : Nonempty (SourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

theorem source_count_parameters {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

end SevenEighths.ProbeFinalAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ParametersHighDataFine
namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.Parameters

theorem exists_high_data_fine (Δ:ℝ)(hΔ:0<Δ)(mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0<t→0< mesh t):
    ∃D:HighData Δ,∀j,D.ell j≤ mesh D.t/200:=by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j≤ mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring

end SevenEighths.Parameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyChosenData
namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem chosen_input_of_fine_oai (h:FineMomentInput):ChosenMomentInput:=by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩:=h hβ
  obtain ⟨D,hD⟩:=exists_high_data_fine (HeckeZeroSupremum.beta-7/8) (by linarith) mesh hmesh
  obtain ⟨F⟩:=exists_source_data D
  obtain ⟨counts⟩:=source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

end SevenEighths.ProbeFinalAssembly

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeFinalAssembly.chosen_input_of_fine_oai := @OAI.SevenEighths.ProbeFinalAssembly.chosen_input_of_fine_oai
