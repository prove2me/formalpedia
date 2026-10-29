-- Prove2me | solution 1 for OAI.ContingencyTables.RootedPlainTrial.trial_failure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:35:46.993983+00:00
-- url     : https://prove2.me/submissions/8fe6cc0a-ff15-487f-baad-cbe5804dfddb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_RootedObservationStart_observed_failure_near
import Theorems.Thm_OAI_ContingencyTables_RootedOracleDensity_goodEstimate_failure

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_AnnealingMultipliers
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion's multiplier update from empirical type counts

The old multiplier cancels from the update relative to the current ideal
multiplier. Relative accuracy of two positive type means, followed by the
proved adjacent-parameter factor two, gives the required factor four at
the next parameter. This is deterministic algebra of the actual update.
-/

namespace ContingencyTables.AnnealingMultipliers

variable {eta p q ph qh w ideal nextIdeal : ℝ}

theorem empirical_positive (hp : 0<p) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph) : 0<ph := by
  have h : 0<(1-eta)*p := mul_pos (by linarith) hp
  exact h.trans_le hph

/-- The normalized ratio of two empirically observed positive means. -/
theorem relative_ratio (hp : 0<p) (hq : 0<q) (he0 : 0≤eta) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph ∧ ph≤(1+eta)*p)
    (hqh : (1-eta)*q≤qh ∧ qh≤(1+eta)*q) :
    0<ph*q/(qh*p) ∧
      1/2≤ph*q/(qh*p) ∧ ph*q/(qh*p)≤2 ∧
      |Real.log (ph*q/(qh*p))|≤4*eta := by
  have hp' := empirical_positive hp he hph.1
  have hq' := empirical_positive hq he hqh.1
  have hden : 0<qh*p := mul_pos hq' hp
  have hr : 0<ph*q/(qh*p) := div_pos (mul_pos hp' hq) hden
  have hlow : (1-eta)*(p*q)≤ph*q := by nlinarith [mul_le_mul_of_nonneg_right hph.1 hq.le]
  have hupp : ph*q≤(1+eta)*(p*q) := by nlinarith [mul_le_mul_of_nonneg_right hph.2 hq.le]
  have dlow : (1-eta)*(p*q)≤qh*p := by nlinarith [mul_le_mul_of_nonneg_right hqh.1 hp.le]
  have dupp : qh*p≤(1+eta)*(p*q) := by nlinarith [mul_le_mul_of_nonneg_right hqh.2 hp.le]
  have hpq : 0≤p*q := (mul_pos hp hq).le
  have htwice : (1+eta)*(p*q)≤2*((1-eta)*(p*q)) := by
    have := mul_nonneg (show 1-3*eta≥0 by linarith) hpq
    nlinarith
  have hlo : 1/2≤ph*q/(qh*p) := by
    rw [le_div_iff₀ hden]
    linarith
  have hup : ph*q/(qh*p)≤2 := by
    rw [div_le_iff₀ hden]
    linarith
  have hstretch : (1+eta)*(p*q)≤(1+4*eta)*((1-eta)*(p*q)) := by
    have hcoeff : 0≤2*eta-4*eta^2 := by nlinarith
    have := mul_nonneg hcoeff hpq
    nlinarith
  have hscale : 0≤1+4*eta := by linarith
  have hrup : ph*q/(qh*p)≤1+4*eta := by
    rw [div_le_iff₀ hden]
    have := mul_le_mul_of_nonneg_left dlow hscale
    nlinarith
  have hinvup : (ph*q/(qh*p))⁻¹≤1+4*eta := by
    rw [inv_div]
    rw [div_le_iff₀ (mul_pos hp' hq)]
    have := mul_le_mul_of_nonneg_left hlow hscale
    nlinarith
  have hlogup := Real.log_le_sub_one_of_pos hr
  have hloglo := Real.one_sub_inv_le_log_of_pos hr
  refine ⟨hr,hlo,hup,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith

/-- The concrete update w*(observed plain count)/(observed defect count)
is good for the next parameter. Earlier multiplier errors do not compound. -/
theorem update_good (hp : 0<p) (hq : 0<q) (hw : 0<w)
    (he0 : 0≤eta) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph ∧ ph≤(1+eta)*p)
    (hqh : (1-eta)*q≤qh ∧ qh≤(1+eta)*q)
    (hideal : w*p/q=ideal)
    (hnext : ideal/2≤nextIdeal ∧ nextIdeal≤2*ideal) :
    nextIdeal/4≤w*ph/qh ∧ w*ph/qh≤4*nextIdeal := by
  have h := relative_ratio hp hq he0 he hph hqh
  have hq' := empirical_positive hq he hqh.1
  have hi : 0 < ideal := by rw [← hideal]; positivity
  have hid : w*ph/qh=ideal*(ph*q/(qh*p)) := by
    rw [← hideal]
    field_simp [ne_of_gt hp,ne_of_gt hq,ne_of_gt hq']
  rw [hid]
  have hlo := mul_le_mul_of_nonneg_left h.2.1 hi.le
  have hup := mul_le_mul_of_nonneg_left h.2.2.1 hi.le
  constructor <;> nlinarith [hnext.1,hnext.2]

end ContingencyTables.AnnealingMultipliers

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section DerivativeClosure
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance12 : Fintype ι] [sectionInstance13 : DecidableEq ι]

omit sectionInstance12 in
lemma slotDirection_nonneg [Fintype ι] (E : Finset ι) (i : ι) : 0 ≤ slotDirection E i := by
  unfold slotDirection
  split_ifs <;> norm_num

end DerivativeClosure

section MatroidWeights
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance30 : Fintype ι] [sectionInstance31 : DecidableEq ι]

omit sectionInstance31 in
lemma coeffDeriv_scale [DecidableEq ι] (a : ι → ℝ) (f : Set ι → ℝ) (c : ℝ) (A : Set ι) :
    coeffDeriv a (fun S => c * f S) A = c * coeffDeriv a f A := by
  simp only [coeffDeriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

lemma coeffDerivs_scale (as : List (ι → ℝ)) (f : Set ι → ℝ) (c : ℝ) (A : Set ι) :
    coeffDerivs as (fun S => c * f S) A = c * coeffDerivs as f A := by
  induction as generalizing A with
  | nil => rfl
  | cons a as ih =>
    change coeffDeriv a (coeffDerivs as (fun S => c * f S)) A = _
    have h : coeffDerivs as (fun S => c * f S) = fun S => c * coeffDerivs as f S := by
      funext S; exact ih S
    rw [h,coeffDeriv_scale]
    rfl

end MatroidWeights

section Observable
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance52 : Fintype Γ] [DecidableEq Γ]

omit sectionInstance52 in
lemma defectTypes_card_le [Fintype Γ] (gs : List (Γ × Γ)) :
    (defectTypes gs).card ≤ gs.length*gs.length := by
  calc
    _ ≤ gs.toFinset.card*gs.toFinset.card := by simp [defectTypes,Finset.offDiag_card]
    _ ≤ _ := Nat.mul_le_mul (List.toFinset_card_le _) (List.toFinset_card_le _)

lemma chainTotal_le (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hf : ∀ S, 0 < f S)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainTotal gs w f ≤ 5*(gs.length:ℝ)^2*slotTotal gs f ∅ := by
  rw [chainTotal_eq gs hgs hcover w f]
  have hz := slotTotal_pos gs f hf ∅ hgs
  have hc : (∑ pr ∈ defectTypes gs, w pr.1 pr.2*slotDefect gs f ∅ pr.1 pr.2) ≤
      (defectTypes gs).card*(4*slotTotal gs f ∅) := by
    calc
      _ ≤ ∑ _pr ∈ defectTypes gs, 4*slotTotal gs f ∅ := by
        apply Finset.sum_le_sum
        intro pr hm
        obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
        exact (le_div_iff₀ (slotDefect_pos gs f hf ∅ hgs pr.1 pr.2 hp hr hpr)).mp
          (hupper pr.1 hp pr.2 hr hpr)
      _ = _ := by simp
  have hcard : ((defectTypes gs).card:ℝ) ≤ (gs.length:ℝ)^2 := by
    exact_mod_cast (show (defectTypes gs).card ≤ gs.length^2 by simpa [pow_two] using defectTypes_card_le gs)
  have hn : 1 ≤ (gs.length:ℝ) := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn2 : 1 ≤ (gs.length:ℝ)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcard (show 0 ≤ 4*slotTotal gs f ∅ by positivity)]

end Observable

open scoped BigOperators Classical

section TracePoincare
open scoped Classical BigOperators
variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
  (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
  (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)

lemma metropolis_insideMass :
    (metropolisChain gs hgs hne hcover w f hw hf).insideMass (plainPredicate gs) =
      slotTotal gs f ∅/chainTotal gs w f := by
  change (∑ S : PlainIndex gs,chainWeight gs w f S.val.val/chainTotal gs w f) = _
  have he (S : PlainIndex gs) : chainWeight gs w f S.val.val = f S.val.val := by
    rw [chainWeight,chainMultiplier_plain gs w S.val.val S.property,one_mul]
  simp_rw [he]
  rw [← Finset.sum_div,plainIndex_sum,slotTotal_eq_plain_sum gs hgs hcover]

lemma metropolisTrace_pi (S : PlainIndex gs) :
    (metropolisTrace gs hgs hne hcover w f hw hf).π S = f S.val.val/slotTotal gs f ∅ := by
  change (chainWeight gs w f S.val.val/chainTotal gs w f)/
    (metropolisChain gs hgs hne hcover w f hw hf).insideMass (plainPredicate gs) = _
  rw [metropolis_insideMass gs hgs hne hcover w f hw hf,chainWeight,
    chainMultiplier_plain gs w S.val.val S.property,one_mul]
  field_simp [(chainTotal_pos gs hgs hcover w f hf hw).ne']

end TracePoincare

section SamplingObservables
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance85 : Fintype Γ] [DecidableEq Γ]
lemma plainObservable_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) : chainMean gs w f (plainObservable gs g) =
      slotTotal gs (fun S =>  f S*g S) ∅/chainTotal gs w f := by
  unfold chainMean
  congr 1
  simp only [chainWeight,mul_assoc]
  rw [chain_sum_decomposition,slotTotal_eq_plain_sum gs hgs hcover]
  have hplain : (∑ S with PlainState gs S,f S*plainObservable gs g S)=
      ∑ S with PlainState gs S,f S*g S := by
    apply Finset.sum_congr rfl
    intro S hS
    simp [plainObservable,(Finset.mem_filter.mp hS).2]
  rw [hplain]
  have hdef : ∀ pr ∈ defectTypes gs,(∑ S with DefectState gs pr.1 pr.2 S,f S*plainObservable gs g S)=0 := by
    intro pr hpr
    apply Finset.sum_eq_zero
    intro S hS
    simp [plainObservable,((Finset.mem_filter.mp hS).2).not_plain]
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro pr hpr
  rw [hdef pr hpr,mul_zero]
lemma defectIndicator_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (p r : Γ × Γ) (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    chainMean gs w f (defectIndicator gs p r) =
      w p r*slotDefect gs f ∅ p r/chainTotal gs w f := by
  unfold chainMean
  congr 1
  simp only [chainWeight,mul_assoc]
  rw [chain_sum_decomposition,slotDefect_eq_defect_sum gs hgs hcover f p r hp hr hpr]
  have hplain : (∑ S with PlainState gs S,f S*defectIndicator gs p r S)=0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hh : ¬DefectState gs p r S := fun h =>  h.not_plain (Finset.mem_filter.mp hS).2
    simp [defectIndicator,hh]
  rw [hplain,zero_add]
  rw [Finset.sum_eq_single (p,r)]
  · congr 1
    apply Finset.sum_congr rfl
    intro S hS
    simp [defectIndicator,(Finset.mem_filter.mp hS).2]
  · intro pr hm hne
    have he : ∀ S,DefectState gs pr.1 pr.2 S → ¬DefectState gs p r S := by
      intro S hS h
      exact hne (Prod.ext (hS.unique h).1 (hS.unique h).2)
    have hz : (∑ S with DefectState gs pr.1 pr.2 S,f S*defectIndicator gs p r S)=0 := by
      apply Finset.sum_eq_zero
      intro S hS
      simp [defectIndicator,he S (Finset.mem_filter.mp hS).2]
    rw [hz,mul_zero]
  · intro h
    exact (h ((mem_defectTypes gs (p,r)).mpr ⟨hp,hr,hpr⟩)).elim
lemma plain_mass_lower (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (hupper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    1/(5*(gs.length:ℝ)^2) ≤ slotTotal gs f ∅/chainTotal gs w f := by
  have hz := slotTotal_pos gs f hf ∅ hgs
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  apply (div_le_div_iff₀ (by positivity) hΛ).mpr
  simpa only [one_mul,mul_one,mul_comm] using chainTotal_le gs hgs hne hcover w f hf hupper
end SamplingObservables

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
section ActualAnnealing
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance93 : Fintype Γ] [sectionInstance94 : DecidableEq Γ]
lemma slotTotal_mono (ps : List (Γ × Γ)) (f g : Set Γ → ℝ)
    (h : ∀ S,f S ≤ g S) (A : Set Γ) : slotTotal ps f A ≤ slotTotal ps g A := by
  induction ps generalizing A with
  | nil => exact h A
  | cons p ps ih =>
    change coeffDeriv (pairDirection p) (slotTotal ps f) A ≤ coeffDeriv (pairDirection p) (slotTotal ps g) A
    unfold coeffDeriv
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · rfl
    · exact mul_le_mul_of_nonneg_left (ih _) (slotDirection_nonneg _ _)
lemma slotTotal_scale (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (c : ℝ) (A : Set Γ) :
    slotTotal ps (fun S => c*f S) A=c*slotTotal ps f A := coeffDerivs_scale _ _ _ _
lemma plain_probability_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) :
    chainMean gs w f (plainObservable gs (fun _ => 1))=slotTotal gs f ∅/chainTotal gs w f := by
  rw [plainObservable_mean gs hgs hcover]
  simp
lemma weight_mean_identity (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (f : Set Γ → ℝ) (hf : ∀ S,0<f S)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hw : ∀ p r,0<w p r)
    (p r : Γ × Γ) (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    w p r*(chainMean gs w f (plainObservable gs (fun _ => 1))/
      chainMean gs w f (defectIndicator gs p r))=slotTotal gs f ∅/slotDefect gs f ∅ p r := by
  rw [plain_probability_mean gs hgs hcover,defectIndicator_mean gs hgs hcover _ _ p r hp hr hpr]
  field_simp [(chainTotal_pos gs hgs hcover w f hf hw).ne',(hw p r).ne']

lemma relative_error_bounds (x m η : ℝ) (h : |x-m| ≤ η*m) :
    (1-η)*m ≤ x ∧ x ≤ (1+η)*m := by
  obtain ⟨h1,h2⟩ := abs_le.mp h
  constructor <;> nlinarith
lemma accurate_plain (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (η : ℝ) (l : List (Set Γ)) (h : AccuratePhase gs w f g η l) :
    (1-η)*chainMean gs w f (plainObservable gs (fun _ => 1)) ≤ empirical (plainObservable gs (fun _ => 1)) l ∧
    empirical (plainObservable gs (fun _ => 1)) l ≤ (1+η)*chainMean gs w f (plainObservable gs (fun _ => 1)) :=
  relative_error_bounds _ _ _ (h (.inl none))
lemma accurate_defect (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (η : ℝ) (l : List (Set Γ)) (h : AccuratePhase gs w f g η l)
    (p r : Γ × Γ) (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    (1-η)*chainMean gs w f (defectIndicator gs p r) ≤ empirical (defectIndicator gs p r) l ∧
    empirical (defectIndicator gs p r) l ≤ (1+η)*chainMean gs w f (defectIndicator gs p r) :=
  relative_error_bounds _ _ _ (h (.inl (some ⟨(p,r),(mem_defectTypes gs (p,r)).mpr ⟨hp,hr,hpr⟩⟩)))

end ActualAnnealing
section WarmLift
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance102 : Fintype Γ] [sectionInstance103 : DecidableEq Γ]
omit sectionInstance102 sectionInstance103 in
lemma plainLift_nonneg [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (ν : PlainIndex gs → ℝ) (hν : ∀ x,0 ≤ ν x) (S : ChainIndex gs) :
    0 ≤ plainLift gs ν S := by unfold plainLift; split_ifs; exact hν _; rfl
omit sectionInstance103 in
lemma plainLift_mass [DecidableEq Γ] (gs : List (Γ × Γ)) (ν : PlainIndex gs → ℝ) :
    (∑ S,plainLift gs ν S)=∑ S : PlainIndex gs,ν S := by
  have h := Fintype.sum_subtype_add_sum_subtype (plainPredicate gs) (fun S => plainLift gs ν S)
  have ht : ∀ S : PlainIndex gs,plainLift gs ν S.val=ν S := by
    intro S; exact dite_eq_left S.property
  have hf : ∀ S : {S : ChainIndex gs // ¬plainPredicate gs S},plainLift gs ν S.val=0 := by
    intro S; exact dite_eq_right S.property
  simp_rw [ht,hf,Finset.sum_const_zero,add_zero] at h
  exact h.symm
lemma plainLift_warm (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hf : ∀ S,0<f S) (hw : GoodMultipliers gs f w)
    (ν : PlainIndex gs → ℝ)
    (hν : ∀ S,ν S ≤ 2*(metropolisTrace gs hgs hne hcover w f hw.positive hf).π S)
    (S : ChainIndex gs) :
    plainLift gs ν S ≤ (10*(gs.length:ℝ)^2)*chainWeight gs w f S.val/chainTotal gs w f := by
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw.positive
  unfold plainLift
  split_ifs with hS
  · have hn : (0:ℝ)<gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
    have hz := slotTotal_pos gs f hf ∅ hgs
    have hbound := plain_mass_lower gs hgs hne hcover w f hw.positive hf hw.upper
    have hh := hν ⟨S,hS⟩
    rw [metropolisTrace_pi] at hh
    rw [chainWeight,chainMultiplier_plain gs w S.val hS,one_mul]
    apply hh.trans
    rw [← mul_div_assoc,div_le_div_iff₀ hz hΛ]
    have hm := (div_le_div_iff₀ (by positivity : (0:ℝ)<5*(gs.length:ℝ)^2) hΛ).mp hbound
    nlinarith [mul_nonneg (hf S.val).le (sub_nonneg.mpr (show chainTotal gs w f ≤ 5*(gs.length:ℝ)^2*slotTotal gs f ∅ by nlinarith))]
  · exact div_nonneg (mul_nonneg (by positivity) (chainWeight_pos gs w f hw.positive hf S.val).le) hΛ.le
end WarmLift
open scoped BigOperators Classical

end

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    uniformAverage (fun x => f x+g x)=uniformAverage f+uniformAverage g := by
  simp [uniformAverage,Finset.sum_add_distrib,add_div]
lemma uniformAverage_mul_left {X : Type*} [Fintype X] (r : ℝ) (f : X → ℝ) :
    uniformAverage (fun x => r*f x)=r*uniformAverage f := by
  simp [uniformAverage,← Finset.mul_sum,mul_div_assoc]
lemma uniformAverage_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun y => f (x,y))) := by
  simp only [uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← Finset.sum_div]
  ring
lemma uniformAverage_fin_succ {X : Type*} [Fintype X] (D : ℕ)
    (f : (Fin (D+1) → X) → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun rest => f (Fin.cons x rest))) := by
  rw [← uniformAverage_equiv (Fin.consEquiv (fun _ : Fin (D+1) => X)) f,uniformAverage_prod]
  rfl

lemma uniformAverage_sum {X J : Type*} [Fintype X] [Fintype J] (f : J → X → ℝ) :
    uniformAverage (fun x => ∑ j,f j x)=∑ j,uniformAverage (f j) := by
  unfold uniformAverage
  rw [Finset.sum_comm,Finset.sum_div]

lemma uniformAverage_nonneg {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x,0≤f x) : 0≤uniformAverage f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)
lemma uniformAverage_mono {X : Type*} [Fintype X] (f g : X → ℝ)
    (hfg : ∀ x,f x≤g x) : uniformAverage f≤uniformAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hfg x)) (Nat.cast_nonneg _)
section RationalSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance112 : Fintype Γ] [sectionInstance113 : DecidableEq Γ]
omit sectionInstance112 sectionInstance113 in
lemma rationalEmpirical_cast [Fintype Γ] [DecidableEq Γ] (H : Set Γ → ℚ) (l : List (Set Γ)) :
    (rationalEmpirical H l:ℝ)=empirical (fun S => (H S:ℝ)) l := by
  simp [rationalEmpirical,empirical,Rat.cast_list_sum,List.map_map,Function.comp_def]
omit sectionInstance112 sectionInstance113 in
lemma rationalPlain_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (S : Set Γ) :
    (rationalPlain gs g S:ℝ)=plainObservable gs (fun S => (g S:ℝ)) S := by
  unfold rationalPlain plainObservable; split_ifs <;> simp
omit sectionInstance112 sectionInstance113 in
lemma rationalDefect_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) :
    (rationalDefect gs p r S:ℝ)=defectIndicator gs p r S := by
  unfold rationalDefect defectIndicator; split_ifs <;> simp
lemma rationalLearn_cast (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (l : List (Set Γ)) (p r : Γ × Γ) :
    (rationalLearn gs w l p r:ℝ)=learnedMultipliers gs (fun p r => (w p r:ℝ)) l p r := by
  unfold rationalLearn learnedMultipliers
  split_ifs <;> simp [rationalEmpirical_cast,rationalPlain_cast,rationalDefect_cast]
end RationalSampling

open scoped BigOperators Classical

end

open scoped BigOperators Classical

section ActualSize
open scoped BigOperators Classical
lemma indicator_list_sum {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℚ) else 0)).sum=(l.countP (fun x => decide (P x)):ℚ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]
end ActualSize

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

lemma median_bad_count (l : List ℚ) (hl : 0<l.length) (a b : ℚ)
    (hbad : ¬(a ≤ rationalMedian l ∧ rationalMedian l≤b)) :
    l.length ≤ 2*l.countP (outsideInterval a b) := by
  let s := l.mergeSort (· ≤ ·)
  have hlen : s.length=l.length := List.length_mergeSort _
  have hs : s.SortedLE := List.sortedLE_mergeSort
  have hk : l.length/2 < s.length := by rw [hlen]; omega
  have he : rationalMedian l=s[l.length/2] := List.getD_eq_getElem s 0 hk
  rw [he] at hbad
  have hc : s.countP (outsideInterval a b)=l.countP (outsideInterval a b) :=
    List.Perm.countP_eq _ (List.mergeSort_perm _ _)
  by_cases ha : a ≤ s[l.length/2]
  · have hb : b < s[l.length/2] := lt_of_not_ge (fun hh => hbad ⟨ha,hh⟩)
    have htail : (s.drop (l.length/2)).countP (outsideInterval a b)=(s.drop (l.length/2)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_drop]
      apply decide_eq_true
      intro hh
      have hm := hs.getElem_le_getElem_of_le (i := l.length/2) (j := l.length/2+i) (hi := hk) (hj := by simp only [List.length_drop] at hi; omega) (by omega)
      exact (not_le_of_gt (hb.trans_le hm)) hh.2
    have hdecomp := List.countP_append (p := outsideInterval a b)
      (l₁ := s.take (l.length/2)) (l₂ := s.drop (l.length/2))
    rw [List.take_append_drop,htail,hc,List.length_drop,hlen] at hdecomp
    omega
  · have hfront : (s.take (l.length/2+1)).countP (outsideInterval a b)=(s.take (l.length/2+1)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_take]
      apply decide_eq_true
      intro hh
      have hi' : i≤l.length/2 := by simp only [List.length_take] at hi; omega
      have hm := hs.getElem_le_getElem_of_le (i := i) (j := l.length/2) (hi := by simp only [List.length_take] at hi; omega) (hj := hk) hi'
      exact ha (hh.1.trans hm)
    have hdecomp := List.countP_append (p := outsideInterval a b)
      (l₁ := s.take (l.length/2+1)) (l₂ := s.drop (l.length/2+1))
    rw [List.take_append_drop,hfront,hc,List.length_take,hlen] at hdecomp
    omega

lemma uniformAverage_mul_const {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    uniformAverage (fun x => f x*c)=uniformAverage f*c := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring

lemma countP_ofFn_cons {X : Type*} (p : X → Bool) (x : X) {R : ℕ} (xs : Fin R → X) :
    (List.ofFn (Fin.cons x xs)).countP p=(if p x then 1 else 0)+(List.ofFn xs).countP p := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,List.countP_cons]
  change (List.ofFn xs).countP p+(if p x then 1 else 0)=(if p x then 1 else 0)+(List.ofFn xs).countP p
  omega

lemma independent_bad_moment {X : Type*} [Fintype X] [Nonempty X]
    (bad : X → Bool) (R : ℕ) :
    uniformAverage (fun xs : Fin R → X => (4:ℝ)^((List.ofFn xs).countP bad))=
      (1+3*uniformAverage (fun x => if bad x then (1:ℝ) else 0))^R := by
  induction R with
  | zero => simp [List.ofFn_zero,uniformAverage_const]
  | succ R ih =>
    rw [uniformAverage_fin_succ]
    simp_rw [countP_ofFn_cons,pow_add,uniformAverage_mul_left,ih]
    rw [uniformAverage_mul_const]
    have he : (fun x : X => (4:ℝ)^(if bad x then 1 else 0:ℕ))=
        fun x => 1+3*(if bad x then (1:ℝ) else 0) := by
      funext x; cases bad x <;> norm_num
    rw [he,uniformAverage_add,uniformAverage_const,uniformAverage_mul_left,pow_succ]
    ring

lemma countP_map {X Y : Type*} (l : List X) (f : X → Y) (p : Y → Bool) :
    (l.map f).countP p=l.countP (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.countP_cons,ih]

theorem median_failure_bound {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (a b : ℚ) (R : ℕ) (hR : 0<R)
    (hbad : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0)≤5/16) :
    uniformAverage (fun xs : Fin R → X =>
      if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i))))
      then (1:ℝ) else 0) ≤ (31/32:ℝ)^R := by
  let bad : X → Bool := fun x => outsideInterval a b (output x)
  have hx : ∀ xs : Fin R → X,
      (if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i)))) then (1:ℝ) else 0)
      ≤ (4:ℝ)^((List.ofFn xs).countP bad)/(2:ℝ)^R := by
    intro xs
    by_cases he : outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i))))=true
    · rw [ite_eq_left he]
      have hc := median_bad_count (List.ofFn (fun i => output (xs i))) (by simpa using hR) a b (by
        simpa only [outsideInterval,decide_eq_true_eq] using he)
      have hmap : List.ofFn (fun i => output (xs i))=(List.ofFn xs).map output := by rw [List.map_ofFn]; rfl
      rw [hmap,countP_map,List.length_map,List.length_ofFn] at hc
      have hp : (2:ℝ)^R≤4^((List.ofFn xs).countP bad) := by
        calc
          (2:ℝ)^R ≤ 2^(2*((List.ofFn xs).countP bad)) := pow_le_pow_right₀ (by norm_num) hc
          _ = _ := by rw [pow_mul]; norm_num
      exact (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
    · rw [ite_eq_right he]; positivity
  have hm := uniformAverage_mono _ _ hx
  have hrw : uniformAverage (fun xs : Fin R → X => (4:ℝ)^((List.ofFn xs).countP bad)/(2:ℝ)^R)=
      (1+3*uniformAverage (fun x => if bad x then (1:ℝ) else 0))^R/(2:ℝ)^R := by
    simp_rw [div_eq_mul_inv]
    rw [uniformAverage_mul_const,independent_bad_moment]
  rw [hrw] at hm
  apply hm.trans
  rw [←div_pow]
  apply pow_le_pow_left₀ (by
    apply div_nonneg _ (by norm_num)
    have hz := uniformAverage_nonneg (fun x => if bad x then (1:ℝ) else 0) (by intro x; split_ifs <;> norm_num)
    linarith)
  dsimp [bad] at *
  linarith

lemma repetitionCount_pos (δ : ℚ) : 0 < repetitionCount δ := by unfold repetitionCount; omega
lemma rational_binary_accuracy (δ : ℚ) (hδ : 0<δ) :
    (1/2:ℝ)^(δ.den.bits.length+1) ≤ (δ:ℝ) := by
  have hd : (0:ℝ)<δ.den := by exact_mod_cast δ.den_pos
  have hn : (1:ℝ)≤(δ.num:ℝ) := by exact_mod_cast (show (1:ℤ)≤δ.num by have h := Rat.num_pos.mpr hδ; omega)
  have hp : (δ.den:ℝ)≤(2:ℝ)^(δ.den.bits.length+1) := by
    exact_mod_cast (Nat.le_of_lt ((Nat.size_le.mp (show δ.den.size≤δ.den.bits.length+1 by rw [Nat.size_eq_bits_len]; omega))))
  rw [one_div,inv_pow,Rat.cast_def]
  apply le_trans (inv_anti₀ hd hp)
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hn hd.le
lemma confidence_decay (δ : ℚ) (hδ : 0<δ) :
    (31/32:ℝ)^(repetitionCount δ) ≤ (δ:ℝ) := by
  unfold repetitionCount
  rw [pow_mul]
  apply le_trans _ (rational_binary_accuracy δ hδ)
  apply pow_le_pow_left₀ (by positivity)
  norm_num

theorem median_confidence {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (a b : ℚ) (δ : ℚ) (hδ : 0<δ)
    (hbad : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0)≤5/16) :
    1-(δ:ℝ) ≤ uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
  have h := (median_failure_bound output a b (repetitionCount δ) (repetitionCount_pos δ) hbad).trans
    (confidence_decay δ hδ)
  have he : (fun xs : Fin (repetitionCount δ) → X =>
      if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i)))) then (1:ℝ) else 0)=
    fun xs => 1-(if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
    funext xs
    simp only [outsideInterval,decide_eq_true_eq]
    split_ifs <;> simp_all
  rw [he] at h
  have hei : uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      1-(if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0))=
      1-uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
    unfold uniformAverage
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    rw [sub_div,div_self (by exact_mod_cast ne_of_gt (Fintype.card_pos))]
  rw [hei] at h
  linarith

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

end CommonBasesFPRAS

open CommonBasesFPRAS

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestPhysicalCompletion ForestLiteralCount

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Absolute component totals sum to at most the total absolute demand.
Each vertex is counted in one component, including isolated vertices. -/
theorem sum_abs_componentTotal (root : V → V) (r : V → ℝ) :
    (∑ a, |∑ v, if root v=a then r v else 0|)≤∑ v, |r v| := by
  calc
    _ ≤ ∑ a, ∑ v, |if root v=a then r v else 0| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      have he (a v : V) : |if root v=a then r v else 0|=
          if root v=a then |r v| else 0 := by split_ifs <;> simp
      simp_rw [he]
      rw [Finset.sum_comm]
      simp

end Generic

end ContingencyTables.ForestRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionAnnealing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Adjacent actual companion weights and ideal multipliers

The parameter step is 1/(H/A). Its factor-two bounds are proved from
the literal forest penalty bound, then passed to the actual labelled
weights and their exact transversal/defect totals.
-/

namespace ContingencyTables.CompanionAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The source's j*A/H parameter is exactly j/(H/A), for its literal
integer H=10*A*d²*(W+1). The arbitrary positive penalty coefficient
therefore cancels from every adjacent-phase estimate below. -/
lemma source_parameter (A : Instance I J) (coefficient j : ℕ) (hc : 0< coefficient) :
    (j:ℝ)*(coefficient:ℝ)/((10*coefficient*A.d^2*(A.W+1):ℕ):ℝ)=
      (j:ℝ)/scale A := by
  have hcR : (coefficient:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  have hQ : scale A≠0 := (scale_positive A).ne'
  have he : ((10*coefficient*A.d^2*(A.W+1):ℕ):ℝ)=(coefficient:ℝ)*scale A := by
    unfold scale
    push_cast
    ring
  rw [he]
  field_simp [hcR,hQ]

end ContingencyTables.CompanionAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinPopulation
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact integer bin populations for the companion weight evaluator -/

namespace ContingencyTables.CompanionBinPopulation

open scoped BigOperators Classical

variable {C : Type*} [Fintype C]

lemma assignment_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    Fintype.card (Assignments B N v)=∏ c,(FairBits.fiber B (N c) (v c)).card := by
  simp only [Assignments,Fintype.card_pi,Fintype.card_coe]

/-- The product formula is exactly B^e times the integer bin population
divided by the total number of free assignments. -/
lemma population_eq_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    population B N v=(B:ℚ)^Fintype.card C*(Fintype.card (Assignments B N v):ℚ)/
      (∏ c,(N c:ℚ)) := by
  rw [assignment_card]
  simp only [population,coordinatePopulation,Finset.prod_div_distrib,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Nat.cast_prod]

private lemma reverse_bernoulli (u : ℚ) (hu : 0 ≤ u) (n : ℕ) :
    (1+u)^n*(1-(n:ℚ)*u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have haux : (1+u)*(1-((n:ℚ)+1)*u) ≤ 1-(n:ℚ)*u := by
      nlinarith [mul_nonneg (show (0:ℚ) ≤ n+1 by positivity) (sq_nonneg u)]
    calc
      _ = (1+u)^n*((1+u)*(1-((n:ℚ)+1)*u)) := by
        rw [pow_succ,Nat.cast_add,Nat.cast_one]
        ring
      _ ≤ (1+u)^n*(1-(n:ℚ)*u) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
      _ ≤ 1 := ih

/-- The source's alpha_v lies between one half and two, including the
empty-coordinate product. No large interval is enumerated to establish
the bound; its exact cardinality is the proved ceiling difference. -/
theorem population_bounds (B d : ℕ) (N : C → ℕ) (v : C → ℕ)
    (hB : 0 < B) (hd : 1 ≤ d) (hcard : Fintype.card C ≤ d)
    (hN : ∀ c,100*d*B ≤ N c) (hv : ∀ c,v c < B) :
    1/2 ≤ population B N v ∧ population B N v ≤ 2 := by
  let u : ℚ := 1/(100*(d:ℚ))
  have hdQ : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : u ≤ 1/100 := by
    dsimp only [u]
    rw [div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hcountQ : (Fintype.card C:ℚ) ≤ d := by exact_mod_cast hcard
  have hsum : (Fintype.card C:ℚ)*u ≤ 1/100 := by
    dsimp only [u]
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hfactor (c : C) : 1-u ≤ coordinatePopulation B (N c) (v c) ∧
      coordinatePopulation B (N c) (v c) ≤ 1+u := by
    have hh := abs_le.mp (coordinate_error B (N c) d (v c) hB hd (hN c) (hv c))
    constructor <;> linarith
  have hpos (c : C) : 0 ≤ coordinatePopulation B (N c) (v c) := by
    unfold coordinatePopulation
    positivity
  have hlo : (1-u)^Fintype.card C ≤ population B N v := by
    unfold population
    calc
      _ = ∏ _c : C,(1-u) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by linarith) (fun c _ => (hfactor c).1)
  have hup : population B N v ≤ (1+u)^Fintype.card C := by
    unfold population
    calc
      _ ≤ ∏ _c : C,(1+u) := Finset.prod_le_prod (fun c _ => hpos c) (fun c _ => (hfactor c).2)
      _ = _ := by simp
  have hbern := one_add_mul_le_pow (show (-2:ℚ) ≤ -u by linarith) (Fintype.card C)
  have hreverse := reverse_bernoulli u hu (Fintype.card C)
  have hpower : 0 ≤ (1+u)^Fintype.card C := by positivity
  constructor
  · have hh : 1-(Fintype.card C:ℚ)*u ≤ (1-u)^Fintype.card C := by
      simpa only [mul_neg,sub_eq_add_neg] using hbern
    linarith
  · nlinarith

end ContingencyTables.CompanionBinPopulation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the actual scaled forest-penalty Lipschitz bound -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_change (x y : ℝ) : |intervalCost x-intervalCost y| ≤ |x-y| := by
  have hsub (x y : ℝ) : intervalCost x ≤ intervalCost y+|x-y| := by
    unfold intervalCost
    apply max_le
    · linarith [le_max_left (0:ℝ) (max (-y) (y-1)),abs_nonneg (x-y)]
    · apply max_le
      · have hh : -y ≤ max 0 (max (-y) (y-1)) :=
          (le_max_left _ _).trans (le_max_right _ _)
        linarith [neg_le_abs (x-y)]
      · have hh : y-1 ≤ max 0 (max (-y) (y-1)) :=
          (le_max_right _ _).trans (le_max_right _ _)
        linarith [le_abs_self (x-y)]
  apply abs_le.mpr
  constructor
  · have hh := hsub y x
    rw [abs_sub_comm y x] at hh
    linarith
  · linarith [hsub x y]

lemma tree_card_le (A : Instance I J) : Fintype.card (TreeCell A.T) ≤ A.d := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer free assignments use the original scaled affine tree values -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_div (x b : ℝ) (hb : 0 < b) :
    intervalCost (x/b)=max 0 (max (-x) (x-b))/b := by
  unfold intervalCost
  have he : x/b-1=(x-b)/b := by field_simp [hb.ne']
  rw [he,← neg_div, max_div_div_right hb.le]
  simpa only [zero_div] using max_div_div_right hb.le (0:ℝ) (max (-x) (x-b))

lemma tree_sum_eq (A : Instance I J) (F : I×J → ℝ) :
    (∑ t : TreeCell A.T,F t.val)=
      ∑ i,∑ j,if A.T.Adj (.inl i) (.inr j) then F (i,j) else 0 := by
  let p : I×J → Prop := fun a => A.T.Adj (.inl a.1) (.inr a.2)
  calc
    _ = ∑ a ∈ Finset.univ.filter p,F a :=
      (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun _ => by simp) F).symm
    _ = ∑ a : I×J,if p a then F a else 0 := Finset.sum_filter _ _
    _ = _ := by rw [Fintype.sum_prod_type]

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual continuous forest penalty stays within the source allowance -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty
open ForestCountIdentification BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rowCounts_bounds (A : Instance I J) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (i : I) (j : J) (hs : A.small i j=true) :
    0 ≤ rowCounts A z i j ∧ rowCounts A z i j ≤ A.b i j := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  have hh : smallX A.small z i j ≤ A.b i j := by
    simpa only [smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
  change (smallX A.small z i j:ℤ) ≤ (A.b i j:ℤ)
  exact_mod_cast hh

lemma columnCounts_bounds (A : Instance I J) (z : View A → ℕ) (i : I) (j : J) :
    0 ≤ columnCounts A z i j ∧ columnCounts A z i j ≤ A.b i j := by
  unfold columnCounts
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast Nat.sub_le (A.b i j) (smallY A.small z i j)⟩

lemma integerCube_zero (A : Instance I J) (B : ℝ) : integerCube A B (zeroAssignment A)=0 := by
  funext a
  simp only [integerCube,zeroAssignment,Nat.cast_zero,mul_zero,zero_div,Pi.zero_apply]

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal weight-evaluator density on its finite-dimensional bin cube -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma binWidth_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < binWidth A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold binWidth
  positivity

lemma height_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < height A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold height
  positivity

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleMixing
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative mixing for the companion's actual evaluator grid -/

namespace ContingencyTables.CompanionOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_grid_card (q K : ℕ) : Fintype.card (Grid (I := Fin q) K)=K^q := by
  have hc : Fintype.card (Set.Icc (0:ℤ) ((K:ℤ)-1))=K := by
    have hh := Int.card_fintype_Icc_of_le 0 ((K:ℤ)-1)
      (show (0:ℤ) ≤ (K:ℤ)-1+1 by omega)
    omega
  simp only [Grid,Fintype.card_fun,Fintype.card_fin,hc]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the literal companion weight -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma pull_integerPoint (A : Instance I J) (C : ℝ) (f : FreeIndex A.small A.T A.b) :
    pull A (integerPoint A C f)=integerCube A (binWidth A C) f := by
  funext t
  simp only [pull,integerPoint,Equiv.apply_symm_apply]

lemma ownFiber_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) :
    0 < (integerFiber A K hK (integerBin A K hK f)).card := by
  apply Finset.card_pos.mpr
  exact ⟨f,by simp [integerFiber]⟩

lemma assignmentCount_positive (A : Instance I J) : 0 < assignmentCount A := by
  let : Nonempty (FreeIndex A.small A.T A.b) := ⟨fun _ => 0⟩
  exact Fintype.card_pos


end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer bins have the manuscript's Cartesian populations -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem integerFiber_card (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    (integerFiber A K hK v).card=
      ∏ t : FreeCell A.small A.T,(FairBits.fiber K (freeRange A t) (naturalBin A v t)).card := by
  let : DecidableEq (FreeCell A.small A.T) := Classical.decEq _
  calc
    _ = Fintype.card {f // f∈integerFiber A K hK v} := (Fintype.card_coe _).symm
    _ = _ := Fintype.card_congr (integerFiberEquiv A K hK v)
    _ = _ := CompanionBinPopulation.assignment_card K (freeRange A) (naturalBin A v)

theorem integerFiber_nonempty (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) :
    (integerFiber A K hK v).Nonempty := by
  have hpop (t : FreeCell A.small A.T) :
      (FairBits.fiber K (freeRange A t) (naturalBin A v t)).Nonempty := by
    apply CompanionBinPopulation.coordinate_nonempty K (freeRange A t) A.d _ hK A.hd
    · have hh := (A.hlarge t.val.1 t.val.2 t.property.1).1
      unfold freeRange
      omega
    · exact naturalBin_lt A v t
  let x : CompanionBinPopulation.Assignments K (freeRange A) (naturalBin A v) :=
    fun t => ⟨(hpop t).choose,(hpop t).choose_spec⟩
  exact ⟨((integerFiberEquiv A K hK v).symm x).val,
    ((integerFiberEquiv A K hK v).symm x).property⟩

lemma assignmentCount_eq_prod (A : Instance I J) :
    assignmentCount A=∏ t : FreeCell A.small A.T,freeRange A t := by
  simp only [assignmentCount,FreeIndex,Fintype.card_pi,Fintype.card_fin,freeRange]

theorem population_eq_integerFiber (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    CompanionBinPopulation.population K (freeRange A) (naturalBin A v)=
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A := by
  rw [CompanionBinPopulation.population_eq_card,CompanionBinPopulation.assignment_card,
    ←integerFiber_card A K hK,
    assignmentCount_eq_prod]
  simp only [dimension,Nat.cast_prod]

theorem actual_population_bounds (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ≤ 2 := by
  have hh := CompanionBinPopulation.population_bounds K A.d (freeRange A) (naturalBin A v)
    hK A.hd (ForestScaledPenalty.free_card_le A)
    (by
      intro t
      have hb := (A.hlarge t.val.1 t.val.2 t.property.1).1
      unfold freeRange
      omega)
    (naturalBin_lt A v)
  simpa only [population_eq_integerFiber A K hK] using hh

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleJointLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization of the actual bin-then-integer sampling law -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma integerPoint_distance (A : Instance I J) (C : ℝ) (K : ℕ) (hK : 0 < K)
    (hB : (K:ℝ)=binWidth A C) (f : FreeIndex A.small A.T A.b) :
    ∀ i,|integerPoint A C f i-realCorner (integerBin A K hK f) i| ≤ 1 := by
  intro i
  let t := index A i
  let N := freeRange A t
  let x := (f t).val
  have hq : (0:ℚ) ≤ (K:ℚ)*x/N := by positivity
  have hlo : (FairBits.scale K N x:ℚ) ≤ (K:ℚ)*x/N := Nat.floor_le hq
  have hhi : (K:ℚ)*x/N < (FairBits.scale K N x:ℚ)+1 := Nat.lt_floor_add_one _
  have hloR : (FairBits.scale K N x:ℝ) ≤ (K:ℝ)*x/N := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div] using (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR : (K:ℝ)*x/N < (FairBits.scale K N x:ℝ)+1 := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).mpr hhi
  have hN : (N:ℝ)=(A.b t.val.1 t.val.2:ℝ)+1 := by simp [N,freeRange]
  change |binWidth A C*(f t).val/((A.b t.val.1 t.val.2:ℝ)+1)-
    (FairBits.scale K N (f t).val:ℝ)| ≤ 1
  rw [←hB,←hN]
  change |(K:ℝ)*x/N-(FairBits.scale K N x:ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinIntervals
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit integer intervals inside the companion evaluator bins -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem exactBinLaw_mass (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (f : FreeIndex A.small A.T A.b) :
    (exactBinLaw A K hK hW v).mass f=
      if integerBin A K hK f=v then 1/((integerFiber A K hK v).card:ℚ) else 0 := by
  let : ∀ i : Fin (dimension A),Nonempty (Fin (binSize A K v i)) :=
    fun i => ⟨⟨0,binSize_positive A K hK hW v i⟩⟩
  let : Nonempty {f // f∈integerFiber A K hK v} :=
    ⟨⟨(integerFiber_nonempty A K hK hW v).choose,(integerFiber_nonempty A K hK hW v).choose_spec⟩⟩
  have hi (i : Fin (dimension A)) :
      FairBits.uniformIntLaw (binSize A K v i) (binSize_positive A K hK hW v i)=
        uniformLaw (α := Fin (binSize A K v i)) := by
    apply RationalLaw.ext
    funext x
    simp only [FairBits.uniformIntLaw,uniformLaw,uniformMass,Fintype.card_fin]
  unfold exactBinLaw
  simp_rw [hi]
  rw [pi_uniformLaw]
  change (mapLaw (uniformLaw (α := (i : Fin (dimension A)) → Fin (binSize A K v i)))
    (fun x => (binOffsetsEquiv A K hK v x).val)).mass f=_
  rw [←FairBits.map_equiv (binOffsetsEquiv A K hK v),FairBits.uniform_equiv]
  change (∑ x : {g // g∈integerFiber A K hK v},
    if x.val=f then (1:ℚ)/Fintype.card {g // g∈integerFiber A K hK v} else 0)=_
  rw [Fintype.card_coe]
  by_cases hf : integerBin A K hK f=v
  · rw [ite_eq_left hf]
    let g : {g // g∈integerFiber A K hK v} := ⟨f,by simp only [integerFiber,Finset.mem_filter,
      Finset.mem_univ,true_and,hf]⟩
    have he (x : {g // g∈integerFiber A K hK v}) : x.val=f ↔ x=g := by
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp_rw [he]
    simp
  · rw [ite_eq_right hf]
    apply Finset.sum_eq_zero
    intro x _
    have hxf : x.val≠f := by
      intro he
      have hx := (Finset.mem_filter.mp x.property).2
      rw [he] at hx
      exact hf hx
    simp only [hxf,ite_false]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawMoments
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expectations of concrete finite-word output laws -/

namespace ContingencyTables.FiniteLawMoments

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma expectation_bounds (p : RationalLaw X) (g : X → ℝ) (L U : ℝ)
    (hg : ∀ x,L ≤ g x ∧ g x ≤ U) : L ≤ expectation p g ∧ expectation p g ≤ U := by
  have htotal : ∑ x,(p.mass x:ℝ)=1 := by exact_mod_cast p.total
  unfold expectation
  constructor
  · calc
      L = ∑ x,(p.mass x:ℝ)*L := by rw [←Finset.sum_mul,htotal,one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).1 (by exact_mod_cast p.nonnegative x))
  · calc
      _ ≤ ∑ x,(p.mass x:ℝ)*U := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).2 (by exact_mod_cast p.nonnegative x))
      _ = U := by rw [←Finset.sum_mul,htotal,one_mul]

end ContingencyTables.FiniteLawMoments

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteIndependentFailures
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate marginals and a union bound for independent finite blocks -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

lemma uniformAverage_coordinate {J : Type*} [Fintype J] {X : J → Type*}
    [∀ j,Fintype (X j)] [∀ j,Nonempty (X j)] (i : J) (g : X i → ℝ) :
    uniformAverage (fun x : (j : J) → X j => g (x i))=uniformAverage g := by
  have he := uniformAverage_equiv (Equiv.piSplitAt i X) (fun x => g x.1)
  change uniformAverage (fun x : (j : J) → X j => g (x i))=
    uniformAverage (fun x : X i × ((j : {j // j≠i}) → X j.val) => g x.1) at he
  rw [he,uniformAverage_prod]
  simp_rw [uniformAverage_const]

lemma uniform_union_bound {X J : Type*} [Fintype X] [Fintype J]
    (bad : J → X → Prop) :
    uniformAverage (fun x => if ∃ j,bad j x then (1:ℝ) else 0) ≤
      ∑ j,uniformAverage (fun x => if bad j x then (1:ℝ) else 0) := by
  rw [←uniformAverage_sum]
  apply uniformAverage_mono
  intro x
  by_cases h : ∃ j,bad j x
  · obtain ⟨j,hj⟩ := h
    rw [ite_eq_left ⟨j,hj⟩]
    calc
      1 = (if bad j x then (1:ℝ) else 0) := by rw [ite_eq_left hj]
      _ ≤ ∑ k : J,if bad k x then (1:ℝ) else 0 :=
        Finset.single_le_sum (f := fun k => if bad k x then (1:ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

/-- Each block is an actual independently uniform finite experiment.
The event may test a different observable on each block. -/
theorem independent_union_failure {J : Type*} [Fintype J] {X : J → Type*}
    [∀ j,Fintype (X j)] [∀ j,Nonempty (X j)] (bad : (j : J) → X j → Prop) :
    uniformAverage (fun draws : (j : J) → X j =>
      if ∃ j,bad j (draws j) then (1:ℝ) else 0) ≤
      ∑ j,uniformAverage (fun x : X j => if bad j x then (1:ℝ) else 0) := by
  apply (uniform_union_bound (fun j (draws : (k : J) → X k) => bad j (draws j))).trans_eq
  apply Finset.sum_congr rfl
  intro j _
  exact uniformAverage_coordinate j (fun x => if bad j x then (1:ℝ) else 0)

end

end ContingencyTables.FiniteIndependentAverages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionReferenceAccuracy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative accuracy of the literal companion ratio estimator

The source's tolerance epsilon/(200(H+1)) turns the proved accumulated
logarithmic error into the required multiplicative error. The terminal
contamination bound supplies the remaining error term.
-/

namespace ContingencyTables.CompanionReferenceAccuracy

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication

theorem relative_of_log_error (epsilon R : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hR : 0 < R) (herr : |Real.log R| ≤ epsilon/50) :
    1-epsilon/4 ≤ R ∧ R ≤ 1+epsilon/4 := by
  have hl := Real.log_le_sub_one_of_pos hR
  have hu := Real.one_sub_inv_le_log_of_pos hR
  have he := abs_le.mp herr
  have hinv : 1-epsilon/50 ≤ R⁻¹ := by linarith
  have hm := mul_le_mul_of_nonneg_right hinv hR.le
  rw [inv_mul_cancel₀ hR.ne'] at hm
  have hc : (1-epsilon/50)*(1+epsilon/4) ≥ 1 := by
    nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1.le)]
  constructor
  · linarith
  · exact le_of_mul_le_mul_left (hm.trans hc) (show 0 < 1-epsilon/50 by linarith)

end ContingencyTables.CompanionReferenceAccuracy

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteProductAccuracy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative accuracy of the finite product used by the weight oracle -/

namespace ContingencyTables.FiniteProductAccuracy

open scoped BigOperators Classical

variable {J : Type*} [Fintype J]

lemma relative_log (x y delta : ℝ) (hy : 0 < y) (hd0 : 0 ≤ delta) (hd : delta ≤ 1/4)
    (herr : |x-y| ≤ delta*y) : 0 < x ∧ |Real.log (x/y)| ≤ 4*delta := by
  have hh := abs_le.mp herr
  have hx : (1-delta)*y ≤ x ∧ x ≤ (1+delta)*y := by constructor <;> nlinarith
  have h1 : (1-delta)*(1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ (1+delta)*1 := by constructor <;> nlinarith
  have hp := AnnealingMultipliers.relative_ratio hy (by norm_num : (0:ℝ)<1) hd0 hd hx h1
  refine ⟨AnnealingMultipliers.empirical_positive hy hd hx.1,?_⟩
  simpa only [mul_one,one_mul] using hp.2.2.2

lemma product_log (x y : J → ℝ) (hy : ∀ j,0 < y j) (delta : ℝ)
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1/4) (herr : ∀ j,|x j-y j| ≤ delta*y j) :
    0 < ∏ j,x j ∧ |Real.log ((∏ j,x j)/(∏ j,y j))| ≤ 4*(Fintype.card J:ℝ)*delta := by
  have hstep := fun j => relative_log (x j) (y j) delta (hy j) hd0 hd (herr j)
  refine ⟨Finset.prod_pos (fun j _ => (hstep j).1),?_⟩
  rw [←Finset.prod_div_distrib,Real.log_prod (fun j _ => div_ne_zero (hstep j).1.ne' (hy j).ne')]
  calc
    _ ≤ ∑ j,|Real.log (x j/y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J,4*delta := Finset.sum_le_sum (fun j _ => (hstep j).2)
    _ = _ := by simp; ring

/-- The source has j+1 factors, each observed to the same tolerance.
This scalar budget is sufficient for its requested relative interval. -/
theorem product_relative (x y : J → ℝ) (hy : ∀ j,0 < y j) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (herr : ∀ j,|x j-y j| ≤ (epsilon/(200*(Fintype.card J:ℝ)))*y j)
    (hcard : 0 < Fintype.card J) :
    (1-epsilon/4)*(∏ j,y j) ≤ ∏ j,x j ∧
      (∏ j,x j) ≤ (1+epsilon/4)*(∏ j,y j) := by
  have hc : (0:ℝ) < Fintype.card J := by exact_mod_cast hcard
  have hc1 : (1:ℝ) ≤ Fintype.card J := by exact_mod_cast hcard
  have hd0 : 0 ≤ epsilon/(200*(Fintype.card J:ℝ)) := by positivity
  have hd : epsilon/(200*(Fintype.card J:ℝ)) ≤ 1/4 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ)<200*(Fintype.card J:ℝ))]
    linarith
  have hh := product_log x y hy _ hd0 hd herr
  have hb : 4*(Fintype.card J:ℝ)*(epsilon/(200*(Fintype.card J:ℝ)))=epsilon/50 := by
    field_simp [hc.ne']
    ring
  have ht := Finset.prod_pos (s := Finset.univ) (fun j _ => hy j)
  have hr := CompanionReferenceAccuracy.relative_of_log_error epsilon
    ((∏ j,x j)/(∏ j,y j)) he0 he1 (div_pos hh.1 ht) (hh.2.trans_eq hb)
  exact ⟨(le_div_iff₀ ht).mp hr.1,(div_le_iff₀ ht).mp hr.2⟩

end ContingencyTables.FiniteProductAccuracy

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEstimatorConfidence
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma innerTolerance_pos (epsilon : ℚ) (j : ℕ) (he : 0 < epsilon) :
    0 < innerTolerance epsilon j := by unfold innerTolerance; positivity

lemma innerTolerance_lt_one (epsilon : ℚ) (j : ℕ) (he : epsilon < 1) :
    innerTolerance epsilon j < 1 := by
  unfold innerTolerance
  rw [div_lt_iff₀ (by positivity : (0:ℚ)<200*(j+1))]
  have hj : (0:ℚ) ≤ j := Nat.cast_nonneg _
  nlinarith

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteMedianConfidence
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational medians with real target intervals -/

namespace ContingencyTables.FiniteMedianConfidence

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

/-- Rational thresholds used only in the proof permit direct reuse of
finite median amplification when the intended target is a real number. -/
theorem median_confidence_real {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (L L' U' U : ℝ) (hL : L < L') (hU : U' < U)
    (delta : ℚ) (hdelta : 0 < delta)
    (hbad : uniformAverage (fun x =>
      if (output x:ℝ) < L' ∨ U' < (output x:ℝ) then (1:ℝ) else 0) ≤ 5/16) :
    1-(delta:ℝ) ≤ uniformAverage (fun xs : Fin (repetitionCount delta) → X =>
      if L ≤ (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ≤ U
      then (1:ℝ) else 0) := by
  obtain ⟨a,haL,haL'⟩ := exists_rat_btwn hL
  obtain ⟨b,hU'b,hbU⟩ := exists_rat_btwn hU
  have hab : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0) ≤ 5/16 := by
    apply (uniformAverage_mono _ _ (fun x => ?_)).trans hbad
    simp only [outsideInterval,decide_eq_true_eq]
    by_cases hn : ¬(a ≤ output x ∧ output x ≤ b)
    · have hor : output x < a ∨ b < output x := by
        by_cases ha : output x < a
        · exact Or.inl ha
        · right
          by_contra hb
          exact hn ⟨le_of_not_gt ha,le_of_not_gt hb⟩
      have ht : (output x:ℝ) < L' ∨ U' < (output x:ℝ) := by
        rcases hor with ha|hb
        · left
          exact lt_trans (by exact_mod_cast ha) haL'
        · right
          exact lt_trans hU'b (by exact_mod_cast hb)
      simp [hn,ht]
    · simp only [hn,ite_false]
      split_ifs <;> norm_num
  have hm := median_confidence output a b delta hdelta hab
  apply hm.trans
  apply uniformAverage_mono
  intro xs
  by_cases hg : a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
      rationalMedian (List.ofFn (fun i => output (xs i))) ≤ b
  · have hreal : L ≤ (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ≤ U :=
      ⟨le_trans haL.le (by exact_mod_cast hg.1),le_trans (by exact_mod_cast hg.2) hbU.le⟩
    simp [hg,hreal]
  · simp only [hg,ite_false]
    split_ifs <;> norm_num

end

end ContingencyTables.FiniteMedianConfidence

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionWeightOracle
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.CompanionWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma profile_inBox (A : Instance I J) (S : Set (Labels A×Bool)) :
    BalancedBox.InBox (bounds A) (profile A S) := by
  rw [←label_capacity]
  exact SliceFactorial.groupCount_inBox _ _

lemma factorialRatio_positive (A : Instance I J) (S : Set (Labels A×Bool)) :
    0 < factorialRatio A S := by
  unfold factorialRatio factorialNumerator factorialDenominator
  positivity

lemma factorialRatio_cast (A : Instance I J) (S : Set (Labels A×Bool)) :
    (factorialRatio A S:ℝ)=
      FactorialSignatures.factorialProduct (profile A S)/CompanionFactorialApplication.denominator A := by
  simp only [factorialRatio,factorialNumerator,factorialDenominator,Rat.cast_div,Rat.cast_prod,
    Rat.cast_natCast,Nat.cast_prod,FactorialSignatures.factorialProduct,CompanionFactorialApplication.denominator,
    TwoLiftStates.denominator,label_width]

end

end ContingencyTables.CompanionWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRationalUpdates
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational multiplier updates of the outer annealing run -/

namespace ContingencyTables.CompanionRationalUpdates

open CompanionFactorialApplication
open CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma plainCount_le (A : Instance I J) (l : List (Set (Labels A×Bool))) :
    plainCount A l ≤ l.length := List.countP_le_length

lemma rationalLearn_counts (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (l : List (Set (Labels A×Bool))) (hl : 0 < l.length) (p q : Pair A) :
    rationalLearn pairs w l p q=
      if p∈pairs ∧ q∈pairs ∧ p≠q then w p q*(plainCount A l:ℚ)/(defectCount A l p q:ℚ)
      else w p q := by
  have hN : (l.length:ℚ)≠0 := by exact_mod_cast hl.ne'
  unfold rationalLearn rationalEmpirical rationalPlain rationalDefect plainCount defectCount
  simp only [indicator_list_sum]
  split_ifs <;> simp only [div_div_div_cancel_right₀ hN,mul_div_assoc]

lemma checkedUpdate_positive (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (l : List (Set (Labels A×Bool)))
    (w' : Pair A → Pair A → ℚ) (hu : checkedUpdate A w l=some w') :
    ∀ p q,0 < w' p q := by
  unfold checkedUpdate at hu
  split_ifs at hu with hc
  · cases Option.some.inj hu
    have hl : 0 < l.length := lt_of_lt_of_le hc.1 (plainCount_le A l)
    intro p q
    rw [rationalLearn_counts A w l hl]
    split_ifs with hpq
    · exact div_pos (mul_pos (hw p q) (by exact_mod_cast hc.1))
        (by exact_mod_cast hc.2 p hpq.1 q hpq.2.1 hpq.2.2)
    · exact hw p q

end

end ContingencyTables.CompanionRationalUpdates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseOracleError
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Error contributed by the actual fresh weight calls in a phase -/

namespace ContingencyTables.CompanionPhaseWords

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open scoped BigOperators Classical

noncomputable section

lemma average_ext_instances {X : Type*} (s t : Fintype X) (f g : X → ℝ)
    (h : ∀ x,f x=g x) : @uniformAverage X s f=@uniformAverage X t g := by
  cases Subsingleton.elim s t
  exact congrArg (@uniformAverage X s) (funext h)

lemma failure_of_success {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) (delta : ℝ)
    (h : 1-delta ≤ uniformAverage (fun x => if P x then (1:ℝ) else 0)) :
    uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) ≤ delta := by
  have hp (x : X) : (if P x then (1:ℝ) else 0)+(if ¬P x then 1 else 0)=1 := by
    by_cases hx : P x <;> simp [hx]
  have he := uniformAverage_add (fun x => if P x then (1:ℝ) else 0)
    (fun x => if ¬P x then (1:ℝ) else 0)
  simp_rw [hp] at he
  rw [uniformAverage_const] at he
  linarith

lemma independent_pair_failure {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (P : X → Prop) (Q : Y → Prop)
    (a b : ℝ) (hP : uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) ≤ a)
    (hQ : uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) ≤ b) :
    uniformAverage (fun xy : X×Y => if ¬(P xy.1 ∧ Q xy.2) then (1:ℝ) else 0) ≤ a+b := by
  have hfst : uniformAverage (fun xy : X×Y => if ¬P xy.1 then (1:ℝ) else 0)=
      uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) := by
    calc
      _ = uniformAverage (fun x : X => uniformAverage (fun _y : Y => if ¬P x then (1:ℝ) else 0)) :=
        @uniformAverage_prod X Y _ _ (fun xy : X×Y => if ¬P xy.1 then (1:ℝ) else 0)
      _ = _ := by simp_rw [uniformAverage_const]
  have hsnd : uniformAverage (fun xy : X×Y => if ¬Q xy.2 then (1:ℝ) else 0)=
      uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) := by
    calc
      _ = uniformAverage (fun _x : X => uniformAverage (fun y : Y => if ¬Q y then (1:ℝ) else 0)) :=
        @uniformAverage_prod X Y _ _ (fun xy : X×Y => if ¬Q xy.2 then (1:ℝ) else 0)
      _ = _ := uniformAverage_const _
  calc
    _ ≤ uniformAverage (fun xy : X×Y =>
        (if ¬P xy.1 then (1:ℝ) else 0)+(if ¬Q xy.2 then (1:ℝ) else 0)) := by
      apply uniformAverage_mono
      intro xy
      by_cases hp : P xy.1 <;> by_cases hq : Q xy.2 <;> simp [hp,hq]
    _ = uniformAverage (fun x => if ¬P x then (1:ℝ) else 0)+
        uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) := by
      rw [uniformAverage_add,hfst,hsnd]
    _ ≤ a+b := add_le_add hP hQ

lemma independent_reindex_failure {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    (N : ℕ) (e : Y ≃ (Fin N → X)) (P : Fin N → X → Prop) :
    uniformAverage (fun y : Y => if ¬(∀ i,P i (e y i)) then (1:ℝ) else 0) ≤
      ∑ i : Fin N,uniformAverage (fun x : X => if ¬P i x then (1:ℝ) else 0) := by
  let bad (i : Fin N) (x : X) := ¬P i x
  have he := uniformAverage_equiv e
    (fun xs : Fin N → X => if ∃ i,bad i (xs i) then (1:ℝ) else 0)
  have hb : uniformAverage (fun xs : Fin N → X => if ∃ i,bad i (xs i) then (1:ℝ) else 0) ≤
      ∑ i : Fin N,uniformAverage (fun x : X => if bad i x then (1:ℝ) else 0) := by
    convert independent_union_failure bad using 1
    all_goals try with_reducible_and_instances rfl
    all_goals
      congr 1 <;> try exact Subsingleton.elim _ _
    · funext xs
      by_cases h : ∃ i,bad i (xs i) <;> simp [h]
    · funext i
      congr 1
      funext x
      by_cases h : bad i x <;> simp [h]
  simpa only [bad,not_forall] using he.trans_le hb

end

end ContingencyTables.CompanionPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTraceWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Capped trace returns from the actual companion Boolean walk

The return search scans the recorded path after its initial state. Its
reference expectation is the finite Green sum defining the capped trace;
the Boolean walk contributes its path error.
-/

namespace ContingencyTables.CompanionTraceWords

open CommonBasesFPRAS CompanionFactorialApplication CompanionBooleanPhase
open CompanionPhaseTrajectory CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

lemma eventIndicator_eq (P : Prop) [Decidable P] :
    eventIndicator P=(if P then (1:ℝ) else 0) := by
  by_cases h : P <;> simp only [eventIndicator,h,ite_true, if_true,ite_false]

end
end ContingencyTables.CompanionTraceWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FinitePlainLift
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact moment and distance identities for the transversal embedding -/

namespace ContingencyTables.FinitePlainLift

open CommonBasesFPRAS RealKernelApproximation
open scoped BigOperators Classical

noncomputable section
variable {Γ : Type*} [Fintype Γ]

lemma sum_mul (gs : List (Γ × Γ)) (p : PlainIndex gs → ℝ)
    (g : ChainIndex gs → ℝ) :
    (∑ S,plainLift gs p S*g S)=∑ S : PlainIndex gs,p S*g S.val := by
  have h := Fintype.sum_subtype_add_sum_subtype (plainPredicate gs)
    (fun S => plainLift gs p S*g S)
  have ht (S : PlainIndex gs) : plainLift gs p S.val*g S.val=p S*g S.val := by
    rw [plainLift,dite_eq_left S.property]
  have hf (S : {S : ChainIndex gs // ¬plainPredicate gs S}) :
      plainLift gs p S.val*g S.val=0 := by
    rw [plainLift,dite_eq_right S.property,zero_mul]
  simp_rw [ht,hf,Finset.sum_const_zero,add_zero] at h
  exact h.symm

lemma distance_lift (gs : List (Γ × Γ)) (p q : PlainIndex gs → ℝ) :
    distance (plainLift gs p) (plainLift gs q)=distance p q := by
  have h := Fintype.sum_subtype_add_sum_subtype (plainPredicate gs)
    (fun S => |plainLift gs p S-plainLift gs q S|)
  have ht (S : PlainIndex gs) :
      |plainLift gs p S.val-plainLift gs q S.val|=|p S-q S| := by
    rw [plainLift,dite_eq_left S.property,plainLift,dite_eq_left S.property]
  have hf (S : {S : ChainIndex gs // ¬plainPredicate gs S}) :
      |plainLift gs p S.val-plainLift gs q S.val|=0 := by
    rw [plainLift,dite_eq_right S.property,plainLift,dite_eq_right S.property,sub_self,abs_zero]
  simp_rw [ht,hf,Finset.sum_const_zero,add_zero] at h
  unfold distance
  rw [h]

end
end ContingencyTables.FinitePlainLift

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCut
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit endpoint on the side away from a selected root

One reachability test in the edge-deleted forest selects the endpoint.
No choice of a component representative or of a cut vertex is needed.
-/

namespace ContingencyTables.RootedCut

open scoped BigOperators Classical
open SimpleGraph MaximumForest RootedCompletion GraphCompletionCounts ForestCut
open ForestCapacity

variable {V : Type*}

theorem selected_nonroot (T : SimpleGraph V) (S : Selection T) (hT : T.IsAcyclic)
    {u v a : V} (ht : T.Adj u v) (ha : cut T u v (S.root u) a=true) : a≠S.root a := by
  intro he
  have hp := away_properties T hT ht (S.root u) (S.reachable u).symm
  have hreach : (T.deleteEdges {s(u,v)}).Reachable (away T u v (S.root u)) a := by
    simpa only [cut,side,decide_eq_true_eq] using ha
  have hcomp := hp.1.trans (hreach.mono (T.deleteEdges_le {s(u,v)}))
  have hsame : S.root a=S.root u :=
    (S.constant hcomp).symm.trans (S.idempotent u)
  have hae : a=S.root u := he.trans hsame
  have hbad : cut T u v (S.root u) (S.root u)=true := by simpa only [hae] using ha
  exact Bool.false_ne_true (hp.2.1.symm.trans hbad)

variable {I J : Type*}

lemma treeCut_nonroot (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) (v : I⊕J) (hv : treeCut T S t v=true) : v≠S.root v :=
  selected_nonroot T S hT t.property hv

lemma sign_abs_le_one (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) : |sign T S t a|≤1 := by
  unfold sign
  cases treeCut T S t (.inl a.1) <;> cases treeCut T S t (.inr a.2) <;>
    norm_num [indicator]

lemma other_tree_sign_zero (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) (ha : T.Adj (.inl a.1) (.inr a.2)) (hne : a≠t.val) :
    sign T S t a=0 := by
  have hh := side_eq_of_tree_edge T (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (away T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1))) ha
    (by intro he; exact hne (cell_edge_injective he))
  exact sub_eq_zero.mpr (congrArg indicator hh)

end ContingencyTables.RootedCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAffine
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cut coefficients for an explicitly selected forest root

The same signed cut calculation applies to the executed root selector.
In particular, coefficient size and the maximum-forest capacity bound
do not depend on a classical choice of cut representative.
-/

namespace ContingencyTables.RootedAffine

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedCut GraphCompletionCounts
open ForestCapacity ForestCut MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

lemma coefficient_abs_le_one (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : |coefficient A S t a|≤1 := by
  unfold coefficient
  split_ifs
  · rw [abs_div,abs_neg,sign_abs_self A.T S A.hT,div_one]
    exact sign_abs_le_one A.T S t a
  · norm_num

lemma capacity_le_of_coefficient_ne_zero (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (ha : coefficient A S t a≠0) :
    A.b a.1 a.2≤A.b t.val.1 t.val.2 := by
  have hf : A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2) := by
    by_contra hn
    exact ha (by simp only [coefficient,hn,ite_false])
  have hcross : treeCut A.T S t (.inl a.1)≠treeCut A.T S t (.inr a.2) := by
    intro he
    apply ha
    simp [coefficient,hf,sign,he]
  have h := crossing_free_edge_le (cellGraph A.small) A.T (capacity A.b)
    A.hTG A.hT A.hmax (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (by simpa using t.property)
    (away A.T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1)))
    (show (cellGraph A.small).Adj (.inl a.1) (.inr a.2) from hf.1) hf.2 hcross
  simpa only [capacity_cell] using h

theorem normalized_coefficient_bound (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (B : ℝ) (hB : 0<B) :
    |coefficient A S t a*((A.b a.1 a.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)|≤2/B := by
  have hb : (1:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
  by_cases ha : coefficient A S t a=0
  · simp only [ha,zero_mul,zero_div,abs_zero]
    positivity
  have hcap : (A.b a.1 a.2:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast capacity_le_of_coefficient_ne_zero A S t a ha
  rw [abs_div,abs_div,abs_mul,abs_of_pos hB,
    abs_of_pos (by linarith : (0:ℝ)<A.b t.val.1 t.val.2),
    abs_of_nonneg (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)]
  apply (div_le_iff₀ (by linarith : (0:ℝ)<A.b t.val.1 t.val.2)).mpr
  rw [div_le_iff₀ hB]
  have hh := mul_le_mul_of_nonneg_right (coefficient_abs_le_one A S t a)
    (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)
  field_simp [hB.ne']
  nlinarith

theorem affine_of_nonroot_equations (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q z : I → J → ℝ)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) →
      rowDifference A.small x z (fun i j => (A.X i j:ℝ)) i=0)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) →
      columnDifference A.small q z (fun i j => (A.X i j:ℝ)) j=0) :
    z t.val.1 t.val.2=affineTree A S t x q (fun a => z a.1 a.2) := by
  let f : I×J → ℝ := fun a => cutTerm A.small
    (fun i => treeCut A.T S t (.inl i)) (fun j => treeCut A.T S t (.inr j))
    x q z (fun i j => (A.X i j:ℝ)) a.1 a.2
  have hsum : (∑ a,f a)=0 := by
    rw [Fintype.sum_prod_type]
    exact cut_sum_zero A.small _ _ x q z _
      (fun i hi => hr i (treeCut_nonroot A.T S A.hT t (.inl i) hi))
      (fun j hj => hc j (treeCut_nonroot A.T S A.hT t (.inr j) hj))
  have hterm (a : I×J) : f a=
      (if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)+
      (if A.small a.1 a.2 then
        indicator (treeCut A.T S t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          indicator (treeCut A.T S t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0)-
      sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2) := by
    by_cases he : a=t.val
    · subst a
      have hs : A.small t.val.1 t.val.2=false := A.hTG t.property
      simp only [f,cutTerm,hs,Bool.false_eq_true,ite_false,ite_true, if_true,coefficient,t.property,
        not_true_eq_false,and_false,sign,mul_zero,zero_mul,add_zero,sub_zero]
    · by_cases hs : A.small a.1 a.2=true
      · simp [f,cutTerm,hs,he,coefficient]
      · have hs' : A.small a.1 a.2=false := Bool.eq_false_iff.mpr hs
        by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
        · have hz := other_tree_sign_zero A.T S t a ht he
          simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_true_eq_false,and_false,zero_add,mul_zero,zero_mul,sub_zero]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=0
          rw [hz,zero_mul]
        · simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_false_eq_true,and_self,ite_true, if_true,zero_add,zero_sub]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=
            -(sign A.T S t t.val*(-sign A.T S t a/sign A.T S t t.val)*
              (z a.1 a.2-A.X a.1 a.2))
          field_simp [sign_self_ne_zero A.T S A.hT t]
  simp_rw [hterm] at hsum
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  have hsingle : (∑ a : I×J,
      if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)=
      sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2) := by simp
  rw [hsingle] at hsum
  change sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2)+
    smallContribution A S t x q-
    (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=0 at hsum
  have hprod : (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=
      sign A.T S t t.val*((∑ a : I×J,coefficient A S t a*z a.1 a.2)-
        ∑ a : I×J,coefficient A S t a*(A.X a.1 a.2:ℝ)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hprod] at hsum
  unfold affineTree AffinePenalty.affineValue offset
  apply mul_left_cancel₀ (sign_self_ne_zero A.T S A.hT t)
  rw [mul_add,mul_sub,mul_sub,←mul_div_assoc,
    mul_div_cancel_left₀ _ (sign_self_ne_zero A.T S A.hT t)]
  nlinarith [hsum]

end ContingencyTables.RootedAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalCompletion
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residual completion for the executed root convention

The row and column small views remain distinct. The explicit selected
roots determine which incidence equations are enforced; the resulting
integral completion is exactly the selected-cut affine formula.
-/

namespace ContingencyTables.RootedPhysicalCompletion

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedAffine GraphCompletionCounts ForestCut
open ForestPhysicalCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The cut-defined coefficients evaluate the actual integral solution
for this root convention, including every unbalanced small profile. -/
theorem solved_eq_affine (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T)
    (x q free : I → J → ℤ) :
    (solved A S x q free t.val.1 t.val.2:ℝ)=
      affineTree A S t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
        (fun a => (free a.1 a.2:ℝ)) := by
  let z : I → J → ℝ := fun i j => (completed A S x q free i j:ℝ)
  have hh := affine_of_nonroot_equations A S t (fun i j => (x i j:ℝ))
    (fun i j => (q i j:ℝ)) z (by
      intro i hi
      have hr := row_completed_sum A S x q free i hi
      unfold rowDifference
      have he : (∑ j,if A.small i j then (x i j:ℝ) else z i j)=(A.r i:ℝ) := by
        dsimp only [z]
        exact_mod_cast hr
      have hX : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast A.hXr i
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else z i j)-(∑ j,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self]) (by
      intro j hj
      have hc := column_completed_sum A S x q free j hj
      unfold columnDifference
      have he : (∑ i,if A.small i j then (q i j:ℝ) else z i j)=(A.c j:ℝ) := by
        dsimp only [z]
        exact_mod_cast hc
      have hX : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast A.hXc j
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else z i j)-(∑ i,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self])
  have hz : z t.val.1 t.val.2=(solved A S x q free t.val.1 t.val.2:ℝ) := by
    simp only [z,completed,t.property,ite_true, if_true]
  rw [hz] at hh
  rw [hh]
  unfold affineTree AffinePenalty.affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
  · simp only [coefficient,ht,not_true_eq_false,and_false,ite_false,zero_mul]
  · simp only [z,completed,ht,ite_false]

end ContingencyTables.RootedPhysicalCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root discrepancy is independent of the free entries

Every large-cell edge stays in a maximum-forest component.  Its two
incidences therefore cancel in the selected-root component sum.
-/

namespace ContingencyTables.RootedRootPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestPhysicalCompletion (rowResidual columnResidual fixedRow fixedColumn)
open ForestRootPenalty (residualDemand smallDemand)

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma componentSum_decidable (A : Instance I J) (S : Selection A.T)
    (d : I⊕J → ℤ) (a : I⊕J) :
    (∑ v,@ite ℤ (S.root v=a) (Classical.propDecidable _) (d v) 0)=
      ∑ v,if S.root v=a then d v else 0 := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : S.root v=a <;> simp only [h,ite_true, if_true,ite_false]

lemma root_eq_large (A : Instance I J) (S : Selection A.T) (i : I) (j : J)
    (hs : A.small i j=false) : S.root (.inl i)=S.root (.inr j) := by
  have hcap : ∀ e∈(ForestCapacity.cellGraph A.small).edgeSet,0<ForestCapacity.capacity A.b e := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    have hg : (ForestCapacity.cellGraph A.small).Adj u v := by simpa using he
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim hg
      | inr j => exact (A.hlarge i j hg).2
    | inr j =>
      cases v with
      | inl i => exact (A.hlarge i j hg).2
      | inr j' => exact False.elim hg
  have hspans := MaximumForest.maximum_spans (ForestCapacity.cellGraph A.small) A.T
    (ForestCapacity.capacity A.b) A.hTG A.hT A.hmax hcap
  apply S.constant
  rw [hspans]
  exact (show (ForestCapacity.cellGraph A.small).Adj (.inl i) (.inr j) from hs).reachable

lemma componentTotal_residual (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a=
      componentTotal A S (smallDemand A.small A.X x q) a := by
  let R : I → ℤ := fun i => if S.root (.inl i)=a then 1 else 0
  let C : J → ℤ := fun j => if S.root (.inr j)=a then 1 else 0
  have hrow (i : I) : R i*rowResidual A.small A.T A.r x free i=
      ∑ j,R i*(A.X i j-fixedRow A.small A.T x free i j) := by
    rw [rowResidual,←A.hXr i,←Finset.sum_sub_distrib,Finset.mul_sum]
  have hcol (j : J) : C j*(-columnResidual A.small A.T A.c q free j)=
      ∑ i,C j*(fixedColumn A.small A.T q free i j-A.X i j) := by
    rw [columnResidual,←A.hXc j,neg_sub,←Finset.sum_sub_distrib,Finset.mul_sum]
  unfold componentTotal residualDemand smallDemand
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  change (∑ i,R i*rowResidual A.small A.T A.r x free i)+
      (∑ j,C j*(-columnResidual A.small A.T A.c q free j))=
    (∑ i,R i*(∑ j,if A.small i j then A.X i j-x i j else 0))+
      ∑ j,C j*(∑ i,if A.small i j then q i j-A.X i j else 0)
  simp_rw [hrow,hcol,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => C j*(fixedColumn A.small A.T q free i j-A.X i j)),
    Finset.sum_comm (f := fun j i => C j*(if A.small i j then q i j-A.X i j else 0)),
    ←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : A.small i j=true
  · simp [fixedRow,fixedColumn,hs]
  · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
    have he : R i=C j := by unfold R C; rw [root_eq_large A S i j hs']
    rw [he]
    simp only [fixedRow,fixedColumn,hs',Bool.false_eq_true,ite_false]
    ring

lemma table_row_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (i : I) :
    (∑ j,table A.T S r c i j)=
      r i-∑ v,if S.root v=Sum.inl i then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inl i)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ i',flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply flow_supported
    intro h
    exact A.hTG h
  simp only [hz,zero_add,Sum.elim_inl] at hs
  rw [componentSum_decidable] at hs
  simpa only [table] using hs

lemma table_column_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (j : J) :
    -(∑ i,table A.T S r c i j)=
      -c j-∑ v,if S.root v=Sum.inr j then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inr j)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ j',flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply flow_supported
    intro h
    exact A.hTG h
  have hskew : (∑ i,flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i,table A.T S r c i j) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact flow_skew S _ _ _
  simp only [hz,add_zero,Sum.elim_inr,hskew] at hs
  rw [componentSum_decidable] at hs
  exact hs

theorem signedResidual_eq_small (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    signedResidual A S x q free a=-componentTotal A S (smallDemand A.small A.X x q) a := by
  suffices he : signedResidual A S x q free a=
      -componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a by
    rw [he,componentTotal_residual]
  have htotal : ∀ d : I⊕J → ℤ,
      (∑ v,if S.root v=a then d v else 0)=componentTotal A S d a := by
    intro d
    simp [componentTotal,ite_mul]
  cases a with
  | inl i =>
    simp only [signedResidual,Sum.elim_inl]
    simp_rw [row_pointwise]
    rw [Finset.sum_add_distrib]
    have hr := table_row_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) i
    change (∑ j,solved A S x q free i j)=_ at hr
    rw [hr,htotal]
    unfold residualDemand rowResidual columnResidual
    ring
  | inr j =>
    simp only [signedResidual,Sum.elim_inr]
    simp_rw [column_pointwise]
    rw [Finset.sum_add_distrib]
    have hc := table_column_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) j
    change -(∑ i,solved A S x q free i j)=_ at hc
    have hc' : (∑ i,solved A S x q free i j)=columnResidual A.small A.T A.c q free j+
        ∑ v,if S.root v=Sum.inr j then
          Sum.elim (rowResidual A.small A.T A.r x free)
            (fun j => -columnResidual A.small A.T A.c q free j) v else 0 := by linarith
    rw [hc',htotal]
    unfold residualDemand rowResidual columnResidual
    ring

theorem signedResidual_independent (A : Instance I J) (S : Selection A.T)
    (x q free free' : I → J → ℤ) :
    signedResidual A S x q free=signedResidual A S x q free' := by
  funext a
  rw [signedResidual_eq_small,signedResidual_eq_small]

lemma abs_actualDeviation_solved (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (a : I⊕J) :
    |ForestLiteralCount.actualDeviation A.small A.T A.b x y free A.r A.c
      (solved A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
        (fun i j => (free i j:ℤ))) a|=
    |(signedResidual A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
      (fun i j => (free i j:ℤ)) a:ℝ)| := by
  cases a with
  | inl i =>
    simp only [ForestLiteralCount.actualDeviation,signedResidual,Sum.elim_inl,completed,
      ForestLiteralCount.largeValue]
    push_cast
    rfl
  | inr j =>
    simp only [ForestLiteralCount.actualDeviation,signedResidual,Sum.elim_inr,completed,
      ForestLiteralCount.largeValue]
    push_cast
    rw [abs_neg]

end ContingencyTables.RootedRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the physical scaled Lipschitz bound for selected roots -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedRootPenalty
open ForestScaledPenalty (intervalCost intervalCost_nonnegative intervalCost_change
  free_card_le tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem penalty_change (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (x q : I → J → ℤ)
    (v w : FreeCell A.small A.T → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ f,|v f-w f|≤ r) :
    |penalty A S C B x q v-penalty A S C B x q w|≤(2*C*(A.d:ℝ)^2/B)*r := by
  have hterm (t : TreeCell A.T) :
      |intervalCost (scaledTree A S B x q v t)-intervalCost (scaledTree A S B x q w t)|≤
        (A.d:ℝ)*(2/B)*r := by
    apply (intervalCost_change _ _).trans
    have hh := AffinePenalty.affineValue_change (normalizedOffset A S t x q)
      (normalizedCoefficient A S B t) v w (2/B) r (by positivity)
      (fun f => normalized_coefficient_bound A S t f.val B hB) hvw
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast free_card_le A) (by positivity : (0:ℝ)≤2/B)) hr)
  have he : penalty A S C B x q v-penalty A S C B x q w=
      C*∑ t : TreeCell A.T,(intervalCost (scaledTree A S B x q v t)-
        intervalCost (scaledTree A S B x q w t)) := by
    unfold penalty
    rw [Finset.sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg hC]
  calc
    _≤ C*∑ t : TreeCell A.T,|intervalCost (scaledTree A S B x q v t)-
      intervalCost (scaledTree A S B x q w t)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hC
    _≤ C*∑ _t : TreeCell A.T,(A.d:ℝ)*(2/B)*r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hterm t)) hC
    _=C*((Fintype.card (TreeCell A.T):ℝ)*((A.d:ℝ)*(2/B)*r)) := by simp
    _≤ C*((A.d:ℝ)*((A.d:ℝ)*(2/B)*r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by exact_mod_cast tree_card_le A) (by positivity)) hC
    _=_ := by ring

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root geometric density is the literal completion weight -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedPhysicalCompletion RootedRootPenalty
open ForestScaledPenalty (integerCube intervalCost intervalCost_div tree_sum_eq)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma free_coefficient_sum (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (F : I×J → ℝ) :
    (∑ f : FreeCell A.small A.T,coefficient A S t f.val*F f.val)=
      ∑ a : I×J,coefficient A S t a*F a := by
  let p : I×J → Prop := fun a => A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  calc
    _=∑ a ∈ Finset.univ.filter p,coefficient A S t a*F a :=
      (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun _ => by simp)
        (fun a => coefficient A S t a*F a)).symm
    _=_ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ ha
      have hp : ¬p a := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using ha
      change ¬(A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)) at hp
      simp only [coefficient,hp,ite_false,zero_mul]

theorem scaledTree_integer (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (x q : I → J → ℤ) (f : FreeIndex A.small A.T A.b) (t : TreeCell A.T) :
    scaledTree A S B x q (integerCube A B f) t=
      (solved A S x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
        t.val.1 t.val.2:ℝ)/(A.b t.val.1 t.val.2:ℝ) := by
  let F : I×J → ℝ := fun a => (freeTable A.small A.T A.b f a.1 a.2:ℝ)
  have hterm (a : FreeCell A.small A.T) :
      normalizedCoefficient A S B t a*integerCube A B f a=
        coefficient A S t a.val*F a.val/(A.b t.val.1 t.val.2:ℝ) := by
    have hN : (A.b a.val.1 a.val.2:ℝ)+1≠0 := by positivity
    have hbt : (A.b t.val.1 t.val.2:ℝ)≠0 := by
      exact_mod_cast (Nat.ne_of_gt (A.hlarge _ _ (A.hTG t.property)).2)
    have hF : F a.val=(f a).val := by simp [F,freeTable,a.property]
    rw [hF]
    unfold normalizedCoefficient integerCube
    field_simp [hB.ne',hN,hbt]
  unfold scaledTree AffinePenalty.affineValue normalizedOffset
  simp_rw [hterm]
  rw [←Finset.sum_div,free_coefficient_sum,←add_div]
  have hh := solved_eq_affine A S t x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
  unfold affineTree AffinePenalty.affineValue at hh
  apply congrArg (fun z : ℝ => z/(A.b t.val.1 t.val.2:ℝ))
  simpa only [F,Int.cast_natCast] using hh.symm

theorem rootConstant_eq_assignment (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) :
    rootConstant A S x q=
      ∑ a,if RootedPenalty.rootFlag S a then |(signedResidual A S x q free a:ℝ)| else 0 := by
  have hh := signedResidual_independent A S x q free 0
  unfold rootConstant
  apply Finset.sum_congr rfl
  intro a _
  rw [hh]

theorem penalty_at_integer (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hB : 0<B) (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    penalty A S C B (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))
      (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))
      (integerCube A B f)=C*RootedLiteralCount.actualPenalty A S
        (ForestCountIdentification.smallX A.small z) (ForestCountIdentification.smallY A.small z)
        (freeTable A.small A.T A.b f)
        (solved A S (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))
          (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))
          (fun i j => (freeTable A.small A.T A.b f i j:ℤ))) := by
  let x := ForestCountIdentification.smallX A.small z
  let y := ForestCountIdentification.smallY A.small z
  let free := freeTable A.small A.T A.b f
  let tree := solved A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
    (fun i j => (free i j:ℤ))
  have hroot : rootConstant A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))=
      ∑ a,if RootedPenalty.rootFlag S a then
        |ForestLiteralCount.actualDeviation A.small A.T A.b x y free A.r A.c tree a| else 0 := by
    rw [rootConstant_eq_assignment A S _ _ (fun i j => (free i j:ℤ))]
    apply Finset.sum_congr rfl
    intro a _
    rw [abs_actualDeviation_solved]
  have htree : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B (fun i j => (x i j:ℤ))
      (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (integerCube A B f) t))=
      ∑ i,∑ j,if A.T.Adj (.inl i) (.inr j) then
        max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-A.b i j))/(A.b i j:ℝ) else 0 := by
    calc
      _=∑ t : TreeCell A.T,
          max 0 (max (-(tree t.val.1 t.val.2:ℝ)) ((tree t.val.1 t.val.2:ℝ)-A.b t.val.1 t.val.2))/
            (A.b t.val.1 t.val.2:ℝ) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [scaledTree_integer A S B hB]
        exact intervalCost_div _ _ (by exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2)
      _=_ := tree_sum_eq A (fun a =>
        max 0 (max (-(tree a.1 a.2:ℝ)) ((tree a.1 a.2:ℝ)-A.b a.1 a.2))/(A.b a.1 a.2:ℝ))
  unfold penalty
  change C*(rootConstant A S (fun i j => (x i j:ℤ))
    (fun i j => ((A.b i j-y i j:ℕ):ℤ))+_)=_
  rw [hroot,htree]
  rfl

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source height bounds the entire selected-root density cube -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedRootPenalty RootedPhysicalCompletion BalancedBox
open ForestScaledPenalty (rowCounts columnCounts rowCounts_bounds columnCounts_bounds
  intervalCost intervalCost_div integerCube integerCube_zero zeroAssignment tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rootConstant_bound (A : Instance I J) (S : Selection A.T)
    (z : View A → ℕ) (hz : InBox (bounds A) z) :
    rootConstant A S (rowCounts A z) (columnCounts A z)≤2*(A.d:ℝ)*A.W := by
  let d := ForestRootPenalty.smallDemand A.small A.X (rowCounts A z) (columnCounts A z)
  have he (a : I⊕J) : (signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)=
      -(∑ v,if S.root v=a then (d v:ℝ) else 0) := by
    rw [signedResidual_eq_small]
    unfold componentTotal
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : S.root v=a <;> simp [hv,d]
  have hrow (i : I) : |((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|≤
      ∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |A.X i j-rowCounts A z i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(rowCounts_bounds A z hz i j hs).1,
          (rowCounts_bounds A z hz i j hs).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hcol (j : J) : |((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|≤
      ∑ i,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |columnCounts A z i j-A.X i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(columnCounts_bounds A z i j).1,
          (columnCounts_bounds A z i j).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hdemand : (∑ a,|(d a:ℝ)|)≤2*∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ i,|((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|)+
      (∑ j,|((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|)≤_
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
    have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcol j)
    rw [Finset.sum_comm] at hc
    linarith
  have hsmall : (∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0)≤(A.d:ℝ)*A.W := by
    calc
      _≤∑ _i : I,∑ _j : J,(A.W:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        cases hs : A.small i j
        · simp only [Bool.false_eq_true,ite_false]
          positivity
        · simp only [ite_true, if_true]
          exact_mod_cast (A.hsmall i j hs).le
      _=(Fintype.card I*Fintype.card J:ℕ)*(A.W:ℝ) := by simp; ring
      _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast A.hcard) (Nat.cast_nonneg _)
  unfold rootConstant
  calc
    _≤∑ a,|(signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)| := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs <;> first | exact le_rfl | exact abs_nonneg _
    _=∑ a,|∑ v,if S.root v=a then (d v:ℝ) else 0| := by simp_rw [he,abs_neg]
    _≤∑ v,|(d v:ℝ)| := ForestRootPenalty.sum_abs_componentTotal S.root (fun v => (d v:ℝ))
    _≤_ := hdemand.trans (by linarith)

lemma zero_tree_bound (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (z : View A → ℕ) (hz : InBox (bounds A) z) (t : TreeCell A.T) :
    intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t)≤10*(A.d:ℝ) := by
  have hzero : (fun i j => (freeTable A.small A.T A.b (zeroAssignment A) i j:ℤ))=0 := by
    funext i j
    unfold freeTable zeroAssignment
    split_ifs <;> rfl
  have hinterval := RootedIntervals.solved_in_intervals A S
    (rowCounts A z) (columnCounts A z) 0
    (by intro i j hs; exact ⟨rowCounts_bounds A z hz i j hs,columnCounts_bounds A z i j⟩)
    (by intro i j _ _; exact ⟨le_rfl,Nat.cast_nonneg _⟩)
    t.val.1 t.val.2 t.property
  rw [←integerCube_zero A B,scaledTree_integer A S B hB,hzero,intervalCost_div]
  · have hb : (0:ℝ)<A.b t.val.1 t.val.2 := by exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
    rw [div_le_iff₀ hb]
    have hlo : -(10*(A.d:ℝ)*A.b t.val.1 t.val.2)≤
        (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ) := by
      exact_mod_cast hinterval.1
    have hup : (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ)≤
        10*(A.d:ℝ)*A.b t.val.1 t.val.2 := by exact_mod_cast hinterval.2
    apply max_le
    · positivity
    · apply max_le <;> linarith
  · exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2

theorem penalty_cube_bound (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (v : FreeCell A.small A.T → ℝ) (hv : ∀ f,0≤ v f ∧ v f≤ B) :
    0≤ penalty A S C B (rowCounts A z) (columnCounts A z) v ∧
      penalty A S C B (rowCounts A z) (columnCounts A z) v≤ C*(10*(A.d:ℝ)^2*((A.W:ℝ)+1)) := by
  have hzero : penalty A S C B (rowCounts A z) (columnCounts A z) 0≤
      C*(2*(A.d:ℝ)*A.W+10*(A.d:ℝ)^2) := by
    unfold penalty
    apply mul_le_mul_of_nonneg_left _ hC
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => zero_tree_bound A S B hB z hz t)
    have ht : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t))≤
        10*(A.d:ℝ)^2 := by
      calc
        _≤(Fintype.card (TreeCell A.T):ℝ)*(10*(A.d:ℝ)) := by simpa using hsum
        _≤(A.d:ℝ)*(10*(A.d:ℝ)) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast tree_card_le A) (by positivity)
        _=_ := by ring
    linarith [rootConstant_bound A S z hz]
  have hchange := (le_abs_self _).trans (penalty_change A S C B hC hB
    (rowCounts A z) (columnCounts A z) v 0 B hB.le (by
      intro f
      simpa only [Pi.zero_apply,sub_zero,abs_of_nonneg (hv f).1] using (hv f).2))
  have hcancel : (2*C*(A.d:ℝ)^2/B)*B=2*C*(A.d:ℝ)^2 := div_mul_cancel₀ _ hB.ne'
  rw [hcancel] at hchange
  have hd : (1:ℝ)≤ A.d := by exact_mod_cast A.hd
  have hW : (2:ℝ)≤ A.W := by exact_mod_cast A.hW
  have hscalar : 2*(A.d:ℝ)*A.W+12*(A.d:ℝ)^2≤10*(A.d:ℝ)^2*((A.W:ℝ)+1) := by
    have hdd : (A.d:ℝ)≤(A.d:ℝ)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hdd (by positivity : (0:ℝ)≤ A.W)
    have hp' := mul_le_mul_of_nonneg_left hW (sq_nonneg (A.d:ℝ))
    nlinarith
  refine ⟨penalty_nonnegative A S C B hC _ _ v,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hscalar hC]

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAnnealing
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Adjacent selected-root weights and ideal multipliers

The actual computed-root penalty satisfies the source height bound.
It gives the factor-two annealing estimates for the same literal
completion count used by the executed density evaluator.
-/

namespace ContingencyTables.RootedAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial
open CompanionAnnealing (scale scale_positive source_parameter)
open ForestAssignmentSplit
open ForestScaledPenalty (rowCounts columnCounts integerCube)
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The source height bound holds for the selected, computed root too. -/
theorem penalty_bound (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (z : View A → ℕ) (hz : InBox (bounds A) z)
    (f : FreeIndex A.small A.T A.b) :
    0≤ penalty A R z f ∧ penalty A R z f≤ scale A := by
  have hv (a : FreeCell A.small A.T) :
      0≤ integerCube A 1 f a ∧ integerCube A 1 f a≤1 := by
    have hp : (0:ℝ)<(A.b a.val.1 a.val.2:ℝ)+1 := by positivity
    have hf : ((f a).val:ℝ)≤(A.b a.val.1 a.val.2:ℝ)+1 := by
      exact_mod_cast (Nat.le_of_lt (f a).isLt)
    unfold integerCube
    simp only [one_mul]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,(div_le_one hp).mpr hf⟩
  have hb := RootedScaledPenalty.penalty_cube_bound A R 1 1
    (by norm_num) (by norm_num) z hz (integerCube A 1 f) hv
  have he := RootedScaledPenalty.penalty_at_integer A R 1 1 (by norm_num) z f
  have hr : (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))=rowCounts A z := rfl
  have hc : (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))=
      columnCounts A z := rfl
  rw [hr,hc] at he
  rw [he] at hb
  simpa only [one_mul,penalty,scale] using hb

theorem count_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (z : View A → ℕ)
    (hz : InBox (bounds A) z) :
    (1/2)*RootedCountIdentification.h A R ((j:ℝ)/scale A) z≤ RootedCountIdentification.h A R (((j+1:ℕ):ℝ)/scale A) z ∧
      RootedCountIdentification.h A R (((j+1:ℕ):ℝ)/scale A) z≤ RootedCountIdentification.h A R ((j:ℝ)/scale A) z := by
  let K (k : ℕ) (a : ForestAssignmentSplit.FreeIndex A.small A.T A.b) : ℝ :=
    (2:ℝ)^(-((k:ℝ)/scale A)*penalty A R z a)
  have hterm (a : ForestAssignmentSplit.FreeIndex A.small A.T A.b) :
      (1/2)*K j a≤ K (j+1) a ∧ K (j+1) a≤ K j a := by
    have hp := penalty_bound A R z hz a
    have hQ := scale_positive A
    have hPQ0 : 0≤ penalty A R z a/scale A := div_nonneg hp.1 hQ.le
    have hPQ1 : penalty A R z a/scale A≤1 := (div_le_one hQ).mpr hp.2
    have hlo : (1/2:ℝ)≤(2:ℝ)^(-(penalty A R z a/scale A)) := by
      calc
        _ = (2:ℝ)^(-1:ℝ) := by norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hup : (2:ℝ)^(-(penalty A R z a/scale A))≤1 := by
      calc
        _ ≤ (2:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by norm_num
    have he : K (j+1) a=K j a*(2:ℝ)^(-(penalty A R z a/scale A)) := by
      unfold K
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      push_cast
      ring
    have hK : 0≤ K j a := (Real.rpow_pos_of_pos (by norm_num) _).le
    rw [he]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hlo hK]
    · nlinarith [mul_le_mul_of_nonneg_left hup hK]
  change (1/2)*(∑ a, K j a)≤(∑ a, K (j+1) a) ∧ (∑ a, K (j+1) a)≤∑ a, K j a
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (hterm a).1)
  · exact Finset.sum_le_sum (fun a _ => (hterm a).2)

theorem weight_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2)*weight A R j S≤ weight A R (j+1) S ∧ weight A R (j+1) S≤ weight A R j S := by
  have hz : InBox (bounds A) (groupCount (group (labelCell A)) S) := by
    rw [← label_capacity]
    exact SliceFactorial.groupCount_inBox _ _
  have h := count_adjacent A R j _ hz
  have hc : 0≤ FactorialSignatures.factorialProduct (groupCount (group (labelCell A)) S)/
      CompanionFactorialApplication.denominator A :=
    (div_pos (FactorialSignatures.factorialProduct_positive _)
      (CompanionFactorialApplication.denominator_positive A)).le
  unfold weight RootedFactorialApplication.f firstLift
  simp only [mul_div_assoc]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h.1 hc]
  · exact mul_le_mul_of_nonneg_right h.2 hc

theorem total_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (ps : List ((Labels A×Bool)×(Labels A×Bool))) (S : Set (Labels A×Bool)) :
    (1/2)*slotTotal ps (weight A R j) S≤ slotTotal ps (weight A R (j+1)) S ∧
      slotTotal ps (weight A R (j+1)) S≤ slotTotal ps (weight A R j) S := by
  constructor
  · rw [← slotTotal_scale]
    exact slotTotal_mono _ _ _ (fun T => (weight_adjacent A R j T).1) _
  · exact slotTotal_mono _ _ _ (fun T => (weight_adjacent A R j T).2) _

theorem ideal_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs) (hpr : p≠r) :
    (slotTotal pairs (weight A R j) ∅/slotDefect pairs (weight A R j) ∅ p r)/2≤
      slotTotal pairs (weight A R (j+1)) ∅/slotDefect pairs (weight A R (j+1)) ∅ p r ∧
    slotTotal pairs (weight A R (j+1)) ∅/slotDefect pairs (weight A R (j+1)) ∅ p r≤
      2*(slotTotal pairs (weight A R j) ∅/slotDefect pairs (weight A R j) ∅ p r) := by
  have h0 := slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh
  have hd0 := slotDefect_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh p r hp hr hpr
  have hd1 := slotDefect_pos pairs _ (weight_positive A R (j+1)) ∅ PairedLabels.fresh p r hp hr hpr
  have ha := total_adjacent A R j pairs ∅
  have hb' : (1/2)*slotDefect pairs (weight A R j) ∅ p r≤ slotDefect pairs (weight A R (j+1)) ∅ p r ∧
      slotDefect pairs (weight A R (j+1)) ∅ p r≤ slotDefect pairs (weight A R j) ∅ p r := by
    unfold slotDefect
    constructor
    · rw [← slotTotal_scale]
      exact slotTotal_mono _ _ _ (fun S => (weight_adjacent A R j S).1) _
    · exact slotTotal_mono _ _ _ (fun S => (weight_adjacent A R j S).2) _
  constructor
  · rw [div_div,div_le_div_iff₀ (mul_pos hd0 (by norm_num)) hd1]
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hb'.2),mul_nonneg hd0.le (sub_nonneg.mpr ha.1)]
  · rw [← mul_div_assoc,div_le_div_iff₀ hd1 hd0]
    nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr ha.2),mul_nonneg h0.le (sub_nonneg.mpr hb'.1)]

end ContingencyTables.RootedAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root evaluator density on its actual finite bin cube -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit
open CompanionOracleDensity (dimension index pull binWidth height)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem D_bounds (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Fin (dimension A) → ℝ) (hv : ∀ i,0≤ v i ∧ v i≤ binWidth A C) :
    0≤ D A S C z v ∧ D A S C z v≤ height A C := by
  have hh := RootedScaledPenalty.penalty_cube_bound A S C (binWidth A C) hC.le
    (CompanionOracleDensity.binWidth_positive A C hC) z hz (pull A v)
    (fun f => hv ((index A).symm f))
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  unfold height
  ring

theorem D_change (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ i,|v i-w i|≤ r) : |D A S C z v-D A S C z w|≤ r/8 := by
  have hh := RootedScaledPenalty.penalty_change A S C (binWidth A C) hC.le
    (CompanionOracleDensity.binWidth_positive A C hC)
    (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)
    (pull A v) (pull A w) r hr (fun f => hvw ((index A).symm f))
  have hd : (A.d:ℝ)≠0 := by exact_mod_cast (show A.d≠0 by have hh := A.hd; omega)
  have he : (2*C*(A.d:ℝ)^2/binWidth A C)*r=r/8 := by
    unfold binWidth
    field_simp [hC.ne',hd]
    ring
  simpa only [D,he] using hh

theorem exponent_change (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ i,|v i-w i|≤ r) :
    |(a/height A C)*D A S C z v-(a/height A C)*D A S C z w|≤ r/8 := by
  have hH := CompanionOracleDensity.height_positive A C hC
  have hf0 : 0≤ a/height A C := div_nonneg ha hH.le
  have hf1 : a/height A C≤1 := (div_le_one hH).mpr haH
  rw [←mul_sub,abs_mul,abs_of_nonneg hf0]
  exact (mul_le_mul_of_nonneg_left (D_change A S C hC z v w r hr hvw) hf0).trans
    (mul_le_of_le_one_left (by positivity) hf1)

theorem bin_comparison (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (hvw : ∀ i,|v i-w i|≤1) :
    V A S C a z v/4≤ rho A S C a z w ∧ rho A S C a z w≤2*V A S C a z v := by
  have hh := exponent_change A S C a hC ha haH z w v 1 (by norm_num)
    (fun i => by simpa only [abs_sub_comm] using hvw i)
  exact DenseWeights.bin_density_comparison _ _ w v (hh.trans (by norm_num))

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the computed-root completion count

Integer bins and their executable interval draws are the existing
physical bins.  Only their positive density weights change with the
explicit root selector.  All normalizer identities are finite sums.
-/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GridBoundary
open CompanionOracleDensity (dimension index pull binWidth height integerPoint integerBin integerFiber
  assignmentCount ownFiber_positive assignmentCount_positive integerFiber_nonempty)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma gridWeight_positive (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    0<gridWeight A S C a z v := DenseWeights.binWeight_pos _ _ _

lemma density_at_integer (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    rho A S C a z (integerPoint A C f)=
      (2:ℝ)^(-(a*C/height A C)*RootedLiteralCount.actualPenalty A S
        (ForestCountIdentification.smallX A.small z) (ForestCountIdentification.smallY A.small z)
        (freeTable A.small A.T A.b f)
        (RootedPhysicalCompletion.solved A S (ForestScaledPenalty.rowCounts A z)
          (ForestScaledPenalty.columnCounts A z) (fun i j => (freeTable A.small A.T A.b f i j:ℤ)))) := by
  unfold rho DenseWeights.density D
  rw [CompanionOracleDensity.pull_integerPoint]
  have hp := RootedScaledPenalty.penalty_at_integer A S C (binWidth A C)
    (CompanionOracleDensity.binWidth_positive A C hC) z f
  have hr : (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))=
      ForestScaledPenalty.rowCounts A z := rfl
  have hc : (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))=
      ForestScaledPenalty.columnCounts A z := rfl
  rw [hr,hc] at hp
  rw [hp]
  congr 1
  ring

lemma sum_density_integer (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) :
    (∑ f : FreeIndex A.small A.T A.b,rho A S C a z (integerPoint A C f))=
      RootedCountIdentification.h A S (a*C/height A C) z := by
  unfold RootedCountIdentification.h
  apply Finset.sum_congr rfl
  intro f _
  exact density_at_integer A S C a hC z f

lemma binSum_positive (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) : 0<binSum A S C a z K := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  exact Finset.sum_pos (fun _ _ => gridWeight_positive _ _ _ _ _ _) Finset.univ_nonempty

theorem correction_bounds (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0<K) (hW : 100*A.d*K≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (f : FreeIndex A.small A.T A.b) :
    1/8≤ correction A S C a z K hK f ∧ correction A S C a z K hK f≤4 := by
  let v := integerBin A K hK f
  have hpQ := CompanionOracleDensity.actual_population_bounds A K hK hW v
  have hp : (1/2:ℝ)≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A≤2 := by
    constructor
    · simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.2
  have hdist : ∀ i,|realCorner v i-integerPoint A C f i|≤1 := by
    intro i
    simpa only [abs_sub_comm] using CompanionOracleDensity.integerPoint_distance A C K hK hB f i
  have hb := bin_comparison A S C a hC ha haH z (realCorner v) (integerPoint A C f) hdist
  have hw := gridWeight_positive A S C a z v
  have hr : (1/4:ℝ)≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v ∧
      rho A S C a z (integerPoint A C f)/gridWeight A S C a z v≤2 := by
    constructor
    · apply (le_div_iff₀ hw).mpr
      simpa only [gridWeight,div_eq_mul_inv,mul_comm,one_mul] using hb.1
    · exact (div_le_iff₀ hw).mpr (by simpa only [gridWeight] using hb.2)
  have he : correction A S C a z K hK f=
      ((K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)*
        (rho A S C a z (integerPoint A C f)/gridWeight A S C a z v) := by
    unfold correction
    ring
  rw [he]
  constructor
  · have hh := mul_le_mul hp.1 hr.1 (by norm_num : (0:ℝ)≤1/4) (by linarith :
        0≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)
    norm_num at hh ⊢
    exact hh
  · have hh := mul_le_mul hp.2 hr.2 (by linarith [hr.1] :
        0≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v)
      (by norm_num : (0:ℝ)≤2)
    norm_num at hh ⊢
    exact hh

lemma corrected_mass_product (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) :
    correctedMass A S C a z K hK f*correction A S C a z K hK f=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A S C a z K))*
        rho A S C a z (integerPoint A C f) := by
  have hw := (gridWeight_positive A S C a z (integerBin A K hK f)).ne'
  have hf : ((integerFiber A K hK (integerBin A K hK f)).card:ℝ)≠0 := by
    exact_mod_cast (ownFiber_positive A K hK f).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  have hz := (binSum_positive A S C a z K hK).ne'
  unfold correctedMass correction
  field_simp [hw,hf,hc,hz]

theorem corrected_expectation (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) (K : ℕ) (hK : 0<K) :
    (∑ f : FreeIndex A.small A.T A.b,
      correctedMass A S C a z K hK f*correction A S C a z K hK f)=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A S C a z K))*
        RootedCountIdentification.h A S (a*C/height A C) z := by
  simp_rw [corrected_mass_product]
  rw [←Finset.mul_sum,sum_density_integer A S C a hC]

lemma ratioMean_eq (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (a : ℕ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) :
    ratioMean A S C a z K=binSum A S C (a+1) z K/binSum A S C a z K := by
  unfold ratioMean binSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  have hv := (gridWeight_positive A S C a z v).ne'
  have hz := (binSum_positive A S C a z K hK).ne'
  unfold ratioObservable
  change (gridWeight A S C a z v/binSum A S C a z K)*
    (gridWeight A S C (a+1) z v/gridWeight A S C a z v)=
      gridWeight A S C (a+1) z v/binSum A S C a z K
  field_simp [hv,hz]

lemma binSum_zero (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (z : View A → ℕ) (K : ℕ) : binSum A S C 0 z K=(K:ℝ)^dimension A := by
  simp only [binSum,gridWeight,V,DenseWeights.binWeight,zero_div,zero_mul,Int.floor_zero,
    Int.cast_zero,neg_zero,Real.rpow_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,CompanionOracleDensity.oracle_grid_card,Nat.cast_pow]

lemma ratio_telescope (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (j : ℕ) :
    (∏ a∈Finset.range j,ratioMean A S C a z K)=binSum A S C j z K/(K:ℝ)^dimension A := by
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  induction j with
  | zero => simp only [Finset.range_zero,Finset.prod_empty,Nat.cast_zero,binSum_zero,div_self hp]
  | succ j ih =>
    rw [Finset.prod_range_succ,ih,ratioMean_eq A S C j z K hK]
    have hz := (binSum_positive A S C j z K hK).ne'
    push_cast
    field_simp [hp,hz]

theorem oracle_telescope (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (K : ℕ) (hK : 0<K) (j : ℕ) :
    (assignmentCount A:ℝ)*(∏ a∈Finset.range j,ratioMean A S C a z K)*
      (∑ f : FreeIndex A.small A.T A.b,
        correctedMass A S C j z K hK f*correction A S C j z K hK f)=
      RootedCountIdentification.h A S ((j:ℝ)*C/height A C) z := by
  rw [ratio_telescope A S C z K hK j,corrected_expectation A S C j hC z K hK]
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  have hz := (binSum_positive A S C j z K hK).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  field_simp [hp,hz,hc]

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleChain
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bin chain for the computed-root forest penalty

All cut geometry is proved from the selected-root density. The only
conditional inputs are the same finite-box Prékopa–Leindler inequality
and finite reversible-chain Cheeger theorem used by the original chain.
-/

namespace ContingencyTables.RootedOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open CompanionOracleDensity (dimension height proposal_bounds proposal_degree cutConstant)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracleChain_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    (oracleChain A R C a z hK).π v = gridWeight A R C a z v/
      ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w := rfl

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational grid transitions for the selected-root evaluator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open CompanionOracleDensity (dimension height binWidth height_positive oracleProposalRat oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem oracleStationaryLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    ((oracleStationaryLaw A R C a z hK).mass v:ℝ)=(oracleChain A R C a z hK).π v := by
  change ((rationalGridWeight A R C a z v/
    ∑ w : Grid (I := Fin (dimension A)) K,rationalGridWeight A R C a z w:ℚ):ℝ)=_
  simp only [Rat.cast_div,Rat.cast_sum,rationalGridWeight_cast]
  rfl

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual fixed-word corrected draws for the selected-root count -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The stationary bin draw followed by the actual uniform integer
interval draw is precisely the corrected mass used in the exact h identity. -/
theorem stationaryIntegerLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (f : FreeIndex A.small A.T A.b) :
    ((stationaryIntegerLaw A R C a z K hK hW).mass f:ℝ)=correctedMass A R C a z K (by omega) f := by
  change ((∑ v,(oracleStationaryLaw A R C a z hK).mass v*
    (exactBinLaw A K (by omega) hW v).mass f:ℚ):ℝ)=_
  simp only [Rat.cast_sum,Rat.cast_mul,exactBinLaw_mass,oracleStationaryLaw_cast,
    oracleChain_pi,apply_ite,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_zero]
  calc
    _ = ∑ v : Grid (I := Fin (dimension A)) K,
        if integerBin A K (by omega) f=v then
          gridWeight A R C a z v/binSum A R C a z K/(integerFiber A K (by omega) v).card else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp only [binSum,div_eq_mul_inv,one_mul,mul_zero]
    _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,correctedMass]

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSamples
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence for the actual rational correction samples -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma correctionMean_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) :
    correctionMean A R C a z K hK hW=
      ∑ f : FreeIndex A.small A.T A.b,
        correctedMass A R C a z K (by omega) f*correction A R C a z K (by omega) f := by
  unfold correctionMean expectation
  simp_rw [stationaryIntegerLaw_cast]

lemma correctionMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) :
    1/8 ≤ correctionMean A R C a z K hK hW ∧ correctionMean A R C a z K hK hW ≤ 4 := by
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  exact expectation_bounds _ _ _ _ (correction_bounds A R C a (by exact_mod_cast hC)
    (Nat.cast_nonneg _) haHR z K (by omega) hW hB)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSamples
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete rational observations of the companion annealing ratios -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma floor_step (x q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ⌊x+q⌋=⌊x⌋ ∨ ⌊x+q⌋=⌊x⌋+1 := by
  have hlo := Int.floor_mono (show x ≤ x+q by linarith)
  have hhi := Int.floor_mono (show x+q ≤ x+1 by linarith)
  rw [Int.floor_add_one] at hhi
  omega

/-- The actual phase observable takes exactly the two source values,
since one annealing step changes its integer exponent by zero or one. -/
theorem ratioObservable_cases (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    ratioObservable A R C a z v=1 ∨ ratioObservable A R C a z v=1/2 := by
  have hD := D_bounds A R C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  let q := D A R C z (realCorner v)/height A C
  have hq0 : 0 ≤ q := div_nonneg hD.1 (height_positive A C hC).le
  have hq1 : q ≤ 1 := (div_le_one (height_positive A C hC)).mpr hD.2
  let x := (a:ℝ)/height A C*D A R C z (realCorner v)
  have he : ((a:ℝ)+1)/height A C*D A R C z (realCorner v)=x+q := by
    dsimp only [x,q]
    ring
  have hr : ratioObservable A R C a z v=(2:ℝ)^(-((⌊x+q⌋:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)) := by
    unfold ratioObservable gridWeight V DenseWeights.binWeight
    rw [he,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    change -((⌊x+q⌋:ℤ):ℝ)- -((⌊x⌋:ℤ):ℝ)=_
    ring
  rcases floor_step x q hq0 hq1 with hf|hf
  · left
    rw [hr,hf]
    simp
  · right
    rw [hr,hf]
    have hh : -(((⌊x⌋:ℤ)+1:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)=(-1:ℝ) := by
      push_cast
      ring
    rw [hh]
    norm_num

lemma ratioObservable_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ ratioObservable A R C a z v ∧ ratioObservable A R C a z v ≤ 1 := by
  rcases ratioObservable_cases A R C hC a z hz hKB v with h|h <;> rw [h] <;> norm_num

lemma ratioMean_stationary (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) :
    expectation (oracleStationaryLaw A R C a z hK) (ratioObservable A R C a z)=ratioMean A R C a z K := by
  unfold expectation ratioMean
  apply Finset.sum_congr rfl
  intro v _
  rw [oracleStationaryLaw_cast,oracleChain_pi]
  rfl

lemma ratioMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C) :
    1/2 ≤ ratioMean A R C a z K ∧ ratioMean A R C a z K ≤ 1 := by
  rw [←ratioMean_stationary A R C a z hK]
  exact expectation_bounds _ _ _ _ (ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleEstimator
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal rational product estimator for a companion h-value -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The exact means appearing in the implemented product telescope to
h, including the integer-population correction and the free-assignment count. -/
theorem targetFactor_product (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) :
    (assignmentCount A:ℝ)*(∏ i,targetFactor A R C z K hK hW j i)=
      RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := by
  have hp : (∏ a : Fin j,ratioMean A R C a.val z K)=
      ∏ a∈Finset.range j,ratioMean A R C a z K :=
    Fin.prod_univ_eq_prod_range (fun a : ℕ => ratioMean A R (C:ℝ) a z K) j
  rw [Fintype.prod_option]
  simp only [targetFactor]
  rw [hp,correctionMean_eq]
  have ht := oracle_telescope A R C (by exact_mod_cast hC) z K (by omega) j
  convert ht using 1 <;> first | rfl | ring

lemma targetFactor_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C) (i : Option (Fin j)) :
    0 < targetFactor A R C z K hK hW j i := by
  cases i with
  | none =>
    have hh := (correctionMean_bounds A R C j hC hj z K hK hW hB).1
    change 0 < correctionMean A R C j z K hK hW
    linarith
  | some a =>
    have hh := (ratioMean_bounds A R C a.val hC z hz hK hB.le).1
    change 0 < ratioMean A R C a.val z K
    linarith

/-- On the event certified by the actual independent block experiments,
the returned rational product estimates the literal original h-value. -/
theorem goodEstimate_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K)
    (draws : EstimatorInput A C K j (innerTolerance epsilon j) failure)
    (hgood : GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws) :
    (1-(epsilon:ℝ)/4)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ≤
        (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) ∧
      (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) ≤
        (1+(epsilon:ℝ)/4)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := by
  have htol : (innerTolerance epsilon j:ℝ)=
      (epsilon:ℝ)/(200*(Fintype.card (Option (Fin j)):ℝ)) := by
    simp only [innerTolerance,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_one,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have hprod := FiniteProductAccuracy.product_relative
    (fun i => (observedFactor A R C z K hK hW j (innerTolerance epsilon j) failure v draws i:ℝ))
    (targetFactor A R C z K hK hW j) (targetFactor_positive A R C hC z hz K hK hW hB j hj)
    epsilon (by exact_mod_cast he0) (by exact_mod_cast he1)
    (by intro i; rw [←htol]; exact hgood i) (by simp)
  have hcount : (0:ℝ) ≤ assignmentCount A := Nat.cast_nonneg _
  have hlow := mul_le_mul_of_nonneg_left hprod.1 hcount
  have hupp := mul_le_mul_of_nonneg_left hprod.2 hcount
  have htarget := targetFactor_product A R C hC z K hK hW j
  have hvalue : (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)=
      (assignmentCount A:ℝ)*∏ i,
        (observedFactor A R C z K hK hW j (innerTolerance epsilon j) failure v draws i:ℝ) := by
    simp only [estimateValue,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod]
  rw [hvalue]
  rw [←htarget]
  constructor
  · simpa only [mul_left_comm] using hlow
  · simpa only [mul_left_comm] using hupp

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorConfidence
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A concrete rational estimator with bounded independent Boolean input
has the required relative-error guarantee for the original h-value. -/
theorem estimateValue_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  have ht : 0 ≤ RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := (RootedCountIdentification.h_positive A R _ _).le
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hp (draws : EstimatorInput A C K j (innerTolerance epsilon j) failure) :
      (if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤
        if ¬GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws then 1 else 0 := by
    by_cases hg : GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws
    · have ha := goodEstimate_accuracy A R C hC z hz K hK hW hB j hj epsilon failure he0 he1 v draws hg
      have hn : ¬((estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)) := by
        rintro (hb|hb) <;> nlinarith
      simp only [hn,hg,not_true_eq_false,ite_false,le_refl]
    · simp only [hg,not_false_eq_true,ite_true, if_true]
      split_ifs <;> norm_num
  exact (uniformAverage_mono _ _ hp).trans
    (goodEstimate_failure A R C hC z hz K hK hW hB j hj (innerTolerance epsilon j) failure
      (innerTolerance_pos epsilon j he0) (innerTolerance_lt_one epsilon j he1) hf hPL hCheeger v)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWords
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single Boolean word for the literal companion weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The single fixed-length word has exactly the previously analyzed
independent-product law. -/
theorem wordEstimate_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool =>
      if (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  let test := fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure) test
  change uniformAverage (fun bits => test
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure bits)) ≤ _
  exact he.trans_le
    (estimateValue_failure A R C hC z hz K hK hW hB j hj epsilon failure he0 he1 hf hPL hCheeger v)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorAmplification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic confidence amplification of the actual weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteMedianConfidence
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem medianEstimate_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    1-(delta:ℝ) ≤ uniformAverage (fun bits : Fin (medianEstimatorBits A C K j epsilon delta) → Bool =>
      if (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ≤
          (medianEstimate A R C z K hK hW j epsilon delta v bits:ℝ) ∧
        (medianEstimate A R C z K hK hW j epsilon delta v bits:ℝ) ≤
          (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z
      then (1:ℝ) else 0) := by
  have heh0 : 0 < epsilon/2 := by positivity
  have heh1 : epsilon/2 < 1 := by linarith
  have ht : 0 < RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := RootedCountIdentification.h_positive A R _ _
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hbase := wordEstimate_failure A R C hC z hz K hK hW hB j hj (epsilon/2) 1 heh0 heh1
    (by norm_num) hPL hCheeger v
  have hbad : uniformAverage (fun bits : Fin (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) → Bool =>
      if (wordEstimate A R C z K hK hW j (epsilon/2) 1 v bits:ℝ) <
          (1-(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (wordEstimate A R C z K hK hW j (epsilon/2) 1 v bits:ℝ)
      then (1:ℝ) else 0) ≤ 5/16 := by
    have hh : (1:ℝ)/4 ≤ 5/16 := by norm_num
    apply le_trans ?_ hh
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using hbase
  have hm := median_confidence_real
    (wordEstimate A R C z K hK hW j (epsilon/2) 1 v)
    ((1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    ((1-(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    ((1+(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    ((1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    (by nlinarith) (by nlinarith) delta hd hbad
  let test := fun xs : Fin (repetitionCount delta) →
      (Fin (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) → Bool) =>
      if (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ≤
          (rationalMedian (List.ofFn (fun i => wordEstimate A R C z K hK hW j (epsilon/2) 1 v (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => wordEstimate A R C z K hK hW j (epsilon/2) 1 v (xs i))):ℝ) ≤
          (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z
      then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1)) test
  change 1-(delta:ℝ) ≤ uniformAverage (fun bits => test
      (oracleWalkWordEquiv (repetitionCount delta)
        (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits))
  exact hm.trans_eq he.symm


end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedMultiplierUpdate
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selected-root empirical multiplier and counting updates

The observables and empirical counts are those of the actual labelled
chain. The update cancels the preceding multiplier, and the next-parameter
comparison is derived from the literal bounded forest penalty.
-/

namespace ContingencyTables.RootedMultiplierUpdate

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

lemma ratio_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2:ℝ)≤ ratio A R j S ∧ ratio A R j S≤1 := by
  have h := weight_adjacent A R j S
  unfold ratio
  constructor
  · exact (le_div_iff₀ (weight_positive A R j S)).mpr h.1
  · exact (div_le_one (weight_positive A R j S)).mpr h.2

lemma ratio_mean (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ) :
    chainMean pairs w (weight A R j) (plainObservable pairs (ratio A R j))=
      slotTotal pairs (weight A R (j+1)) ∅/chainTotal pairs w (weight A R j) := by
  rw [plainObservable_mean pairs PairedLabels.fresh PairedLabels.cover]
  congr 2
  funext S
  unfold ratio
  exact mul_div_cancel₀ _ (weight_positive A R j S).ne'

/-- The explicit observed-type-count update gives good multipliers for
j+1. Its only statistical hypothesis is relative accuracy of the actual
finite observations at phase j. -/
theorem successful_phase_learns (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0< w p r) (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4)
    (l : List (Set (Labels A×Bool)))
    (hacc : AccuratePhase pairs w (weight A R j) (ratio A R j) eta l) :
    GoodMultipliers pairs (weight A R (j+1)) (learnedMultipliers pairs w l) := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover w
    (weight A R j) (weight_positive A R j) hw
  have hp0 : 0< chainMean pairs w (weight A R j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos (slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh) hZ
  have hplain := accurate_plain pairs w (weight A R j) (ratio A R j) eta l hacc
  have hp0h := AnnealingMultipliers.empirical_positive hp0 he hplain.1
  have hpt (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs)
      (hpr : p≠r) : 0< chainMean pairs w (weight A R j) (defectIndicator pairs p r) := by
    rw [defectIndicator_mean pairs PairedLabels.fresh PairedLabels.cover _ _ p r hp hr hpr]
    exact div_pos (mul_pos (hw p r)
      (slotDefect_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh p r hp hr hpr)) hZ
  have hpth (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs)
      (hpr : p≠r) : 0< empirical (defectIndicator pairs p r) l :=
    AnnealingMultipliers.empirical_positive (hpt p r hp hr hpr) he
      (accurate_defect pairs w (weight A R j) (ratio A R j) eta l hacc p r hp hr hpr).1
  have hb (p r : (Labels A×Bool)×(Labels A×Bool)) (hp : p∈pairs) (hr : r∈pairs)
      (hpr : p≠r) :
      (slotTotal pairs (weight A R (j+1)) ∅/slotDefect pairs (weight A R (j+1)) ∅ p r)/4≤
          learnedMultipliers pairs w l p r ∧
        learnedMultipliers pairs w l p r≤
          4*(slotTotal pairs (weight A R (j+1)) ∅/slotDefect pairs (weight A R (j+1)) ∅ p r) := by
    rw [learnedMultipliers,ite_eq_left ⟨hp,hr,hpr⟩]
    have hu := AnnealingMultipliers.update_good hp0 (hpt p r hp hr hpr) (hw p r)
      he0 he hplain (accurate_defect pairs w (weight A R j) (ratio A R j) eta l hacc p r hp hr hpr)
      (by simpa only [mul_div_assoc] using (weight_mean_identity pairs PairedLabels.fresh
        PairedLabels.cover (weight A R j) (weight_positive A R j) w hw p r hp hr hpr))
      (ideal_adjacent A R j p r hp hr hpr)
    simpa only [mul_div_assoc] using hu
  refine ⟨?_,?_,?_⟩
  · intro p r
    unfold learnedMultipliers
    split_ifs with ht
    · exact mul_pos (hw p r) (div_pos hp0h (hpth p r ht.1 ht.2.1 ht.2.2))
    · exact hw p r
  · intro p hp r hr hpr
    simpa only [div_div,mul_comm] using (hb p r hp hr hpr).1
  · intro p hp r hr hpr
    simpa only [mul_div_assoc] using (hb p r hp hr hpr).2

/-- Relative accuracy of the actual counting and plain observations
bounds one logarithmic counting-ratio error by 4 eta. -/
theorem successful_phase_ratio_log (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0< w p r) (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4)
    (l : List (Set (Labels A×Bool)))
    (hacc : AccuratePhase pairs w (weight A R j) (ratio A R j) eta l) :
    |Real.log (empiricalRatio pairs (ratio A R j) l/
      (slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅))|≤4*eta := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover w
    (weight A R j) (weight_positive A R j) hw
  have hC := slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh
  have hC' := slotTotal_pos pairs _ (weight_positive A R (j+1)) ∅ PairedLabels.fresh
  have hp : 0< chainMean pairs w (weight A R j) (plainObservable pairs (ratio A R j)) := by
    rw [ratio_mean]
    exact div_pos hC' hZ
  have hq : 0< chainMean pairs w (weight A R j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos hC hZ
  have hph := relative_error_bounds _ _ _ (hacc (.inr ()))
  simp only [phaseObservable] at hph
  have hqh := accurate_plain pairs w (weight A R j) (ratio A R j) eta l hacc
  have h := (AnnealingMultipliers.relative_ratio hp hq he0 he hph hqh).2.2.2
  rw [ratio_mean,plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover] at h
  unfold empiricalRatio
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp [hZ.ne',hC.ne',hC'.ne']

end ContingencyTables.RootedMultiplierUpdate

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWeightOracle
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.RootedWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open CompanionWeightOracle
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem weight_source (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (j : ℕ)
    (S : Set (Labels A×Bool)) :
    RootedAnnealing.weight A R j S=
      RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (profile A S)*(factorialRatio A S:ℝ) := by
  rw [factorialRatio_cast]
  have he : (j:ℝ)*(C:ℝ)/height A C=(j:ℝ)/CompanionAnnealing.scale A := by
    simpa only [height,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using
      CompanionAnnealing.source_parameter A C j hC
  rw [he]
  simp only [RootedAnnealing.weight,RootedFactorialApplication.f,firstLift,profile,mul_div_assoc]

/-- Every query at the actual labelled state uses a fresh bounded word.
Only PL and finite Cheeger remain in the evaluation guarantee. -/
theorem evaluate_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (j : ℕ) (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    1-(xi:ℝ) ≤ uniformAverage (fun bits : WeightWord A C K j xi =>
      if accurateCall A R C K j hK hW xi v S bits then (1:ℝ) else 0) := by
  unfold accurateCall
  have hs := RootedOracleDensity.medianEstimate_success A R C hC (profile A S) (profile_inBox A S)
    K hK hW hB j hj xi xi hx0 hx1 hx0 hPL hCheeger v
  apply hs.trans
  apply uniformAverage_mono
  intro bits
  by_cases hg : (1-(xi:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (profile A S) ≤
      (RootedOracleDensity.medianEstimate A R C (profile A S) K hK hW j xi xi v bits:ℝ) ∧
    (RootedOracleDensity.medianEstimate A R C (profile A S) K hK hW j xi xi v bits:ℝ) ≤
      (1+(xi:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (profile A S)
  · have hf : (0:ℝ) ≤ factorialRatio A S := by exact_mod_cast (factorialRatio_positive A S).le
    have hlo := mul_le_mul_of_nonneg_right hg.1 hf
    have hhi := mul_le_mul_of_nonneg_right hg.2 hf
    have ho : (1-(xi:ℝ))*RootedAnnealing.weight A R j S ≤ (evaluate A R C K hK hW j xi v S bits:ℝ) ∧
        (evaluate A R C K hK hW j xi v S bits:ℝ) ≤ (1+(xi:ℝ))*RootedAnnealing.weight A R j S := by
      rw [weight_source A R C hC j S]
      simpa only [evaluate,Rat.cast_mul,mul_assoc] using And.intro hlo hhi
    simp only [hg,ho,le_refl]
  · simp only [hg,ite_false]
    split_ifs <;> norm_num

end

end ContingencyTables.RootedWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseWords
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh selected-root oracle words and actual rational phase updates -/

namespace ContingencyTables.RootedPhaseWords

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS GridBoundary FirstSuccess FairBits TwoLiftStates
open CompanionPhaseWords (phaseBits phaseWordEquiv Stored)
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma update_multiplier_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (old next : Stored A)
    (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hu : update A R C K j N hK hW xi v old states bits=some next) (p q : Pair A) :
    (next.multiplier p q:ℝ)=
      learnedMultipliers pairs (fun p q => (old.multiplier p q:ℝ)) (List.ofFn states) p q := by
  unfold update at hu
  split_ifs at hu
  · cases Option.some.inj hu
    exact rationalLearn_cast _ _ _ _ _

end
end ContingencyTables.RootedPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseOracleError
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Error of actual selected-root calls in a rational phase update -/

namespace ContingencyTables.RootedPhaseWords

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open CompanionPhaseWords (phaseBits phaseWordEquiv average_ext_instances failure_of_success
  independent_pair_failure independent_reindex_failure)
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma accurateCall_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi =>
      if ¬accurateCall A R C K j hK hW xi v S bits then (1:ℝ) else 0) ≤ (xi:ℝ) := by
  have hs := evaluate_success A R C hC K hK hW hB j hj xi hx0 hx1 hPL hCheeger v S
  exact @failure_of_success (WeightWord A C K j xi) inferInstance inferInstance
    (accurateCall A R C K j hK hW xi v S) (xi:ℝ) hs

lemma pairedCalls_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi =>
      if ¬(accurateCall A R C K j hK hW xi v S bits.1 ∧
        accurateCall A R C K (j+1) hK hW xi v S bits.2) then (1:ℝ) else 0) ≤ (xi:ℝ)+(xi:ℝ) := by
  have hS := accurateCall_failure A R C hC K j hK hW hB (by omega) xi hx0 hx1 hPL hCheeger v S
  have hT := accurateCall_failure A R C hC K (j+1) hK hW hB hj xi hx0 hx1 hPL hCheeger v S
  exact @independent_pair_failure (WeightWord A C K j xi) (WeightWord A C K (j+1) xi)
    inferInstance inferInstance inferInstance inferInstance
    (accurateCall A R C K j hK hW xi v S) (accurateCall A R C K (j+1) hK hW xi v S)
    (xi:ℝ) (xi:ℝ) hS hT

/-- The calls use independent actual finite words even for a fixed,
arbitrary sequence of observed states. No sampling assumption on that
sequence is required for this oracle-error estimate. -/
theorem accurateCalls_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool)) :
    uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
      if ¬accurateCalls A R C K j N hK hW xi v states bits then (1:ℝ) else 0) ≤
        2*(N:ℝ)*(xi:ℝ) := by
  let X := WeightWord A C K j xi × WeightWord A C K (j+1) xi
  let Y := Fin (phaseBits A C K j N xi) → Bool
  let good (i : Fin N) (b : X) :=
    accurateCall A R C K j hK hW xi v (states i) b.1 ∧
      accurateCall A R C K (j+1) hK hW xi v (states i) b.2
  have hbad (i : Fin N) : uniformAverage (fun b : X => if ¬good i b then (1:ℝ) else 0) ≤
      (xi:ℝ)+(xi:ℝ) := by
    exact pairedCalls_failure A R C hC K j hK hW hB hj xi hx0 hx1 hPL hCheeger v (states i)
  have he := @independent_reindex_failure X Y inferInstance inferInstance inferInstance N
      (phaseWordEquiv A C K j N xi) good
  have hfun : (fun bits : Y =>
      if ¬accurateCalls A R C K j N hK hW xi v states bits then (1:ℝ) else 0)=
      (fun bits : Y => if ¬(∀ i,good i (phaseWordEquiv A C K j N xi bits i)) then (1:ℝ) else 0) := by
    funext bits
    have hi : accurateCalls A R C K j N hK hW xi v states bits ↔
        ∀ i,good i (phaseWordEquiv A C K j N xi bits i) := Iff.rfl
    by_cases h : ∀ i,good i (phaseWordEquiv A C K j N xi bits i)
    · simp [hi,h]
    · simp [hi,h]
  rw [hfun]
  calc
    _ ≤ ∑ i : Fin N,uniformAverage (fun b : X => if ¬good i b then (1:ℝ) else 0) :=
      by
        convert he using 1
        · apply average_ext_instances
          intro bits
          by_cases hh : ∀ i,good i (phaseWordEquiv A C K j N xi bits i) <;> simp [hh]
        · apply Finset.sum_congr rfl
          intro i _
          apply average_ext_instances
          intro b
          by_cases hh : good i b <;> simp [hh]
    _ ≤ ∑ _ : Fin N,((xi:ℝ)+(xi:ℝ)) := Finset.sum_le_sum (fun i _ => hbad i)
    _ = 2*(N:ℝ)*(xi:ℝ) := by simp; ring

private lemma indicator_list_sum_real {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℝ) else 0)).sum=(l.countP (fun x => decide (P x)):ℝ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]

lemma exactObservedRatio_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) :
    exactObservedRatio A R j N states=
      empiricalRatio pairs (RootedMultiplierUpdate.ratio A R j) (List.ofFn states) := by
  by_cases hN : N=0
  · subst N
    simp [exactObservedRatio,empiricalRatio,empirical,plainCount]
  · have hNR : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN
    unfold exactObservedRatio empiricalRatio empirical
    unfold plainObservable
    rw [indicator_list_sum_real]
    simp only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,plainCount]
    exact (div_div_div_cancel_right₀ hNR _ _).symm

private lemma ratio_exponential_bounds {u v uh vh e : ℝ}
    (hu : 0 < u) (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1/4)
    (huh : (1-e)*u ≤ uh ∧ uh ≤ (1+e)*u)
    (hvh : (1-e)*v ≤ vh ∧ vh ≤ (1+e)*v) :
    Real.exp (-4*e)*(v/u) ≤ vh/uh ∧ vh/uh ≤ Real.exp (4*e)*(v/u) := by
  have huh0 := AnnealingMultipliers.empirical_positive hu he1 huh.1
  have hr := AnnealingMultipliers.relative_ratio hv hu he0 he1 hvh huh
  have hid : vh*u/(uh*v)=(vh/uh)/(v/u) := by
    field_simp [hu.ne',hv.ne',huh0.ne']
  rw [hid] at hr
  have hlo : Real.exp (-4*e) ≤ (vh/uh)/(v/u) := by
    calc
      _ ≤ Real.exp (Real.log ((vh/uh)/(v/u))) :=
        Real.exp_le_exp.mpr (by linarith [(abs_le.mp hr.2.2.2).1])
      _ = _ := Real.exp_log hr.1
  have hhi : (vh/uh)/(v/u) ≤ Real.exp (4*e) := by
    calc
      _ = Real.exp (Real.log ((vh/uh)/(v/u))) := (Real.exp_log hr.1).symm
      _ ≤ _ := Real.exp_le_exp.mpr (abs_le.mp hr.2.2.2).2
  exact ⟨(le_div_iff₀ (div_pos hv hu)).mp hlo,(div_le_iff₀ (div_pos hv hu)).mp hhi⟩

lemma observedTerm_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi)
    (hcall : accurateCall A R C K j hK hW xi v S bits.1 ∧
      accurateCall A R C K (j+1) hK hW xi v S bits.2) :
    Real.exp (-4*(xi:ℝ))*plainObservable pairs (RootedMultiplierUpdate.ratio A R j) S ≤
      (observedTerm A R C K j hK hW xi v S bits:ℝ) ∧
      (observedTerm A R C K j hK hW xi v S bits:ℝ) ≤
        Real.exp (4*(xi:ℝ))*plainObservable pairs (RootedMultiplierUpdate.ratio A R j) S := by
  by_cases hp : PlainState pairs S
  · simp only [observedTerm,plainObservable,hp,ite_true, if_true,Rat.cast_div,
      RootedMultiplierUpdate.ratio]
    exact ratio_exponential_bounds (RootedAnnealing.weight_positive A R j S)
      (RootedAnnealing.weight_positive A R (j+1) S) (by exact_mod_cast hx0)
      (by
        have h4 : (4:ℝ)*(xi:ℝ) ≤ 1 := by
          exact_mod_cast (show (4:ℚ)*xi ≤ 1 by linarith)
        linarith) hcall.1 hcall.2
  · simp only [observedTerm,plainObservable,hp,ite_false,Rat.cast_zero,mul_zero,le_refl,and_self]

lemma exactObservedRatio_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) (hc : 0 < plainCount A (List.ofFn states)) :
    0 < exactObservedRatio A R j N states := by
  obtain ⟨S,hS,hplain⟩ := List.countP_pos_iff.mp hc
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hS
  have hpi : PlainState pairs (states i) := by
    rw [hi]
    exact of_decide_eq_true hplain
  have hterm : 0 < plainObservable pairs (RootedMultiplierUpdate.ratio A R j) (states i) := by
    rw [plainObservable,ite_eq_left hpi]
    exact lt_of_lt_of_le (by norm_num) (RootedMultiplierUpdate.ratio_bounds A R j (states i)).1
  unfold exactObservedRatio
  apply div_pos _ (by exact_mod_cast hc)
  apply hterm.trans_le
  apply Finset.single_le_sum _ (Finset.mem_univ i)
  intro k _
  by_cases hk : PlainState pairs (states k)
  · rw [plainObservable,ite_eq_left hk]
    exact le_trans (by norm_num) (RootedMultiplierUpdate.ratio_bounds A R j (states k)).1
  · simp only [plainObservable,hk,ite_false,le_refl]

/-- Relative errors of all fresh calls remain bounded after averaging
the state ratios. The number of observations does not enlarge this
deterministic multiplicative error. -/
theorem observedRatio_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hg : accurateCalls A R C K j N hK hW xi v states bits) :
    Real.exp (-4*(xi:ℝ))*exactObservedRatio A R j N states ≤
      (observedRatio A R C K j N hK hW xi v states bits:ℝ) ∧
      (observedRatio A R C K j N hK hW xi v states bits:ℝ) ≤
        Real.exp (4*(xi:ℝ))*exactObservedRatio A R j N states := by
  have hb (i : Fin N) := observedTerm_bounds A R C K j hK hW xi hx0 hx1 v (states i)
    (phaseWordEquiv A C K j N xi bits i) (hg i)
  simp only [observedRatio,exactObservedRatio,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
  constructor
  · rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hb i).1)
  · rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hb i).2)

theorem observedRatio_log_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (hc : 0 < plainCount A (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hg : accurateCalls A R C K j N hK hW xi v states bits) :
    |Real.log ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/
      exactObservedRatio A R j N states)| ≤ 4*(xi:ℝ) := by
  have he := exactObservedRatio_positive A R j N states hc
  have hb := observedRatio_bounds A R C K j N hK hW xi hx0 hx1 v states bits hg
  have ho := lt_of_lt_of_le (mul_pos (Real.exp_pos _) he) hb.1
  have hl := (le_div_iff₀ he).mpr hb.1
  have hu := (div_le_iff₀ he).mpr hb.2
  have hlogl := Real.log_le_log (Real.exp_pos _) hl
  have hlogu := Real.log_le_log (div_pos ho he) hu
  rw [Real.log_exp] at hlogl hlogu
  exact abs_le.mpr ⟨by linarith, hlogu⟩

end
end ContingencyTables.RootedPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseAccuracy
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root guarded rational phase update and logarithmic error -/

namespace ContingencyTables.RootedPhaseAccuracy

open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open RootedMultiplierUpdate CompanionRationalUpdates RootedPhaseWords
open CompanionPhaseWords (phaseBits Stored)
open TwoLiftStates GridBoundary CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

private lemma indicator_sum {X : Type*} (P : X → Prop) (xs : List X) :
    (xs.map (fun x => if P x then (1:ℝ) else 0)).sum=
      (xs.countP (fun x => decide (P x)):ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases h : P x <;> simp [h,ih,add_comm]

private lemma count_positive_of_empirical {X : Type*} (P : Set X → Prop)
    (xs : List (Set X))
    (h : 0<empirical (fun S => if P S then (1:ℝ) else 0) xs) :
    0<xs.countP (fun S => decide (P S)) := by
  by_contra hn
  have hz := Nat.eq_zero_of_not_pos hn
  simp only [empirical,indicator_sum,hz,Nat.cast_zero,zero_div] at h
  exact (lt_irrefl (0:ℝ)) h

variable {I J : Type} [Fintype I] [Fintype J]

theorem accurate_counts_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (w : Pair A → Pair A → ℝ) (hw : ∀ p q,0<w p q)
    (eta : ℝ) (heta : eta≤1/4) (xs : List (Set (Labels A×Bool)))
    (hacc : AccuratePhase pairs w (weight A R j) (ratio A R j) eta xs) :
    CountsPositive A xs := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover w
    (weight A R j) (weight_positive A R j) hw
  have hplain : 0 < chainMean pairs w (weight A R j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos (slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh) hZ
  have hpemp := AnnealingMultipliers.empirical_positive hplain heta
    (accurate_plain pairs w (weight A R j) (ratio A R j) eta xs hacc).1
  constructor
  · exact count_positive_of_empirical (PlainState pairs) xs hpemp
  · intro p hp q hq hpq
    have hdef : 0 < chainMean pairs w (weight A R j) (defectIndicator pairs p q) := by
      rw [defectIndicator_mean pairs PairedLabels.fresh PairedLabels.cover _ _ p q hp hq hpq]
      exact div_pos (mul_pos (hw p q)
        (slotDefect_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh p q hp hq hpq)) hZ
    have hdemp := AnnealingMultipliers.empirical_positive hdef heta
      (accurate_defect pairs w (weight A R j) (ratio A R j) eta xs hacc p q hp hq hpq).1
    exact count_positive_of_empirical (DefectState pairs p q) xs hdemp

theorem observed_ratio_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ) (hx0 : 0≤xi) (hx1 : xi≤1/4)
    (v : Grid (I := Fin (dimension A)) K)
    (w : Pair A → Pair A → ℝ) (hw : ∀ p q,0<w p q)
    (eta : ℝ) (he0 : 0≤eta) (he1 : eta≤1/4)
    (states : Fin N → Set (Labels A×Bool))
    (hacc : AccuratePhase pairs w (weight A R j) (ratio A R j) eta (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hcalls : accurateCalls A R C K j N hK hW xi v states bits) :
    0<(observedRatio A R C K j N hK hW xi v states bits:ℝ) ∧
      |Real.log ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/
        (slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅))|≤
          4*(xi:ℝ)+4*eta := by
  have hcount := (accurate_counts_positive A R j w hw eta he1 (List.ofFn states) hacc).1
  have he := exactObservedRatio_positive A R j N states hcount
  have hb := observedRatio_bounds A R C K j N hK hW xi hx0 hx1 v states bits hcalls
  have ho : 0<(observedRatio A R C K j N hK hW xi v states bits:ℝ) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) he) hb.1
  have horacle := observedRatio_log_error A R C K j N hK hW xi hx0 hx1 v states hcount bits hcalls
  have hsample := RootedMultiplierUpdate.successful_phase_ratio_log
    A R j w hw eta he0 he1 (List.ofFn states) hacc
  rw [←exactObservedRatio_eq A R j N states] at hsample
  let ratioTotal := slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅
  have hR : 0 < ratioTotal := div_pos
    (slotTotal_pos pairs _ (weight_positive A R (j+1)) ∅ PairedLabels.fresh)
    (slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh)
  have hm : (observedRatio A R C K j N hK hW xi v states bits:ℝ)/ratioTotal=
      ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/exactObservedRatio A R j N states)*
        (exactObservedRatio A R j N states/ratioTotal) := by
    field_simp [he.ne',hR.ne']
  refine ⟨ho,?_⟩
  change |Real.log ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/ratioTotal)|≤_
  rw [hm,Real.log_mul (div_ne_zero ho.ne' he.ne') (div_ne_zero he.ne' hR.ne')]
  exact (abs_add_le _ _).trans (_root_.add_le_add horacle hsample)

/-- The actual guarded rational update succeeds on the proved accuracy
events; its stored multipliers are good for the next literal weight. -/
theorem update_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ) (hx0 : 0≤xi) (hx1 : xi≤1/4)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A)
    (hw : ∀ p q,0<old.multiplier p q) (hE : 0<old.estimate)
    (eta : ℝ) (he0 : 0≤eta) (he1 : eta≤1/4)
    (states : Fin N → Set (Labels A×Bool))
    (hacc : AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ))
      (weight A R j) (ratio A R j) eta (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hcalls : accurateCalls A R C K j N hK hW xi v states bits) :
    ∃ next,update A R C K j N hK hW xi v old states bits=some next ∧
      (∀ p q,0<next.multiplier p q) ∧ 0<next.estimate ∧
      GoodMultipliers pairs (weight A R (j+1)) (fun p q => (next.multiplier p q:ℝ)) ∧
      |Real.log ((next.estimate:ℝ)/((old.estimate:ℝ)*
        (slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅)))|≤
          4*(xi:ℝ)+4*eta := by
  have hwr : ∀ p q,0<(old.multiplier p q:ℝ) := fun p q => by exact_mod_cast hw p q
  have hc := accurate_counts_positive A R j _ hwr eta he1 (List.ofFn states) hacc
  let next : Stored A := ⟨rationalLearn pairs old.multiplier (List.ofFn states),
    old.estimate*observedRatio A R C K j N hK hW xi v states bits⟩
  have hu : update A R C K j N hK hW xi v old states bits=some next := by
    simp only [update,hc,ite_true, if_true,next]
  have hnpos : ∀ p q,0<next.multiplier p q := by
    apply checkedUpdate_positive A old.multiplier hw (List.ofFn states)
    simp only [checkedUpdate,hc,ite_true, if_true,next]
  have hobs := observed_ratio_error A R C K j N hK hW xi hx0 hx1 v _ hwr eta he0 he1
    states hacc bits hcalls
  have ho : 0<observedRatio A R C K j N hK hW xi v states bits := by exact_mod_cast hobs.1
  have hgood := RootedMultiplierUpdate.successful_phase_learns A R j _ hwr eta he0 he1
    (List.ofFn states) hacc
  have hcast : (fun p q => (next.multiplier p q:ℝ))=
      learnedMultipliers pairs (fun p q => (old.multiplier p q:ℝ)) (List.ofFn states) := by
    funext p q
    exact update_multiplier_cast A R C K j N hK hW xi v old next states bits hu p q
  refine ⟨next,hu,hnpos,mul_pos hE ho,?_,?_⟩
  · rw [hcast]
    exact hgood
  · have hER : (old.estimate:ℝ)≠0 := by exact_mod_cast hE.ne'
    change |Real.log (((old.estimate*observedRatio A R C K j N hK hW xi v states bits:ℚ):ℝ)/_)|≤_
    rw [Rat.cast_mul,mul_div_mul_left _ _ hER]
    exact hobs.2

end
end ContingencyTables.RootedPhaseAccuracy

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseTrial
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete finite-word selected-root phase trial

The trajectory and its weight queries use disjoint words. The output is
the actual guarded rational multiplier and count update.
-/

namespace ContingencyTables.RootedPhaseTrial

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedAnnealing RootedMultiplierUpdate
open RootedPhaseExperiment RootedPhaseWords RootedPhaseAccuracy RootedObservationStart
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseWords (Stored phaseBits)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
private lemma paired_average_bound {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X × Y → ℝ) (g : X → ℝ) (q : X → Y → ℝ)
    (e : ℝ) (hpoint : ∀ z,f z ≤ g z.1+q z.1 z.2)
    (hq : ∀ x,uniformAverage (q x) ≤ e) :
    uniformAverage f ≤ uniformAverage g+e := by
  have hmean := uniformAverage_mono (fun x => uniformAverage (q x)) (fun _ : X => e) hq
  rw [uniformAverage_const] at hmean
  calc
    uniformAverage f ≤ uniformAverage (fun z : X × Y => g z.1+q z.1 z.2) :=
      uniformAverage_mono _ _ hpoint
    _ = uniformAverage g+uniformAverage (fun x => uniformAverage (q x)) := by
      rw [uniformAverage_prod]
      simp only [uniformAverage_add,uniformAverage_const]
    _ ≤ uniformAverage g+e := _root_.add_le_add (le_refl (uniformAverage g)) hmean

variable {I J : Type} [Fintype I] [Fintype J]

theorem trial_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A)
    (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (S : State A) (bits : TrialWords A C K j k N xi) (eta : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1/4)
    (hacc : AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j) (ratio A R j)
      eta (List.ofFn (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1)))
    (hcalls : accurateCalls A R C K j (N+1) hK hW xi v
      (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1) bits.2) :
    ∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
      ValidOutput A R j old xi eta next := by
  exact update_success A R C K j (N+1) hK hW xi hx0 hx1 v old hw hE eta he0 he1
    (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1) hacc bits.2 hcalls

private theorem calls_failure_indicator (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool)) :
    uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
      eventIndicator (¬accurateCalls A R C K j N hK hW xi v states bits)) ≤
        2*(N:ℝ)*(xi:ℝ) := by
  have ht := accurateCalls_failure A R C hC K j N hK hW hB hj xi hx0 hx1 hPL hCheeger v states
  have he : uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
      eventIndicator (¬accurateCalls A R C K j N hK hW xi v states bits))=
      uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
        if ¬accurateCalls A R C K j N hK hW xi v states bits then (1:ℝ) else 0) := by
    apply CompanionPhaseWords.average_ext_instances
    intro bits
    exact CompanionTraceWords.eventIndicator_eq _
  exact he.trans_le ht

/-- Actual guarded output failure is bounded by trajectory concentration,
the proved weight-call error, and the distance of its incoming law from
the exact warm reference. -/
theorem trial_failure (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (old : Stored A) (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (old.multiplier p q:ℝ)))
    (p q : State A → ℝ) (hp0 : ∀ S,0 ≤ p S) (hp1 : ∑ S,p S=1)
    (hq : ∀ S,0 ≤ q S) (hq1 : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j))
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    (∑ S,p S*uniformAverage (fun bits : TrialWords A C K j k N xi =>
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
        ValidOutput A R j old xi eta next))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+2*RealKernelApproximation.distance p q+
          2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
  let states (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :=
    observedStates A R C K j k N hK hW xi v old.multiplier S bits
  let badObservation (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :=
    ¬AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j) (ratio A R j)
      eta (List.ofFn (states S bits))
  have hpoint (S : State A) (bits : TrialWords A C K j k N xi) :
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
        ValidOutput A R j old xi eta next) ≤
      eventIndicator (badObservation S bits.1)+
        eventIndicator (¬accurateCalls A R C K j (N+1) hK hW xi v (states S bits.1) bits.2) := by
    by_cases ha : badObservation S bits.1
    · unfold eventIndicator
      split_ifs <;> norm_num
    · have ha' : AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j)
          (ratio A R j) eta (List.ofFn (states S bits.1)) := not_not.mp ha
      by_cases hc : accurateCalls A R C K j (N+1) hK hW xi v (states S bits.1) bits.2
      · have hs := trial_success A R C K j k N hK hW xi hx0.le hx1 v old hw hE S bits
          eta he0.le he1 ha' hc
        simp only [eventIndicator,ha,hc,hs,not_true_eq_false,ite_false,zero_add]
        exact le_rfl
      · unfold eventIndicator
        split_ifs <;> norm_num
  have hlocal (S : State A) :
      uniformAverage (fun bits : TrialWords A C K j k N xi =>
        eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
          ValidOutput A R j old xi eta next)) ≤
      uniformAverage (fun bits => eventIndicator (badObservation S bits))+
        2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
    have hc (bits : Fin (N*stepBits A C K j k xi) → Bool) :
        uniformAverage (fun fresh : Fin (phaseBits A C K j (N+1) xi) → Bool =>
          eventIndicator (¬accurateCalls A R C K j (N+1) hK hW xi v (states S bits) fresh)) ≤
            2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
      exact calls_failure_indicator A R C hC K j (N+1) hK hW hB hj xi hx0
        (lt_of_le_of_lt hx1 (by norm_num)) hPL hCheeger v (states S bits)
    exact paired_average_bound _ _ _ _ (hpoint S) hc
  have hsum := Finset.sum_le_sum (fun S (_ : S∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hlocal S) (hp0 S))
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,hp1,one_mul] at hsum
  have hobs := observed_failure_near A R C hC K j k N hK hW hB (by omega) xi hx0 hx1
    hPL hCheeger v hp old.multiplier hw hgood p q hq hq1 hwarm eta he0
  dsimp only [badObservation,states] at hsum
  have hb := _root_.add_le_add hobs (le_refl (2*((N+1:ℕ):ℝ)*(xi:ℝ)))
  exact hsum.trans hb

end
end ContingencyTables.RootedPhaseTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPlainTrial
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A selected-root phase begun from its actual transversal law -/

namespace ContingencyTables.RootedPlainTrial

open CommonBasesFPRAS FirstSuccess ResidualMixture RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open RootedAnnealing RootedWarmStart RootedPhaseTrial
open CompanionPhaseWords (Stored)
open CompanionConcentration (pairs_ne_nil)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma lift_warm (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0 < Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (q : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hq : ∀ S,q S ≤ 2*law A R j S.val.val)
    (S : ChainIndex (pairs : List (Pair A))) :
    plainLift pairs q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j) := by
  have hpos : ∀ p q,0 < (w p q:ℝ) := fun p q => by exact_mod_cast hw p q
  have htrace (T : PlainIndex (pairs : List (Pair A))) :
      q T ≤ 2*(metropolisTrace pairs PairedLabels.fresh (pairs_ne_nil A hp)
        PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j) hpos
        (weight_positive A R j)).π T := by
    rw [metropolisTrace_pi]
    exact hq T
  have h := plainLift_warm pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (weight_positive A R j) hgood q htrace S
  simpa only [PairedLabels.length] using h

/-- The incoming law is the actual rational output law on transversals;
only the comparison reference is warm. -/
theorem trial_failure_oai (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (old : Stored A) (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (old.multiplier p q:ℝ)))
    (p : RationalLaw (PlainIndex (pairs : List (Pair A))))
    (q : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hq : ∀ S,0 ≤ q S) (hq1 : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ 2*law A R j S.val.val)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    (∑ S,(p.mass S:ℝ)*uniformAverage (fun bits : TrialWords A C K j k N xi =>
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S.val bits=some next ∧
        ValidOutput A R j old xi eta next))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+
          2*distance (fun S => (p.mass S:ℝ)) q+2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
  have hp0 (S : PlainIndex (pairs : List (Pair A))) : 0 ≤ (p.mass S:ℝ) := by
    exact_mod_cast p.nonnegative S
  have hp1 : (∑ S,(p.mass S:ℝ))=1 := by exact_mod_cast p.total
  have hfull := RootedPhaseTrial.trial_failure A R C hC K j k N hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp old hw hE hgood
    (plainLift pairs (fun S => (p.mass S:ℝ))) (plainLift pairs q)
    (plainLift_nonneg pairs _ hp0)
    (by rw [plainLift_mass]; exact hp1)
    (plainLift_nonneg pairs _ hq)
    (by rw [plainLift_mass]; exact hq1)
    (lift_warm A R j hp old.multiplier hw hgood q hwarm) eta he0 he1
  rw [FinitePlainLift.sum_mul,FinitePlainLift.distance_lift] at hfull
  exact hfull

end
end ContingencyTables.RootedPlainTrial

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.RootedPlainTrial.trial_failure_oai := @OAI.ContingencyTables.RootedPlainTrial.trial_failure_oai
