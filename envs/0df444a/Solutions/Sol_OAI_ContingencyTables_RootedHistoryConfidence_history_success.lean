-- Prove2me | solution 1 for OAI.ContingencyTables.RootedHistoryConfidence.history_success
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:32:45.640479+00:00
-- url     : https://prove2.me/submissions/bc3df7aa-a6a1-4335-a1d3-1f1b34ab8e5a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_RootedPlainTrial_trial_failure
import Theorems.Thm_OAI_ContingencyTables_RootedTargetMixing_targetTrace_poincare
import Theorems.Thm_OAI_ContingencyTables_RootedTraceWords_arithmetic_recorded_event_bound

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

omit sectionInstance13 in
lemma ncard_insert_eq [DecidableEq ι] (A : Set ι) (i : ι) (hi : i ∉ A) :
    (insert i A).ncard = A.ncard + 1 := Set.ncard_insert_of_notMem hi

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

namespace FiniteChain
variable {X : Type*} [sectionInstance56 : Fintype X] (C : FiniteChain X)

lemma pathExpectation_add (N : ℕ) (x : X) (F G : List X → ℝ) :
    C.pathExpectation N x (fun l => F l+G l) = C.pathExpectation N x F+C.pathExpectation N x G := by
  induction N generalizing x F G with
  | zero => rfl
  | succ N ih => simp [pathExpectation,ih,mul_add,Finset.sum_add_distrib]
lemma pathExpectation_mul (N : ℕ) (x : X) (a : ℝ) (F : List X → ℝ) :
    C.pathExpectation N x (fun l => a*F l) = a*C.pathExpectation N x F := by
  induction N generalizing x F with
  | zero => rfl
  | succ N ih => simp [pathExpectation,ih,Finset.mul_sum,mul_left_comm]
lemma pathExpectation_const (N : ℕ) (x : X) (a : ℝ) : C.pathExpectation N x (fun _ => a) = a := by
  induction N generalizing x with
  | zero => rfl
  | succ N ih => simp [pathExpectation,ih,← Finset.sum_mul,C.stochastic]
lemma pathExpectation_congr (N : ℕ) (x : X) (F G : List X → ℝ) (hFG : ∀ l,F l=G l) :
    C.pathExpectation N x F = C.pathExpectation N x G := by
  congr 1
  funext l
  exact hFG l

end FiniteChain

namespace KilledKernel
open scoped BigOperators Classical
open Filter
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
lemma apply_mul (a : ℝ) (f : B → ℝ) : Q.apply (fun x => a*f x) = fun x => a*Q.apply f x := by
  funext x
  simp only [apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring
lemma iterate_mul (a : ℝ) (f : B → ℝ) (k : ℕ) :
    Q.iterate k (fun x => a*f x) = fun x => a*Q.iterate k f x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Q.iterate_succ,ih,Q.apply_mul,← Q.iterate_succ]

end KilledKernel
namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
variable (Q : KilledKernel (Outside A)) (hQ : ∀ x y : Outside A,Q.Q x y = C.P x.val y.val)

lemma mean_residual (f : X → ℝ) : C.mean (fun x => f x-C.apply f x) = 0 := by
  unfold mean
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  change C.mean f-C.mean (C.apply f) = 0
  rw [C.mean_apply,sub_self]

lemma duration_nonneg (x : Outside A) : 0 ≤ duration A Q x :=
  Q.green_nonneg _ (by intro; norm_num) x
lemma returnCost_nonneg (x : Inside A) : 0 ≤ C.returnCost A Q x :=
  add_nonneg (by norm_num) (Finset.sum_nonneg (fun y _ =>
    mul_nonneg (C.nonnegative _ _) (duration_nonneg A Q y)))

include hQ in
lemma expected_returnCost : (∑ x : Inside A,C.π x.val*C.returnCost A Q x) = 1 := by
  let l : X → ℝ := mergeFun A (fun _ => 0) (duration A Q)
  have hi (x : Inside A) : l x.val = 0 := by simp [l]
  have ho (x : Outside A) : l x.val = duration A Q x := by simp [l]
  have hai (x : Inside A) : C.apply l x.val = ∑ y : Outside A,C.P x.val y.val*duration A Q y := by
    unfold apply
    rw [← Fintype.sum_subtype_add_sum_subtype A]
    simp only [hi,ho,mul_zero,Finset.sum_const_zero,zero_add]
  have hao (x : Outside A) : C.apply l x.val = Q.apply (duration A Q) x := by
    unfold apply
    rw [← Fintype.sum_subtype_add_sum_subtype A]
    simp only [hi,ho,mul_zero,Finset.sum_const_zero,zero_add,KilledKernel.apply,hQ]
  have hr (x : Outside A) : l x.val-C.apply l x.val = 1 := by
    rw [ho,hao]
    have hg := Q.green_firstStep (fun _ => (1:ℝ)) x
    change duration A Q x = 1+Q.apply (duration A Q) x at hg
    linarith
  have hm := C.mean_residual l
  unfold mean at hm
  rw [← Fintype.sum_subtype_add_sum_subtype A] at hm
  simp only [hi,hai,hr,zero_sub,mul_neg,Finset.sum_neg_distrib,mul_one] at hm
  have hmass := Fintype.sum_subtype_add_sum_subtype A C.π
  rw [C.normalized] at hmass
  unfold returnCost
  simp only [mul_add,mul_one,Finset.sum_add_distrib]
  linarith

lemma traceChain_returnCost [Nonempty (Inside A)] :
    (C.traceChain A Q hQ).mean (C.returnCost A Q) = 1/C.insideMass A := by
  change (∑ x : Inside A,(C.π x.val/C.insideMass A)*C.returnCost A Q x) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,C.expected_returnCost A Q hQ]

lemma warm_returnCost [Nonempty (Inside A)] (ν : Inside A → ℝ) (U : ℝ)
    (hν : ∀ x,ν x ≤ U*(C.traceChain A Q hQ).π x) :
    (∑ x,ν x*C.returnCost A Q x) ≤ U/C.insideMass A := by
  calc
    _ ≤ ∑ x,U*(C.traceChain A Q hQ).π x*C.returnCost A Q x :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hν x) (C.returnCost_nonneg A Q x))
    _ = U*(C.traceChain A Q hQ).mean (C.returnCost A Q) := by simp [mean,Finset.mul_sum,mul_assoc]
    _ = _ := by rw [C.traceChain_returnCost A Q hQ]; ring
end
open scoped Classical BigOperators
end FiniteChain
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

namespace KilledKernel
open scoped BigOperators Classical
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
lemma apply_mono {f g : B → ℝ} (h : ∀ x,f x ≤ g x) (x : B) : Q.apply f x ≤ Q.apply g x :=
  Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (h y) (Q.nonnegative x y))
lemma iterate_mono {f g : B → ℝ} (h : ∀ x,f x ≤ g x) (k : ℕ) (x : B) :
    Q.iterate k f x ≤ Q.iterate k g x := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih => rw [Q.iterate_succ,Q.iterate_succ]; exact Q.apply_mono ih x
lemma survival_antitone (x : B) : Antitone (fun k => Q.iterate k (fun _ => 1) x) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [Q.iterate_succ']
  apply Q.iterate_mono
  intro y
  simpa only [apply,mul_one] using (Q.rowbound y).trans Q.rlt.le
lemma duration_tail (N : ℕ) (x : B) :
    (N:ℝ)*Q.iterate N (fun _ => 1) x ≤ Q.green (fun _ => 1) x := by
  calc
    _ = ∑ k ∈ Finset.range N,Q.iterate N (fun _ => 1) x := by simp
    _ ≤ ∑ k ∈ Finset.range N,Q.iterate k (fun _ => 1) x :=
      Finset.sum_le_sum (fun k hk => Q.survival_antitone x (Finset.mem_range.mp hk).le)
    _ ≤ _ := (Q.summable_iterate (fun _ => 1) x).sum_le_tsum (Finset.range N)
      (fun k _ => Q.iterate_nonneg k _ (by intro; norm_num) x)
lemma partialGreen_le (N : ℕ) (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) :
    Q.partialGreen N f x ≤ Q.green f x :=
  (Q.summable_iterate f x).sum_le_tsum (Finset.range N) (fun k _ => Q.iterate_nonneg k f hf x)
lemma partialGreen_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) (N : ℕ) (x : B) :
    Q.partialGreen N (fun y => ∑ j ∈ s,f j y) x = ∑ j ∈ s,Q.partialGreen N (f j) x := by
  unfold partialGreen
  simp_rw [Q.iterate_sum]
  exact Finset.sum_comm
end KilledKernel

namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
  (Q : KilledKernel (Outside A)) (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)

lemma cappedTrace_le (N : ℕ) (x y : Inside A) : C.cappedTrace A Q N x y ≤ C.traceMatrix A Q x y := by
  unfold cappedTrace traceMatrix
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_left (Q.partialGreen_le N _ (fun t => C.nonnegative _ _) z) (C.nonnegative _ _)
include hQ in
lemma cappedTrace_mass (N : ℕ) (x : Inside A) :
    ∑ y,C.cappedTrace A Q N x y = 1-∑ z : Outside A,C.P x.val z.val*Q.iterate N (fun _ => 1) z := by
  unfold cappedTrace
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,← Q.partialGreen_sum]
  have he : (fun t : Outside A => ∑ y : Inside A,C.P t.val y.val) =
      fun t => 1-Q.apply (fun _ => 1) t := by
    funext t
    exact C.exitRow A Q hQ t
  rw [he]
  simp_rw [KilledKernel.partialGreen,Q.iterate_residual_sum,mul_sub,mul_one,Finset.sum_sub_distrib]
  have hs := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
  rw [C.stochastic] at hs
  linarith

include hQ in
lemma cappedTrace_loss (N : ℕ) (x : Inside A) :
    (N:ℝ)*(1-∑ y,C.cappedTrace A Q N x y) ≤ C.returnCost A Q x := by
  rw [C.cappedTrace_mass A Q hQ]
  simp only [sub_sub_cancel]
  calc
    _ = ∑ z : Outside A,C.P x.val z.val*((N:ℝ)*Q.iterate N (fun _ => 1) z) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    _ ≤ ∑ z : Outside A,C.P x.val z.val*duration A Q z :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (Q.duration_tail N z) (C.nonnegative _ _))
    _ ≤ _ := by unfold returnCost; linarith

include hQ in
lemma cappedTrace_substochastic (N : ℕ) (x : Inside A) : ∑ y,C.cappedTrace A Q N x y ≤ 1 := by
  calc
    _ ≤ ∑ y,C.traceMatrix A Q x y := Finset.sum_le_sum (fun y _ => C.cappedTrace_le A Q N x y)
    _ = 1 := C.traceMatrix_stochastic A Q hQ x

lemma cappedTrace_warm_loss [Nonempty (Inside A)] (N : ℕ) (U : ℝ) (ν : Inside A → ℝ)
    (hν : ∀ x,0 ≤ ν x) (hwarm : ∀ x,ν x ≤ U*(C.traceChain A Q hQ).π x) :
    (N:ℝ)*(∑ x,ν x*(1-∑ y,C.cappedTrace A Q N x y)) ≤ U/C.insideMass A := by
  calc
    _ = ∑ x,ν x*((N:ℝ)*(1-∑ y,C.cappedTrace A Q N x y)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ ∑ x,ν x*C.returnCost A Q x := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (C.cappedTrace_loss A Q hQ N x) (hν x))
    _ ≤ _ := C.warm_returnCost A Q hQ ν U hwarm
end FiniteChain

namespace FiniteKernel
open scoped BigOperators Classical
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
lemma push_mono (K : FiniteKernel X Y) {ν ν' : X → ℝ} (h : ∀ x,ν x ≤ ν' x) (y : Y) :
    K.push ν y ≤ K.push ν' y := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (h x) (K.nonnegative x y))
lemma push_comp (K : FiniteKernel X Y) (L : FiniteKernel Y Z) (ν : X → ℝ) :
    (K.comp L).push ν = L.push (K.push ν) := by
  funext z
  simp only [push,comp,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm
lemma push_identity (ν : X → ℝ) : (identity : FiniteKernel X X).push ν = ν := by
  funext x; simp [push,identity]
lemma power_push_succ (K : FiniteKernel X X) (n : ℕ) (ν : X → ℝ) :
    (K.power (n+1)).push ν = K.push ((K.power n).push ν) := (K.power n).push_comp K ν
end FiniteKernel

namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma push_warm (ν : X → ℝ) (U : ℝ) (hν : ∀ x,ν x ≤ U*C.π x) (y : X) :
    C.kernel.push ν y ≤ U*C.π y := by
  calc
    _ ≤ ∑ x,U*C.π x*C.P x y := C.kernel.push_mono hν y
    _ = U*C.π y := by simp only [mul_assoc,← Finset.mul_sum,C.stationary]
lemma power_warm (n : ℕ) (ν : X → ℝ) (U : ℝ) (hν : ∀ x,ν x ≤ U*C.π x) (y : X) :
    (C.kernel.power n).push ν y ≤ U*C.π y := by
  induction n generalizing y with
  | zero => simpa [FiniteKernel.power,FiniteKernel.push_identity] using hν y
  | succ n ih => rw [FiniteKernel.power_push_succ]; exact C.push_warm _ U (fun y => ih y) y
lemma power_push_mass (n : ℕ) (ν : X → ℝ) : ∑ y,(C.kernel.power n).push ν y = ∑ x,ν x := by
  rw [FiniteKernel.push_mass]
  simp_rw [C.kernel_power_stochastic,mul_one]

end

open scoped BigOperators Classical
end FiniteChain

section SamplingObservables
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance85 : Fintype Γ] [DecidableEq Γ]
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

namespace FiniteExperiment
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance89 : Fintype X]

lemma expect_nonneg (K : List X → X → ℝ) (hK : ∀ h x,0 ≤ K h x)
    (φ : List X → ℝ) (hφ : ∀ h,0 ≤ φ h) (t : ℕ) (h : List X) :
    0 ≤ expect K t h φ := by
  induction t generalizing h with
  | zero => exact hφ h
  | succ t ih => exact Finset.sum_nonneg (fun x _ => mul_nonneg (hK h x) (ih _))
omit sectionInstance89 in
lemma restrict_nonneg [Fintype X] (P : List X → X → ℝ) (Good : List X → Prop) (hP : ∀ h x,0 ≤ P h x)
    (h : List X) (x : X) : 0 ≤ restrict P Good h x := by
  unfold restrict; split_ifs; exact hP _ _; rfl
omit sectionInstance89 in
lemma restrict_le [Fintype X] (P : List X → X → ℝ) (Good : List X → Prop) (hP : ∀ h x,0 ≤ P h x)
    (h : List X) (x : X) : restrict P Good h x ≤ P h x := by
  unfold restrict; split_ifs; rfl; exact hP _ _
omit sectionInstance89 in
lemma restrict_support [Fintype X] (P : List X → X → ℝ) (Good : List X → Prop)
    (h : List X) (x : X) (hx : 0 < restrict P Good h x) : Good (h++[x]) := by
  by_contra hg
  simp [restrict,hg] at hx
lemma mass_le_good_probability (P : List X → X → ℝ) (Good : List X → Prop)
    (hP : ∀ h x,0 ≤ P h x) (t : ℕ) (h : List X) (hh : Good h) :
    mass (restrict P Good) t h ≤ expect P t h (fun l => if Good l then 1 else 0) := by
  induction t generalizing h with
  | zero => simp [mass,expect,hh]
  | succ t ih =>
    change (∑ x,restrict P Good h x*mass (restrict P Good) t (h++[x])) ≤ _
    apply Finset.sum_le_sum
    intro x _
    by_cases hg : Good (h++[x])
    · simpa only [restrict,ite_eq_left hg] using mul_le_mul_of_nonneg_left (ih _ hg) (hP h x)
    · have hr : restrict P Good h x=0 := by simp [restrict,hg]
      rw [hr,zero_mul]
      exact mul_nonneg (hP h x) (expect_nonneg P hP _ (by intro l; split_ifs <;> norm_num) t _)

end FiniteExperiment
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma kernel_point_mixing (K m : ℝ) (hK : 1≤K) (hm : 0 < m) (hπ : ∀ x,m≤C.π x)
    (hp : ∀ f : X → ℝ,C.variance f≤K*C.energy f) (k : ℕ) (x y : X) :
    |(C.kernel.power k).P x y/C.π y-1|≤Real.exp (-(k:ℝ)/K)/m := by
  rw [C.kernel_power_density]
  exact C.point_mixing_exp K m hK hm hπ hp k x y

end FiniteChain

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
end ActualAnnealing
namespace FiniteExperiment
open scoped BigOperators Classical
variable {X : Type*} [Fintype X]
theorem adaptive_success_bounded (K : List X → X → ℝ) (Good : List X → Prop)
    (hK : ∀ h x,0 ≤ K h x) (hrow : ∀ h,∑ x,K h x ≤ 1)
    (hsupport : ∀ h,Good h → ∀ x,0<K h x → Good (h++[x]))
    (L : ℕ) (e : ℝ) (he : 0 ≤ e)
    (hloss : ∀ h,Good h → h.length<L → 1-e ≤ ∑ x,K h x)
    (t : ℕ) (h : List X) (hh : Good h) (hsize : h.length+t ≤ L) :
    1-(t:ℝ)*e ≤ mass K t h := by
  induction t generalizing h with
  | zero => simp [mass,expect]
  | succ t ih =>
    have hlocal : ∀ x,K h x*(1-(t:ℝ)*e) ≤ K h x*mass K t (h++[x]) := by
      intro x
      by_cases hz : K h x=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (ih _ (hsupport h hh x (lt_of_le_of_ne (hK h x) (Ne.symm hz))) (by simp only [List.length_append,List.length_singleton]; omega)) (hK h x)
    change 1-((t+1:ℕ):ℝ)*e ≤ ∑ x,K h x*mass K t (h++[x])
    have hs := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => hlocal x)
    rw [← Finset.sum_mul] at hs
    have hm := hloss h hh (by omega)
    have hu := hrow h
    have ht : 0 ≤ (t:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he
    push_cast
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hu)]
theorem good_probability_bounded (P : List X → X → ℝ) (Good : List X → Prop)
    (hP : ∀ h x,0 ≤ P h x) (hrow : ∀ h,∑ x,P h x ≤ 1)
    (L : ℕ) (e : ℝ) (he : 0 ≤ e)
    (hstep : ∀ h,Good h → h.length<L → 1-e ≤ ∑ x,restrict P Good h x) :
    Good [] → 1-(L:ℝ)*e ≤ expect P L [] (fun l => if Good l then 1 else 0) := by
  intro hh
  have hb := adaptive_success_bounded (restrict P Good) Good (restrict_nonneg P Good hP)
    (fun h => (Finset.sum_le_sum (fun x _ => restrict_le P Good hP h x)).trans (hrow h))
    (fun h _ x hx => restrict_support P Good h x hx) L e he hstep L [] hh (by simp)
  exact hb.trans (mass_le_good_probability P Good hP L [] hh)
end FiniteExperiment
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

lemma uniformAverage_mono {X : Type*} [Fintype X] (f g : X → ℝ)
    (hfg : ∀ x,f x≤g x) : uniformAverage f≤uniformAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hfg x)) (Nat.cast_nonneg _)
open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion signature marginal is the literal weighted completion count

The physical all-large product is split bijectively into tree and free
assignments. Exact nonroot equations then retain one tree completion per
free assignment, with exactly its root/tree exponential penalty.
-/

namespace ContingencyTables.ForestCountIdentification

open scoped BigOperators Classical
open SimpleGraph LargePairEnumeration PhysicalLargeProfiles
open ForestCapacity GraphCompletionCounts ForestAssignmentSplit ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

/-- At annealing parameter zero the original count is exactly the
product of the free interval lengths. -/
theorem sourceMarginal_zero (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b : I → J → ℕ) (r : I → ℤ) (c : J → ℤ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) :
    sourceMarginal small T d b r c 0 z=
      ∏ a : FreeCell small T, ((b a.val.1 a.val.2+1:ℕ):ℝ) := by
  simp [sourceMarginal,Fintype.card_pi,Nat.cast_prod]

end ContingencyTables.ForestCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TwoLiftStates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures LabelledFactorial

variable {P C : Type*} [Fintype P] [Fintype C]

omit [Fintype C] in
lemma viewCounts_eq_occupancy (cell : P → C) (S : Set (P × Bool)) (c : C) :
    viewCount cell S c false + viewCount cell S c true =
      ∑ p, if cell p=c then occupancy S p else 0 := by
  unfold viewCount occupancy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : cell p=c <;> simp [hc]

omit [Fintype P] in
lemma occupancy_single (S : Set (P × Bool)) (p : P) (h : PairSingle (pair p) S) :
    occupancy S p = 1 := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [occupancy,pair] at ha hb ⊢ <;> simp [ha,hb]

omit [Fintype P] in
lemma occupancy_empty (S : Set (P × Bool)) (p : P) (h : PairEmpty (pair p) S) :
    occupancy S p = 0 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

omit [Fintype P] in
lemma occupancy_full (S : Set (P × Bool)) (p : P) (h : PairFull (pair p) S) :
    occupancy S p = 2 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

omit [Fintype C] in
/-- Every actual plain state is balanced in every physical cell. -/
theorem plain_counts (cell : P → C) (S : Set (P × Bool))
    (hS : PlainState pairs S) (c : C) :
    viewCount cell S c false + viewCount cell S c true = width cell c := by
  rw [viewCounts_eq_occupancy,width_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [occupancy_single S p (hS _ (pair_mem p))]

lemma defect_occupancy (S : Set (P × Bool)) (p q : P)
    (hS : DefectState pairs (pair p) (pair q) S) (k : P) :
    occupancy S k + (if k=p then 1 else 0) = 1 + (if k=q then 1 else 0) := by
  have hpq : p ≠ q := fun h => hS.2.2.1 (congrArg pair h)
  by_cases hkp : k=p
  · subst k
    rw [occupancy_empty S p hS.2.2.2.1]
    simp [hpq]
  · by_cases hkq : k=q
    · subst k
      rw [occupancy_full S q hS.2.2.2.2.1]
      simp [hkp]
    · rw [occupancy_single S k (hS.2.2.2.2.2 _ (pair_mem k)
        (fun h => hkp (pair_injective h)) (fun h => hkq (pair_injective h)))]
      simp [hkp,hkq]

omit [Fintype C] in
/-- Cell occupancies of an actual defect have exactly one unit missing at
its hole and one unit extra at its full pair, including coinciding cells. -/
theorem defect_counts (cell : P → C) (S : Set (P × Bool)) (p q : P)
    (hS : DefectState pairs (pair p) (pair q) S) (c : C) :
    viewCount cell S c false + viewCount cell S c true + (if cell p=c then 1 else 0) =
      width cell c + (if cell q=c then 1 else 0) := by
  have hs : (∑ k, if cell k=c then occupancy S k + (if k=p then 1 else 0) else 0) =
      ∑ k, if cell k=c then 1 + (if k=q then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [defect_occupancy S p q hS k]
  have hd (u v : P → ℕ) : (∑ k, if cell k=c then u k+v k else 0) =
      (∑ k, if cell k=c then u k else 0)+(∑ k, if cell k=c then v k else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> rfl
  rw [hd,hd] at hs
  have he (a : P) : (∑ k, if cell k=c then (if k=a then (1:ℕ) else 0) else 0) =
      if cell a=c then 1 else 0 := by
    calc
      _ = ∑ k, if k=a then (if cell k=c then 1 else 0) else 0 := by
        apply Finset.sum_congr rfl; intro k _; split_ifs <;> rfl
      _ = _ := by simp
  rw [he p,he q,← width_eq_sum,← viewCounts_eq_occupancy] at hs
  exact hs

end ContingencyTables.TwoLiftStates

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_InitializationBrackets
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact local factorial sums for the companion's initial multipliers

These are the four brackets in the manuscript's exact initialization
formula. The full-pair case reduces to an explicitly evaluated quadratic
sum, so the rational initializer uses no factorial evaluation oracle.
-/

namespace ContingencyTables.InitializationBrackets

open scoped BigOperators
open Nat

private lemma choose_factorial (n k : ℕ) (hk : k≤n) :
    (n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ)=(n !:ℝ) := by
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk

private lemma shifted_choose_factorial (n k : ℕ) (hk : k≤n) :
    (n.choose k:ℝ)*((k+1)!:ℝ)*((n-k+1)!:ℝ)=
      (n !:ℝ)*((k:ℝ)+1)*((n-k:ℕ)+1:ℝ) := by
  rw [Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  calc
    _ = ((n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ))*((k:ℝ)+1)*((n-k:ℕ)+1:ℝ) := by ring
    _ = _ := by rw [choose_factorial n k hk]

private lemma linear_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1))=((n:ℝ)+1)*((n:ℝ)+2)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

private lemma quadratic_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1)*((n-k:ℕ)+1:ℝ))=
      ((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hterms :
        (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1)*((n+1-k:ℕ)+1:ℝ))=
        (∑ k ∈ Finset.range (n+1), ((k:ℝ)+1)*((n-k:ℕ)+1:ℝ))+
          ∑ k ∈ Finset.range (n+1), ((k:ℝ)+1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have he : n+1-k=(n-k)+1 := by have := Finset.mem_range.mp hk; omega
      rw [he]
      push_cast
      ring
    rw [hterms,ih,linear_sum]
    simp only [Nat.sub_self,Nat.cast_zero,zero_add]
    push_cast
    ring

private lemma unshifted_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ))=
      ((n:ℝ)+1)*(n !:ℝ) := by
  calc
    _ = ∑ _k ∈ Finset.range (n+1), (n !:ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact choose_factorial n k (by have := Finset.mem_range.mp hk; omega)
    _ = _ := by simp

private lemma shifted_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*((k+1)!:ℝ)*((n-k+1)!:ℝ))=
      (n !:ℝ)*(((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)/6) := by
  calc
    _ = ∑ k ∈ Finset.range (n+1), (n !:ℝ)*(((k:ℝ)+1)*((n-k:ℕ)+1:ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [shifted_choose_factorial n k (by have := Finset.mem_range.mp hk; omega)]
      ring
    _ = _ := by rw [← Finset.mul_sum,quadratic_sum]

theorem bracket_neither (b : ℕ) : bracket b 0 0=(b:ℝ)+1 := by
  unfold bracket
  simp only [Nat.sub_zero,Nat.add_zero]
  rw [unshifted_sum]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b))

theorem bracket_hole (n : ℕ) : bracket (n+1) 1 0=1 := by
  unfold bracket
  simp only [Nat.add_sub_cancel,Nat.sub_zero,Nat.add_zero]
  rw [unshifted_sum,Nat.factorial_succ]
  push_cast
  exact div_self (mul_ne_zero (by positivity) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))

theorem bracket_full (n : ℕ) :
    bracket (n+1) 0 1=((n:ℝ)+2)*((n:ℝ)+3)/6 := by
  unfold bracket
  simp only [Nat.sub_zero,Nat.add_sub_cancel]
  rw [shifted_sum,Nat.factorial_succ]
  push_cast
  have hf : (n !:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n:ℝ)+1≠0 := by positivity
  field_simp [hf,hn]

theorem bracket_both (n : ℕ) : bracket (n+2) 1 1=((n:ℝ)+3)/6 := by
  unfold bracket
  have he : n+2-1-1=n := by omega
  rw [he,shifted_sum]
  rw [show n+2=(n+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  have hf : (n !:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n:ℝ)+1≠0 := by positivity
  have hn' : (n:ℝ)+2≠0 := by positivity
  field_simp [hf,hn,hn']
  ring

end ContingencyTables.InitializationBrackets

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialLocalChoices
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initialization brackets are actual sums over remaining row labels -/

namespace ContingencyTables.InitialLocalChoices

open scoped BigOperators Classical
open Nat
open InitializationBrackets

/-- Enumerating all choices of the remaining row labels gives exactly
the binomial/factorial bracket, including empty local spaces. -/
theorem sum_localWeight (b u v : ℕ) :
    (∑ S : Finset (Fin (b-u-v)), localWeight b u v S)=bracket b u v := by
  have h := Finset.sum_powerset_apply_card
    (fun k => ((k+v)!:ℝ)*((b-u-v-k+v)!:ℝ)/(b !:ℝ))
    (x := (Finset.univ : Finset (Fin (b-u-v))))
  simpa [localWeight,bracket,nsmul_eq_mul,Finset.sum_div,mul_div_assoc,mul_assoc] using h

/-- Independent choices in the cells factor exactly; the expression is
a finite combinatorial sum before evaluating its four bracket cases. -/
theorem sum_independent_choices {C : Type*} [Fintype C] (b u v : C → ℕ) :
    (∑ S : ((c : C) → Finset (Fin (b c-u c-v c))),
      ∏ c, localWeight (b c) (u c) (v c) (S c))=
      ∏ c, bracket (b c) (u c) (v c) := by
  rw [← Fintype.prod_sum]
  simp_rw [sum_localWeight]

end ContingencyTables.InitialLocalChoices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialTransversals
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial transversal sum is an actual finite row-label choice sum

For every cell, a choice of row labels gives exactly one paired
transversal. Its factorial weight is the local factorial weight used in
the evaluated initialization brackets.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat
open CommonBasesFPRAS TwoLiftStates LabelledFactorial InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

lemma width_cell (c : C) : width (cell b) c=b c := by
  rw [width_eq_sum,Fintype.sum_sigma]
  have hinner (x : C) :
      (∑ k : Fin (b x), if cell b ⟨x,k⟩=c then 1 else 0)=
        if x=c then b x else 0 := by
    by_cases hx : x=c
    · subst x
      simp
    · simp [hx]
  convert (show (∑ x : C, if x=c then b x else 0)=b c by simp) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  exact hinner x

lemma row_count (S : (c : C) → Finset (Fin (b c))) (c : C) :
    viewCount (cell b) (encode b S) c false=(S c).card := by
  unfold viewCount
  rw [Fintype.sum_sigma]
  have hinner (x : C) :
      (∑ k : Fin (b x), if cell b ⟨x,k⟩=c ∧ ((⟨x,k⟩,false):Copy b×Bool)∈encode b S then 1 else 0)=
        if x=c then (S c).card else 0 := by
    by_cases hx : x=c
    · subst x
      simp only [cell,true_and,encode_false]
      simp
    · simp [hx]
  convert (show (∑ x : C, if x=c then (S c).card else 0)=(S c).card by simp) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  exact hinner x

lemma column_count (S : (c : C) → Finset (Fin (b c))) (c : C) :
    viewCount (cell b) (encode b S) c true=b c-(S c).card := by
  have h := plain_counts (cell b) (encode b S) (encode_plain b S) c
  rw [row_count,width_cell] at h
  omega

lemma firstLift_encode (M : ℝ) (S : (c : C) → Finset (Fin (b c))) :
    firstLift (group (cell b)) (fun _ => M) (denominator b) (encode b S)=
      M*∏ c, localWeight (b c) 0 0 (S c) := by
  unfold firstLift FactorialSignatures.factorialProduct denominator
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,groupCount_eq_viewCount,row_count,column_count]
  simp only [localWeight,Nat.sub_zero,Nat.add_zero]
  rw [Finset.prod_div_distrib]
  have he : (∏ c, ((b c-(S c).card)!:ℝ)*((S c).card !:ℝ))=
      ∏ c, ((S c).card !:ℝ)*((b c-(S c).card)!:ℝ) := by
    apply Finset.prod_congr rfl
    intro c _
    exact mul_comm _ _
  rw [he]
  ring

/-- The actual paired-transversal total at a constant raw completion
count M is exactly the manuscript's M*product(b+1). -/
theorem slotTotal_constant (M : ℝ) :
    slotTotal pairs (firstLift (group (cell b)) (fun _ => M) (denominator b)) ∅=
      M*∏ c, ((b c:ℝ)+1) := by
  rw [slotTotal_eq_plain_sum pairs PairedLabels.fresh PairedLabels.cover]
  rw [Finset.sum_subtype (p := PlainState (pairs : List ((Copy b×Bool)×(Copy b×Bool)))) _
    (by intro S; simp)]
  calc
    _ = ∑ S : ((c : C) → Finset (Fin (b c))), M*∏ c, localWeight (b c) 0 0 (S c) := by
      apply Fintype.sum_equiv (plainEquivChoices b)
      intro S
      have h := firstLift_encode b M ((plainEquivChoices b) S)
      have he : encode b ((plainEquivChoices b) S)=S.val :=
        congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply S)
      rwa [he] at h
    _ = _ := by
      rw [← Finset.mul_sum]
      have he := sum_independent_choices b (fun _ => 0) (fun _ => 0)
      simp only [Nat.sub_zero] at he
      rw [he]
      simp_rw [InitializationBrackets.bracket_neither]

end ContingencyTables.InitialTransversals

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialization
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact initial normalizer for the literal companion completion count -/

namespace ContingencyTables.CompanionInitialization

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

theorem h_zero (A : Instance I J) (z : View A → ℕ) : h A 0 z=freeTotal A :=
  ForestCountIdentification.sourceMarginal_zero A.small A.T A.d A.b A.r A.c z

theorem denominator_eq (A : Instance I J) :
    CompanionFactorialApplication.denominator A=
      InitialTransversals.denominator (fun s : SmallCell A => A.b s.val.1 s.val.2) := by
  unfold CompanionFactorialApplication.denominator TwoLiftStates.denominator InitialTransversals.denominator
  simp_rw [label_width]

/-- C(0) is derived for the actual source f, using the finite
paired-transversal enumeration and the literal free-completion count. -/
theorem total_zero (A : Instance I J) :
    slotTotal pairs (f A 0) ∅=freeTotal A*∏ s : SmallCell A, ((A.b s.val.1 s.val.2:ℝ)+1) := by
  have he : f A 0=firstLift (group (labelCell A)) (fun _ => freeTotal A)
      (CompanionFactorialApplication.denominator A) := by
    funext S
    unfold f firstLift
    rw [h_zero]
  rw [he,denominator_eq]
  convert InitialTransversals.slotTotal_constant
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (freeTotal A) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

end ContingencyTables.CompanionInitialization

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialDefectChoices
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual remaining label choices for an initial defect

The hole and full pair are removed before the remaining row labels are
chosen. This gives the finite combinatorial space underlying the exact
local initialization brackets, including two removed labels in one cell.
-/

namespace ContingencyTables.InitialDefectChoices

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates
open InitialTransversals (Copy)

variable {C : Type*} [Fintype C] (b : C → ℕ) (p q : Copy b)

omit [Fintype C] in
lemma fiber_eq_sum (c : C) (a : Copy b) :
    (∑ k : Fin (b c), if (⟨c,k⟩:Copy b)=a then (1:ℕ) else 0)=
      if a.1=c then 1 else 0 := by
  rcases a with ⟨a,k⟩
  by_cases ha : a=c
  · subst a
    simp
  · have hn (k' : Fin (b c)) : (⟨c,k'⟩:Copy b)≠⟨a,k⟩ :=
      fun h => ha (congrArg Sigma.fst h).symm
    simp [ha,hn]

omit [Fintype C] in
/-- There are exactly b-u-v remaining labels in each cell. This proof
uses distinct physical labels, so the coinciding-cell case is included. -/
theorem local_card_balance (hpq : p≠q) (c : C) :
    Fintype.card (Local b p q c)+(if p.1=c then 1 else 0)+(if q.1=c then 1 else 0)=b c := by
  have ht (k : Fin (b c)) :
      (if (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q then (1:ℕ) else 0)+
        (if (⟨c,k⟩:Copy b)=p then 1 else 0)+
        (if (⟨c,k⟩:Copy b)=q then 1 else 0)=1 := by
    by_cases hp : (⟨c,k⟩:Copy b)=p
    · have hq : (⟨c,k⟩:Copy b)≠q := fun h => hpq (hp.symm.trans h)
      simp [hp,hpq]
    · by_cases hq : (⟨c,k⟩:Copy b)=q <;> simp [hp,hq,Ne.symm hpq]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => ht k)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,fiber_eq_sum,fiber_eq_sum] at hs
  have he : (∑ k : Fin (b c), if (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q then (1:ℕ) else 0)=
      Fintype.card (Local b p q c) := by
    rw [Fintype.card_subtype]
    simp
  rw [he] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hs
  exact hs

omit [Fintype C] in
lemma local_card (hpq : p≠q) (c : C) :
    Fintype.card (Local b p q c)=b c-(if p.1=c then 1 else 0)-(if q.1=c then 1 else 0) := by
  have h := local_card_balance b p q hpq c
  omega

omit [Fintype C] in
lemma chosen_ne (S : (c : C) → Finset (Local b p q c)) (c : C) (k : Fin (b c))
    (hk : k∈chosen b p q S c) : (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hk
  exact a.property

omit [Fintype C] in
lemma encode_row (S : (c : C) → Finset (Local b p q c)) (a : Copy b) :
    (a,false)∈encode b p q S ↔ a=q ∨ a.2∈chosen b p q S a.1 := by
  by_cases haq : a=q
  · exact iff_of_true (haq ▸ encode_full b p q S false) (Or.inl haq)
  · by_cases hap : a=p
    · subst a
      have hn : p.2∉chosen b p q S p.1 := fun h => (chosen_ne b p q S _ _ h).1 rfl
      exact iff_of_false (encode_hole b p q haq S false) (by simp [haq,hn])
    · rw [encode_false b p q S a ⟨hap,haq⟩]
      simp only [haq,false_or,chosen,Finset.mem_map]
      constructor
      · intro h
        exact ⟨⟨a.2,hap,haq⟩,h,rfl⟩
      · rintro ⟨k,hk,he⟩
        have he' : k=⟨a.2,hap,haq⟩ := Subtype.ext he
        rwa [he'] at hk

lemma row_count (_hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) (c : C) :
    viewCount (InitialTransversals.cell b) (encode b p q S) c false=
      (S c).card+(if q.1=c then 1 else 0) := by
  unfold viewCount
  rw [Fintype.sum_sigma]
  have hi (x : C) :
      (∑ k : Fin (b x), if InitialTransversals.cell b ⟨x,k⟩=c ∧
        ((⟨x,k⟩,false):Copy b×Bool)∈encode b p q S then (1:ℕ) else 0)=
        if x=c then (S c).card+(if q.1=c then 1 else 0) else 0 := by
    by_cases hx : x=c
    · subst x
      simp only [InitialTransversals.cell,true_and,encode_row]
      have he (k : Fin (b c)) :
          (if (⟨c,k⟩:Copy b)=q ∨ k∈chosen b p q S c then (1:ℕ) else 0)=
            (if k∈chosen b p q S c then 1 else 0)+(if (⟨c,k⟩:Copy b)=q then 1 else 0) := by
        by_cases hq : (⟨c,k⟩:Copy b)=q
        · have hn : k∉chosen b p q S c := fun h => (chosen_ne b p q S c k h).2 hq
          simp [hq,hn]
        · by_cases hk : k∈chosen b p q S c <;> simp [hq,hk]
      simp_rw [he]
      rw [Finset.sum_add_distrib,fiber_eq_sum]
      simp only [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]
      rw [chosen,Finset.card_map]
      simp
    · simp [hx]
  calc
    _ = ∑ x : C, if x=c then (S c).card+(if q.1=c then 1 else 0) else 0 :=
      Finset.sum_congr rfl (fun x _ => hi x)
    _ = _ := by simp

lemma column_count (hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) (c : C) :
    viewCount (InitialTransversals.cell b) (encode b p q S) c true=
      Fintype.card (Local b p q c)-(S c).card+(if q.1=c then 1 else 0) := by
  have h := defect_counts (InitialTransversals.cell b) (encode b p q S) p q
    (encode_defect b p q hpq S) c
  rw [row_count b p q hpq,InitialTransversals.width_cell] at h
  have hc := local_card_balance b p q hpq c
  have hS := Finset.card_le_univ (S c)
  simp only [InitialTransversals.cell] at h
  omega

omit [Fintype C] in
lemma sum_localWeight (hpq : p≠q) (c : C) :
    (∑ S : Finset (Local b p q c),localWeight b p q c S)=
      InitializationBrackets.bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0) := by
  have h := Finset.sum_powerset_apply_card
    (fun k => (((k+(if q.1=c then 1 else 0)).factorial:ℝ)*
      ((Fintype.card (Local b p q c)-k+(if q.1=c then 1 else 0)).factorial:ℝ))/(b c).factorial)
    (x := (Finset.univ : Finset (Local b p q c)))
  simpa [localWeight,InitializationBrackets.bracket,local_card b p q hpq,
    nsmul_eq_mul,Finset.sum_div,mul_div_assoc,mul_assoc] using h

lemma firstLift_encode (hpq : p≠q) (M : ℝ) (S : (c : C) → Finset (Local b p q c)) :
    LabelledFactorial.firstLift (group (InitialTransversals.cell b)) (fun _ => M)
      (InitialTransversals.denominator b) (encode b p q S)=M*∏ c,localWeight b p q c (S c) := by
  unfold LabelledFactorial.firstLift FactorialSignatures.factorialProduct InitialTransversals.denominator
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,groupCount_eq_viewCount,row_count b p q hpq,column_count b p q hpq]
  unfold localWeight
  rw [Finset.prod_div_distrib]
  have he : (∏ c, ((Fintype.card (Local b p q c)-(S c).card+(if q.1=c then 1 else 0)).factorial:ℝ)*
      (((S c).card+(if q.1=c then 1 else 0)).factorial:ℝ))=
      ∏ c, (((S c).card+(if q.1=c then 1 else 0)).factorial:ℝ)*
        ((Fintype.card (Local b p q c)-(S c).card+(if q.1=c then 1 else 0)).factorial:ℝ) := by
    apply Finset.prod_congr rfl
    intro c _
    exact mul_comm _ _
  rw [he]
  ring

/-- The source bracket product is the actual finite defect normalizer,
with no assumption about where its missing and full labels lie. -/
theorem slotDefect_constant (hpq : p≠q) (M : ℝ) :
    slotDefect pairs (LabelledFactorial.firstLift (group (InitialTransversals.cell b))
      (fun _ => M) (InitialTransversals.denominator b)) ∅ (TwoLiftStates.pair p) (TwoLiftStates.pair q)=
      M*∏ c,InitializationBrackets.bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0) := by
  rw [slotDefect_eq_defect_sum pairs PairedLabels.fresh PairedLabels.cover _
    (TwoLiftStates.pair p) (TwoLiftStates.pair q) (pair_mem p) (pair_mem q)
    (fun h => hpq (pair_injective h))]
  rw [Finset.sum_subtype (p := DefectState pairs (TwoLiftStates.pair p) (TwoLiftStates.pair q)) _
    (by intro S; simp)]
  calc
    _ = ∑ S : ((c : C) → Finset (Local b p q c)),M*∏ c,localWeight b p q c (S c) := by
      apply Fintype.sum_equiv (defectEquivChoices b p q hpq)
      intro S
      have h := firstLift_encode b p q hpq M ((defectEquivChoices b p q hpq) S)
      have he : encode b p q ((defectEquivChoices b p q hpq) S)=S.val :=
        congrArg Subtype.val ((defectEquivChoices b p q hpq).symm_apply_apply S)
      rwa [he] at h
    _ = _ := by
      rw [← Finset.mul_sum,← Fintype.prod_sum]
      simp_rw [sum_localWeight b p q hpq]

end ContingencyTables.InitialDefectChoices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_InitialMultiplierValues
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact source initial multipliers for actual labelled defects -/

namespace ContingencyTables.InitialMultiplierValues

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates InitialTransversals InitializationBrackets

variable {C : Type*} [Fintype C] (b : C → ℕ)

lemma bracket_hole_of_pos (n : ℕ) (hn : 0< n) : bracket n 1 0=1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact bracket_hole k

lemma bracket_full_of_pos (n : ℕ) (hn : 0< n) :
    bracket n 0 1=((n:ℝ)+1)*((n:ℝ)+2)/6 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [bracket_full]
  push_cast
  ring

lemma bracket_both_of_two (n : ℕ) (hn : 2≤ n) : bracket n 1 1=((n:ℝ)+1)/6 := by
  have he : n=(n-2)+2 := by omega
  conv_lhs => rw [he]
  rw [bracket_both]
  have hc : (n:ℝ)=((n-2:ℕ):ℝ)+2 := by exact_mod_cast he
  rw [hc]
  ring

omit [Fintype C] in
lemma same_cell_capacity (p q : Copy b) (hpq : p≠q) (hcell : p.1=q.1) : 2≤ b p.1 := by
  rcases p with ⟨c,p⟩
  rcases q with ⟨c',q⟩
  simp only at hcell
  subst c'
  have hne : p≠q := fun h => hpq (congrArg (Sigma.mk c) h)
  have hp := p.isLt
  have hq := q.isLt
  have hv : p.val≠q.val := fun h => hne (Fin.ext h)
  change 2≤b c
  omega

omit [Fintype C] in
lemma value_positive (p q : Copy b) : 0< value b p q := by
  unfold value
  split_ifs <;> positivity

lemma bracket_product_same (p q : Copy b) (hpq : p≠q) (hcell : p.1=q.1) :
    (∏ c,bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0))=
      (∏ c,((b c:ℝ)+1))/6 := by
  have he (c : C) :
      bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0)=
        ((b c:ℝ)+1)*(if c=p.1 then (1/6:ℝ) else 1) := by
    by_cases hc : p.1=c
    · subst c
      simp only [hcell,ite_true, if_true,bracket_both_of_two (b q.1) (by
        simpa only [hcell] using same_cell_capacity b p q hpq hcell)]
      ring
    · have hcq : q.1≠c := by rwa [← hcell]
      simp [hc,hcq,Ne.symm hc,bracket_neither]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp
  ring

lemma bracket_product_different (p q : Copy b) (hcell : p.1≠q.1) :
    (∏ c,bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0))=
      (∏ c,((b c:ℝ)+1))*(((b q.1:ℝ)+2)/(6*((b p.1:ℝ)+1))) := by
  have he (c : C) :
      bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0)=
        ((b c:ℝ)+1)*
          ((if c=p.1 then 1/((b p.1:ℝ)+1) else 1)*
            (if c=q.1 then ((b q.1:ℝ)+2)/6 else 1)) := by
    by_cases hp : p.1=c
    · subst c
      have hq : q.1≠p.1 := Ne.symm hcell
      simp only [ite_true, if_true,hq,ite_false,hcell,bracket_hole_of_pos (b p.1) (by have := p.2.isLt; omega),
        mul_one]
      field_simp
    · by_cases hq : q.1=c
      · subst c
        simp only [hp,ite_false,ite_true, if_true,Ne.symm hp,
          bracket_full_of_pos (b q.1) (by have := q.2.isLt; omega),one_mul]
        ring
      · simp [hp,hq,Ne.symm hp,Ne.symm hq,bracket_neither]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true, if_true]
  field_simp

/-- The exact finite transversal/defect ratio is six in a shared cell,
and otherwise six times (b_hole+1)/(b_full+2). -/
theorem ideal_constant [DecidableEq C] (p q : Copy b) (hpq : p≠q) (M : ℝ) (hM : 0< M) :
    slotTotal pairs (LabelledFactorial.firstLift (group (cell b)) (fun _ => M)
      (InitialTransversals.denominator b)) ∅/
      slotDefect pairs (LabelledFactorial.firstLift (group (cell b)) (fun _ => M)
        (InitialTransversals.denominator b)) ∅ (TwoLiftStates.pair p) (TwoLiftStates.pair q)=value b p q := by
  have hd : (inferInstance : DecidableEq C)=Classical.decEq C := Subsingleton.elim _ _
  cases hd
  rw [slotTotal_constant,InitialDefectChoices.slotDefect_constant b p q hpq]
  have hprod : (∏ c,((b c:ℝ)+1))≠0 := ne_of_gt (Finset.prod_pos (fun _ _ => by positivity))
  by_cases hcell : p.1=q.1
  · rw [bracket_product_same b p q hpq hcell]
    simp only [value,hcell,ite_true, if_true]
    field_simp [hM.ne',hprod]
  · rw [bracket_product_different b p q hcell]
    simp only [value,hcell,ite_false]
    field_simp [hM.ne',hprod]

end ContingencyTables.InitialMultiplierValues
namespace ContingencyTables.CompanionInitialMultipliers

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionInitialization LabelledFactorial TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

lemma multiplier_positive (A : Instance I J) (p q : (Labels A×Bool)×(Labels A×Bool)) :
    0< multiplier A p q := InitialMultiplierValues.value_positive _ _ _

lemma freeTotal_positive (A : Instance I J) : 0< freeTotal A := by
  apply Finset.prod_pos
  intro a _
  exact Nat.cast_pos.mpr (Nat.succ_pos _)

/-- The explicit rational initial multiplier equals the ideal for the
literal source count, not just for an abstract constant lift. -/
theorem ideal_at_zero (A : Instance I J) (p q : Labels A) (hpq : p≠q) :
    slotTotal pairs (f A 0) ∅/slotDefect pairs (f A 0) ∅ (TwoLiftStates.pair p) (TwoLiftStates.pair q)=
      multiplier A (TwoLiftStates.pair p) (TwoLiftStates.pair q) := by
  have he : f A 0=firstLift (group (labelCell A)) (fun _ => freeTotal A)
      (CompanionFactorialApplication.denominator A) := by
    funext S
    unfold f firstLift
    rw [h_zero]
  rw [he,denominator_eq]
  convert InitialMultiplierValues.ideal_constant
    (fun s : SmallCell A => A.b s.val.1 s.val.2) p q hpq (freeTotal A) (freeTotal_positive A) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

/-- Initialization has exact ideals, hence satisfies every good-
multiplier inequality for the actual chain without a sampling event. -/
theorem initial_good (A : Instance I J) : GoodMultipliers pairs (f A 0) (multiplier A) := by
  refine ⟨multiplier_positive A,?_,?_⟩
  · intro p hp q hq hpq
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show p∈Finset.univ.toList.map TwoLiftStates.pair from hp)
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp (show q∈Finset.univ.toList.map TwoLiftStates.pair from hq)
    have hab : a≠b := fun h => hpq (congrArg TwoLiftStates.pair h)
    rw [mul_comm (4:ℝ),← div_div,ideal_at_zero A a b hab]
    have hpos := multiplier_positive A (TwoLiftStates.pair a) (TwoLiftStates.pair b)
    linarith
  · intro p hp q hq hpq
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show p∈Finset.univ.toList.map TwoLiftStates.pair from hp)
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp (show q∈Finset.univ.toList.map TwoLiftStates.pair from hq)
    have hab : a≠b := fun h => hpq (congrArg TwoLiftStates.pair h)
    rw [mul_div_assoc,ideal_at_zero A a b hab]
    have hpos := multiplier_positive A (TwoLiftStates.pair a) (TwoLiftStates.pair b)
    linarith

end ContingencyTables.CompanionInitialMultipliers

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

lemma expectation_map [DecidableEq Y] (p : RationalLaw X) (draw : X → Y) (g : Y → ℝ) :
    expectation (mapLaw p draw) g=expectation p (fun x => g (draw x)) := by
  unfold expectation mapLaw
  simp only [Rat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y : Y,if draw x=y then (p.mass x:ℝ)*g y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = _ := by simp

lemma expectation_uniform [Nonempty X] (g : X → ℝ) :
    expectation (uniformLaw (α := X)) g=uniformAverage g := by
  unfold expectation uniformLaw uniformMass uniformAverage
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [←Finset.mul_sum]
  ring

lemma word_expectation [Nonempty X] [DecidableEq Y] (draw : X → Y) (g : Y → ℝ) :
    uniformAverage (fun x => g (draw x))=expectation (mapLaw (uniformLaw (α := X)) draw) g := by
  rw [expectation_map,expectation_uniform]

end ContingencyTables.FiniteLawMoments

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRationalUpdates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

lemma initial_positive (A : Instance I J) (p q : Pair A) : 0 < initial A p q := by
  unfold initial
  split_ifs <;> positivity

lemma initial_cast (A : Instance I J) (p q : Pair A) :
    (initial A p q:ℝ)=CompanionInitialMultipliers.multiplier A p q := by
  simp only [initial,CompanionInitialMultipliers.multiplier,InitialMultiplierValues.value]
  split_ifs <;> simp only [Rat.cast_ofNat,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]

end

end ContingencyTables.CompanionRationalUpdates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRationalThreshold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded dyadic comparison with a rational acceptance probability -/

namespace ContingencyTables.FairBits

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

lemma rationalThreshold_le (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    rationalThreshold k q ≤ 2^k := by
  have h := Nat.floor_le (mul_nonneg (by positivity : (0:ℚ) ≤ 2^k) hq0)
  have h' : (rationalThreshold k q:ℚ) ≤ (2:ℚ)^k := by
    change (⌊(2:ℚ)^k*q⌋₊:ℚ) ≤ (2:ℚ)^k
    exact h.trans (by nlinarith [pow_pos (by norm_num : (0:ℚ)<2) k])
  exact_mod_cast h'

lemma rationalThreshold_count (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (Finset.univ.filter (fun z : Fin (2^k) => z.val < rationalThreshold k q)).card=
      rationalThreshold k q := by
  rw [Fin.card_filter_val_lt,min_eq_right (rationalThreshold_le k q hq0 hq1)]

/-- The finite coin always rounds downward and loses less than one
code word, including the exact endpoint probabilities zero and one. -/
theorem rationalThreshold_error (k : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    0 ≤ rationalThresholdMass k q ∧ rationalThresholdMass k q ≤ q ∧
      q-rationalThresholdMass k q < 1/(2:ℚ)^k := by
  have hp : (0:ℚ)<2^k := by positivity
  have hlo := Nat.floor_le (mul_nonneg hp.le hq)
  have hhi := Nat.lt_floor_add_one ((2:ℚ)^k*q)
  change 0 ≤ (⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k ∧
    (⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k ≤ q ∧
    q-(⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k < 1/(2:ℚ)^k
  refine ⟨by positivity,?_,?_⟩
  · exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hlo)
  · rw [sub_div' hp.ne',div_lt_div_iff_of_pos_right hp]
    nlinarith

/-- An actual k-bit input realizes the stated rounded probability. -/
theorem rationalThreshold_expectation (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    uniformAverage (fun bits : Fin k → Bool =>
      if rationalThresholdAccept k q bits then (1:ℝ) else 0)=
        (rationalThresholdMass k q:ℝ) := by
  have he := uniformAverage_equiv (binaryWordEquiv k)
    (fun z : Fin (2^k) => if z.val < rationalThreshold k q then (1:ℝ) else 0)
  simp only [rationalThresholdAccept]
  rw [he]
  unfold uniformAverage
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,rationalThreshold_count k q hq0 hq1,
    Fintype.card_fin,rationalThresholdMass,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,
    Nat.cast_pow,Nat.cast_ofNat]

end

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DegreeCompletion
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive completion of a single valid degree

A fixed-degree weight is extended by the constant weight one on every
other degree. All off-degree signatures are proved, and all coefficient
sums at the original degree are unchanged. This lets the existing general
nonnegative-derivative theorem retain contracted coordinates without
assuming positivity or signatures of the original weight at other degrees.
-/

namespace ContingencyTables.DegreeCompletion

open scoped BigOperators Classical Topology
open CommonBasesFPRAS BinaryContraction

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Every nonzero derivative term adds precisely one new element; no
fresh-pair or disjointness assumption is needed for this congruence. -/
lemma coeffDerivs_degree_congr (ds : List (Γ → ℝ)) (f g : Set Γ → ℝ) (k : ℕ)
    (heq : ∀ S, S.ncard = k → f S = g S) (A : Set Γ)
    (hdegree : A.ncard + ds.length = k) : coeffDerivs ds f A = coeffDerivs ds g A := by
  induction ds generalizing A with
  | nil => exact heq A (by simpa using hdegree)
  | cons a ds ih =>
    change coeffDeriv a (coeffDerivs ds f) A = coeffDeriv a (coeffDerivs ds g) A
    unfold coeffDeriv
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ A
    · simp only [ite_eq_left hi]
    · simp only [ite_eq_right hi]
      congr 1
      apply ih (insert i A)
      rw [ncard_insert_eq A i hi]
      simp only [List.length_cons] at hdegree
      omega

lemma slotTotal_completeDegree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) :
    slotTotal ps (completeDegree f k) A = slotTotal ps f A := by
  apply coeffDerivs_degree_congr _ _ _ k
  · intro S hS
    simp [completeDegree, hS]
  · simpa only [List.length_map] using hdegree

end ContingencyTables.DegreeCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Observable and trace bounds on the actual valid-degree chain

Positive completion is used only to instantiate the existing finite-chain
constructor. All its state weights, conductances, and conditional projections
are proved equal to the original valid-degree quantities.
-/

namespace ContingencyTables.ObservableBounds

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma observableConstant_lower (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    338*p^5 ≤ observableConstant p q := by
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hprod : 1 ≤ p*q^2 := hp.trans (by nlinarith [mul_le_mul_of_nonneg_left hq2 hp0])
  have hbig : 81*p ≤ 9*(p*(1+8*p*q^2)) := by nlinarith
  have htail : 0 ≤ 2*(8+32*p*q^3) := by positivity
  have hi : (338/10 : ℝ)*p ≤ 9*(p*(1+8*p*q^2))+2*(8+32*p*q^3) := by nlinarith
  calc
    338*p^5 = 10*p^4*((338/10 : ℝ)*p) := by ring
    _ ≤ observableConstant p q := mul_le_mul_of_nonneg_left hi (by positivity)

end ContingencyTables.ObservableBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TraceBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trace mixing for the actual omission-lift Metropolis chain

The finite-chain constructor receives the proved positive completion.
Its state weights equal the original valid-degree weights, and the
transversal trace has the original normalized factorial-lift law.
The trace Poincaré bound uses the proved manuscript-coordinate variance
bound, followed by the existing harmonic-extension and spectral arguments.
-/

namespace ContingencyTables.TraceBounds

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableBounds ComplementChain

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma completed_trace_pi (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r) (hf : DegreePositive f gs.length)
    (S : PlainIndex gs) :
    (metropolisTrace gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)).π S = f S.val.val / slotTotal gs f ∅ := by
  rw [metropolisTrace_pi, slotTotal_completeDegree gs f gs.length ∅ (by simp)]
  simp only [completeDegree, S.property.ncard hgs hcover, ite_true, if_true]

end ContingencyTables.TraceBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionConcentration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of the literal companion phase observables -/

namespace ContingencyTables.CompanionConcentration

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing
open TwoLiftStates BinaryContraction DegreeCompletion ObservableBounds

variable {I J : Type*} [Fintype I] [Fintype J]

lemma square_width_one_le (A : Instance I J) : (1:ℝ)≤(A.W:ℝ)^2 := by
  have hW : (2:ℝ)≤ A.W := by exact_mod_cast A.hW
  nlinarith

end ContingencyTables.CompanionConcentration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealKernelApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accumulating rational implementation errors against a real kernel

The exact companion weights may be real. The implemented probabilities
are rational; comparison takes place after their canonical real cast.
-/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open CommonBasesFPRAS ResidualMixture FirstSuccess

noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma distance_triangle (p q r : X → ℝ) : distance p r ≤ distance p q+distance q r := by
  have h := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => abs_sub_le (p x) (q x) (r x))
  simp only [Finset.sum_add_distrib] at h
  unfold distance
  linarith

lemma distance_push (K : FiniteKernel X Y) (p q : X → ℝ) :
    distance (K.push p) (K.push q) ≤ distance p q := by
  have hp (y : Y) : |K.push p y-K.push q y| ≤ ∑ x, |p x-q x| * K.P x y := by
    unfold FiniteKernel.push
    rw [←Finset.sum_sub_distrib]
    have h := Finset.abs_sum_le_sum_abs
      (fun x => p x*K.P x y-q x*K.P x y) Finset.univ
    simpa only [←sub_mul,abs_mul,abs_of_nonneg (K.nonnegative _ _)] using h
  have hs := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hp y)
  have ht : (∑ y,∑ x, |p x-q x| * K.P x y) ≤ ∑ x,|p x-q x| := by
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (K.substochastic x) (abs_nonneg (p x-q x)))
  unfold distance
  exact div_le_div_of_nonneg_right (hs.trans ht) (by norm_num)

end
end ContingencyTables.RealKernelApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTraceWords
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

variable [Fintype X]

private lemma expectation_congr_start (C : FiniteChain X) (n : ℕ) (x : X)
    (F G : List X → ℝ) (h : ∀ xs,F (x::xs)=G (x::xs)) :
    C.pathExpectation n x F=C.pathExpectation n x G := by
  cases n with
  | zero => exact h []
  | succ n =>
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact C.pathExpectation_congr n y _ _ h

private lemma firstHit_expectation (C : FiniteChain X) (B : X → Prop)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : X) :
    C.pathExpectation n x (fun xs => DrawTree.optionValue phi (firstHit B xs))=
      if hx : B x then phi ⟨x,hx⟩ else C.pathExpectation n x (returnValue B phi) := by
  by_cases hx : B x
  · rw [dite_eq_left hx]
    calc
      _ = C.pathExpectation n x (fun _ => phi ⟨x,hx⟩) := by
        apply expectation_congr_start
        intro xs
        simp only [firstHit,dite_eq_left hx,DrawTree.optionValue]
      _ = _ := C.pathExpectation_const n x _
  · rw [dite_eq_right hx]
    apply expectation_congr_start
    intro xs
    simp only [firstHit,dite_eq_right hx,returnValue,List.tail_cons]

private lemma returnValue_succ (C : FiniteChain X) (B : X → Prop)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : X) :
    C.pathExpectation (n+1) x (returnValue B phi)=
      ∑ y,C.P x y*(if hy : B y then phi ⟨y,hy⟩
        else C.pathExpectation n y (returnValue B phi)) := by
  simp only [FiniteChain.pathExpectation,returnValue,List.tail_cons]
  apply Finset.sum_congr rfl
  intro y _
  rw [firstHit_expectation]

private lemma returnValue_split (C : FiniteChain X) (B : X → Prop)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : X) :
    C.pathExpectation (n+1) x (returnValue B phi)=
      (∑ y : FiniteChain.Inside B,C.P x y.val*phi y)+
      ∑ y : FiniteChain.Outside B,C.P x y.val*C.pathExpectation n y.val (returnValue B phi) := by
  rw [returnValue_succ,←Fintype.sum_subtype_add_sum_subtype B]
  congr 1
  · apply Finset.sum_congr rfl
    intro y _
    rw [dite_eq_left y.property]
  · apply Finset.sum_congr rfl
    intro y _
    rw [dite_eq_right y.property]

private lemma partialGreen_succ (Q : KilledKernel X) (n : ℕ) (f : X → ℝ) (x : X) :
    Q.partialGreen (n+1) f x=f x+Q.apply (Q.partialGreen n f) x := by
  unfold KilledKernel.partialGreen
  rw [Finset.sum_range_succ']
  simp only [KilledKernel.iterate_succ,KilledKernel.iterate_zero]
  rw [KilledKernel.apply_sum]
  exact add_comm _ _

/-- An outside starting state has exactly the truncated Green expectation. -/
theorem outside_return_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : FiniteChain.Outside B) :
    C.pathExpectation n x.val (returnValue B phi)=
      Q.partialGreen n (fun z => ∑ y : FiniteChain.Inside B,C.P z.val y.val*phi y) x := by
  induction n generalizing x with
  | zero => simp [FiniteChain.pathExpectation,returnValue,firstHit,DrawTree.optionValue,
      KilledKernel.partialGreen]
  | succ n ih =>
    rw [returnValue_split,partialGreen_succ]
    congr 1
    unfold KilledKernel.apply
    apply Finset.sum_congr rfl
    intro y _
    rw [ih,hQ]

/-- Starting inside and allowing n+1 transitions gives the manuscript's
capped trace, with n possible further outside transitions. -/
theorem inside_return_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val (returnValue B phi)=
      ∑ y : FiniteChain.Inside B,C.cappedTrace B Q n x y*phi y := by
  rw [returnValue_split]
  simp_rw [outside_return_expectation C B Q hQ]
  simp only [FiniteChain.cappedTrace,add_mul,Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [mul_assoc]
  rw [←Finset.mul_sum,KilledKernel.partialGreen_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  unfold KilledKernel.partialGreen
  simp_rw [show (fun t : FiniteChain.Outside B => C.P t.val y.val*phi y)=
    (fun t => phi y*C.P t.val y.val) by funext t; ring]
  simp only [KilledKernel.iterate_mul,←Finset.mul_sum]
  ring

theorem return_failure_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val
      (fun xs => eventIndicator (firstHit B xs.tail=none))=
      1-∑ y : FiniteChain.Inside B,C.cappedTrace B Q n x y := by
  have hfun : (fun xs : List X =>
      eventIndicator (firstHit B xs.tail=none)+returnValue B (fun _ => 1) xs)=
      fun _ => (1:ℝ) := by
    funext xs
    unfold returnValue
    cases firstHit B xs.tail <;> simp [eventIndicator,DrawTree.optionValue]
  have he := C.pathExpectation_add (n+1) x.val
    (fun xs => eventIndicator (firstHit B xs.tail=none))
    (returnValue B (fun _ => 1))
  rw [hfun,C.pathExpectation_const,inside_return_expectation C B Q hQ] at he
  simp only [mul_one] at he
  linarith

end
end ContingencyTables.CompanionTraceWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCappedReturn
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total bounded trace steps

If a capped return search misses its target, the finite-word experiment
keeps its starting plain state. Its error against the exact trace is the
cap loss plus the error of the recorded Boolean walk.
-/

namespace ContingencyTables.CompanionCappedReturn

open CommonBasesFPRAS CompanionTraceWords CompanionPhaseTrajectory
open CompanionFactorialApplication CompanionBooleanPhase CompanionOracleDensity
open CompanionWeightOracle CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

private lemma returnDefault_value (B : X → Prop) (x : FiniteChain.Inside B)
    (phi : FiniteChain.Inside B → ℝ) (xs : List X) :
    phi (returnDefault B x xs)=returnValue B phi xs+
      phi x*eventIndicator (firstHit B xs.tail=none) := by
  unfold returnDefault returnValue
  cases firstHit B xs.tail <;> simp [DrawTree.optionValue,eventIndicator]

variable [Fintype X]

/-- The missing cap mass is assigned to the starting state, exactly. -/
theorem returnDefault_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val (fun xs => phi (returnDefault B x xs))=
      (∑ y,C.cappedTrace B Q n x y*phi y)+
        phi x*(1-∑ y,C.cappedTrace B Q n x y) := by
  calc
    _ = C.pathExpectation (n+1) x.val (fun xs => returnValue B phi xs+
        phi x*eventIndicator (firstHit B xs.tail=none)) := by
      apply C.pathExpectation_congr
      exact returnDefault_value B x phi
    _ = _ := by
      rw [C.pathExpectation_add,C.pathExpectation_mul,
        inside_return_expectation C B Q hQ,
        return_failure_expectation C B Q hQ]

/-- Bounded observations lose at most the exact omitted return mass. -/
theorem returnDefault_error (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (hphi : ∀ y,0≤phi y ∧ phi y≤1)
    (n : ℕ) (x : FiniteChain.Inside B) :
    |C.pathExpectation (n+1) x.val (fun xs => phi (returnDefault B x xs))-
      (∑ y,C.traceMatrix B Q x y*phi y)|≤
        1-∑ y,C.cappedTrace B Q n x y := by
  let loss : ℝ := 1-∑ y,C.cappedTrace B Q n x y
  have hloss : 0≤loss := sub_nonneg.mpr (C.cappedTrace_substochastic B Q hQ n x)
  have hdiff (y : FiniteChain.Inside B) :
      0≤C.traceMatrix B Q x y-C.cappedTrace B Q n x y :=
    sub_nonneg.mpr (C.cappedTrace_le B Q n x y)
  have hmass : (∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y))=loss := by
    rw [Finset.sum_sub_distrib,C.traceMatrix_stochastic B Q hQ]
  have he0 : 0≤∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*phi y :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hdiff y) (hphi y).1)
  have he1 : (∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*phi y)≤loss := by
    calc
      _ ≤ ∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*1 :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hphi y).2 (hdiff y))
      _ = loss := by simpa only [mul_one] using hmass
  have hkeep0 : 0≤phi x*loss := mul_nonneg (hphi x).1 hloss
  have hkeep1 : phi x*loss≤loss := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hphi x).2 hloss
  have heq : C.pathExpectation (n+1) x.val (fun xs => phi (returnDefault B x xs))-
      (∑ y,C.traceMatrix B Q x y*phi y)=
      phi x*loss-∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*phi y := by
    rw [returnDefault_expectation C B Q hQ]
    simp only [sub_mul,Finset.sum_sub_distrib]
    dsimp only [loss]
    ring
  rw [heq]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem returnDefault_event_upper (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (E : FiniteChain.Inside B → Prop) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val (fun xs => eventIndicator (E (returnDefault B x xs)))≤
      (∑ y,C.traceMatrix B Q x y*eventIndicator (E y))+
        (1-∑ y,C.cappedTrace B Q n x y) := by
  have h := returnDefault_error C B Q hQ (fun y => eventIndicator (E y))
    (by intro y; by_cases he : E y <;> simp [eventIndicator,he]) n x
  have hu := (le_abs_self _).trans h
  linarith

end
end ContingencyTables.CompanionCappedReturn

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequential uniform sampling of a subset of prescribed size

The head is included with probability k/n; conditional on that choice,
the same rule is applied to the remaining coordinates. The exact mass
is k!(n-k)!/n!, matching the factorial factor in the companion lift.
-/

namespace ContingencyTables.FixedCardinalityLaw

open ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

lemma count_le {n : ℕ} (v : Fin n → Bool) : count v≤n := by
  calc
    _ ≤ ∑ _i : Fin n,1 := Finset.sum_le_sum (fun i _ => by cases v i <;> simp)
    _ = n := by simp

lemma count_decompose {n : ℕ} (v : Fin (n+1) → Bool) :
    count v=(if v 0 then 1 else 0)+count (Fin.tail v) := by
  simp only [count,Fin.sum_univ_succ,Fin.tail]
  rfl

lemma consLaw_mass {n : ℕ} (p : RationalLaw Bool) (Q : Bool → RationalLaw (Fin n → Bool))
    (v : Fin (n+1) → Bool) :
    (consLaw p Q).mass v=p.mass (v 0)*(Q (v 0)).mass (Fin.tail v) := rfl

lemma consLaw_variation {n : ℕ} (p q : RationalLaw Bool)
    (Q R : Bool → RationalLaw (Fin n → Bool)) (e : ℚ)
    (he : ∀ b,variation (Q b) (R b)≤e) :
    variation (consLaw p Q) (consLaw q R)≤variation p q+e := by
  rw [consLaw,consLaw,variation_equiv]
  exact variation_dependentJoint_uniform p q Q R e he

private lemma factorialMass_true (n k : ℕ) (hk0 : 0<k) :
    (k:ℚ)/(n+1)*factorialMass n (k-1)=factorialMass (n+1) k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk0)
  simp only [factorialMass,Nat.succ_sub_succ,Nat.sub_zero,Nat.factorial_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one]
  field_simp

private lemma factorialMass_false (n k : ℕ) (hk : k≤n) :
    (1-(k:ℚ)/(n+1))*factorialMass n k=factorialMass (n+1) k := by
  have hs : n+1-k=(n-k)+1 := by omega
  simp only [factorialMass,hs,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [Nat.cast_sub hk]
  field_simp
  ring

/-- Each vector of the requested size has the reciprocal-binomial
mass, and all other vectors have mass zero. -/
theorem fixedLaw_mass (n k : ℕ) (hk : k≤n) (v : Fin n → Bool) :
    (fixedLaw n k).mass v=if count v=k then factorialMass n k else 0 := by
  induction n generalizing k with
  | zero =>
    have hk0 : k=0 := by omega
    subst k
    have hv : v=(fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    subst v
    simp [fixedLaw,pointLaw,count,factorialMass]
  | succ n ih =>
    rw [fixedLaw,consLaw_mass]
    have hcount := count_decompose v
    cases hb : v 0 with
    | false =>
      simp only [hb,Bool.false_eq_true,ite_false,zero_add] at hcount
      by_cases hkn : k≤n
      · rw [show remaining n k false=k by simp [remaining,min_eq_left hkn],ih k hkn]
        have hp : (headLaw n k).mass false=1-(k:ℚ)/(n+1) := by
          simp [headLaw,bernoulli,headProbability,min_eq_left hk]
        rw [hp]
        by_cases hc : count (Fin.tail v)=k
        · simp only [hcount,hc,ite_true, if_true]
          exact factorialMass_false n k hkn
        · simp only [hc,ite_false,mul_zero,hcount]
      · have hke : k=n+1 := by omega
        subst k
        have hp : (headLaw n (n+1)).mass false=0 := by
          simp [headLaw,bernoulli,headProbability,show (n:ℚ)+1≠0 by positivity]
        rw [hp,zero_mul]
        have hc : count v≠n+1 := by rw [hcount]; have := count_le (Fin.tail v); omega
        simp [hc]
    | true =>
      simp only [hb,ite_true, if_true] at hcount
      by_cases hk0 : k=0
      · subst k
        have hp : (headLaw n 0).mass true=0 := by simp [headLaw,bernoulli,headProbability]
        rw [hp,zero_mul]
        have hc : count v≠0 := by omega
        simp [hc]
      · have hkpos : 0<k := Nat.pos_of_ne_zero hk0
        have hr : k-1≤n := by omega
        rw [show remaining n k true=k-1 by simp [remaining],ih (k-1) hr]
        have hp : (headLaw n k).mass true=(k:ℚ)/(n+1) := by
          simp [headLaw,bernoulli,headProbability,min_eq_left hk]
        rw [hp]
        by_cases hc : count (Fin.tail v)=k-1
        · have hc' : count v=k := by omega
          simp only [hc,hc',ite_true, if_true]
          exact factorialMass_true n k hkpos
        · have hc' : count v≠k := by omega
          simp only [hc,hc',ite_false,mul_zero]

end
end ContingencyTables.FixedCardinalityLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityBits
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Boolean implementation of fixed-cardinality subset draws -/

namespace ContingencyTables.FixedCardinalityBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits FixedCardinalityLaw
open scoped BigOperators Classical
noncomputable section

lemma roundedHead_true (B n k : ℕ) :
    (roundedHeadLaw B n k).mass true=rationalThresholdMass B (headProbability n k) := by
  have hword := FiniteLawMoments.word_expectation (headDraw B n k)
    (fun b => if b then (1:ℝ) else 0)
  have hfun : (fun bits : Fin B → Bool => if headDraw B n k bits then (1:ℝ) else 0)=
      (fun bits => if rationalThresholdAccept B (headProbability n k) bits then (1:ℝ) else 0) := by
    funext bits
    simp [headDraw]
  rw [hfun] at hword
  have ht := rationalThreshold_expectation B (headProbability n k)
    (headProbability_bounds n k).1 (headProbability_bounds n k).2
  have he := hword.symm.trans ht
  have hc : ((roundedHeadLaw B n k).mass true:ℝ)=
      (rationalThresholdMass B (headProbability n k):ℝ) := by
    simpa [FiniteLawMoments.expectation,Fintype.sum_bool,roundedHeadLaw] using he
  exact_mod_cast hc

private lemma bool_variation (p q : RationalLaw Bool) :
    variation p q=|p.mass true-q.mass true| := by
  have hp := p.total
  have hq := q.total
  rw [Fintype.sum_bool] at hp hq
  have hf : p.mass false-q.mass false= -(p.mass true-q.mass true) := by linarith
  unfold variation
  rw [Fintype.sum_bool,hf,abs_neg]
  ring

theorem roundedHead_error (B n k : ℕ) :
    variation (roundedHeadLaw B n k) (headLaw n k)≤1/(2:ℚ)^B := by
  rw [bool_variation,roundedHead_true]
  change |rationalThresholdMass B (headProbability n k)-headProbability n k|≤_
  have he := rationalThreshold_error B (headProbability n k) (headProbability_bounds n k).1
  rw [abs_of_nonpos (sub_nonpos.mpr he.2.1)]
  linarith [he.2.2]

theorem roundedFixed_error (B n k : ℕ) :
    variation (roundedFixedLaw B n k) (fixedLaw n k)≤(n:ℚ)/(2:ℚ)^B := by
  induction n generalizing k with
  | zero => simp [roundedFixedLaw,fixedLaw,variation]
  | succ n ih =>
    change variation (consLaw (roundedHeadLaw B n k) _)
      (consLaw (headLaw n k) _)≤_
    have hh := consLaw_variation (roundedHeadLaw B n k) (headLaw n k)
      (fun b => roundedFixedLaw B n (remaining n k b))
      (fun b => fixedLaw n (remaining n k b)) ((n:ℚ)/(2:ℚ)^B)
      (fun b => ih (remaining n k b))
    calc
      _ ≤ variation (roundedHeadLaw B n k) (headLaw n k)+(n:ℚ)/(2:ℚ)^B := hh
      _ ≤ 1/(2:ℚ)^B+(n:ℚ)/(2:ℚ)^B :=
        _root_.add_le_add (roundedHead_error B n k) le_rfl
      _ = _ := by push_cast; ring

private theorem consWordLaw {W V : Type*} [Fintype W] [Fintype V]
    [Nonempty W] [Nonempty V] {n : ℕ} (f : W → Bool)
    (g : Bool → V → (Fin n → Bool)) :
    mapLaw (productLaw (uniformLaw (α := W)) (uniformLaw (α := V)))
      (fun ab => Fin.cons (f ab.1) (g (f ab.1) ab.2))=
    consLaw (mapLaw (uniformLaw (α := W)) f)
      (fun b => mapLaw (uniformLaw (α := V)) (g b)) := by
  change mapLaw _ (fun ab : W×V => consEquiv n (⟨f ab.1,g (f ab.1) ab.2⟩ :
    (_b : Bool) × (Fin n → Bool)))=_
  rw [mapLaw_equiv_output,mapLaw_dependent_product]
  rfl

theorem draw_law (B n k : ℕ) :
    mapLaw (uniformLaw (α := Fin n → Fin B → Bool)) (draw B n k)=
      roundedFixedLaw B n k := by
  induction n generalizing k with
  | zero =>
    apply RationalLaw.ext
    funext v
    simp [draw,roundedFixedLaw,mapLaw,uniformLaw,uniformMass,pointLaw,eq_comm]
  | succ n ih =>
    let E := Fin.consEquiv (fun _ : Fin (n+1) => Fin B → Bool)
    have he := map_equiv E
      (uniformLaw (α := (Fin B → Bool)×(Fin n → Fin B → Bool))) (draw B (n+1) k)
    rw [uniform_equiv,←uniform_product] at he
    have hf : (fun ab => draw B (n+1) k (E ab))=
        (fun ab => Fin.cons (headDraw B n k ab.1)
          (draw B n (remaining n k (headDraw B n k ab.1)) ab.2)) := by
      funext ab
      simp only [draw,E,Fin.consEquiv,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons]
    rw [hf] at he
    have hc := consWordLaw (headDraw B n k)
      (fun b => draw B n (remaining n k b))
    have htail :
        (fun b => mapLaw (uniformLaw (α := Fin n → Fin B → Bool))
          (draw B n (remaining n k b)))=
        (fun b => roundedFixedLaw B n (remaining n k b)) := by
      funext b
      exact ih (remaining n k b)
    rw [htail] at hc
    exact he.trans hc

theorem bitDraw_law (B n k : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*B) → Bool)) (bitDraw B n k)=
      roundedFixedLaw B n k := by
  have he := map_equiv (blockWords n B)
    (uniformLaw (α := Fin (n*B) → Bool)) (draw B n k)
  rw [uniform_equiv] at he
  exact he.symm.trans (draw_law B n k)

end
end ContingencyTables.FixedCardinalityBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityMixture
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform-size mixture realizes the initial factorial weights

A size is drawn uniformly from 0,...,n, followed by the sequential
fixed-cardinality draw. Its subset mass is the literal local factorial
weight divided by n+1. The bounded Boolean implementation uses a fresh
word for the size and for each inclusion decision.
-/

namespace ContingencyTables.FixedCardinalityMixture

open ResidualMixture FirstSuccess FairBits FixedCardinalityLaw FixedCardinalityBits
open scoped BigOperators Classical
noncomputable section

theorem sizeMixture_mass (n : ℕ) (v : Fin n → Bool) :
    (sizeMixture n).mass v=factorialMass n (count v)/(n+1) := by
  let k₀ : Fin (n+1) := ⟨count v,Nat.lt_succ_of_le (count_le v)⟩
  have hiff (k : Fin (n+1)) : count v=k.val ↔ k=k₀ := by
    constructor
    · intro h; apply Fin.ext; exact h.symm
    · intro h; subst k; rfl
  change (∑ k : Fin (n+1),(uniformLaw (α := Fin (n+1))).mass k*
    (fixedLaw n k.val).mass v)=_
  simp_rw [fixedLaw_mass n _ (Nat.le_of_lt_succ (Fin.isLt _)) v,hiff]
  simp [uniformLaw,uniformMass,k₀,mul_comm,div_eq_mul_inv]

lemma count_subset_inverse (n : ℕ) (S : Finset (Fin n)) :
    count ((subsetEquiv n).symm S)=S.card := by
  change (∑ i : Fin n,if decide (i∈S) then 1 else 0)=S.card
  simp only [decide_eq_true_eq]
  rw [←Finset.sum_filter]
  simp

theorem localLaw_mass (n : ℕ) (S : Finset (Fin n)) :
    (localLaw n).mass S=factorialMass n S.card/(n+1) := by
  change (sizeMixture n).mass ((subsetEquiv n).symm S)=_
  rw [sizeMixture_mass,count_subset_inverse]

theorem localLaw_mass_cast (n : ℕ) (S : Finset (Fin n)) :
    ((localLaw n).mass S:ℝ)=InitialLocalChoices.localWeight n 0 0 S/(n+1) := by
  rw [localLaw_mass]
  simp [factorialMass,InitialLocalChoices.localWeight,Rat.cast_div,Rat.cast_mul]

lemma uniformInt_eq (n : ℕ) :
    uniformIntLaw (n+1) (Nat.succ_pos n)=uniformLaw (α := Fin (n+1)) := by
  apply RationalLaw.ext
  funext k
  simp [uniformIntLaw,uniformLaw,uniformMass]

theorem roundedSizeMixture_error (B n : ℕ) :
    variation (roundedSizeMixture B n) (sizeMixture n)≤
      (n+1:ℚ)/(2*(2:ℚ)^B)+(n:ℚ)/(2:ℚ)^B := by
  have h := variation_bind_uniform
    (scaledLaw (n+1) B (Nat.succ_pos n)) (uniformLaw (α := Fin (n+1)))
    (fun k => roundedFixedLaw B n k.val) (fun k => fixedLaw n k.val)
    ((n:ℚ)/(2:ℚ)^B) (fun k => roundedFixed_error B n k.val)
  have hs := scaledLaw_variation (n+1) B (Nat.succ_pos n)
  rw [uniformInt_eq] at hs
  have hs' : variation (scaledLaw (n+1) B (Nat.succ_pos n)) (uniformLaw (α := Fin (n+1)))≤
      (n+1:ℚ)/(2*(2:ℚ)^B) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hs
  exact h.trans (_root_.add_le_add hs' le_rfl)

theorem vectorDraw_law (B n : ℕ) :
    mapLaw (uniformLaw (α := Fin (drawBits B n) → Bool)) (vectorDraw B n)=
      roundedSizeMixture B n := by
  let drawSize := scaledBitInteger (n+1) B (Nat.succ_pos n)
  let finish (k : Fin (n+1)) := bitDraw B n k.val
  have he := map_equiv (splitWordEquiv B (n*B))
    (uniformLaw (α := Fin (B+n*B) → Bool))
    (fun words => finish (drawSize words.1) words.2)
  rw [uniform_equiv,←uniform_product] at he
  have hb := mapLaw_product_finish (uniformLaw (α := Fin B → Bool))
    (uniformLaw (α := Fin (n*B) → Bool)) drawSize finish
  have hsize : mapLaw (uniformLaw (α := Fin B → Bool)) drawSize=
      scaledLaw (n+1) B (Nat.succ_pos n) := scaledBitIntegerLaw_eq _ _ _
  have hfinish : (fun k => mapLaw (uniformLaw (α := Fin (n*B) → Bool)) (finish k))=
      (fun k : Fin (n+1) => roundedFixedLaw B n k.val) := by
    funext k
    exact bitDraw_law B n k.val
  rw [hsize,hfinish] at hb
  exact he.symm.trans hb

theorem subsetDraw_error (B n : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (drawBits B n) → Bool)) (subsetDraw B n))
      (localLaw n)≤(n+1:ℚ)/(2*(2:ℚ)^B)+(n:ℚ)/(2:ℚ)^B := by
  have he := mapLaw_equiv_output (subsetEquiv n)
    (uniformLaw (α := Fin (drawBits B n) → Bool)) (vectorDraw B n)
  change variation (mapLaw _ (fun bits => subsetEquiv n (vectorDraw B n bits))) _≤_
  rw [he,vectorDraw_law,localLaw,variation_equiv]
  exact roundedSizeMixture_error B n

end
end ContingencyTables.FixedCardinalityMixture

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialFactorialLaw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent initial cell choices give the literal companion law

The finite rational law is the product of the uniform-size subset laws.
Encoding a choice as its paired transversal yields exactly the initial
law of the companion's factorial lift, with its actual free-completion
normalizer cancelled.
-/

namespace ContingencyTables.InitialFactorialLaw

open CommonBasesFPRAS ResidualMixture FirstSuccess TwoLiftStates LabelledFactorial
open InitialTransversals FixedCardinalityMixture CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {C : Type*} [Fintype C] (b : C → ℕ)

theorem choiceLaw_mass_cast (S : (c : C) → Finset (Fin (b c))) :
    ((choiceLaw b).mass S:ℝ)=
      (∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c))/(∏ c,((b c:ℝ)+1)) := by
  change ((∏ c,(localLaw (b c)).mass (S c):ℚ):ℝ)=_
  rw [Rat.cast_prod]
  simp_rw [localLaw_mass_cast]
  exact Finset.prod_div_distrib
    (fun c : C => InitialLocalChoices.localWeight (b c) 0 0 (S c))
    (fun c : C => (b c:ℝ)+1)

theorem plainLaw_mass_cast (S : {S : Set (Copy b×Bool) // PlainState pairs S}) :
    ((plainLaw b).mass S:ℝ)=
      (∏ c,InitialLocalChoices.localWeight (b c) 0 0 ((plainEquivChoices b S) c))/
        (∏ c,((b c:ℝ)+1)) :=
  choiceLaw_mass_cast b (plainEquivChoices b S)

theorem plainLaw_lift (M : ℝ) (hM : 0<M)
    (S : {S : Set (Copy b×Bool) // PlainState pairs S}) :
    ((plainLaw b).mass S:ℝ)=
      firstLift (group (cell b)) (fun _ => M) (InitialTransversals.denominator b) S.val/
        (M*∏ c,((b c:ℝ)+1)) := by
  let choices := plainEquivChoices b S
  have he : encode b choices=S.val :=
    congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply S)
  rw [←he,firstLift_encode,plainLaw_mass_cast]
  exact (mul_div_mul_left _ _ (ne_of_gt hM)).symm

variable {I J : Type*} [Fintype I] [Fintype J]

/-- No abstract initialization hypothesis: the rational product law is
the actual phase-zero law of the given bounded-table instance. -/
theorem companionLaw_mass (A : Instance I J)
    (S : {S : Set (Labels A×Bool) // PlainState pairs S}) :
    ((companionLaw A).mass S:ℝ)=CompanionWarmStart.law A 0 S.val := by
  have hM : 0<CompanionInitialization.freeTotal A := by
    apply Finset.prod_pos
    intro a _
    exact Nat.cast_pos.mpr (Nat.succ_pos _)
  have h := plainLaw_lift (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (CompanionInitialization.freeTotal A) hM S
  have hf : f A 0=firstLift (group (labelCell A))
      (fun _ => CompanionInitialization.freeTotal A)
      (CompanionFactorialApplication.denominator A) := by
    funext T
    unfold f firstLift
    rw [CompanionInitialization.h_zero]
  change ((plainLaw _).mass S:ℝ)=_
  unfold CompanionWarmStart.law CompanionWarmStart.total CompanionAnnealing.weight
  simp only [Nat.cast_zero,zero_div]
  rw [CompanionInitialization.total_zero,hf,CompanionInitialization.denominator_eq]
  exact h

end
end ContingencyTables.InitialFactorialLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialFactorialBits
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite Boolean word for the actual initial transversal

The word is split into disjoint cell blocks; each block chooses a size
and then a subset of that size. The total variation errors add before
the exact paired-transversal encoding is applied.
-/

namespace ContingencyTables.InitialFactorialBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits TwoLiftStates
open FixedCardinalityMixture InitialFactorialLaw InitialTransversals
open CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {q : ℕ}

theorem drawChoices_law (b : Fin q → ℕ) (B : ℕ) :
    mapLaw (uniformLaw (α := Fin (bitCount b B) → Bool)) (drawChoices b B)=
      piLaw (fun i => mapLaw (uniformLaw (α := Fin (drawBits B (b i)) → Bool))
        (subsetDraw B (b i))) := by
  have he := map_equiv (wordEquiv b B)
    (uniformLaw (α := Fin (bitCount b B) → Bool))
    (fun words i => subsetDraw B (b i) (words i))
  rw [uniform_equiv,←pi_uniformLaw,pi_mapLaw] at he
  exact he.symm

theorem drawChoices_error (b : Fin q → ℕ) (B : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (bitCount b B) → Bool)) (drawChoices b B))
      (piLaw (fun i => localLaw (b i)))≤
        ∑ i,((b i+1:ℚ)/(2*(2:ℚ)^B)+(b i:ℚ)/(2:ℚ)^B) := by
  rw [drawChoices_law]
  exact (variation_pi _ _ _).trans (Finset.sum_le_sum (fun i _ => subsetDraw_error B (b i)))

theorem drawChoices_error_bound (b : Fin q → ℕ) (B W : ℕ) (hb : ∀ i,b i≤W) :
    variation (mapLaw (uniformLaw (α := Fin (bitCount b B) → Bool)) (drawChoices b B))
      (piLaw (fun i => localLaw (b i)))≤(q:ℚ)*(3*W+1)/(2*(2:ℚ)^B) := by
  apply (drawChoices_error b B).trans
  calc
    _ ≤ ∑ _i : Fin q,((W+1:ℚ)/(2*(2:ℚ)^B)+(W:ℚ)/(2:ℚ)^B) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (b i:ℚ)≤W := by exact_mod_cast hb i
      exact _root_.add_le_add
        (div_le_div_of_nonneg_right (by linarith) (by positivity))
        (div_le_div_of_nonneg_right hi (by positivity))
    _ = _ := by simp; ring

variable {C : Type*} [Fintype C]

theorem choiceEquiv_law (b : C → ℕ) (e : C ≃ Fin q) :
    equivLaw (choiceEquiv b e) (piLaw (fun i => localLaw (b (e.symm i))))=choiceLaw b := by
  apply RationalLaw.ext
  funext S
  change (∏ i : Fin q,(localLaw (b (e.symm i))).mass (S (e.symm i)))=
    ∏ c,(localLaw (b c)).mass (S c)
  symm
  apply Fintype.prod_equiv e
  intro c
  exact congrArg (fun x => (localLaw (b x)).mass (S x)) (e.symm_apply_apply c).symm

theorem transversalDraw_error (b : C → ℕ) (e : C ≃ Fin q) (B W : ℕ)
    (hb : ∀ c,b c≤W) :
    variation (mapLaw (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
      (transversalDraw b e B)) (plainLaw b)≤(q:ℚ)*(3*W+1)/(2*(2:ℚ)^B) := by
  let E := (choiceEquiv b e).trans (plainEquivChoices b).symm
  have he := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
    (drawChoices (fun i => b (e.symm i)) B)
  have ht : equivLaw E (piLaw (fun i => localLaw (b (e.symm i))))=plainLaw b := by
    have hh := choiceEquiv_law b e
    apply RationalLaw.ext
    funext S
    exact congrArg (fun p => p.mass ((plainEquivChoices b) S)) hh
  change variation (mapLaw _ (fun bits => E (drawChoices _ B bits))) _≤_
  rw [he,←ht,variation_equiv]
  exact drawChoices_error_bound _ B W (fun i => hb (e.symm i))

end
end ContingencyTables.InitialFactorialBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded-word initialization of the companion trace

The output is in the literal `PlainIndex` used by the trace chain. Its
ideal rational law is exactly the source's phase-zero law; the bounded
word implementation is within 2^(-h), with an explicit word length.
-/

namespace ContingencyTables.CompanionInitialDraw

open CommonBasesFPRAS ResidualMixture FirstSuccess TwoLiftStates
open CompanionFactorialApplication InitialFactorialLaw InitialFactorialBits
open RealKernelApproximation
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem idealLaw_mass (A : Instance I J)
    (S : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    ((idealLaw A).mass S:ℝ)=CompanionWarmStart.law A 0 S.val.val :=
  companionLaw_mass A ((indexEquiv A).symm S)

lemma cellCount_bound (A : Instance I J) : Fintype.card (SmallCell A)≤A.d := by
  exact (Fintype.card_le_of_injective (fun s : SmallCell A => s.val) Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

theorem draw_error (A : Instance I J) (B : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (initialBits A B) → Bool)) (draw A B))
      (idealLaw A)≤(A.d:ℚ)*(3*A.W+1)/(2*(2:ℚ)^B) := by
  unfold draw initialBits cellCapacity
  have he := mapLaw_equiv_output (indexEquiv A)
    (uniformLaw (α := Fin (bitCount
      (fun i => A.b ((cellEnum A).symm i).val.1 ((cellEnum A).symm i).val.2) B) → Bool))
    (transversalDraw (fun s : SmallCell A => A.b s.val.1 s.val.2) (cellEnum A) B)
  rw [he,idealLaw,variation_equiv]
  have ht := transversalDraw_error (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (cellEnum A) B A.W (fun s => (A.hsmall _ _ s.property).le)
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast cellCount_bound A

lemma precision_error (A : Instance I J) (h : ℕ) :
    (A.d:ℚ)*(3*A.W+1)/(2*(2:ℚ)^precision A h)≤1/(2:ℚ)^h := by
  have hc : A.d*(3*A.W+1)≤2^Nat.clog 2 (A.d*(3*A.W+1)+1) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have hcr : (A.d:ℚ)*(3*A.W+1)≤(2:ℚ)^Nat.clog 2 (A.d*(3*A.W+1)+1) := by
    exact_mod_cast hc
  unfold precision
  rw [pow_add]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp := mul_le_mul_of_nonneg_right hcr (show 0≤(2:ℚ)^h by positivity)
  have hp0 : 0≤(2:ℚ)^Nat.clog 2 (A.d*(3*A.W+1)+1)*(2:ℚ)^h := by positivity
  nlinarith [pow_pos (by norm_num : (0:ℚ)<2) h]

/-- The implemented initial word is compared directly to the literal
phase-zero law, so later restart estimates need no initializer oracle. -/
theorem initial_distance (A : Instance I J) (h : ℕ) :
    distance (fun S => ((mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
      (draw A (precision A h))).mass S:ℝ))
      (fun S => CompanionWarmStart.law A 0 S.val.val)≤1/(2:ℝ)^h := by
  have hh := (draw_error A (precision A h)).trans (precision_error A h)
  have he : distance
      (fun S => ((mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
        (draw A (precision A h))).mass S:ℝ))
      (fun S => CompanionWarmStart.law A 0 S.val.val)=
      (variation (mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
        (draw A (precision A h))) (idealLaw A):ℝ) := by
    simp_rw [←idealLaw_mass A]
    simp only [distance,variation,Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat]
  rw [he]
  have hc : (variation (mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
      (draw A (precision A h))) (idealLaw A):ℝ)≤((1/(2:ℚ)^h:ℚ):ℝ) := Rat.cast_le.mpr hh
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hc

end
end ContingencyTables.CompanionInitialDraw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMinMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-size minimum mass of the actual companion transversal law

The factorial denominator cancels against the two complementary
factorials. The surviving binomial coefficient is bounded by 2^b,
giving the p+K exponent used in the paper's restart schedule.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat InitialLocalChoices CommonBasesFPRAS LabelledFactorial TwoLiftStates

lemma localWeight_lower (b : ℕ) (S : Finset (Fin b)) :
    (1/2:ℝ)^b ≤ localWeight b 0 0 S := by
  have hk : S.card ≤ b := by
    simpa using S.card_le_univ
  have hD : (0:ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have hF : (b.choose S.card:ℝ)*(S.card.factorial:ℝ)*((b-S.card).factorial:ℝ)=
      (b.factorial:ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hprod : (b.choose S.card:ℝ)*localWeight b 0 0 S=1 := by
    unfold localWeight
    simp only [Nat.sub_zero,Nat.add_zero]
    rw [← mul_div_assoc,← mul_assoc,hF,div_self hD.ne']
  have hlocal : 0 ≤ localWeight b 0 0 S := by
    unfold localWeight
    positivity
  have hchoose : (b.choose S.card:ℝ) ≤ (2:ℝ)^b := by
    exact_mod_cast Nat.choose_le_two_pow b S.card
  have hm := mul_le_mul_of_nonneg_right hchoose hlocal
  have hpow : (0:ℝ) < (2:ℝ)^b := by positivity
  rw [hprod] at hm
  rw [div_pow,one_pow,div_le_iff₀ hpow]
  nlinarith

variable {C : Type*} [Fintype C]

/-- On every actual paired transversal, the constant-count factorial
display is at least M times 2 to the negative number of copy labels. -/
theorem firstLift_plain_lower (b : C → ℕ) (M : ℝ) (hM : 0 ≤ M)
    (S : Set (Copy b×Bool)) (hS : PlainState pairs S) :
    M*(1/2:ℝ)^(∑ c,b c) ≤
      firstLift (group (cell b)) (fun _ => M) (denominator b) S := by
  let T := plainEquivChoices b ⟨S,hS⟩
  have he : encode b T=S := congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply ⟨S,hS⟩)
  rw [← he,firstLift_encode]
  apply mul_le_mul_of_nonneg_left _ hM
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro c _
    positivity
  · intro c _
    exact localWeight_lower (b c) (T c)

end ContingencyTables.InitialTransversals

namespace ContingencyTables.CompanionMinMass

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing CompanionInitialization
open CompanionWarmStart TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

lemma label_card (A : Instance I J) :
    Fintype.card (Labels A)=∑ s : SmallCell A,A.b s.val.1 s.val.2 := by
  simp [Labels,Fintype.card_sigma]

lemma initial_weight_lower (A : Instance I J) (S : Set (Labels A×Bool))
    (hS : PlainState pairs S) :
    freeTotal A*(1/2:ℝ)^Fintype.card (Labels A) ≤ weight A 0 S := by
  have hM : (0:ℝ) ≤ freeTotal A :=
    (Finset.prod_pos (fun _ _ => Nat.cast_pos.mpr (Nat.succ_pos _))).le
  have hh := InitialTransversals.firstLift_plain_lower
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (freeTotal A) hM S hS
  rw [← label_card] at hh
  unfold weight f firstLift
  simp only [Nat.cast_zero,zero_div]
  rw [denominator_eq]
  rw [h_zero]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

end ContingencyTables.CompanionMinMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTrace
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace restart bounds for the literal companion weights

The actual factorial lifts supply the trace inverse gap, and exact
binomial cancellation supplies its minimum mass. The restart stage
therefore has a two-warm endpoint from every initial subprobability law.
-/

namespace ContingencyTables.CompanionTrace

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing TwoLiftStates
open CompanionConcentration BinaryContraction DegreeCompletion TraceBounds ObservableBounds

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma restart_exponential (M : ℕ) :
    Real.exp (-2*((M:ℝ)+5))/(1/2:ℝ)^M ≤ 1 := by
  have h2 : (2:ℝ) ≤ Real.exp 2 := by
    linarith [Real.add_one_le_exp (2:ℝ)]
  have he : Real.exp (-2:ℝ) ≤ 1/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) h2
  have hp := pow_le_pow_left₀ (Real.exp_nonneg (-2)) he M
  have h10 : Real.exp (-10:ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hid : Real.exp (-2*((M:ℝ)+5))=Real.exp (-2:ℝ)^M*Real.exp (-10:ℝ) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  rw [hid,div_le_one (by positivity : (0:ℝ) < (1/2:ℝ)^M)]
  exact (mul_le_of_le_one_right (pow_nonneg (Real.exp_nonneg _) _) h10).trans hp

lemma integerConstant_cast (A : Instance I J) :
    (integerConstant A:ℝ)=observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
  unfold integerConstant observableConstant
  push_cast
  ring

lemma minimumMass_positive (A : Instance I J) (H K : ℕ) : 0 < minimumMass A H K := by
  unfold minimumMass
  positivity

/-- The manuscript's literal integer restart schedule gives pointwise
relative error at most one with the proved minimum mass. -/
theorem schedule_error (A : Instance I J) (H K : ℕ)
    (hp : 0 < Fintype.card (Labels A)) :
    Real.exp (-(time A H K:ℝ)/observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))/
      minimumMass A H K ≤ 1 := by
  have hpR : (0:ℝ) < Fintype.card (Labels A) := by exact_mod_cast hp
  have hp1 : (1:ℝ) ≤ Fintype.card (Labels A) := by exact_mod_cast hp
  have hbound := observableConstant_lower (Fintype.card (Labels A)) ((A.W:ℝ)^2)
    hp1 (square_width_one_le A)
  have hconst : 0 < observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) :=
    lt_of_lt_of_le (by positivity) hbound
  have hexp : -(time A H K:ℝ)/observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)=
      -2*((H+Fintype.card (Labels A)+K:ℕ)+5:ℝ) := by
    unfold time
    push_cast
    rw [integerConstant_cast]
    field_simp [hconst.ne']
  rw [hexp]
  exact restart_exponential (H+Fintype.card (Labels A)+K)

end ContingencyTables.CompanionTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTargetMixing
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing of the literal dyadic trace

The original and degree-completed state chains agree. Their traces
therefore agree as well, and the dyadic holding factor costs at most
two in the trace Poincare estimate.
-/

namespace ContingencyTables.CompanionTargetMixing

open CommonBasesFPRAS CompanionFactorialApplication CompanionBooleanPhase
open CompanionTraceWords CompanionConcentration
open CompanionAnnealing CompanionWarmStart CompanionRationalUpdates TwoLiftStates
open DegreeCompletion ObservableBounds
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem restart_schedule (A : Instance I J) (H K : ℕ) (hp : 0<Fintype.card (Labels A)) :
    Real.exp (-(restartTime A H K:ℝ)/
      (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)))/
        CompanionTrace.minimumMass A H K≤1 := by
  have he : -(restartTime A H K:ℝ)/
      (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))=
      -(CompanionTrace.time A H K:ℝ)/
        observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
    unfold restartTime
    push_cast
    rw [show -(2*(CompanionTrace.time A H K:ℝ))=2*(-(CompanionTrace.time A H K:ℝ)) by ring]
    exact mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)
  rw [he]
  exact CompanionTrace.schedule_error A H K hp

end
end ContingencyTables.CompanionTargetMixing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteVaryingWordWalk
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent words for successive draws with varying widths -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits
noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem varyingWalk_law (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X) (x : X) (n : ℕ) :
    mapLaw (uniformLaw (α := VaryingWords width n)) (varyingWalk width step x n)=
      varyingLaw width step (pointLaw x) n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext y
    simp [varyingWalk,varyingLaw,pointLaw,mapLaw,uniformLaw,uniformMass,eq_comm]
  | succ n ih =>
    let E : (VaryingWords width n × (Fin (width n) → Bool)) ≃ VaryingWords width (n+1) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun i : Fin (n+1) => Fin (width i.val) → Bool))
    have hc : varyingWalk width step x (n+1) ∘ E=
        fun ab => step n (varyingWalk width step x n ab.1) ab.2 := by
      funext ab
      rcases ab with ⟨pref,last⟩
      change step n (varyingWalk width step x n (Fin.init
        (Fin.snoc (α := fun i : Fin (n+1) => Fin (width i.val) → Bool) pref last)))
        ((Fin.snoc (α := fun i : Fin (n+1) => Fin (width i.val) → Bool) pref last)
          (Fin.last n))=_
      simp only [Fin.init_snoc,Fin.snoc_last]
    apply RationalLaw.ext
    funext y
    change (mapLaw (uniformLaw (α := VaryingWords width (n+1)))
      (varyingWalk width step x (n+1))).mass y=
      (bindLaw (varyingLaw width step (pointLaw x) n)
        (fun z => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n z))).mass y
    rw [←ih]
    simp only [bindLaw,uniform_map_mass]
    have he := uniformMapMass_equiv E (varyingWalk width step x (n+1)) y
    rw [hc] at he
    rw [←he]
    exact uniformMapMass_prod (varyingWalk width step x n) (step n) y

omit [DecidableEq X] in
private lemma bindLaw_associative (p : RationalLaw X) (q r : X → RationalLaw X) :
    bindLaw (bindLaw p q) r=bindLaw p (fun x => bindLaw (q x) r) := by
  apply RationalLaw.ext
  funext z
  simp only [bindLaw,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem varyingLaw_start (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X)
    (p : RationalLaw X) (n : ℕ) :
    bindLaw p (fun x => varyingLaw width step (pointLaw x) n)=varyingLaw width step p n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext y
    simp [varyingLaw,bindLaw,pointLaw]
  | succ n ih =>
    change bindLaw p (fun x => bindLaw (varyingLaw width step (pointLaw x) n)
      (fun z => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n z)))=
      bindLaw (varyingLaw width step p n)
        (fun z => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n z))
    rw [←ih,bindLaw_associative]

/-- The flattened word consumes exactly the sum of the successive
widths, including unused bits on any branch of the deterministic draws. -/
theorem flatVaryingWalk_law (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X) (x : X) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (∑ i : Fin n,width i.val) → Bool))
      (fun bits => varyingWalk width step x n (varyingWordEquiv width n bits))=
      varyingLaw width step (pointLaw x) n := by
  have he := map_equiv (varyingWordEquiv width n)
    (uniformLaw (α := Fin (∑ i : Fin n,width i.val) → Bool)) (varyingWalk width step x n)
  rw [uniform_equiv] at he
  exact he.symm.trans (varyingWalk_law width step x n)

end
end ContingencyTables.FirstSuccess

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root physical marginal is its literal completion count -/

namespace ContingencyTables.RootedCountIdentification

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty RootedLiteralCount
open ForestCountIdentification ForestAssignmentSplit ForestLiteralCount
open PhysicalLargeProfiles LargePairEnumeration BalancedBox GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

theorem h_zero (A : Instance I J) (S : Selection A.T) (z : View A → ℕ) :
    h A S 0 z=∏ a : FreeCell A.small A.T,((A.b a.val.1 a.val.2+1:ℕ):ℝ) := by
  simp [h,Fintype.card_pi,Nat.cast_prod]

end ContingencyTables.RootedCountIdentification

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
open CompanionAnnealing (scale scale_positive )
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

end ContingencyTables.RootedAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWarmStart
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual companion transversal masses and adjacent warm starts -/

namespace ContingencyTables.RootedWarmStart

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open CompanionInitialization (freeTotal)
open TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The initial factorial weight is independent of the selected root. -/
lemma zero_weight_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    weight A R 0=CompanionAnnealing.weight A 0 := by
  funext S
  unfold weight CompanionAnnealing.weight
  simp only [Nat.cast_zero,zero_div]
  unfold RootedFactorialApplication.f CompanionFactorialApplication.f firstLift
  rw [RootedCountIdentification.h_zero,CompanionInitialization.h_zero]
  rfl

lemma total_zero (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    slotTotal pairs (weight A R 0) ∅=
      freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) := by
  rw [zero_weight_eq]
  simpa only [CompanionAnnealing.weight,Nat.cast_zero,zero_div] using
    CompanionInitialization.total_zero A

lemma total_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) : 0< total A R j :=
  slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh

private lemma free_positive (A : Instance I J) : 0< freeTotal A := by
  apply Finset.prod_pos
  intro a _
  exact Nat.cast_pos.mpr (Nat.succ_pos _)

/-- The exact phase-j transversal law is two-warm for phase j+1.
The statement applies in particular to every actual paired transversal. -/
theorem law_adjacent (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    law A R j S≤2*law A R (j+1) S := by
  have hS := weight_adjacent A R j S
  have hT := total_adjacent A R j pairs ∅
  have h0 := total_positive A R j
  have h1 := total_positive A R (j+1)
  have hweight := weight_positive A R j S
  unfold law
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ h0 h1).mpr
  unfold total at *
  nlinarith [mul_le_mul_of_nonneg_left hT.2 hweight.le,
    mul_le_mul_of_nonneg_right hS.1 h0.le]

theorem weight_bounds_zero (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    (1/2:ℝ)^j*weight A R 0 S≤ weight A R j S ∧ weight A R j S≤ weight A R 0 S := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := weight_adjacent A R j S
    constructor
    · rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left ih.1 (show (0:ℝ)≤1/2 by norm_num)]
    · exact h.2.trans ih.2

theorem total_bounds_zero (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) :
    (1/2:ℝ)^j*total A R 0≤ total A R j ∧ total A R j≤ total A R 0 := by
  unfold total
  constructor
  · rw [← slotTotal_scale]
    exact slotTotal_mono _ _ _ (fun S => (weight_bounds_zero A R j S).1) _
  · exact slotTotal_mono _ _ _ (fun S => (weight_bounds_zero A R j S).2) _

/-- The existing executed initializer is exactly the selected-root phase-zero law. -/
lemma law_zero_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (S : Set (Labels A×Bool)) :
    law A R 0 S=CompanionWarmStart.law A 0 S := by
  unfold law total CompanionWarmStart.law CompanionWarmStart.total
  rw [zero_weight_eq]

theorem initial_distance (A : Instance I J) (R : RootedCompletion.Selection A.T) (h : ℕ) :
    RealKernelApproximation.distance
      (fun S => ((FirstSuccess.mapLaw
        (FirstSuccess.uniformLaw (α := Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A h)) → Bool))
        (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h))).mass S:ℝ))
      (fun S => law A R 0 S.val.val)≤1/(2:ℝ)^h := by
  simp_rw [law_zero_eq]
  exact CompanionInitialDraw.initial_distance A h

lemma initial_weight_lower (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (S : Set (Labels A×Bool)) (hS : PlainState pairs S) :
    freeTotal A*(1/2:ℝ)^Fintype.card (Labels A)≤ weight A R 0 S := by
  rw [zero_weight_eq]
  exact CompanionMinMass.initial_weight_lower A S hS

/-- The sharp source minimum mass uses only the original bounded-cell label count. -/
theorem plain_law_lower (A : Instance I J) (R : RootedCompletion.Selection A.T) (K j : ℕ)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^K)
    (S : Set (Labels A×Bool)) (hS : PlainState pairs S) :
    (1/2:ℝ)^(j+Fintype.card (Labels A)+K)≤ law A R j S := by
  have hM := free_positive A
  have hT := (total_bounds_zero A R j).2
  have hT0 : total A R 0=freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) :=
    total_zero A R
  rw [hT0] at hT
  have hupper : total A R j≤ freeTotal A*(2:ℝ)^K :=
    hT.trans (mul_le_mul_of_nonneg_left hB hM.le)
  have hw := (weight_bounds_zero A R j S).1
  have hi := initial_weight_lower A R S hS
  have hlower : freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A))≤ weight A R j S := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hi (show (0:ℝ)≤(1/2:ℝ)^j by positivity)]
  have hpos := total_positive A R j
  unfold law
  rw [le_div_iff₀ hpos,pow_add]
  have hm := mul_le_mul_of_nonneg_left hupper
    (show (0:ℝ)≤(1/2:ℝ)^(j+Fintype.card (Labels A))*(1/2:ℝ)^K by positivity)
  have hcancel : (1/2:ℝ)^K*(2:ℝ)^K=1 := by
    rw [←mul_pow]
    norm_num
  have he : ((1/2:ℝ)^(j+Fintype.card (Labels A))*(1/2:ℝ)^K)*
      (freeTotal A*(2:ℝ)^K)=freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A)) := by
    calc
      _=freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A))*
          ((1/2:ℝ)^K*(2:ℝ)^K) := by ring
      _=_ := by rw [hcancel,mul_one]
  rw [he] at hm
  exact hm.trans hlower

end ContingencyTables.RootedWarmStart

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCappedReturn
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root capped returns with their literal fallback -/

namespace ContingencyTables.RootedCappedReturn

open CommonBasesFPRAS RootedBooleanPhase RootedTraceWords
open CompanionFactorialApplication CompanionOracleDensity CompanionRationalUpdates
open CompanionBooleanPhase (State stepBits)
open CompanionCappedReturn (returnDefault returnDefault_event_upper)
open CompanionTraceWords (eventIndicator firstHit)
open CompanionPhaseTrajectory (historyPrefix)
open FirstSuccess RealKernelApproximation TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

private theorem returnWordDefault_to_path (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (returnWordDefault A R C K j k n hK hW xi v w S bits)))≤
      (targetChain A R j hp w hw).pathExpectation (n+1) S.val
        (fun xs => eventIndicator (E (returnDefault (plainPredicate pairs) S xs)))+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  exact arithmetic_recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw (n+1) S.val
    (fun xs => E (returnDefault (plainPredicate pairs) S xs))

private theorem target_returnDefault_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (n : ℕ)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    (targetChain A R j hp w hw).pathExpectation (n+1) S.val
      (fun xs => eventIndicator (E (returnDefault (plainPredicate pairs) S xs)))≤
      (∑ T,(targetChain A R j hp w hw).traceMatrix (plainPredicate pairs)
        (targetKilled A R j hp w hw) S T*eventIndicator (E T))+
      (1-∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A R j hp w hw) n S T) := by
  exact returnDefault_event_upper (targetChain A R j hp w hw) (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw) E n S

/-- The implemented total return step is compared to the exact trace,
with its cap loss left explicit for subsequent warm-law averaging. -/
theorem returnWordDefault_event (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (returnWordDefault A R C K j k n hK hW xi v w S bits)))≤
      (∑ T,(targetChain A R j hp w hw).traceMatrix (plainPredicate pairs)
        (targetKilled A R j hp w hw) S T*eventIndicator (E T))+
      (1-∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A R j hp w hw) n S T)+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  have he := returnWordDefault_to_path A R C hC K j k n hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw S E
  have ht := target_returnDefault_bound A R j hp w hw n S E
  have hb := _root_.add_le_add ht
    (le_refl (((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)))
  exact he.trans hb

end
end ContingencyTables.RootedCappedReturn

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_WarmKernelIteration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeating an implementation bound averaged under the exact warm law -/

namespace ContingencyTables.WarmKernelIteration

open CommonBasesFPRAS RealKernelApproximation
open scoped BigOperators Classical

noncomputable section
variable {X : Type*} [Fintype X]

/-- At every replacement step the reference distribution remains warm.
No warmness assumption is imposed on the implemented distribution. -/
theorem power_distance (C : FiniteChain X) (K : FiniteKernel X X)
    (nu : X → ℝ) (hnu : ∀ x,0≤nu x) (hmass : ∑ x,nu x≤1)
    (U e : ℝ) (hwarm : ∀ x,nu x≤U*C.π x)
    (hstep : ∀ rho : X → ℝ,(∀ x,0 ≤ rho x) → (∑ x,rho x≤1) →
      (∀ x,rho x≤U*C.π x) → distance (K.push rho) (C.kernel.push rho)≤e)
    (n : ℕ) :
    distance ((K.power n).push nu) ((C.kernel.power n).push nu)≤n*e := by
  induction n with
  | zero => simp [FiniteKernel.power,FiniteKernel.push_identity,distance]
  | succ n ih =>
    let p := (K.power n).push nu
    let q := (C.kernel.power n).push nu
    have hq0 : ∀ x,0≤q x := (C.kernel.power n).push_nonneg nu hnu
    have hq1 : ∑ x,q x≤1 := by
      dsimp only [q]
      rw [C.power_push_mass]
      exact hmass
    have hqwarm : ∀ x,q x≤U*C.π x := C.power_warm n nu U hwarm
    have ht := distance_triangle (K.push p) (K.push q) (C.kernel.push q)
    have hc := distance_push K p q
    have hs := hstep q hq0 hq1 hqwarm
    rw [FiniteKernel.power_push_succ,FiniteKernel.power_push_succ]
    change distance (K.push p) (C.kernel.push q)≤_
    have hh : distance (K.push p) (C.kernel.push q)≤distance p q+e := by linarith
    exact hh.trans (by dsimp only [p,q]; push_cast; linarith)

end
end ContingencyTables.WarmKernelIteration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTargetTrace
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root dyadic trace return and explicit warm cap estimates -/

namespace ContingencyTables.RootedTargetTrace

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTraceWords
open CompanionCappedReturn RootedAnnealing RootedWarmStart TwoLiftStates
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem insideMass_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q) :
    (targetChain A R j hp w hw).insideMass (plainPredicate pairs)=
      total A R j/chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j) := by
  exact metropolis_insideMass pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j)

theorem actualTrace_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    (actualTrace A R j hp w hw).π S=law A R j S.val.val := by
  have h := metropolisTrace_pi pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j) S
  exact h

theorem insideMass_lower (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ))) :
    1/(5*(Fintype.card (Labels A):ℝ)^2)≤
      (targetChain A R j hp w hw).insideMass (plainPredicate pairs) := by
  rw [insideMass_eq]
  have h := plain_mass_lower pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j) hgood.upper
  simpa only [PairedLabels.length,RootedWarmStart.total] using h

end
end ContingencyTables.RootedTargetTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTrace
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace restart bounds for the selected-root companion weights

The actual factorial lifts supply the trace inverse gap, and exact
binomial cancellation supplies its minimum mass. The restart stage
therefore has a two-warm endpoint from every initial subprobability law.
-/

namespace ContingencyTables.RootedTrace

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing TwoLiftStates
open CompanionAnnealing (scale scale_positive)
open CompanionTrace (integerConstant time minimumMass minimumMass_positive schedule_error)
open BinaryContraction DegreeCompletion TraceBounds ObservableBounds
open RootedWarmStart (actual_degree)
open CompanionConcentration (pairs_ne_nil square_width_one_le)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma trace_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0 < w p r) (S : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    (trace A R j hp w hw).π S=RootedWarmStart.law A R j S.val.val := by
  exact completed_trace_pi pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w
    (weight A R j) hw (actual_degree A R j).1 S

lemma trace_minimum (A : Instance I J) (R : RootedCompletion.Selection A.T) (H K j : ℕ) (hj : j ≤ H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^K)
    (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0 < w p r) (S : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    minimumMass A H K ≤ (trace A R j hp w hw).π S := by
  rw [trace_pi]
  apply le_trans _ (RootedWarmStart.plain_law_lower A R K j hB S.val.val S.property)
  exact pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) (by omega)

end ContingencyTables.RootedTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTargetMixing
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root dyadic trace mixing and warm restart schedule -/

namespace ContingencyTables.RootedTargetMixing

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTargetTrace
open RootedTraceWords RootedAnnealing RootedWarmStart CompanionRationalUpdates TwoLiftStates
open DegreeCompletion ObservableBounds
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil square_width_one_le)
open CompanionTargetMixing (restartTime restart_schedule)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem target_point_mixing (A : Instance I J) (R : RootedCompletion.Selection A.T) (H K j : ℕ) (hj : j≤H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^K)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ))) (t : ℕ)
    (x y : PlainIndex (pairs : List (Pair A))) :
    |((RootedTargetTrace.actualTrace A R j hp w hw).kernel.power t).P x y/
      law A R j y.val.val-1|≤
        Real.exp (-(t:ℝ)/(2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)))/
          CompanionTrace.minimumMass A H K := by
  have hpR : (1:ℝ)≤Fintype.card (Labels A) := by exact_mod_cast hp
  have hK : 1≤2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
    have hh := observableConstant_lower (Fintype.card (Labels A)) ((A.W:ℝ)^2)
      hpR (square_width_one_le A)
    have hp5 : (1:ℝ)≤(Fintype.card (Labels A):ℝ)^5 := one_le_pow₀ hpR
    linarith
  have hmin (S : PlainIndex (pairs : List (Pair A))) :
      CompanionTrace.minimumMass A H K≤(RootedTargetTrace.actualTrace A R j hp w hw).π S := by
    rw [actualTrace_pi]
    have hh := RootedTrace.trace_minimum A R H K j hj hB hp
      (fun p q => (w p q:ℝ)) (fun p q => by exact_mod_cast hw p q) S
    rw [RootedTrace.trace_pi] at hh
    exact hh
  have hh := (RootedTargetTrace.actualTrace A R j hp w hw).kernel_point_mixing
    (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))
    (CompanionTrace.minimumMass A H K) hK (CompanionTrace.minimumMass_positive A H K)
    hmin (targetTrace_poincare A R j hp w hw hgood) t x y
  rwa [actualTrace_pi] at hh

/-- The exact dyadic trace reaches the required two-warm law at the
explicit doubled schedule, including subprobability incoming laws. -/
theorem restart_warm (A : Instance I J) (R : RootedCompletion.Selection A.T) (H K j : ℕ) (hj : j≤H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^K)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : PlainIndex (pairs : List (Pair A)) → ℝ) (hnu : ∀ S,0≤nu S)
    (hmass : ∑ S,nu S≤1) (y : PlainIndex (pairs : List (Pair A))) :
    ((RootedTargetTrace.actualTrace A R j hp w hw).kernel.power (restartTime A H K)).push nu y≤
      2*law A R j y.val.val := by
  have hy : 0<law A R j y.val.val :=
    div_pos (weight_positive A R j _) (total_positive A R j)
  have hrow (x : PlainIndex (pairs : List (Pair A))) :
      ((RootedTargetTrace.actualTrace A R j hp w hw).kernel.power (restartTime A H K)).P x y≤
        2*law A R j y.val.val := by
    have hh := (le_abs_self _).trans
      ((target_point_mixing A R H K j hj hB hp w hw hgood (restartTime A H K) x y).trans
        (restart_schedule A H K hp))
    apply (div_le_iff₀ hy).mp
    linarith
  calc
    _ ≤ ∑ x,nu x*(2*law A R j y.val.val) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrow x) (hnu x))
    _ = (∑ x,nu x)*(2*law A R j y.val.val) := by rw [Finset.sum_mul]
    _ ≤ _ := by nlinarith

end
end ContingencyTables.RootedTargetMixing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWarmReturn
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Warm input error of the actual selected-root bounded return law -/

namespace ContingencyTables.RootedWarmReturn

open CommonBasesFPRAS ResidualMixture FirstSuccess FiniteLawMoments RealKernelApproximation
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionWeightOracle CompanionRationalUpdates RootedTraceWords
open RootedCappedReturn RootedTargetTrace RootedAnnealing RootedWarmStart
open CompanionConcentration (pairs_ne_nil)
open CompanionBooleanPhase (State stepBits)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma weighted_error {Y : Type*} [Fintype Y]
    (nu f g loss : Y → ℝ) (delta e : ℝ) (hnu : ∀ y,0≤nu y)
    (hmass : ∑ y,nu y≤1) (he : 0≤e)
    (hpoint : ∀ y,f y≤g y+loss y+e) (hloss : ∑ y,nu y*loss y≤delta) :
    (∑ y,nu y*f y)≤(∑ y,nu y*g y)+delta+e := by
  have h := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint y) (hnu y))
  have hm := mul_le_mul_of_nonneg_right hmass he
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,one_mul] at h hm
  linarith

private lemma push_observation {X Y : Type*} [Fintype X] [Fintype Y]
    (K : FiniteKernel X Y) (nu : X → ℝ) (g : Y → ℝ) :
    (∑ y,K.push nu y*g y)=∑ x,nu x*(∑ y,K.P x y*g y) := by
  simp only [FiniteKernel.push,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

private theorem distance_of_events {Y : Type*} [Fintype Y]
    (p q : Y → ℝ) (delta : ℝ) (hmass : ∑ y,p y=∑ y,q y)
    (hevent : ∀ E : Y → Prop,(∑ y,p y*eventIndicator (E y))≤
      (∑ y,q y*eventIndicator (E y))+delta) : distance p q≤delta := by
  let E : Y → Prop := fun y => 0≤p y-q y
  have hzero : (∑ y,(p y-q y))=0 := by
    rw [Finset.sum_sub_distrib,hmass,sub_self]
  have hpoint (y : Y) : |p y-q y|=
      2*((p y-q y)*eventIndicator (E y))-(p y-q y) := by
    by_cases h : 0≤p y-q y
    · simp only [E,eventIndicator,h,ite_true, if_true,abs_of_nonneg h,mul_one]
      ring
    · simp only [E,eventIndicator,h,ite_false,abs_of_neg (lt_of_not_ge h),mul_zero]
      ring
  have hsum : (∑ y,|p y-q y|)=2*(∑ y,(p y-q y)*eventIndicator (E y)) := by
    simp only [hpoint,Finset.sum_sub_distrib,←Finset.mul_sum,hzero,sub_zero]
  have hh := hevent E
  simp only [sub_mul,Finset.sum_sub_distrib] at hsum
  unfold distance
  rw [hsum]
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

private lemma return_observation (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    (∑ T,(returnKernel A R C K j k n hK hW xi v w).P S T*eventIndicator (E T))=
      uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
        eventIndicator (E (returnWordDefault A R C K j k n hK hW xi v w S bits))) := by
  exact (word_expectation (returnWordDefault A R C K j k n hK hW xi v w S)
    (fun T => eventIndicator (E T))).symm

theorem warm_cap_loss (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (n : ℕ) (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A R j S.val.val) :
    (∑ S,nu S*(1-∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
      (targetKilled A R j hp w hw) n S T))≤(5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ) := by
  let := plainIndex_nonempty (pairs : List (Pair A)) PairedLabels.fresh PairedLabels.cover
  have hwar : ∀ S,nu S≤U*((targetChain A R j hp w hw).traceChain (plainPredicate pairs)
      (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw)).π S := by
    intro S
    have hs := hwarm S
    rw [←actualTrace_pi A R j hp w hw S] at hs
    simpa only [RootedTargetTrace.actualTrace] using hs
  have hl := (targetChain A R j hp w hw).cappedTrace_warm_loss (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw) n U nu hnu hwar
  have hpR : (0:ℝ)<Fintype.card (Labels A) := by exact_mod_cast hp
  have hd : (0:ℝ)<5*(Fintype.card (Labels A):ℝ)^2 := by positivity
  have hm := insideMass_lower A R j hp w hw hgood
  have hb : U/(targetChain A R j hp w hw).insideMass (plainPredicate pairs)≤
      5*(Fintype.card (Labels A):ℝ)^2*U := by
    calc
      _ ≤ U/(1/(5*(Fintype.card (Labels A):ℝ)^2)) :=
        div_le_div_of_nonneg_left hU (one_div_pos.mpr hd) hm
      _ = _ := by simp only [one_div,div_inv_eq_mul]; ring
  apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr
  have hc := hl.trans hb
  simpa only [mul_comm] using hc

private lemma returnKernel_stochastic (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    ∑ T,(returnKernel A R C K j k n hK hW xi v w).P S T=1 := by
  change (∑ T,((returnLaw A R C K j k n hK hW xi v w S).mass T:ℝ))=1
  exact_mod_cast (returnLaw A R C K j k n hK hW xi v w S).total

private theorem weighted_return_event (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A R j S.val.val)
    (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    (∑ S,nu S*(∑ T,(returnKernel A R C K j k n hK hW xi v w).P S T*eventIndicator (E T)))≤
      (∑ S,nu S*(∑ T,(RootedTargetTrace.actualTrace A R j hp w hw).kernel.P S T*
        eventIndicator (E T)))+
        (5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  let f : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    ∑ T,(returnKernel A R C K j k n hK hW xi v w).P S T*eventIndicator (E T)
  let g : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    ∑ T,(RootedTargetTrace.actualTrace A R j hp w hw).kernel.P S T*eventIndicator (E T)
  let loss : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    1-∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
      (targetKilled A R j hp w hw) n S T
  let err : ℝ := ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)
  have herr : 0≤err := by dsimp only [err]; positivity
  have hpoint (S) : f S≤g S+loss S+err := by
      dsimp only [f,g,loss,err]
      rw [return_observation]
      exact returnWordDefault_event A R C hC K j k n hK hW hB hj xi hx0 hx1
        hPL hCheeger v hp w hw S E
  have hcap := warm_cap_loss A R j hp w hw hgood n hn nu hnu U hU hwarm
  have hsum := @weighted_error (PlainIndex (pairs : List (Pair A))) inferInstance
    nu f g loss ((5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)) err
    hnu hmass herr hpoint hcap
  exact hsum

/-- This is the law of the implemented Boolean return, compared to the
literal trace on the same incoming warm distribution. -/
theorem warm_return_distance (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A R j S.val.val) :
    distance ((returnKernel A R C K j k n hK hW xi v w).push nu)
      ((RootedTargetTrace.actualTrace A R j hp w hw).kernel.push nu)≤
        (5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  apply distance_of_events
  · rw [FiniteKernel.push_mass,FiniteKernel.push_mass]
    simp only [returnKernel_stochastic,FiniteChain.kernel,FiniteChain.stochastic,mul_one]
  · intro E
    rw [push_observation,push_observation]
    have he := weighted_return_event A R C hC K j k n hK hW hB hj xi hx0 hx1 hPL hCheeger
      v hp w hw hgood hn nu hnu hmass U hU hwarm E
    simpa only [add_assoc] using he

end
end ContingencyTables.RootedWarmReturn

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedReturnIteration
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated actual selected-root returns and their stationary error -/

namespace ContingencyTables.RootedReturnIteration

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open RootedBooleanPhase CompanionOracleDensity CompanionRationalUpdates
open RootedWarmReturn RootedTargetTrace RootedTargetMixing
open RootedAnnealing RootedWarmStart TwoLiftStates GridBoundary
open CompanionBooleanPhase (State)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem repeated_return_distance (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A R j S.val.val) (t : ℕ) :
    distance (((returnKernel A R C K j k n hK hW xi v w).power t).push nu)
      (((RootedTargetTrace.actualTrace A R j hp w hw).kernel.power t).push nu)≤
        (t:ℝ)*((5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)) := by
  have hwar : ∀ S,nu S≤U*(RootedTargetTrace.actualTrace A R j hp w hw).π S := by
    intro S
    rw [actualTrace_pi]
    exact hwarm S
  have hstep (rho : PlainIndex (pairs : List (Pair A)) → ℝ)
      (hrho : ∀ S,0 ≤ rho S) (hrmass : ∑ S,rho S≤1)
      (hrwarm : ∀ S,rho S≤U*(RootedTargetTrace.actualTrace A R j hp w hw).π S) :=
    warm_return_distance A R C hC K j k n hK hW hB hj xi hx0 hx1 hPL hCheeger
      v hp w hw hgood hn rho hrho hrmass U hU
      (fun S => by simpa only [actualTrace_pi] using hrwarm S)
  exact WarmKernelIteration.power_distance
    (RootedTargetTrace.actualTrace A R j hp w hw)
    (returnKernel A R C K j k n hK hW xi v w) nu hnu hmass U _ hwar hstep t

end
end ContingencyTables.RootedReturnIteration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedReturnWords
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed Boolean word for selected-root repeated capped returns

The restart routine iterates the actual defaulted return experiment.
Every iteration receives a disjoint block, and an optional initial
finite-word draw receives its own disjoint block as well.
-/

namespace ContingencyTables.RootedReturnWords

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits RealKernelApproximation
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionBooleanPhase (stepBits)
open CompanionReturnWords (returnBits)
open RootedCappedReturn RootedWarmReturn RootedReturnIteration
open CompanionRationalUpdates RootedAnnealing TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private theorem walkLaw_cast_power {X : Type*} [Fintype X] [DecidableEq X]
    (Q : X → RationalLaw X) (x : X) (n : ℕ) (y : X) :
    ((walkLaw Q x n).mass y:ℝ)=((rationalKernel Q).power n).P x y := by
  induction n generalizing y with
  | zero =>
    simp only [walkLaw,pointLaw,FiniteKernel.power,FiniteKernel.identity]
    by_cases h : x=y
    · subst y; simp
    · simp [h,Ne.symm h]
  | succ n ih =>
    change ((∑ z,(walkLaw Q x n).mass z*(Q z).mass y:ℚ):ℝ)=_
    simp only [Rat.cast_sum,Rat.cast_mul,ih,
      FiniteKernel.power,FiniteKernel.comp,rationalKernel]

variable {I J : Type} [Fintype I] [Fintype J]

theorem booleanReturnsLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    booleanReturnsLaw A R C K j k n t hK hW xi v w S=
      walkLaw (returnLaw A R C K j k n hK hW xi v w) S t := by
  let step := returnWordDefault A R C K j k n hK hW xi v w
  change mapLaw (uniformLaw (α := Fin (t*((n+1)*stepBits A C K j k xi)) → Bool))
    (fun bits => wordWalk step S t
      (gridWordEquiv t ((n+1)*stepBits A C K j k xi) bits))=_
  have he := map_equiv (gridWordEquiv t ((n+1)*stepBits A C K j k xi))
    (uniformLaw (α := Fin (t*((n+1)*stepBits A C K j k xi)) → Bool))
    (wordWalk step S t)
  rw [uniform_equiv] at he
  exact he.symm.trans (wordWalkLaw_eq step S t)

theorem booleanReturnsLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S T : PlainIndex (pairs : List (Pair A))) :
    ((booleanReturnsLaw A R C K j k n t hK hW xi v w S).mass T:ℝ)=
      ((returnKernel A R C K j k n hK hW xi v w).power t).P S T := by
  rw [booleanReturnsLaw_eq]
  exact walkLaw_cast_power (returnLaw A R C K j k n hK hW xi v w) S t T

end
end ContingencyTables.RootedReturnWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartStages
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successive selected-root restart stages

The reference law is refreshed by the exact trace at each successive
parameter. Only that reference law is asserted to be warm. The actual
bounded-return law is compared to it by contraction and accumulated error.
-/

namespace ContingencyTables.RootedRestartStages

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates RootedAnnealing RootedWarmStart RootedTargetTrace
open RootedTargetMixing RootedWarmReturn RootedReturnIteration
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

lemma reference_nonnegative (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q) (j : ℕ) :
    ∀ S,0 ≤ reference A R H L hp w hw j S := by
  induction j with
  | zero =>
    intro S
    exact (div_pos (weight_positive A R 0 _) (total_positive A R 0)).le
  | succ j ih =>
    exact ((actualTrace A R (j+1) hp (w (j+1)) (hw (j+1))).kernel.power
      (restartTime A H L)).push_nonneg _ ih

lemma reference_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q) (j : ℕ) :
    ∑ S,reference A R H L hp w hw j S=1 := by
  induction j with
  | zero =>
    exact (by simpa only [reference,actualTrace_pi] using
      (actualTrace A R 0 hp (w 0) (hw 0)).normalized)
  | succ j ih =>
    change ∑ S,((actualTrace A R (j+1) hp (w (j+1)) (hw (j+1))).kernel.power
      (restartTime A H L)).push (reference A R H L hp w hw j) S=1
    rw [FiniteChain.power_push_mass]
    exact ih

end
end ContingencyTables.RootedRestartStages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartPrefix
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restart accuracy from only the learned multiplier prefix

The horizon controls the fixed mixing schedule. Goodness is required only
at the parameters which the actual restart has visited.
-/

namespace ContingencyTables.RootedRestartPrefix

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates RootedAnnealing RootedWarmStart RootedTargetTrace
open RootedTargetMixing RootedWarmReturn RootedReturnIteration RootedRestartStages
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

private lemma accumulate (j : ℕ) (r s u e : ℝ)
    (hr : r ≤ s+e) (hs : s ≤ u+(j:ℝ)*e) :
    r ≤ u+((j+1:ℕ):ℝ)*e := by
  push_cast
  linarith

theorem reference_two_warm_at (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (j : ℕ) (hj : j ≤ H)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w j p q:ℝ)))
    (S : PlainIndex (pairs : List (Pair A))) :
    reference A R H L hp w hw j S ≤ 2*law A R j S.val.val := by
  cases j with
  | zero =>
    change law A R 0 S.val.val ≤ 2*law A R 0 S.val.val
    have h := div_pos (weight_positive A R 0 S.val.val) (total_positive A R 0)
    change 0 < law A R 0 S.val.val at h
    linarith
  | succ j =>
    exact restart_warm A R H L (j+1) hj hbox hp (w (j+1)) (hw (j+1))
      hgood (reference A R H L hp w hw j)
      (reference_nonnegative A R H L hp w hw j)
      (reference_mass A R H L hp w hw j).le S

theorem reference_next_four_warm_at (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (j : ℕ) (hj : j ≤ H)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w j p q:ℝ)))
    (S : PlainIndex (pairs : List (Pair A))) :
    reference A R H L hp w hw j S ≤ 4*law A R (j+1) S.val.val := by
  have h := reference_two_warm_at A R H L hbox hp w hw j hj hgood S
  have ha := law_adjacent A R j S.val.val
  linarith

theorem implemented_distance_prefix (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K H L k n : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (hH : H ≤ CompanionOracleDensity.rationalHeight A C)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (CompanionOracleDensity.dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger
      (Grid (I := Fin (CompanionOracleDensity.dimension A)) K))
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (hn : 0 < n)
    (initial : PlainIndex (pairs : List (Pair A)) → ℝ) (j : ℕ) (hj : j ≤ H)
    (hgood : ∀ i,i ≤ j → GoodMultipliers pairs (weight A R i)
      (fun p q => (w i p q:ℝ))) :
    distance (implemented A R C K H L k n hK hW xi v w initial j)
      (reference A R H L hp w hw j) ≤
      distance initial (fun S => law A R 0 S.val.val)+
      (j:ℝ)*((restartTime A H L:ℝ)*
        ((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))) := by
  revert hj hgood
  induction j with
  | zero =>
    intro _ _
    simp only [implemented,reference,Nat.cast_zero,zero_mul,add_zero]
    exact le_rfl
  | succ j ih =>
    intro hj hgood
    have hj0 : j ≤ H := by omega
    have hs := repeated_return_distance A R C hC K (j+1) k n hK hW hB
      (hj.trans hH) xi hx0 hx1 hPL hCheeger v hp (w (j+1)) (hw (j+1))
      (hgood (j+1) le_rfl) hn (reference A R H L hp w hw j)
      (reference_nonnegative A R H L hp w hw j)
      (reference_mass A R H L hp w hw j).le 4 (by norm_num)
      (reference_next_four_warm_at A R H L hbox hp w hw j hj0 (hgood j (Nat.le_succ j)))
      (restartTime A H L)
    have hc := distance_push
      ((returnKernel A R C K (j+1) k n hK hW xi v (w (j+1))).power (restartTime A H L))
      (implemented A R C K H L k n hK hW xi v w initial j)
      (reference A R H L hp w hw j)
    have ht := distance_triangle
      (implemented A R C K H L k n hK hW xi v w initial (j+1))
      (((returnKernel A R C K (j+1) k n hK hW xi v (w (j+1))).power
        (restartTime A H L)).push (reference A R H L hp w hw j))
      (reference A R H L hp w hw (j+1))
    have hprev := ih hj0 (fun i hi => hgood i (hi.trans (Nat.le_succ j)))
    rw [show 5*(Fintype.card (Labels A):ℝ)^2*4=
      20*(Fintype.card (Labels A):ℝ)^2 by ring] at hs
    have hsum := _root_.add_le_add hc hs
    have hstep := ht.trans hsum
    exact accumulate j _ _ _ _ hstep hprev


end
end ContingencyTables.RootedRestartPrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartWords
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite Boolean words for all successive restart stages -/

namespace ContingencyTables.RootedRestartWords

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open CompanionTargetMixing (restartTime)
open CompanionReturnWords (returnBits)
open RootedReturnWords RootedWarmStart RootedRestartStages RootedRestartPrefix
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem stages_law (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    mapLaw (uniformLaw (α := Fin (∑ i : Fin j,stageWidth A C K H L k n xi i.val) → Bool))
      (stages A R C K H L k n j hK hW xi v w S)=
      varyingLaw (stageWidth A C K H L k n xi)
        (stageStep A R C K H L k n hK hW xi v w) (pointLaw S) j :=
  flatVaryingWalk_law _ _ S j

private lemma stageStep_law (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (i : ℕ) (S : PlainIndex (pairs : List (Pair A))) :
    mapLaw (uniformLaw (α := Fin (stageWidth A C K H L k n xi i) → Bool))
      (stageStep A R C K H L k n hK hW xi v w i S)=
      booleanReturnsLaw A R C K (i+1) k n (restartTime A H L) hK hW xi v (w (i+1)) S := by
  rfl

theorem stageLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (p : RationalLaw (PlainIndex (pairs : List (Pair A)))) (j : ℕ)
    (T : PlainIndex (pairs : List (Pair A))) :
    ((varyingLaw (stageWidth A C K H L k n xi)
      (stageStep A R C K H L k n hK hW xi v w) p j).mass T:ℝ)=
      implemented A R C K H L k n hK hW xi v w (fun S => (p.mass S:ℝ)) j T := by
  induction j generalizing T with
  | zero => rfl
  | succ j ih =>
    simp only [varyingLaw,stageStep_law,bindLaw,Rat.cast_sum,Rat.cast_mul,
      ih,booleanReturnsLaw_cast,implemented,FiniteKernel.push]

theorem initializedStages_law (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n h j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ) :
    mapLaw (uniformLaw (α := Fin (initialStageBits A C K H L k n h j xi) → Bool))
      (initializedStages A R C K H L k n h j hK hW xi v w)=
      varyingLaw (stageWidth A C K H L k n xi)
        (stageStep A R C K H L k n hK hW xi v w)
        (mapLaw (uniformLaw (α := Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A h)) → Bool))
          (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h))) j := by
  let r := CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A h)
  let s := ∑ i : Fin j,stageWidth A C K H L k n xi i.val
  let init := CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h)
  let run := stages A R C K H L k n j hK hW xi v w
  change mapLaw (uniformLaw (α := Fin (r+s) → Bool))
    (fun bits => run (init (splitWordEquiv r s bits).1) (splitWordEquiv r s bits).2)=_
  have he := map_equiv (splitWordEquiv r s)
    (uniformLaw (α := Fin (r+s) → Bool)) (fun z => run (init z.1) z.2)
  rw [uniform_equiv,←uniform_product] at he
  refine he.symm.trans ?_
  rw [mapLaw_product_finish]
  dsimp only [run]
  have hf : (fun x => mapLaw (uniformLaw (α := Fin s → Bool))
      (stages A R C K H L k n j hK hW xi v w x))=
      (fun x => varyingLaw (stageWidth A C K H L k n xi)
        (stageStep A R C K H L k n hK hW xi v w) (pointLaw x) j) := by
    funext x
    exact stages_law A R C K H L k n j hK hW xi v w x
  have heq := congrArg (fun F : PlainIndex (pairs : List (Pair A)) →
      RationalLaw (PlainIndex (pairs : List (Pair A))) =>
        bindLaw (mapLaw (uniformLaw (α := Fin r → Bool)) init) F) hf
  exact heq.trans (varyingLaw_start _ _ _ _)

/-- The actual initialized finite word is close to the exact warm
restart reference; it includes every fresh stage and initializer word. -/
theorem initializedStages_distance (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K H L k n h j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hH : H ≤ rationalHeight A C)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ i p q,0 < w i p q)
    (hgood : ∀ i,i ≤ j → GoodMultipliers pairs (RootedAnnealing.weight A R i)
      (fun p q => (w i p q:ℝ))) (hn : 0 < n) (hj : j ≤ H) :
    distance (fun T => ((mapLaw (uniformLaw
      (α := Fin (initialStageBits A C K H L k n h j xi) → Bool))
      (initializedStages A R C K H L k n h j hK hW xi v w)).mass T:ℝ))
      (reference A R H L hp w hw j) ≤ 1/(2:ℝ)^h+
        (j:ℝ)*((restartTime A H L:ℝ)*((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))) := by
  rw [initializedStages_law]
  simp_rw [stageLaw_cast]
  let initial : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    ((mapLaw (uniformLaw (α := Fin (CompanionInitialDraw.initialBits A
      (CompanionInitialDraw.precision A h)) → Bool))
      (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h))).mass S:ℝ)
  have h0 : distance initial (fun S => law A R 0 S.val.val) ≤ 1/(2:ℝ)^h :=
    initial_distance A R h
  have hh := implemented_distance_prefix A R C hC K H L k n hK hW hB hH hbox xi hx0 hx1
    hPL hCheeger v hp w hw hn initial j hj hgood
  have hadd := _root_.add_le_add h0 (le_refl ((j:ℝ)*((restartTime A H L:ℝ)*
    ((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)))))
  have hb := hh.trans hadd
  simpa only [initial] using hb

end
end ContingencyTables.RootedRestartWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartTrial
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual initialized restart followed by the finite phase update -/

namespace ContingencyTables.RootedRestartTrial

open CommonBasesFPRAS FirstSuccess ResidualMixture RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open RootedAnnealing RootedWarmStart RootedPhaseTrial RootedRestartWords
open RootedRestartStages RootedRestartPrefix
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma replace_distance (r B d D e : ℝ) (hr : r ≤ B+2*d+e) (hd : d ≤ D) :
    r ≤ B+2*D+e := by linarith

variable {I J : Type} [Fintype I] [Fintype J]

/-- All source conditions concern the learned prefix. The words
for initialization, successive restarts, observations and weight calls
are independent, and all are part of this single finite experiment. -/
theorem failure (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K H L j k n N h : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hH : H ≤ rationalHeight A C) (hj : j < H)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ i p q,0 < w i p q)
    (hgood : ∀ i,i ≤ j → GoodMultipliers pairs (weight A R i)
      (fun p q => (w i p q:ℝ))) (hn : 0 < n)
    (estimate : ℚ) (hE : 0 < estimate) (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    uniformAverage (fun bits : Words A C K H L j k n N h xi =>
      eventIndicator (¬∃ next,run A R C K H L j k n N h hK hW xi v w estimate bits=some next ∧
        ValidOutput A R j ⟨w j,estimate⟩ xi eta next)) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+
          2*(1/(2:ℝ)^h+(j:ℝ)*((restartTime A H L:ℝ)*
            ((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
              ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))))+
            2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
  let draw := initializedStages A R C K H L k n h j hK hW xi v w
  let p := mapLaw (uniformLaw (α := Fin (initialStageBits A C K H L k n h j xi) → Bool)) draw
  let q := reference A R H L hp w hw j
  let g (S : PlainIndex (pairs : List (Pair A))) : ℝ :=
    uniformAverage (fun bits : TrialWords A C K j k N xi =>
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v ⟨w j,estimate⟩ S.val bits=some next ∧
        ValidOutput A R j ⟨w j,estimate⟩ xi eta next))
  have he : uniformAverage (fun bits : Words A C K H L j k n N h xi =>
      eventIndicator (¬∃ next,run A R C K H L j k n N h hK hW xi v w estimate bits=some next ∧
        ValidOutput A R j ⟨w j,estimate⟩ xi eta next))=∑ S,(p.mass S:ℝ)*g S := by
    rw [uniformAverage_prod]
    exact FiniteLawMoments.word_expectation draw g
  have hpast := RootedPlainTrial.trial_failure A R C hC K j k N hK hW hB
    ((Nat.succ_le_of_lt hj).trans hH) xi hx0 hx1 hPL hCheeger v hp
    ⟨w j,estimate⟩ (hw j) hE (hgood j le_rfl) p q
    (reference_nonnegative A R H L hp w hw j)
    (reference_mass A R H L hp w hw j).le
    (reference_two_warm_at A R H L hbox hp w hw j hj.le (hgood j le_rfl)) eta he0 he1
  have hd := initializedStages_distance A R C hC K H L k n h j hK hW hB hH hbox
    xi hx0 hx1 hPL hCheeger v hp w hw hgood hn hj.le
  rw [he]
  exact replace_distance _ _ _ _ _ hpast hd

end
end ContingencyTables.RootedRestartTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedStoredEstimate
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Soundness of the actual stored rational count estimate -/

namespace ContingencyTables.RootedStoredEstimate

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedWarmStart RootedPhaseTrial
open CompanionTerminalMass (Endpoints tableCount )
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma initialTotal_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    (initialTotal A:ℝ)=total A R 0 := by
  rw [total,total_zero]
  simp only [initialTotal,CompanionInitialization.freeTotal,Rat.cast_mul,Rat.cast_prod,
    Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Nat.cast_add,Nat.cast_one]

lemma initialStored_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    (∀ p q,0 < (initialStored A).multiplier p q) ∧ 0 < (initialStored A).estimate := by
  constructor
  · exact initial_positive A
  · have h : (0:ℝ) < (initialTotal A:ℝ) := by
      rw [initialTotal_cast A R]
      exact total_positive A R 0
    exact_mod_cast h

lemma initialStored_good (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    GoodMultipliers pairs (RootedAnnealing.weight A R 0)
      (fun p q => ((initialStored A).multiplier p q:ℝ)) := by
  have hw : (fun p q => ((initialStored A).multiplier p q:ℝ))=
      CompanionInitialMultipliers.multiplier A := by
    funext p q
    exact initial_cast A p q
  rw [hw,zero_weight_eq]
  simpa only [CompanionAnnealing.weight,Nat.cast_zero,zero_div] using
    CompanionInitialMultipliers.initial_good A

end
end ContingencyTables.RootedStoredEstimate

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedStoredHistory
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stored rational outputs of the actual outer phases

The initial record is at index zero. Later records are the outputs
stored in the finite history; the initial record also supplies every
unused future entry to the restart's multiplier function.
-/

namespace ContingencyTables.RootedStoredHistory

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedStoredEstimate RootedPhaseTrial
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma lookup_snoc_old (A : Instance I J) (history : List (Stored A))
    (next : Stored A) (i : ℕ) (hi : i ≤ history.length) :
    lookup A (history++[next]) i=lookup A history i := by
  cases i with
  | zero => rfl
  | succ i => exact List.getD_append history [next] (initialStored A) i (by omega)

lemma lookup_snoc_new (A : Instance I J) (history : List (Stored A)) (next : Stored A) :
    lookup A (history++[next]) (history.length+1)=next := by
  simp only [lookup,List.getD_append_right history [next] (initialStored A) history.length le_rfl,
    Nat.sub_self,List.getD_cons_zero]

lemma lookup_future (A : Instance I J) (history : List (Stored A)) (i : ℕ)
    (hi : history.length < i) : lookup A history i=initialStored A := by
  cases i with
  | zero => omega
  | succ i => exact List.getD_eq_default history (initialStored A) (by omega)

lemma good_nil (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ) :
    Good A R xi eta [] := by
  intro i hi
  simp at hi

lemma good_snoc (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) (next : Stored A) :
    Good A R xi eta (history++[next]) ↔
      Good A R xi eta history ∧
        ValidOutput A R history.length (lookup A history history.length) xi eta next := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hstep := h i (by simp; omega)
      rw [lookup_snoc_old A history next i (by omega),
        lookup_snoc_old A history next (i+1) (by omega)] at hstep
      exact hstep
    · have hstep := h history.length (by simp)
      rw [lookup_snoc_old A history next history.length le_rfl,
        lookup_snoc_new] at hstep
      exact hstep
  · rintro ⟨hold,hnext⟩ i hi
    have hi' : i ≤ history.length := by simpa using Nat.le_of_lt_succ (by simpa using hi)
    by_cases heq : i=history.length
    · subst i
      rw [lookup_snoc_old A history next history.length le_rfl,lookup_snoc_new]
      exact hnext
    · have hlt : i < history.length := by omega
      rw [lookup_snoc_old A history next i hi',
        lookup_snoc_old A history next (i+1) (by omega)]
      exact hold i hlt

lemma good_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) (hg : Good A R xi eta history) (i : ℕ) :
    (∀ p q,0 < (lookup A history i).multiplier p q) ∧
      0 < (lookup A history i).estimate := by
  by_cases hi : i ≤ history.length
  · cases i with
    | zero => exact initialStored_positive A R
    | succ i =>
      have h := hg i (by omega)
      exact ⟨h.1,h.2.1⟩
  · rw [lookup_future A history i (by omega)]
    exact initialStored_positive A R

lemma good_multipliers (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) (hg : Good A R xi eta history) (i : ℕ)
    (hi : i ≤ history.length) :
    GoodMultipliers pairs (RootedAnnealing.weight A R i)
      (fun p q => ((lookup A history i).multiplier p q:ℝ)) := by
  cases i with
  | zero => exact initialStored_good A R
  | succ i => exact (hg i (by omega)).2.2.1

end
end ContingencyTables.RootedStoredHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual adaptive phases on a common finite Boolean word space -/

namespace ContingencyTables.RootedPhaseHistory

open CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (stepBits)
open RootedStoredHistory
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma decoded_nil (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A) :
    decoded A R s []=[] := rfl

lemma decoded_snoc (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : List (Word A s)) (bits : Word A s) :
    decoded A R s (words++[bits])=
      decoded A R s words++[step A R s (decoded A R s words) bits] := by
  simp only [decoded,List.foldl_append,List.foldl_cons,List.foldl_nil]

private lemma fold_length {X Y : Type*} (f : List Y → X → Y) (xs : List X) (ys : List Y) :
    (xs.foldl (fun history x => history++[f history x]) ys).length=ys.length+xs.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil]
    omega

lemma decoded_length (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : List (Word A s)) : (decoded A R s words).length=words.length := by
  simpa only [decoded,List.length_nil,Nat.zero_add] using fold_length (step A R s) words []

lemma good_snoc_iff (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (eta : ℝ) (words : List (Word A s)) (bits : Word A s) :
    Good A R s.xi eta (decoded A R s (words++[bits])) ↔
      Good A R s.xi eta (decoded A R s words) ∧
        RootedPhaseTrial.ValidOutput A R words.length
          (lookup A (decoded A R s words) words.length) s.xi eta
          (step A R s (decoded A R s words) bits) := by
  rw [decoded_snoc,RootedStoredHistory.good_snoc,decoded_length]

end
end ContingencyTables.RootedPhaseHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePaddedAverage
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Observables of a padded and reindexed finite Boolean word -/

namespace ContingencyTables.FairBits

open CommonBasesFPRAS FirstSuccess ResidualMixture FiniteLawMoments
open scoped BigOperators Classical

noncomputable section

lemma padded_equiv_average {k N : ℕ} (hk : k ≤ N) {X : Type*} [Fintype X]
    (e : (Fin k → Bool) ≃ X) (f : X → ℝ) :
    uniformAverage (fun bits : Fin N → Bool => f (e (prefixWord hk bits)))=
      uniformAverage f := by
  have hp := word_expectation (prefixWord hk) (fun bits => f (e bits))
  rw [prefixWord_uniform,expectation_uniform] at hp
  exact hp.trans (uniformAverage_equiv e f)

end
end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedHistoryStep
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional accuracy of each actual adaptive outer phase -/

namespace ContingencyTables.RootedHistoryStep

open CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity RootedPhaseHistory RootedStoredHistory
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma default_failure {X : Type*} (o : Option X) (d : X) (P : X → Prop) :
    eventIndicator (¬P (o.getD d)) ≤
      eventIndicator (¬∃ x,o=some x ∧ P x) := by
  cases o with
  | none => by_cases hd : P d <;> simp [eventIndicator,hd]
  | some x => by_cases hx : P x <;> simp [eventIndicator,hx]

variable {I J : Type} [Fintype I] [Fintype J]

lemma error_mono (A : Instance I J) (s : Settings A) (eta : ℝ) (j l : ℕ)
    (hj : j ≤ l) (hx : 0 ≤ s.xi) : error A s eta j ≤ error A s eta l := by
  have hxR : (0:ℝ) ≤ (s.xi:ℝ) := by exact_mod_cast hx
  have hcoef : 0 ≤ (restartTime A s.H s.L:ℝ)*
      ((20*(Fintype.card (Labels A):ℝ)^2)/(s.n:ℝ)+
        ((s.n+1:ℕ):ℝ)*((6*(s.xi:ℝ)+1/(2:ℝ)^s.k)/2)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right (show (j:ℝ) ≤ l by exact_mod_cast hj) hcoef
  unfold error
  linarith

/-- On each good past history, the actual next stored value fails the
source update conditions with the proved common error bound. -/
theorem step_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
    (hH : s.H ≤ rationalHeight A s.C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
    (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
    (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4)
    (history : List (Stored A)) (hg : Good A R s.xi eta history)
    (hj : history.length < s.H) :
    uniformAverage (fun bits : Word A s =>
      eventIndicator (¬RootedPhaseTrial.ValidOutput A R history.length
        (lookup A history history.length) s.xi eta (step A R s history bits))) ≤
      error A s eta history.length := by
  let j := history.length
  let old := lookup A history j
  let w : ℕ → Pair A → Pair A → ℚ := fun i => (lookup A history i).multiplier
  let P : Stored A → Prop := RootedPhaseTrial.ValidOutput A R j old s.xi eta
  let F : RootedRestartTrial.Words A s.C s.K s.H s.L j s.k s.n s.N s.h s.xi → ℝ :=
    fun bits => eventIndicator (¬∃ next,
      RootedRestartTrial.run A R s.C s.K s.H s.L j s.k s.n s.N s.h s.hK s.hW s.xi
        s.v w old.estimate bits=some next ∧ P next)
  have hs := RootedRestartTrial.failure A R s.C hC s.K s.H s.L j s.k s.n s.N s.h
    s.hK s.hW hB hH hj hbox s.xi hx0 hx1 hPL hCheeger s.v hp w
    (fun i => (good_positive A R s.xi eta history hg i).1)
    (fun i hi => good_multipliers A R s.xi eta history hg i hi) hn old.estimate
    (good_positive A R s.xi eta history hg j).2 eta he0 he1
  have hpw (bits : Word A s) :
      eventIndicator (¬P (step A R s history bits)) ≤
        F (split A s j (prefixWord (width_le A s j hj) bits)) := by
    simp only [step,hj,dite_true]
    exact default_failure _ old P
  have havg := uniformAverage_mono _ _ hpw
  have heq := padded_equiv_average (width_le A s j hj) (split A s j) F
  rw [heq] at havg
  have hbound : uniformAverage F ≤ error A s eta j := hs
  exact havg.trans hbound

end
end ContingencyTables.RootedHistoryStep

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteUniformHistory
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent-word law of a finite adaptive-history experiment -/

namespace ContingencyTables.FiniteUniformHistory

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {X : Type*} [Fintype X] [Nonempty X]

lemma kernel_nonneg (h : List X) (x : X) : 0 ≤ kernel h x := by
  unfold kernel
  positivity

lemma kernel_mass (h : List X) : ∑ x,kernel h x=1 := by
  have hx : (Fintype.card X:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [kernel,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [hx]

lemma expectation (N : ℕ) (h : List X) (f : List X → ℝ) :
    FiniteExperiment.expect kernel N h f=
      uniformAverage (fun xs : Fin N → X => f (h++List.ofFn xs)) := by
  induction N generalizing h with
  | zero => simp only [FiniteExperiment.expect,List.ofFn_zero,List.append_nil,uniformAverage_const]
  | succ N ih =>
    simp only [FiniteExperiment.expect,ih]
    rw [uniformAverage_fin_succ]
    have he : (fun x : X => uniformAverage
        (fun xs : Fin N → X => f ((h++[x])++List.ofFn xs)))=
        (fun x : X => uniformAverage
          (fun xs : Fin N → X => f (h++List.ofFn (Fin.cons x xs)))) := by
      funext x
      congr 1
      funext xs
      simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,List.append_assoc,List.singleton_append]
    rw [←he]
    let g : X → ℝ := fun x => uniformAverage
      (fun xs : Fin N → X => f ((h++[x])++List.ofFn xs))
    change (∑ x,kernel h x*g x)=uniformAverage g
    unfold kernel uniformAverage
    rw [←Finset.mul_sum]
    ring

/-- A history-dependent success predicate is evaluated on genuinely
independent finite words; only its conditional one-step loss is assumed. -/
theorem good_probability (Good : List X → Prop) (N : ℕ) (e : ℝ) (he : 0 ≤ e)
    (hstep : ∀ h,Good h → h.length<N →
      1-e ≤ uniformAverage (fun x : X => if Good (h++[x]) then (1:ℝ) else 0))
    (hzero : Good []) :
    1-(N:ℝ)*e ≤ uniformAverage (fun xs : Fin N → X =>
      if Good (List.ofFn xs) then (1:ℝ) else 0) := by
  have hs (h : List X) (hh : Good h) (hlen : h.length<N) :
      1-e ≤ ∑ x,FiniteExperiment.restrict kernel Good h x := by
    have hprob := hstep h hh hlen
    unfold FiniteExperiment.restrict kernel
    have heq (x : X) :
        (if Good (h ++ [x]) then (1:ℝ)/Fintype.card X else 0)=
          (if Good (h ++ [x]) then (1:ℝ) else 0)/Fintype.card X := by
      split_ifs <;> simp
    simp_rw [heq]
    rw [←Finset.sum_div]
    exact hprob
  have hp := FiniteExperiment.good_probability_bounded kernel Good kernel_nonneg
    (fun h => (kernel_mass h).le) N e he hs hzero
  rw [expectation] at hp
  simpa only [List.nil_append] using hp

end
end ContingencyTables.FiniteUniformHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedHistoryConfidence
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Success probability of the actual adaptive selected-root history -/

namespace ContingencyTables.RootedHistoryConfidence

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory RootedHistoryStep
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma success_of_failure {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) (e : ℝ)
    (hf : uniformAverage (fun x => eventIndicator (¬P x)) ≤ e) :
    1-e ≤ uniformAverage (fun x => if P x then (1:ℝ) else 0) := by
  have hpoint (x : X) : (if P x then (1:ℝ) else 0)+eventIndicator (¬P x)=1 := by
    by_cases hx : P x <;> simp [eventIndicator,hx]
  have hadd := uniformAverage_add (fun x => if P x then (1:ℝ) else 0)
    (fun x => eventIndicator (¬P x))
  simp_rw [hpoint] at hadd
  rw [uniformAverage_const] at hadd
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

lemma error_nonnegative (A : Instance I J) (s : Settings A) (eta : ℝ)
    (hx : 0 ≤ s.xi) (j : ℕ) : 0 ≤ error A s eta j := by
  have hxR : (0:ℝ) ≤ (s.xi:ℝ) := by exact_mod_cast hx
  unfold error ObservableBounds.observableConstant
  positivity

/-- Each conditional probability is proved from the actual finite-word
phase; independent word histories then accumulate these losses. -/
theorem history_success_oai (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
    (hH : s.H ≤ rationalHeight A s.C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
    (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
    (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    1-(s.H:ℝ)*error A s eta s.H ≤
      uniformAverage (fun words : Fin s.H → Word A s =>
        if GoodWords A R s eta (List.ofFn words) then (1:ℝ) else 0) := by
  apply FiniteUniformHistory.good_probability (GoodWords A R s eta) s.H
    (error A s eta s.H) (error_nonnegative A s eta hx0.le s.H)
  · intro words hgood hlen
    have hgood' : Good A R s.xi eta (decoded A R s words) := hgood
    have hj : (decoded A R s words).length < s.H := by simpa only [decoded_length] using hlen
    have hf := step_failure A R s hC hB hH hbox hx0 hx1 hPL hCheeger hp hn eta he0 he1
      (decoded A R s words) hgood' hj
    have he := (error_mono A s eta (decoded A R s words).length s.H hj.le hx0.le)
    have hf' := hf.trans he
    have hg (bits : Word A s) :
        GoodWords A R s eta (words++[bits]) ↔
          RootedPhaseTrial.ValidOutput A R words.length
            (lookup A (decoded A R s words) words.length) s.xi eta
            (step A R s (decoded A R s words) bits) := by
      rw [GoodWords,good_snoc_iff]
      exact and_iff_right hgood'
    have hf'' : uniformAverage (fun bits : Word A s =>
        eventIndicator (¬GoodWords A R s eta (words++[bits]))) ≤ error A s eta s.H := by
      have heq : (fun bits : Word A s => eventIndicator (¬GoodWords A R s eta (words++[bits])))=
          (fun bits : Word A s => eventIndicator (¬RootedPhaseTrial.ValidOutput A R words.length
            (lookup A (decoded A R s words) words.length) s.xi eta
            (step A R s (decoded A R s words) bits))) := by
        funext bits
        rw [hg bits]
      rw [heq]
      simpa only [decoded_length] using hf'
    exact success_of_failure _ _ hf''
  · change Good A R s.xi eta (decoded A R s [])
    rw [decoded_nil]
    exact good_nil A R s.xi eta

end
end ContingencyTables.RootedHistoryConfidence

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.RootedHistoryConfidence.history_success_oai := @OAI.ContingencyTables.RootedHistoryConfidence.history_success_oai
