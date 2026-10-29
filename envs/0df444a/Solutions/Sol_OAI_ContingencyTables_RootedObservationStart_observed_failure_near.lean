-- Prove2me | solution 1 for OAI.ContingencyTables.RootedObservationStart.observed_failure_near
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:14:18.741123+00:00
-- url     : https://prove2.me/submissions/9001a6f3-43fc-409a-b513-11c8da7c7e22

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_ObservableTrajectory_omission_chain_dual
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

section StateGeometry
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance36 : Fintype Γ] [sectionInstance37 : DecidableEq Γ]

lemma SlotsFresh.nodup {ps : List (Γ × Γ)} {A : Set Γ} (h : SlotsFresh ps A) : ps.Nodup := by
  induction ps generalizing A with
  | nil => exact List.nodup_nil
  | cons p ps ih =>
    exact List.nodup_cons.mpr ⟨fun hp => (h.pair_ne_of_mem hp) rfl,ih h.2.2.2⟩

end StateGeometry

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

lemma inner_sum_right {J : Type*} (s : Finset J) (f : X → ℝ) (g : J → X → ℝ) :
    C.inner f (fun x => ∑ j ∈ s,g j x) = ∑ j ∈ s,C.inner f (g j) := by
  simp only [inner,Finset.mul_sum]
  exact Finset.sum_comm
lemma inner_sum_left {J : Type*} (s : Finset J) (f : J → X → ℝ) (g : X → ℝ) :
    C.inner (fun x => ∑ j ∈ s,f j x) g = ∑ j ∈ s,C.inner (f j) g := by
  rw [inner_symm,inner_sum_right]
  apply Finset.sum_congr rfl
  intro j _
  exact C.inner_symm _ _
lemma apply_add (f g : X → ℝ) : C.apply (fun x => f x+g x) = fun x => C.apply f x+C.apply g x := by
  funext x
  simp [apply,mul_add,Finset.sum_add_distrib]
lemma apply_sum {J : Type*} (s : Finset J) (f : J → X → ℝ) :
    C.apply (fun x => ∑ j ∈ s,f j x) = fun x => ∑ j ∈ s,C.apply (f j) x := by
  funext x
  simp only [apply,Finset.mul_sum]
  exact Finset.sum_comm
lemma iterate_add (k l : ℕ) (f : X → ℝ) : C.iterate (k+l) f = C.iterate k (C.iterate l f) := by
  exact Function.iterate_add_apply C.apply k l f
lemma iterate_selfAdjoint (k : ℕ) (f g : X → ℝ) : C.inner f (C.iterate k g) = C.inner (C.iterate k f) g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    rw [C.iterate_succ,C.apply_selfAdjoint,ih]
    change C.inner (C.iterate k (C.iterate 1 f)) g = _
    rw [← C.iterate_add]

lemma covariance_nonneg (k : ℕ) (f : X → ℝ) : 0 ≤ C.inner f (C.iterate k f) := by
  have hk : k = k/2+k/2 ∨ k = k/2+(k/2+1) := by
    have := Nat.mod_add_div k 2
    have := Nat.mod_lt k (by decide : 0 < 2)
    omega
  rcases hk with hk | hk
  · nth_rw 1 [hk]
    rw [C.iterate_add,C.iterate_selfAdjoint]
    exact C.inner_nonneg _
  · nth_rw 1 [hk]
    rw [C.iterate_add,C.iterate_selfAdjoint,C.iterate_succ]
    exact C.apply_positive _

lemma partialResolvent_zero (f : X → ℝ) : C.partialResolvent 0 f = fun _ => 0 := by
  funext x
  simp [partialResolvent]
lemma partialResolvent_succ (N : ℕ) (f : X → ℝ) :
    C.partialResolvent (N+1) f = fun x => C.partialResolvent N f x+C.iterate N f x := by
  funext x
  exact Finset.sum_range_succ _ _

lemma partialResolvent_residual (N : ℕ) (f : X → ℝ) :
    (fun x => C.partialResolvent N f x-C.apply (C.partialResolvent N f) x) =
      fun x => f x-C.iterate N f x := by
  induction N with
  | zero => rw [C.partialResolvent_zero,C.apply_const]; simp
  | succ N ih =>
    rw [C.partialResolvent_succ,C.apply_add,C.iterate_succ]
    funext x
    have hh := congrFun ih x
    dsimp only at hh ⊢
    linarith

lemma partialResolvent_inner (N : ℕ) (f : X → ℝ) :
    C.inner f (C.partialResolvent N f) = ∑ k ∈ Finset.range N,C.inner f (C.iterate k f) := by
  exact C.inner_sum_right _ _ _

lemma partialResolvent_energy_le (N : ℕ) (f : X → ℝ) :
    C.energy (C.partialResolvent N f) ≤ C.inner f (C.partialResolvent N f) := by
  rw [energy,C.partialResolvent_residual,C.inner_sub_right,C.inner_symm (C.partialResolvent N f) f]
  have hh : 0 ≤ C.inner (C.partialResolvent N f) (C.iterate N f) := by
    change 0 ≤ C.inner (fun x => ∑ k ∈ Finset.range N,C.iterate k f x) (C.iterate N f)
    rw [C.inner_sum_left]
    apply Finset.sum_nonneg
    intro k _
    rw [← C.iterate_selfAdjoint,← C.iterate_add]
    exact C.covariance_nonneg _ f
  linarith

theorem covariance_sum_bound (g : X → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ H, (C.inner g H)^2 ≤ K*C.inner g g*C.energy H) (N : ℕ) :
    (∑ k ∈ Finset.range N,C.inner g (C.iterate k g)) ≤ K*C.inner g g := by
  rw [← C.partialResolvent_inner]
  have h := hdual (C.partialResolvent N g)
  have he := C.partialResolvent_energy_le N g
  have hnon : 0 ≤ K*C.inner g g := mul_nonneg hK (C.inner_nonneg g)
  have hb := mul_le_mul_of_nonneg_left he hnon
  nlinarith

lemma pathExpectation_nonneg (N : ℕ) (x : X) (F : List X → ℝ) (hF : ∀ l,0 ≤ F l) :
    0 ≤ C.pathExpectation N x F := by
  induction N generalizing x F with
  | zero => exact hF _
  | succ N ih =>
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (C.nonnegative x y) (ih y _ (fun l => hF _))
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

omit sectionInstance56 in
lemma pathSum_cons [Fintype X] (g : X → ℝ) (x : X) (l : List X) : pathSum g (x::l) = g x+pathSum g l := rfl
lemma pathExpectation_sum (g : X → ℝ) (N : ℕ) (x : X) :
    C.pathExpectation N x (pathSum g) = C.partialResolvent (N+1) g x := by
  induction N generalizing x with
  | zero => simp [pathExpectation,pathSum,partialResolvent]
  | succ N ih =>
    have hc (y : X) : C.pathExpectation N y (fun l => pathSum g (x::l)) =
        g x+C.partialResolvent (N+1) g y := by
      simp only [pathSum_cons]
      rw [C.pathExpectation_add,C.pathExpectation_const,ih]
    simp only [pathExpectation,hc,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,C.stochastic,one_mul]
    have hh := congrFun (C.partialResolvent_residual (N+1) g) x
    change g x+C.apply (C.partialResolvent (N+1) g) x = _
    rw [C.partialResolvent_succ (N+1)]
    dsimp only at hh ⊢
    linarith

lemma squareMoment_succ (g : X → ℝ) (N : ℕ) (x : X) :
    C.squareMoment g (N+1) x = (g x)^2 +
      2*g x*C.apply (C.partialResolvent N g) x+C.apply (C.squareMoment g N) x := by
  cases N with
  | zero => simp [squareMoment,pathExpectation,pathSum,partialResolvent,apply]
  | succ N =>
    simp only [squareMoment,Nat.succ_ne_zero,ite_false,
      Nat.add_sub_cancel,pathExpectation]
    have he (y : X) : C.pathExpectation N y (fun l => (pathSum g (x::l))^2) =
        (g x)^2+2*g x*C.partialResolvent (N+1) g y+
          C.pathExpectation N y (fun l => (pathSum g l)^2) := by
      calc
        _ = C.pathExpectation N y (fun l => (g x)^2+2*g x*pathSum g l+(pathSum g l)^2) := by
          apply C.pathExpectation_congr
          intro l
          rw [pathSum_cons]
          ring
        _ = _ := by rw [C.pathExpectation_add,C.pathExpectation_add,C.pathExpectation_const,
          C.pathExpectation_mul,C.pathExpectation_sum]
    simp only [he,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,C.stochastic,one_mul]
    unfold apply
    congr 1
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    ring

lemma squareMoment_nonneg (g : X → ℝ) (N : ℕ) (x : X) : 0 ≤ C.squareMoment g N x := by
  unfold squareMoment
  split_ifs
  · exact le_rfl
  · exact C.pathExpectation_nonneg _ x _ (fun l => sq_nonneg _)

lemma stationary_apply (f : X → ℝ) : ∑ x,C.π x*C.apply f x = ∑ x,C.π x*f x := by
  unfold apply
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [← mul_assoc,← Finset.sum_mul,C.stationary]

lemma stationary_squareMoment_succ (g : X → ℝ) (N : ℕ) :
    (∑ x,C.π x*C.squareMoment g (N+1) x) = (∑ x,C.π x*C.squareMoment g N x)+
      C.inner g g+2*∑ k ∈ Finset.range N,C.inner g (C.iterate (k+1) g) := by
  simp_rw [C.squareMoment_succ,mul_add,Finset.sum_add_distrib]
  rw [C.stationary_apply]
  have h₁ : (∑ x,C.π x*(g x)^2) = C.inner g g := by
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h₂ : (∑ x,C.π x*(2*g x*C.apply (C.partialResolvent N g) x)) =
      2*C.inner g (C.apply (C.partialResolvent N g)) := by
    unfold inner
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h₁,h₂]
  have hh : C.apply (C.partialResolvent N g) = fun x => ∑ k ∈ Finset.range N,C.iterate (k+1) g x := by
    change C.apply (fun x => ∑ k ∈ Finset.range N,C.iterate k g x) = _
    rw [C.apply_sum]
    simp_rw [C.iterate_succ]
  rw [hh,C.inner_sum_right]
  ring

theorem stationary_squareMoment_bound (g : X → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ H, (C.inner g H)^2 ≤ K*C.inner g g*C.energy H) (N : ℕ) :
    (∑ x,C.π x*C.squareMoment g N x) ≤ 2*N*K*C.inner g g := by
  induction N with
  | zero => simp [squareMoment]
  | succ N ih =>
    rw [C.stationary_squareMoment_succ]
    have hc := C.covariance_sum_bound g K hK hdual (N+1)
    have hh : (∑ k ∈ Finset.range (N+1),C.inner g (C.iterate k g)) = C.inner g g+
        ∑ k ∈ Finset.range N,C.inner g (C.iterate (k+1) g) := by
      rw [Finset.sum_range_succ']
      simp [add_comm]
    rw [hh] at hc
    have hg := C.inner_nonneg g
    push_cast
    nlinarith

theorem warm_squareMoment_bound (g : X → ℝ) (K U : ℝ) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hdual : ∀ H, (C.inner g H)^2 ≤ K*C.inner g g*C.energy H)
    (ν : X → ℝ) (hwarm : ∀ x,ν x ≤ U*C.π x) (N : ℕ) (hN : 0 < N) :
    (∑ x,ν x*C.squareMoment g N x)/(N:ℝ)^2 ≤ 2*U*K*C.inner g g/N := by
  have hs : (∑ x,ν x*C.squareMoment g N x) ≤ U*∑ x,C.π x*C.squareMoment g N x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hwarm x) (C.squareMoment_nonneg g N x)
  have hb := mul_le_mul_of_nonneg_left (C.stationary_squareMoment_bound g K hK hdual N) hU
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  have he : 2*U*K*C.inner g g/(N:ℝ)*(N:ℝ)^2 = U*(2*(N:ℝ)*K*C.inner g g) := by
    field_simp

  rw [he]
  exact hs.trans hb

end FiniteChain

section ObservableMSE
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma metropolisChain_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) :
    (metropolisChain gs hgs hne hcover w f hw hf).mean (fun S => G S.val) = chainMean gs w f G := by
  change (∑ S : ChainIndex gs,(chainWeight gs w f S.val/chainTotal gs w f)*G S.val) = _
  simp_rw [div_mul_eq_mul_div]
  unfold chainMean
  rw [← Finset.sum_div,chain_sum_subtype]

end ObservableMSE

namespace FiniteChain

open scoped Classical BigOperators
variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma variance_formula (f : X → ℝ) : C.variance f = C.inner f f-(C.mean f)^2 := by
  rw [variance,C.inner_sub_left,C.inner_sub_right,C.inner_sub_right]
  have h₁ : C.inner f (fun _ => C.mean f) = (C.mean f)^2 := by
    unfold inner
    rw [← Finset.sum_mul]
    change C.mean f*C.mean f = (C.mean f)^2
    ring
  have h₂ : C.inner (fun _ => C.mean f) (fun _ => C.mean f) = (C.mean f)^2 := by
    simp only [inner,← Finset.sum_mul,C.normalized,one_mul,pow_two]
  rw [h₁,C.inner_symm (fun _ => C.mean f) f,h₁,h₂]
  ring

end FiniteChain

namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance81 : Fintype X] (C : FiniteChain X)
lemma pathExpectation_mono (N : ℕ) (x : X) (F G : List X → ℝ) (h : ∀ l,F l≤G l) :
    C.pathExpectation N x F≤C.pathExpectation N x G := by
  induction N generalizing x F G with
  | zero => exact h _
  | succ N ih =>
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (ih y _ _ (fun l => h _)) (C.nonnegative x y)
lemma pathExpectation_finsum {J : Type*} (s : Finset J) (N : ℕ) (x : X) (F : J → List X → ℝ) :
    C.pathExpectation N x (fun l => ∑ j ∈ s,F j l) = ∑ j ∈ s,C.pathExpectation N x (F j) := by
  induction s using Finset.induction_on with
  | empty => simp [C.pathExpectation_const]
  | @insert j s hj ih => simp [Finset.sum_insert,hj,C.pathExpectation_add,ih]
lemma pathExpectation_congr_length (N : ℕ) (x : X) (F G : List X → ℝ)
    (h : ∀ l,l.length=N+1 → F l=G l) : C.pathExpectation N x F=C.pathExpectation N x G := by
  induction N generalizing x F G with
  | zero => exact h [x] rfl
  | succ N ih =>
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply ih
    intro l hl
    exact h (x::l) (by simp [hl])
omit sectionInstance81 in
lemma pathSum_center [Fintype X] (G : X → ℝ) (m : ℝ) (l : List X) :
    pathSum (fun x => G x-m) l = pathSum G l-(l.length:ℝ)*m := by
  induction l with
  | nil => simp [pathSum]
  | cons x l ih => simp only [pathSum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]; rw [ih]; ring

lemma pathProbability_union {J : Type*} [Fintype J] (ν : X → ℝ) (hν : ∀ x,0≤ν x)
    (N : ℕ) (E : J → List X → Prop) :
    C.pathProbability ν N (fun l => ∃ j,E j l) ≤ ∑ j,C.pathProbability ν N (E j) := by
  classical
  have h : ∀ l,(if ∃ j,E j l then (1:ℝ) else 0)≤∑ j,if E j l then 1 else 0 := by
    intro l
    by_cases he : ∃ j,E j l
    · obtain ⟨j,hj⟩ := he
      rw [ite_eq_left ⟨j,hj⟩]
      calc
        (1:ℝ) = (if E j l then 1 else 0) := by simp [hj]
        _ ≤ ∑ j,if E j l then 1 else 0 := Finset.single_le_sum (f := fun j => if E j l then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
    · simp [show ∀ j,¬E j l from fun j hj => he ⟨j,hj⟩]
  unfold pathProbability
  calc
    _ = ∑ x,ν x*C.pathExpectation N x (fun l => if ∃ j,E j l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      apply C.pathExpectation_congr
      intro l
      split_ifs <;> rfl
    _ ≤ ∑ x,ν x*C.pathExpectation N x (fun l => ∑ j,if E j l then 1 else 0) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (C.pathExpectation_mono N x _ _ h) (hν x))
    _ = _ := by simp_rw [C.pathExpectation_finsum,Finset.mul_sum]; exact Finset.sum_comm

lemma pathProbability_average_error (ν : X → ℝ) (hν : ∀ x,0≤ν x) (G : X → ℝ)
    (m t : ℝ) (ht : 0<t) (N : ℕ) (hN : 0<N) :
    C.pathProbability ν (N-1) (fun l => t < |pathSum G l/(N:ℝ)-m|) ≤
      ((∑ x,ν x*C.squareMoment (fun x => G x-m) N x)/(N:ℝ)^2)/t^2 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hpoint : ∀ l,(if t < |pathSum G l/(N:ℝ)-m| then (1:ℝ) else 0)≤
      (pathSum G l/(N:ℝ)-m)^2/t^2 := by
    intro l
    by_cases he : t < |pathSum G l/(N:ℝ)-m|
    · rw [ite_eq_left he,le_div_iff₀ (sq_pos_of_pos ht)]
      have hh := (sq_lt_sq₀ ht.le (abs_nonneg _)).mpr he
      simpa only [sq_abs,one_mul] using hh.le
    · rw [ite_eq_right he]; positivity
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (C.pathExpectation_mono (N-1) x _ _ hpoint) (hν x))
  change C.pathProbability ν (N-1) _ ≤ _ at h
  have he : ∀ x,C.pathExpectation (N-1) x (fun l => (pathSum G l/(N:ℝ)-m)^2/t^2) =
      C.squareMoment (fun x => G x-m) N x/(N:ℝ)^2/t^2 := by
    intro x
    rw [squareMoment,ite_eq_right (Nat.ne_of_gt hN)]
    have hh : C.pathExpectation (N-1) x (fun l => (pathSum G l/(N:ℝ)-m)^2/t^2) =
        C.pathExpectation (N-1) x (fun l => (1/(N:ℝ)^2/t^2)*(pathSum (fun x => G x-m) l)^2) := by
      apply C.pathExpectation_congr_length
      intro l hl
      have hl' : l.length=N := by omega
      rw [pathSum_center,hl']
      field_simp

    rw [hh,C.pathExpectation_mul]
    ring
  simp_rw [he] at h
  simpa only [← mul_div_assoc,← Finset.sum_div] using h
end

open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma variance_le_one (G : X → ℝ) (hG : ∀ x,0≤G x ∧ G x≤1) : C.variance G≤1 := by
  rw [C.variance_formula]
  have h : C.inner G G≤1 := by
    calc
      _ ≤ ∑ x,C.π x*1 := Finset.sum_le_sum (fun x _ => by
        have hx := hG x
        have hh : G x*G x≤1 := by nlinarith
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (C.positive x).le)
      _ = 1 := by simpa using C.normalized
  nlinarith [sq_nonneg (C.mean G)]

lemma relative_union_bound {J : Type*} [Fintype J]
    (ν : X → ℝ) (hν : ∀ x,0≤ν x) (G : J → X → ℝ)
    (m η v : ℝ) (hm : 0 < m) (hη : 0<η) (hv : 0≤v)
    (hmean : ∀ j,m≤C.mean (G j)) (N : ℕ) (hN : 0<N)
    (hmse : ∀ j,(∑ x,ν x*C.squareMoment (fun x => G j x-C.mean (G j)) N x)/(N:ℝ)^2≤v) :
    C.pathProbability ν (N-1) (fun l => ∃ j,η*C.mean (G j) <
      |pathSum (G j) l/(N:ℝ)-C.mean (G j)|) ≤ (Fintype.card J:ℝ)*v/(η*m)^2 := by
  calc
    _ ≤ ∑ j,C.pathProbability ν (N-1) (fun l => η*C.mean (G j) <
      |pathSum (G j) l/(N:ℝ)-C.mean (G j)|) := C.pathProbability_union ν hν (N-1) _
    _ ≤ ∑ j,v/(η*m)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have hj : 0<C.mean (G j) := hm.trans_le (hmean j)
      have ht : 0<η*C.mean (G j) := mul_pos hη hj
      have hb := C.pathProbability_average_error ν hν (G j) (C.mean (G j))
        (η*C.mean (G j)) ht N hN
      have hden : (η*m)^2≤(η*C.mean (G j))^2 := by
        exact (sq_le_sq₀ (mul_nonneg hη.le hm.le) ht.le).mpr
          (mul_le_mul_of_nonneg_left (hmean j) hη.le)
      exact hb.trans ((div_le_div_of_nonneg_right (hmse j) (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left hv (sq_pos_of_pos (mul_pos hη hm)) hden))
    _ = _ := by simp [mul_div_assoc]
end FiniteChain

section SamplingObservables
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance85 : Fintype Γ] [DecidableEq Γ]
lemma plainObservable_class (gs : List (Γ × Γ)) (g : Set Γ → ℝ) :
    ClassObservable gs (plainObservable gs g) := by
  intro p r S T hS hT
  simp [plainObservable,hS.not_plain,hT.not_plain]
lemma defectIndicator_class (gs : List (Γ × Γ)) (p r : Γ × Γ) :
    ClassObservable gs (defectIndicator gs p r) := by
  intro p' r' S T hS hT
  have he : DefectState gs p r S ↔ DefectState gs p r T := by
    constructor
    · intro h
      obtain ⟨rfl,rfl⟩ := hS.unique h
      exact hT
    · intro h
      obtain ⟨rfl,rfl⟩ := hT.unique h
      exact hS
  simp [defectIndicator,he]
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
lemma defect_mass_lower (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (hlower : ∀ p∈gs,∀ r∈gs,p≠r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
    (p r : Γ × Γ) (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    1/(20*(gs.length:ℝ)^2) ≤ chainMean gs w f (defectIndicator gs p r) := by
  rw [defectIndicator_mean gs hgs hcover w f p r hp hr hpr]
  have hc := slotDefect_pos gs f hf ∅ hgs p r hp hr hpr
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hwc : slotTotal gs f ∅/4 ≤ w p r*slotDefect gs f ∅ p r := by
    have h := (div_le_iff₀ (show 0 < 4*slotDefect gs f ∅ p r by positivity)).mp (hlower p hp r hr hpr)
    linarith
  calc
    _ = (1/(5*(gs.length:ℝ)^2))/4 := by ring
    _  ≤  (slotTotal gs f ∅/chainTotal gs w f)/4 :=
      div_le_div_of_nonneg_right (plain_mass_lower gs hgs hne hcover w f hw hf hupper) (by norm_num)
    _ = (slotTotal gs f ∅/4)/chainTotal gs w f := by ring
    _  ≤  _ := div_le_div_of_nonneg_right hwc hΛ.le
lemma chainMean_mono (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G H : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (h : ∀ S,ChainState gs S → G S ≤ H S) : chainMean gs w f G ≤ chainMean gs w f H := by
  apply div_le_div_of_nonneg_right _ (chainTotal_pos gs hgs hcover w f hf hw).le
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S (Finset.mem_filter.mp hS).2)
    (mul_nonneg (chainMultiplier_pos gs w hw S).le (hf S).le)
lemma plainObservable_mass_lower (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (hg : ∀ S,PlainState gs S → 1/2 ≤ g S)
    (hupper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    1/(20*(gs.length:ℝ)^2) ≤ chainMean gs w f (plainObservable gs g) := by
  have hm := chainMean_mono gs hgs hcover w f (plainObservable gs (fun _ =>  1/2))
    (plainObservable gs g) hw hf (by intro S hS; unfold plainObservable; split_ifs with hp; exact hg S hp; rfl)
  rw [plainObservable_mean gs hgs hcover] at hm
  have he : slotTotal gs (fun S =>  f S*(1/2)) ∅ = (1/2)*slotTotal gs f ∅ := by
    have hfun : (fun S =>  f S*(1/2)) = fun S =>  (1/2)*f S := by funext S; ring
    rw [hfun]
    exact coeffDerivs_scale _ _ _ _
  rw [he] at hm
  have hl := plain_mass_lower gs hgs hne hcover w f hw hf hupper
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hp : 0 ≤ 1/(5*(gs.length:ℝ)^2) := by positivity
  calc
    _  ≤  (1/(5*(gs.length:ℝ)^2))/2 := by field_simp; norm_num
    _  ≤  (slotTotal gs f ∅/chainTotal gs w f)/2 := div_le_div_of_nonneg_right hl (by norm_num)
    _  ≤  _ := by convert hm using 1 ; ring

lemma phaseObservables_card (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[]) :
    Fintype.card (PhaseObservables gs) ≤ 2*gs.length^2 := by
  have hn := List.length_pos_iff.mpr hne
  have hc : (defectTypes gs).card=gs.length*gs.length-gs.length := by
    rw [defectTypes,Finset.offDiag_card,List.toFinset_card_of_nodup hgs.nodup]
  simp only [PhaseObservables,Fintype.card_sum,Fintype.card_option,Fintype.card_coe,Fintype.card_unit,hc]
  have hh : gs.length ≤ gs.length*gs.length := by nlinarith
  rw [pow_two]
  omega
lemma phaseObservable_class (gs : List (Γ × Γ)) (g : Set Γ → ℝ) (j : PhaseObservables gs) :
    ClassObservable gs (phaseObservable gs g j) := by
  rcases j with (_ | pr) | u
  · exact plainObservable_class gs _
  · exact defectIndicator_class gs _ _
  · exact plainObservable_class gs _
omit sectionInstance85 in
lemma phaseObservable_bounded [Fintype Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℝ)
    (hg : ∀ S,PlainState gs S → 0 ≤ g S ∧ g S ≤ 1)
    (j : PhaseObservables gs) (S : Set Γ) :
    0 ≤ phaseObservable gs g j S ∧ phaseObservable gs g j S ≤ 1 := by
  rcases j with (_ | pr) | u
  · simp only [phaseObservable,plainObservable]; split_ifs <;> norm_num
  · simp only [phaseObservable,defectIndicator]; split_ifs <;> norm_num
  · simp only [phaseObservable,plainObservable]; split_ifs with h
    · exact hg S h
    · norm_num
lemma phaseObservable_mean_lower (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (hg : ∀ S,PlainState gs S → 1/2 ≤ g S)
    (hlower : ∀ p∈gs,∀ r∈gs,p≠r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
    (j : PhaseObservables gs) :
    1/(20*(gs.length:ℝ)^2) ≤ chainMean gs w f (phaseObservable gs g j) := by
  rcases j with (_ | pr) | u
  · exact plainObservable_mass_lower gs hgs hne hcover w f _ hw hf (by intros; norm_num) hupper
  · obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr.val).mp pr.property
    exact defect_mass_lower gs hgs hne hcover w f hw hf hlower hupper _ _ hp hr hpr
  · exact plainObservable_mass_lower gs hgs hne hcover w f g hw hf hg hupper

end SamplingObservables

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma pathProbability_congr_length (ν : X → ℝ) (N : ℕ) (E F : List X → Prop)
    (h : ∀ l,l.length=N+1 → (E l ↔ F l)) :
    C.pathProbability ν N E=C.pathProbability ν N F := by
  unfold pathProbability
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply C.pathExpectation_congr_length
  intro l hl
  simp only [h l hl]
end FiniteChain
open scoped BigOperators Classical

end

section

open scoped BigOperators Classical
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma chainTotal_completion (gs : List (Γ × Γ)) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : chainTotal gs w (completeDegree f gs.length) = chainTotal gs w f := by
  unfold chainTotal chainWeight
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [completeDegree, hd, ite_true, if_true]

end ContingencyTables.ObservableBounds

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteIndependentAverages
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of averages of actual independent finite experiments -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

lemma mean_bounds (g : X → ℝ) (L U : ℝ) (hg : ∀ x,L ≤ g x ∧ g x ≤ U) :
    L ≤ uniformAverage g ∧ uniformAverage g ≤ U := by
  constructor
  · simpa only [uniformAverage_const] using uniformAverage_mono (fun _ : X => L) g (fun x => (hg x).1)
  · simpa only [uniformAverage_const] using uniformAverage_mono g (fun _ : X => U) (fun x => (hg x).2)

end

end ContingencyTables.FiniteIndependentAverages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteChainSlowdown
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact holding slowdown of finite reversible chains -/

namespace ContingencyTables.FiniteChainSlowdown

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X]

/-- Every off-diagonal move and the Dirichlet energy are scaled by the
same holding factor. No irreducibility or nonzero denominator is needed. -/
theorem energy (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (f : X → ℝ) :
    (slow C a ha0 ha1).energy f=a*C.energy f := by
  rw [FiniteChain.energy_eq,FiniteChain.energy_eq,←mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  change C.π x*(a*C.P x y+if x=y then 1-a else 0)*(f x-f y)^2=
    a*(C.π x*C.P x y*(f x-f y)^2)
  by_cases h : x=y
  · subst y
    simp
  · simp only [h,ite_false,add_zero]
    ring

end

end ContingencyTables.FiniteChainSlowdown

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrajectory
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The observed Boolean trajectory has the source path law

The finite history stores the visited prefix. Its exact real reference
expectation is the manuscript's list-path expectation, so the row error
controls events involving all empirical observations simultaneously.
-/

namespace ContingencyTables.CompanionPhaseTrajectory

open CommonBasesFPRAS RealKernelApproximation CompanionBooleanPhase
open FirstSuccess ResidualMixture FiniteLawMoments
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

lemma position_put {N : ℕ} (a : PathState X N) (x : X) (h : a.1.val<N) :
    (pathPut a x).1.val=a.1.val+1 := by
  simp only [pathPut,nextPosition,min_eq_left (Nat.succ_le_of_lt h)]

end

end ContingencyTables.CompanionPhaseTrajectory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteTraceSlowdown
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace transition matrices under an exact holding slowdown -/

namespace ContingencyTables.FiniteChainSlowdown

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {Y : Type*} [Fintype Y]

variable {X : Type*} [Fintype X]

lemma inner (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (f g : X → ℝ) : (slow C a ha0 ha1).inner f g=C.inner f g := rfl

/-- The observable dual estimate is also stable under the holding
factor. This is the estimate used by trajectory concentration; a full
spectral gap for unrelated observables is not needed. -/
theorem dual_bound (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : 1/2 ≤ a) (K : ℝ) (hK : 0 ≤ K) (g H : X → ℝ)
    (h : (C.inner g H)^2 ≤ K*C.inner g g*C.energy H) :
    ((slow C a ha0 ha1).inner g H)^2 ≤
      (2*K)*(slow C a ha0 ha1).inner g g*(slow C a ha0 ha1).energy H := by
  have he : C.energy H ≤ 2*(slow C a ha0 ha1).energy H := by
    rw [energy]
    have hm := mul_le_mul_of_nonneg_right ha (C.energy_nonneg H)
    linarith
  rw [inner,inner]
  calc
    _ ≤ K*C.inner g g*C.energy H := h
    _ ≤ K*C.inner g g*(2*(slow C a ha0 ha1).energy H) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hK (C.inner_nonneg g))
    _ = _ := by ring

/-- Thus all accepted warm-start trajectory moment estimates transfer
to the implemented holding chain with a factor of at most two. -/
theorem warm_moment_bound (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : 1/2 ≤ a) (K U : ℝ) (hK : 0 ≤ K) (hU : 0 ≤ U) (g : X → ℝ)
    (hdual : ∀ H,(C.inner g H)^2 ≤ K*C.inner g g*C.energy H)
    (nu : X → ℝ) (hwarm : ∀ x,nu x ≤ U*C.π x) (N : ℕ) (hN : 0 < N) :
    (∑ x,nu x*(slow C a ha0 ha1).squareMoment g N x)/(N:ℝ)^2 ≤
      4*U*K*C.inner g g/N := by
  have hh := (slow C a ha0 ha1).warm_squareMoment_bound g (2*K) U
    (mul_nonneg (by norm_num) hK) hU
    (fun H => dual_bound C a ha0 ha1 ha K hK g H (hdual H)) nu hwarm N hN
  simpa only [inner,show 2*U*(2*K)=4*U*K by ring] using hh

end

end ContingencyTables.FiniteChainSlowdown

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

end ContingencyTables.RootedAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedMultiplierUpdate
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

end ContingencyTables.RootedMultiplierUpdate

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root Boolean row law and full-history perturbation -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates RootedOracleAcceptance
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open FiniteLawMoments RealKernelApproximation
open CompanionBooleanPhase (State proposal proposalBits proposal_codes stepBits stepWordEquiv
  slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma chain_eq {X : Type*} [Fintype X] (C D : FiniteChain X)
    (hP : C.P=D.P) (hpi : C.π=D.π) : C=D := by
  cases C
  cases D
  dsimp only at hP hpi
  cases hP
  cases hpi
  rfl

/-- The degree completion used to prove the signature and concentration
theorems leaves every state and transition of the literal chain intact. -/
theorem referenceChain_eq_completed (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) :
    referenceChain A R j hp w hw=
      metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
        (fun p q => (w p q:ℝ))
        (DegreeCompletion.completeDegree (RootedAnnealing.weight A R j)
          (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length)
        (fun p q => by exact_mod_cast hw p q)
        (DegreeCompletion.completeDegree_positive _ _ (RootedWarmStart.actual_degree A R j).1) := by
  have he (U : State A) :
      chainWeight pairs (fun p q => (w p q:ℝ))
          (DegreeCompletion.completeDegree (RootedAnnealing.weight A R j)
            (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length) U.val=
        chainWeight pairs (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j) U.val := by
    simp only [chainWeight,DegreeCompletion.completeDegree,
      U.property.ncard PairedLabels.fresh PairedLabels.cover,ite_true, if_true]
  apply chain_eq
  · funext S T
    dsimp only [referenceChain,metropolisChain,FiniteChain.ofMoves]
    simp only [metropolisMove,he]
  · funext S
    dsimp only [referenceChain,metropolisChain,FiniteChain.ofMoves]
    rw [ObservableBounds.chainTotal_completion _ _ _ PairedLabels.fresh PairedLabels.cover,he]

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedSlowConcentration
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root dyadic phase concentration -/

namespace ContingencyTables.RootedSlowConcentration

open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing RootedMultiplierUpdate
open RootedBooleanPhase CompanionRationalUpdates TwoLiftStates ObservableBounds
open RootedWarmStart (actual_degree)
open CompanionConcentration (pairs_ne_nil square_width_one_le)
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open ObservableTrajectory FiniteChainSlowdown
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

private lemma constant_nonnegative (A : Instance I J) :
    0≤observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
  unfold observableConstant
  positivity

lemma target_mean (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (G : Set (Labels A×Bool) → ℝ) :
    (targetChain A R j hp w hw).mean (fun S => G S.val)=
      chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G := by
  change (referenceChain A R j hp w hw).mean (fun S => G S.val)=_
  exact metropolisChain_mean _ _ _ _ _ _ _ _ _

/-- Mean-square concentration of the real chain implemented by the
actual padded proposal. -/
theorem bounded_MSE (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (o : PhaseObservables (pairs : List (Pair A)))
    (nu : State A → ℝ)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (N : ℕ) (hN : 0<N) :
    let D := targetChain A R j hp w hw
    let G := fun S : State A => phaseObservable pairs (ratio A R j) o S.val
    (∑ S,nu S*D.squareMoment (fun S => G S-D.mean G) N S)/(N:ℝ)^2≤
      40*(Fintype.card (Labels A):ℝ)^2*
        observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/N := by
  let C := referenceChain A R j hp w hw
  let D := targetChain A R j hp w hw
  let G : Set (Labels A×Bool) → ℝ := phaseObservable pairs (ratio A R j) o
  let g : State A → ℝ := fun S => G S.val-
    chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G
  let K := observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)
  have hdual (H : State A → ℝ) : (C.inner g H)^2≤K*C.inner g g*C.energy H := by
    dsimp only [C]
    rw [referenceChain_eq_completed]
    simpa only [K,PairedLabels.length,g,G] using
      omission_chain_dual pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
        (fun p q => (w p q:ℝ)) (weight A R j) G hgood.positive
        (actual_degree A R j).1 (actual_degree A R j).2 ((A.W:ℝ)^2) (square_width_one_le A)
        (phaseObservable_class pairs (ratio A R j) o) hgood.lower hgood.upper H
  have hcmean : C.mean (fun S => G S.val)=
      chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G := by
    exact target_mean A R j hp w hw G
  have hvar : C.inner g g≤1 := by
    have hb := C.variance_le_one (fun S => G S.val) (by
      intro S
      exact phaseObservable_bounded pairs (ratio A R j)
        (fun T _ => ⟨by linarith [(ratio_bounds A R j T).1],(ratio_bounds A R j T).2⟩) o S.val)
    simpa only [FiniteChain.variance,hcmean,g] using hb
  have hwm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*C.π S := by
    intro S
    have hpi : C.π S=chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j) := rfl
    rw [hpi]
    simpa only [mul_div_assoc] using hwarm S
  have hm := warm_moment_bound C (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2
    (slowdown_bounds A hp).1 K (10*(Fintype.card (Labels A):ℝ)^2)
    (constant_nonnegative A) (by positivity) g hdual nu hwm N hN
  have hmean : D.mean (fun S => G S.val)=
      chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G := target_mean A R j hp w hw G
  change (∑ S,nu S*D.squareMoment (fun S => G S.val-D.mean (fun S => G S.val)) N S)/(N:ℝ)^2≤_
  rw [hmean]
  apply hm.trans
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
  apply div_le_div_of_nonneg_right _ hN0
  have hmul := mul_le_mul_of_nonneg_left hvar
    (show 0≤4*(10*(Fintype.card (Labels A):ℝ)^2)*K from by
      have := constant_nonnegative A
      dsimp only [K]
      positivity)
  nlinarith

/-- The full collection of phase observables obeys the source union
bound for the actual dyadic holding chain. -/
theorem phase_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : State A → ℝ) (hnu : ∀ S,0≤nu S)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (N : ℕ) (hN : 0<N) (eta : ℝ) (heta : 0<eta) :
    let D := targetChain A R j hp w hw
    D.pathProbability nu (N-1) (fun l => ∃ o : PhaseObservables (pairs : List (Pair A)),
      eta*D.mean (fun S => phaseObservable pairs (ratio A R j) o S.val)<
        |FiniteChain.pathSum (fun S => phaseObservable pairs (ratio A R j) o S.val) l/(N:ℝ)-
          D.mean (fun S => phaseObservable pairs (ratio A R j) o S.val)|)≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/((N:ℝ)*eta^2) := by
  let D := targetChain A R j hp w hw
  let p : ℝ := Fintype.card (Labels A)
  let K := observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)
  have hpR : 0<p := by dsimp only [p]; exact_mod_cast hp
  have hK : 0≤K := constant_nonnegative A
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hmean (o : PhaseObservables (pairs : List (Pair A))) :
      1/(20*p^2)≤D.mean (fun S => phaseObservable pairs (ratio A R j) o S.val) := by
    rw [target_mean]
    have hh := phaseObservable_mean_lower pairs PairedLabels.fresh (pairs_ne_nil A hp)
      PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
      hgood.positive (weight_positive A R j) (fun S _ => (ratio_bounds A R j S).1)
      hgood.lower hgood.upper o
    simpa only [p,PairedLabels.length] using hh
  have hb := D.relative_union_bound nu hnu
    (fun o S => phaseObservable pairs (ratio A R j) o S.val)
    (1/(20*p^2)) eta (40*p^2*K/N) (by positivity) heta (by positivity)
    hmean N hN (fun o => bounded_MSE A R j hp w hw hgood o nu hwarm N hN)
  have hJ : (Fintype.card (PhaseObservables (pairs : List (Pair A))):ℝ)≤2*p^2 := by
    have hc := phaseObservables_card pairs PairedLabels.fresh (pairs_ne_nil A hp)
    simp only [PairedLabels.length] at hc
    dsimp only [p]
    exact_mod_cast hc
  apply hb.trans
  calc
    _ ≤ (2*p^2)*(40*p^2*K/N)/(eta*(1/(20*p^2)))^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hJ (by positivity)) (sq_nonneg _)
    _ = 32000*p^8*K/((N:ℝ)*eta^2) := by
      field_simp [hpR.ne',heta.ne',hNR.ne']
      ring

end
end ContingencyTables.RootedSlowConcentration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseExperiment
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the selected-root executed finite-word phase history -/

namespace ContingencyTables.RootedPhaseExperiment

open CommonBasesFPRAS FirstSuccess RealKernelApproximation
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionRationalUpdates RootedAnnealing RootedMultiplierUpdate
open RootedTraceWords TwoLiftStates GridBoundary
open CompanionPhaseTrajectory (position_put historyPrefix)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (State stepBits)
open scoped BigOperators Classical

noncomputable section

private lemma wordWalk_position {X : Type*} {k : ℕ}
    (step : X → (Fin k → Bool) → X) (N n : ℕ) (x : X) :
    n≤N → ∀ bits : Fin n → Fin k → Bool,
      (wordWalk (fun a b => pathPut a (step (pathRead a) b))
        (pathInitial N x) n bits).1.val=n := by
  induction n with
  | zero => intro _ bits; rfl
  | succ n ih =>
    intro hn bits
    let a := wordWalk (fun a b => pathPut a (step (pathRead a) b))
      (pathInitial N x) n (Fin.init bits)
    have ha : a.1.val=n := ih (by omega) (Fin.init bits)
    have hlt : a.1.val<N := by omega
    change (pathPut a (step (pathRead a) (bits (Fin.last n)))).1.val=n+1
    rw [position_put a _ hlt,ha]

private lemma full_prefix {X : Type*} {N : ℕ} (a : PathState X N)
    (ha : a.1.val=N) : historyPrefix a=List.ofFn a.2 := by
  unfold historyPrefix
  simp only [ha]
  congr 1

variable {I J : Type} [Fintype I] [Fintype J]

theorem observedStates_list (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    List.ofFn (observedStates A R C K j k N hK hW xi v w S bits)=
      (historyPrefix (RootedArithmeticStep.recordedWalk
        A R C K j k N N hK hW xi v w S bits)).map Subtype.val := by
  have hp := wordWalk_position (RootedArithmeticStep.step A R C K j k hK hW xi v w)
    N N S le_rfl (oracleWalkWordEquiv N (stepBits A C K j k xi) bits)
  change (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits).1.val=N at hp
  rw [full_prefix _ hp,List.map_ofFn]
  rfl

private lemma accuratePath_iff (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (eta : ℝ) (l : List (State A)) (hlen : l.length=N+1) :
    (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
      eta (l.map Subtype.val)) ↔
    ∃ o : PhaseObservables (pairs : List (Pair A)),
      eta*(targetChain A R j hp w hw).mean
        (fun S => phaseObservable pairs (ratio A R j) o S.val)<
      |FiniteChain.pathSum (fun S => phaseObservable pairs (ratio A R j) o S.val) l/(N+1:ℕ)-
        (targetChain A R j hp w hw).mean
          (fun S => phaseObservable pairs (ratio A R j) o S.val)| := by
  simp only [AccuratePhase,not_forall,not_le,empirical,List.map_map,List.length_map,
    hlen,FiniteChain.pathSum,RootedSlowConcentration.target_mean,Function.comp_def]

private theorem reference_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : State A → ℝ) (hnu : ∀ S,0≤nu S)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (eta : ℝ) (heta : 0<eta) :
    (targetChain A R j hp w hw).pathProbability nu N (fun l =>
      ¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (l.map Subtype.val))≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2) := by
  have he := (targetChain A R j hp w hw).pathProbability_congr_length nu N _ _
    (fun l hl => accuratePath_iff A R j N hp w hw eta l hl)
  rw [he]
  simpa only [Nat.add_sub_cancel] using
    RootedSlowConcentration.phase_failure A R j hp w hw hgood nu hnu hwarm
      (N+1) (by omega) eta heta

/-- The actual recorded finite-word trajectory satisfies the source
concentration bound plus the accumulated proved one-step error. -/
theorem observed_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : State A → ℝ) (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (eta : ℝ) (heta : 0<eta) :
    (∑ S,nu S*uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits)))))≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  let E : List (State A) → Prop := fun l =>
    ¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
      eta (l.map Subtype.val)
  let err : ℝ := (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)
  have herr : 0≤err := by dsimp only [err]; positivity
  have hpoint (S : State A) :
      uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
        eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
          eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))≤
      (targetChain A R j hp w hw).pathExpectation N S (fun l => eventIndicator (E l))+err := by
    simpa only [observedStates_list] using
      arithmetic_recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1
        hPL hCheeger v hp w hw N S E
  have hs := Finset.sum_le_sum (fun S (_ : S∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint S) (hnu S))
  have hm := mul_le_mul_of_nonneg_right hmass herr
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,one_mul] at hs hm
  dsimp only [err] at hs hm
  have href := reference_failure A R j N hp w hw hgood nu hnu hwarm eta heta
  change (∑ S,nu S*(targetChain A R j hp w hw).pathExpectation N S
    (fun l => eventIndicator (E l)))≤_ at href
  exact hs.trans (by linarith)

end
end ContingencyTables.RootedPhaseExperiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedObservationStart
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual phase observations from an approximate warm start -/

namespace ContingencyTables.RootedObservationStart

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity RootedAnnealing RootedMultiplierUpdate
open RootedPhaseExperiment RootedPhaseWords
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseWords (phaseBits Stored)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma bounded_expectation_error {X : Type*} [Fintype X]
    (p q g : X → ℝ) (hg : ∀ x,0 ≤ g x ∧ g x ≤ 1) :
    (∑ x,p x*g x) ≤ (∑ x,q x*g x)+2*distance p q := by
  have hp (x : X) : p x*g x ≤ q x*g x+|p x-q x| := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (p x-q x)) (hg x).1
    have h2 := mul_le_mul_of_nonneg_left (hg x).2 (abs_nonneg (p x-q x))
    nlinarith
  have h := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => hp x)
  simp only [Finset.sum_add_distrib] at h
  unfold distance
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

theorem observed_failure_near_oai (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0 < w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (p q : State A → ℝ) (hq : ∀ S,0 ≤ q S) (hmass : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (eta : ℝ) (heta : 0 < eta) :
    (∑ S,p S*uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+2*distance p q := by
  let g : State A → ℝ := fun S =>
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))
  have hg (S : State A) : 0 ≤ g S ∧ g S ≤ 1 := by
    apply FiniteIndependentAverages.mean_bounds _ 0 1
    intro bits
    unfold eventIndicator
    split_ifs <;> norm_num
  have he := bounded_expectation_error p q g hg
  have hs := observed_failure A R C hC K j k N hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw hgood q hq hmass hwarm eta heta
  dsimp only [g] at he
  have hsadd := _root_.add_le_add hs (le_refl (2*distance p q))
  have hb := he.trans hsadd
  exact hb

end
end ContingencyTables.RootedObservationStart

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.RootedObservationStart.observed_failure_near_oai := @OAI.ContingencyTables.RootedObservationStart.observed_failure_near_oai
