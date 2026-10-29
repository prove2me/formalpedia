-- Prove2me | solution 1 for OAI.ContingencyTables.exactSampling
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T05:00:09.178997+00:00
-- url     : https://prove2.me/submissions/08460994-df40-40c2-816e-fb7c192fb345

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Definitions.Def_OAIQ089A010
import Theorems.Thm_OAI_ContingencyTables_ExactGatePolynomial_public_bound
import Theorems.Thm_OAI_ContingencyTables_ExactGatePublic_failure
import Theorems.Thm_OAI_ContingencyTables_ExactGatePublic_table_prefix
import Theorems.Thm_OAI_ContingencyTables_ExactPublicCost_table_prefix
import Theorems.Thm_OAI_ContingencyTables_ExactPublicLaw_haltMass_limit
import Theorems.Thm_OAI_ContingencyTables_ExactPublicLaw_halted_feasible
import Theorems.Thm_OAI_ContingencyTables_ExactPublicLaw_tableMass_limit
import Theorems.Thm_OAI_ContingencyTables_ExactTablePrefix_failure_bound
import Theorems.Thm_OAI_ContingencyTables_SmallGraphProfiles_exact_public_correction_bound

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

open scoped BigOperators Classical

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

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerCoarea
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted finite coarea for the published Cheeger input -/
namespace ContingencyTables.CheegerProof
open MeasureTheory CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

lemma level_eq (a : ℝ) :
    level a = Set.indicator (Set.Ico 0 a) (fun _ => (1:ℝ)) := by
  funext t
  simp [level,Set.indicator_apply,Set.mem_Ico]

lemma level_integrable (a : ℝ) : Integrable (level a) := by
  rw [level_eq]
  exact (integrableOn_const (isCompact_Icc.measure_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc 0 a)).mono_set
      Set.Ico_subset_Icc_self |>.integrable_indicator measurableSet_Ico

lemma level_integral {a : ℝ} (ha : 0 ≤ a) : ∫ t, level a t = a := by
  rw [level_eq,integral_indicator measurableSet_Ico]
  simp [ha]

lemma level_abs_sub (a b t : ℝ) :
    |level a t-level b t| = level a t+level b t-2*level (min a b) t := by
  simp only [level,lt_min_iff]
  by_cases h₀ : 0 ≤ t <;> by_cases ha : t < a <;> by_cases hb : t < b <;>
    norm_num [h₀,ha,hb]

lemma level_abs_integrable (a b : ℝ) : Integrable (fun t => |level a t-level b t|) :=
  ((level_integrable a).sub (level_integrable b)).abs

lemma level_abs_integral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ t, |level a t-level b t| = |a-b| := by
  simp_rw [level_abs_sub]
  rw [integral_sub (f := fun t => level a t+level b t)
      ((level_integrable a).add (level_integrable b))
      ((level_integrable (min a b)).const_mul 2),
    integral_add (level_integrable a) (level_integrable b),integral_const_mul,
    level_integral ha,level_integral hb,level_integral (le_min ha hb)]
  rcases le_total a b with h | h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring

variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma mass_mono {S T : Finset X} (h : S ⊆ T) : mass C S ≤ mass C T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => (C.positive x).le)

lemma mass_compl (S : Finset X) : mass C Sᶜ = 1-mass C S := by
  have h := Finset.sum_compl_add_sum S C.π
  rw [C.normalized] at h
  dsimp [mass]
  linarith

lemma cut_indicator (S : Finset X) :
    (∑ x, ∑ y, C.π x*C.P x y*
      |(if x ∈ S then (1:ℝ) else 0)-(if y ∈ S then (1:ℝ) else 0)|) = 2*cut C S := by
  have hs (x y : X) : C.π x*C.P x y*
      |(if x ∈ S then (1:ℝ) else 0)-(if y ∈ S then (1:ℝ) else 0)| =
      (if x ∈ S ∧ y ∉ S then C.π x*C.P x y else 0)+
      (if y ∈ S ∧ x ∉ S then C.π x*C.P x y else 0) := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx,hy]
  simp_rw [hs,Finset.sum_add_distrib]
  have hforward : (∑ x, ∑ y, if x ∈ S ∧ y ∉ S then C.π x*C.P x y else 0) = cut C S := by
    simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_filter]
    congr 1
    ext y
    simp
  have hback : (∑ x, ∑ y, if y ∈ S ∧ x ∉ S then C.π x*C.P x y else 0) = cut C S := by
    rw [Finset.sum_comm]
    simpa only [C.reversible] using hforward
  rw [hforward,hback]
  ring

/-- Coarea on a function supported on a set of stationary mass at most one half. -/
theorem coarea (κ : ℝ)
    (hcut : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hsmall : mass C (Finset.univ.filter fun x => 0 < g x) ≤ 1/2) :
    2*κ*(∑ x, C.π x*g x) ≤ ∑ x, ∑ y, C.π x*C.P x y*|g x-g y| := by
  let F : ℝ → ℝ := fun t => 2*κ*∑ x, C.π x*level (g x) t
  let J : ℝ → ℝ := fun t => ∑ x, ∑ y, C.π x*C.P x y*|level (g x) t-level (g y) t|
  have hF : Integrable F :=
    (integrable_finsetSum _ (fun x _ => (level_integrable (g x)).const_mul (C.π x))).const_mul _
  have hJ : Integrable J := integrable_finsetSum _ fun x _ =>
    integrable_finsetSum _ fun y _ => (level_abs_integrable (g x) (g y)).const_mul _
  have hle (t : ℝ) : F t ≤ J t := by
    let S := Finset.univ.filter fun x => 0 ≤ t ∧ t < g x
    have hi (x : X) : level (g x) t = if x ∈ S then 1 else 0 := by simp [level,S]
    have hm : mass C S ≤ 1/2 := (mass_mono C (by
      intro x hx
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx.1.trans_lt hx.2⟩)).trans hsmall
    have hc := hcut S
    rw [mass_compl,min_eq_left (by linarith : mass C S ≤ 1-mass C S)] at hc
    have hl : (∑ x, C.π x*level (g x) t) = mass C S := by
      simp only [hi,mul_ite,mul_one,mul_zero,mass]
      rw [← Finset.sum_filter]
      simp
    dsimp [F,J]
    rw [hl]
    simp only [hi,cut_indicator]
    linarith
  have H := integral_mono hF hJ hle
  dsimp [F,J] at H
  rw [integral_const_mul,integral_finsetSum _ (fun x _ => (level_integrable (g x)).const_mul _)] at H
  simp_rw [integral_const_mul,level_integral (hg _)] at H
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _
    (fun y _ => (level_abs_integrable (g x) (g y)).const_mul _))] at H
  simp_rw [integral_finsetSum _ (fun y _ => (level_abs_integrable _ _).const_mul _),
    integral_const_mul,level_abs_integral (hg _) (hg _)] at H
  exact H

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerMedian
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A stationary weighted median on a finite chain -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section
variable {X : Type*} [Fintype X] (C : FiniteChain X)

theorem exists_median (f : X → ℝ) : ∃ a : ℝ,
    mass C (Finset.univ.filter fun x => f x < a) ≤ 1/2 ∧
    mass C (Finset.univ.filter fun x => a < f x) ≤ 1/2 := by
  have hne : (Finset.univ : Finset X).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have h := C.normalized
    rw [hz,Finset.sum_empty] at h
    norm_num at h
  let M := Finset.univ.filter fun x =>
    1/2 ≤ mass C (Finset.univ.filter fun y => f y ≤ f x)
  have hM : M.Nonempty := by
    obtain ⟨x,hx,hm⟩ := Finset.exists_max_image Finset.univ f hne
    have he : (Finset.univ.filter fun y => f y ≤ f x) = Finset.univ := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact iff_true_intro (hm y (Finset.mem_univ _))
    refine ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩⟩
    rw [he]
    simp only [mass,C.normalized]
    norm_num
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image M f hM
  have hxM : 1/2 ≤ mass C (Finset.univ.filter fun y => f y ≤ f x) :=
    (Finset.mem_filter.mp hx).2
  refine ⟨f x,?_,?_⟩
  · let L := Finset.univ.filter fun y => f y < f x
    change mass C L ≤ 1/2
    by_contra hn
    have hL : 1/2 < mass C L := lt_of_not_ge hn
    have hLn : L.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hL
      norm_num [mass] at hL
    obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image L f hLn
    have hyx : f y < f x := (Finset.mem_filter.mp hy).2
    have he : (Finset.univ.filter fun z => f z ≤ f y) = L := by
      ext z
      simp only [L,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun hz => hz.trans_lt hyx,fun hz => hymax z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)⟩
    have hyM : y ∈ M := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [he]
      exact hL.le
    exact (not_lt_of_ge (hmin y hyM)) hyx
  · have he : (Finset.univ.filter fun y => f y ≤ f x)ᶜ =
        Finset.univ.filter (fun y => f x < f y) := by
      ext y
      simp
    have h := mass_compl C (Finset.univ.filter fun y => f y ≤ f x)
    rw [he] at h
    linarith

theorem variance_le_centered (f : X → ℝ) (a : ℝ) :
    C.variance f ≤ ∑ x, C.π x*(f x-a)^2 := by
  have he : (∑ x, C.π x*(f x-a)^2) = C.inner f f-2*a*C.mean f+a^2 := by
    calc
      _ = (∑ x, C.π x*f x*f x)-2*a*(∑ x,C.π x*f x)+a^2*(∑ x,C.π x) := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [C.normalized,mul_one]; rfl
  rw [C.variance_formula,he]
  nlinarith [sq_nonneg (C.mean f-a)]

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerPositive
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cheeger energy bound for functions supported on half the mass -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

private lemma weighted_cauchy {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i*a i*b i)^2 ≤ (∑ i, w i*(a i)^2)*(∑ i, w i*(b i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)*a i) (fun i => Real.sqrt (w i)*b i)
  have hmul (i : ι) : (Real.sqrt (w i)*a i)*(Real.sqrt (w i)*b i) = w i*a i*b i := by
    calc
      _ = (Real.sqrt (w i))^2*a i*b i := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i)]
  have hsq (f : ι → ℝ) (i : ι) : (Real.sqrt (w i)*f i)^2 = w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  simpa only [hmul,hsq] using h

variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma sum_pair_squares (g : X → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*((g x)^2+(g y)^2)) = 2*(∑ x, C.π x*(g x)^2) := by
  simp_rw [mul_add,Finset.sum_add_distrib]
  have hleft : (∑ x, ∑ y, C.π x*C.P x y*(g x)^2) = ∑ x, C.π x*(g x)^2 := by
    simp_rw [← Finset.sum_mul,← Finset.mul_sum,C.stochastic,mul_one]
  have hright : (∑ x, ∑ y, C.π x*C.P x y*(g y)^2) = ∑ y, C.π y*(g y)^2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,C.stationary]
  rw [hleft,hright]
  ring

lemma sum_pair_add_square_le (g : X → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*(g x+g y)^2) ≤ 4*(∑ x, C.π x*(g x)^2) := by
  calc
    _ ≤ ∑ x, ∑ y, 2*(C.π x*C.P x y*((g x)^2+(g y)^2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hQ := mul_nonneg (C.positive x).le (C.nonnegative x y)
      have hsq : (g x+g y)^2 ≤ 2*((g x)^2+(g y)^2) := by nlinarith [sq_nonneg (g x-g y)]
      nlinarith [mul_le_mul_of_nonneg_left hsq hQ]
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [sum_pair_squares]; ring

theorem positive_energy (κ : ℝ) (hk : 0 < κ)
    (hcut : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hsmall : mass C (Finset.univ.filter fun x => 0 < g x) ≤ 1/2) :
    κ^2*(∑ x, C.π x*(g x)^2) ≤ 2*C.energy g := by
  let N := ∑ x, C.π x*(g x)^2
  let W := ∑ x, ∑ y, C.π x*C.P x y*|(g x)^2-(g y)^2|
  have hE : 0 ≤ C.energy g := C.energy_nonneg g
  have hN : 0 ≤ N := Finset.sum_nonneg fun x _ => mul_nonneg (C.positive x).le (sq_nonneg _)
  have hW : 0 ≤ W := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (C.positive x).le (C.nonnegative x y)) (abs_nonneg _)
  have hsquare : mass C (Finset.univ.filter fun x => 0 < (g x)^2) ≤ 1/2 := by
    apply le_trans (mass_mono C ?_) hsmall
    intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    nlinarith [hg x]
  have hc : 2*κ*N ≤ W := coarea C κ hcut (fun x => (g x)^2) (fun _ => sq_nonneg _) hsquare
  have hsqW : (2*κ*N)^2 ≤ W^2 := (sq_le_sq₀ (by positivity) hW).mpr hc
  have ha (x y : X) : |(g x)^2-(g y)^2| = |g x-g y| * (g x+g y) := by
    rw [show (g x)^2-(g y)^2 = (g x-g y)*(g x+g y) by ring,
      abs_mul,abs_of_nonneg (add_nonneg (hg x) (hg y))]
  have hcs := weighted_cauchy
    (fun z : X×X => C.π z.1*C.P z.1 z.2)
    (fun z => |g z.1-g z.2|) (fun z => g z.1+g z.2)
    (fun z => mul_nonneg (C.positive _).le (C.nonnegative _ _))
  simp only [Fintype.sum_prod_type,sq_abs] at hcs
  have he : (∑ x, ∑ y, C.π x*C.P x y*(g x-g y)^2) = 2*C.energy g := by
    rw [C.energy_eq]; ring
  have hW' : W = ∑ x, ∑ y, C.π x*C.P x y*|g x-g y| * (g x+g y) := by
    dsimp [W]
    simp_rw [ha,mul_assoc]
  rw [← hW',he] at hcs
  have hb := sum_pair_add_square_le C g
  have hall : (2*κ*N)^2 ≤ (2*C.energy g)*(4*N) :=
    (hsqW.trans hcs).trans (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*C.energy g))
  rcases hN.eq_or_lt with hz | hp
  · change κ^2*N ≤ _
    rw [← hz,mul_zero]
    positivity
  · change κ^2*N ≤ _
    have h : 4*N*(κ^2*N) ≤ 4*N*(2*C.energy g) := by nlinarith [hall]
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*N)).mp h

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.KLS_Convexity_PrekopaLeindler
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace AsymptoticStatistics

private theorem prekopaLeindler_1d_levelInclusion
    {f g h : ℝ → ℝ≥0∞}
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤) :
    t • {x | α < f x} + (1 - t) • {y | α < g y} ⊆ {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨_, hu, _, hv, rfl⟩ := hz
  rw [Set.mem_smul_set] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv

  simp only [smul_eq_mul, Set.mem_ofPred_eq] at hx hy ⊢

  have h_alpha_split : α = α ^ t * α ^ (1 - t) := by
    rw [← ENNReal.rpow_add t (1 - t) hα_pos.ne' hα_top]
    have ht_one : t + (1 - t) = (1 : ℝ) := by ring
    rw [ht_one, ENNReal.rpow_one]

  have h1 : α ^ t < f x ^ t := ENNReal.rpow_lt_rpow hx ht_pos
  have h2 : α ^ (1 - t) < g y ^ (1 - t) := ENNReal.rpow_lt_rpow hy h1t_pos

  have h3 : α ^ t * α ^ (1 - t) < f x ^ t * g y ^ (1 - t) := ENNReal.mul_lt_mul h1 h2

  calc α = α ^ t * α ^ (1 - t) := h_alpha_split
    _ < f x ^ t * g y ^ (1 - t) := h3
    _ ≤ h (t * x + (1 - t) * y) := h_le x y

private lemma oneDim_brunn_minkowski_compact_le
    {K_A K_B : Set ℝ}
    (hA_compact : IsCompact K_A) (hB_compact : IsCompact K_B)
    (hA_ne : K_A.Nonempty) (hB_ne : K_B.Nonempty) :
    volume K_A + volume K_B ≤ volume (K_A + K_B) := by

  set a := sSup K_A with ha_def
  set b := sInf K_B with hb_def
  have ha_mem : a ∈ K_A := hA_compact.sSup_mem hA_ne
  have hb_mem : b ∈ K_B := hB_compact.sInf_mem hB_ne
  have hA_le_a : ∀ x ∈ K_A, x ≤ a :=
    fun x hx => le_csSup hA_compact.bddAbove hx
  have hB_ge_b : ∀ y ∈ K_B, b ≤ y :=
    fun y hy => csInf_le hB_compact.bddBelow hy

  set U : Set ℝ := K_A + {b} with hU_def
  set V : Set ℝ := {a} + K_B with hV_def

  have hU_sub_AB : U ⊆ K_A + K_B := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    exact ⟨x, hx, b, hb_mem, rfl⟩
  have hV_sub_AB : V ⊆ K_A + K_B := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    exact ⟨a, ha_mem, y, hy, rfl⟩

  have hU_vol : volume U = volume K_A := by
    rw [hU_def, Set.add_singleton, Set.image_add_right]
    exact MeasureTheory.measure_preimage_add_right volume (-b) K_A

  have hV_vol : volume V = volume K_B := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact MeasureTheory.measure_preimage_add volume (-a) K_B

  have hU_sub_Iic : U ⊆ Set.Iic (a + b) := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    have := hA_le_a x hx
    simp only [Set.mem_Iic]
    linarith

  have hV_sub_Ici : V ⊆ Set.Ici (a + b) := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    have := hB_ge_b y hy
    simp only [Set.mem_Ici]
    linarith

  have h_inter_sub : U ∩ V ⊆ {a + b} := by
    rintro z ⟨hzU, hzV⟩
    have h1 := hU_sub_Iic hzU
    have h2 := hV_sub_Ici hzV
    simp only [Set.mem_Iic] at h1
    simp only [Set.mem_Ici] at h2
    simp only [Set.mem_singleton_iff]
    linarith

  have h_inter_zero : volume (U ∩ V) = 0 := by
    apply le_antisymm _ (by positivity)
    calc volume (U ∩ V)
        ≤ volume ({a + b} : Set ℝ) := MeasureTheory.measure_mono h_inter_sub
      _ = 0 := MeasureTheory.measure_singleton (a + b)

  have hV_meas : MeasurableSet V := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact (hB_compact.measurableSet).preimage (measurable_const_add (-a))
  have h_inc_excl : volume (U ∪ V) + volume (U ∩ V) = volume U + volume V :=
    MeasureTheory.measure_union_add_inter U hV_meas

  have h_union_sub : U ∪ V ⊆ K_A + K_B := Set.union_subset hU_sub_AB hV_sub_AB
  have h_union_le : volume (U ∪ V) ≤ volume (K_A + K_B) :=
    MeasureTheory.measure_mono h_union_sub

  calc volume K_A + volume K_B
      = volume U + volume V := by rw [hU_vol, hV_vol]
    _ = volume (U ∪ V) + volume (U ∩ V) := h_inc_excl.symm
    _ = volume (U ∪ V) + 0 := by rw [h_inter_zero]
    _ = volume (U ∪ V) := add_zero _
    _ ≤ volume (K_A + K_B) := h_union_le

private theorem oneDim_brunn_minkowski_le
    {A B C : Set ℝ}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (_hC_meas : MeasurableSet C)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty)
    (hAB_sub : A + B ⊆ C) :
    volume A + volume B ≤ volume C := by

  by_cases hA_zero : volume A = 0
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    rw [hA_zero, zero_add]
    calc volume B = volume (({a₀} : Set ℝ) + B) := h_aB_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_aB_sub_C

  by_cases hB_zero : volume B = 0
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    rw [hB_zero, add_zero]
    calc volume A = volume (A + ({b₀} : Set ℝ)) := h_Ab_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_Ab_sub_C

  by_cases hA_top : volume A = ⊤
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hA_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume A = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hA_meas
    calc (⊤ : ℝ≥0∞)
        = volume A := hA_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_A => iSup_le fun hK_A_sub => iSup_le fun _ => ?_
          have h_KA_b0_sub : K_A + ({b₀} : Set ℝ) ⊆ C :=
            fun z ⟨x, hx, _, rfl, hxz⟩ => hAB_sub ⟨x, hK_A_sub hx, b₀, hb₀, hxz⟩
          have h_KA_b0_eq : volume (K_A + ({b₀} : Set ℝ)) = volume K_A := by
            rw [Set.add_singleton, Set.image_add_right]
            exact MeasureTheory.measure_preimage_add_right volume (-b₀) K_A
          calc volume K_A
              = volume (K_A + ({b₀} : Set ℝ)) := h_KA_b0_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_KA_b0_sub

  by_cases hB_top : volume B = ⊤
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hB_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume B = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hB_meas
    calc (⊤ : ℝ≥0∞)
        = volume B := hB_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_B => iSup_le fun hK_B_sub => iSup_le fun _ => ?_
          have h_a0_KB_sub : ({a₀} : Set ℝ) + K_B ⊆ C :=
            fun z ⟨_, rfl, y, hy, hyz⟩ => hAB_sub ⟨a₀, ha₀, y, hK_B_sub hy, hyz⟩
          have h_a0_KB_eq : volume (({a₀} : Set ℝ) + K_B) = volume K_B := by
            rw [Set.singleton_add, Set.image_add_left]
            exact MeasureTheory.measure_preimage_add volume (-a₀) K_B
          calc volume K_B
              = volume (({a₀} : Set ℝ) + K_B) := h_a0_KB_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_a0_KB_sub

  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hC_top

  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hδ_def
  have hδ_pos : (0 : ℝ≥0∞) < δ := by
    rw [hδ_def]
    refine ENNReal.div_pos ?_ (by norm_num)
    exact_mod_cast hε.ne'
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hδ_le : δ ≤ ε := by
    rw [hδ_def]; exact ENNReal.half_le_self

  obtain ⟨K_A, hK_A_sub, hK_A_compact, hK_A_lt⟩ :=
    hA_meas.exists_isCompact_lt_add hA_top hδ_ne
  obtain ⟨K_B, hK_B_sub, hK_B_compact, hK_B_lt⟩ :=
    hB_meas.exists_isCompact_lt_add hB_top hδ_ne

  rcases K_A.eq_empty_or_nonempty with hKA_empty | hKA_ne
  ·
    rw [hKA_empty, MeasureTheory.measure_empty, zero_add] at hK_A_lt

    have hA_le_ε : volume A ≤ (ε : ℝ≥0∞) := le_trans hK_A_lt.le hδ_le

    obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    have hB_le_C : volume B ≤ volume C := by
      rw [← h_aB_eq]; exact MeasureTheory.measure_mono h_aB_sub_C
    calc volume A + volume B ≤ (ε : ℝ≥0∞) + volume C := add_le_add hA_le_ε hB_le_C
      _ = volume C + (ε : ℝ≥0∞) := add_comm _ _
  rcases K_B.eq_empty_or_nonempty with hKB_empty | hKB_ne
  ·
    rw [hKB_empty, MeasureTheory.measure_empty, zero_add] at hK_B_lt
    have hB_le_ε : volume B ≤ (ε : ℝ≥0∞) := le_trans hK_B_lt.le hδ_le
    obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    have hA_le_C : volume A ≤ volume C := by
      rw [← h_Ab_eq]; exact MeasureTheory.measure_mono h_Ab_sub_C
    exact add_le_add hA_le_C hB_le_ε
  ·
    have hKAB_sub : K_A + K_B ⊆ C :=
      fun z ⟨x, hx, y, hy, hxyz⟩ =>
        hAB_sub ⟨x, hK_A_sub hx, y, hK_B_sub hy, hxyz⟩
    have h_compact_bm := oneDim_brunn_minkowski_compact_le
      hK_A_compact hK_B_compact hKA_ne hKB_ne
    have h_KAKB_le_C : volume (K_A + K_B) ≤ volume C :=
      MeasureTheory.measure_mono hKAB_sub

    have h_2δ_le_ε : (2 : ℝ≥0∞) * δ ≤ (ε : ℝ≥0∞) := by
      rw [hδ_def]; exact ENNReal.mul_div_le
    calc volume A + volume B
        ≤ (volume K_A + δ) + (volume K_B + δ) := by gcongr
      _ = (volume K_A + volume K_B) + (δ + δ) := by ring
      _ = (volume K_A + volume K_B) + 2 * δ := by ring
      _ ≤ volume C + 2 * δ := by
          gcongr
          exact le_trans h_compact_bm h_KAKB_le_C
      _ ≤ volume C + (ε : ℝ≥0∞) := by gcongr

private theorem prekopaLeindler_1d_levelMeasureBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤)
    (hA_ne : ({x | α < f x} : Set ℝ).Nonempty)
    (hB_ne : ({y | α < g y} : Set ℝ).Nonempty) :
    ENNReal.ofReal t * volume {x | α < f x}
      + ENNReal.ofReal (1 - t) * volume {y | α < g y}
      ≤ volume {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set A : Set ℝ := {x | α < f x} with hA_def
  set B : Set ℝ := {y | α < g y} with hB_def
  set C : Set ℝ := {z | α < h z} with hC_def

  have hA_meas : MeasurableSet A := hf_meas measurableSet_Ioi
  have hB_meas : MeasurableSet B := hg_meas measurableSet_Ioi
  have hC_meas : MeasurableSet C := hh_meas measurableSet_Ioi

  have h_incl : t • A + (1 - t) • B ⊆ C :=
    prekopaLeindler_1d_levelInclusion ht_pos ht_lt h_le hα_pos hα_top

  have htA_meas : MeasurableSet (t • A) :=
    hA_meas.const_smul_of_ne_zero ht_pos.ne'
  have h1tB_meas : MeasurableSet ((1 - t) • B) :=
    hB_meas.const_smul_of_ne_zero h1t_pos.ne'

  have htA_ne : (t • A).Nonempty := Set.smul_set_nonempty.mpr hA_ne
  have h1tB_ne : ((1 - t) • B).Nonempty := Set.smul_set_nonempty.mpr hB_ne

  have h_bm : volume (t • A) + volume ((1 - t) • B) ≤ volume C :=
    oneDim_brunn_minkowski_le htA_meas h1tB_meas hC_meas htA_ne h1tB_ne h_incl

  have h_finrank : Module.finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ
  have h_smul_t : volume (t • A) = ENNReal.ofReal t * volume A := by
    rw [Measure.addHaar_smul_of_nonneg volume ht_pos.le A, h_finrank, pow_one]
  have h_smul_1t : volume ((1 - t) • B) = ENNReal.ofReal (1 - t) * volume B := by
    rw [Measure.addHaar_smul_of_nonneg volume h1t_pos.le B, h_finrank, pow_one]
  rw [← h_smul_t, ← h_smul_1t]
  exact h_bm

private theorem lintegral_eq_lintegral_meas_lt_ennreal
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x} := by

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  have hfN_meas : ∀ n, Measurable (fN n) :=
    fun n => hf.inf measurable_const
  have hfN_lt_top : ∀ n x, fN n x ≠ ⊤ :=
    fun n x => ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right
  have hfN_mono : Monotone fN := by
    intro m n hmn x
    exact inf_le_inf_left _ (by exact_mod_cast hmn)
  have hfN_iSup_eq : ∀ x, ⨆ n, fN n x = f x := fun x => by
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have hLHS : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fN n x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas hfN_mono]
    exact MeasureTheory.lintegral_congr fun x => (hfN_iSup_eq x).symm

  have h_per_n : ∀ n, ∫⁻ x, fN n x =
      ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    have h_eq : ∫⁻ x, fN n x = ∫⁻ x, ENNReal.ofReal ((fN n x).toReal) :=
      MeasureTheory.lintegral_congr fun x => (ENNReal.ofReal_toReal (hfN_lt_top n x)).symm
    rw [h_eq, MeasureTheory.lintegral_eq_lintegral_meas_lt volume
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        ((hfN_meas n).ennreal_toReal.aemeasurable)]

    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro α hα
    have hα_nn : (0 : ℝ) ≤ α := le_of_lt hα
    change volume {x | α < (fN n x).toReal}
        = volume {x | ENNReal.ofReal α < fN n x}
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mpr h
      rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)] at this
    · have h' : ENNReal.ofReal α < ENNReal.ofReal ((fN n x).toReal) := by
        rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mp h'

  have h_set_mono : ∀ α : ℝ,
      Monotone fun n : ℕ => {x | ENNReal.ofReal α < fN n x} := by
    intro α m n hmn x hx
    exact lt_of_lt_of_le hx (hfN_mono hmn x)
  have h_set_iUnion : ∀ α : ℝ,
      ⋃ n : ℕ, {x | ENNReal.ofReal α < fN n x}
        = {x | ENNReal.ofReal α < f x} := by
    intro α
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => lt_of_lt_of_le hn (le_trans inf_le_left le_rfl), ?_⟩
    intro hx
    rw [← hfN_iSup_eq x] at hx
    exact lt_iSup_iff.mp hx

  have h_meas_vol : ∀ n,
      Measurable fun α : ℝ => volume {x | ENNReal.ofReal α < fN n x} := by
    intro n

    have h_set_meas : MeasurableSet
        {p : ℝ × ℝ | ENNReal.ofReal p.1 < fN n p.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hfN_meas n).comp measurable_snd)

    exact measurable_measure_prodMk_left h_set_meas
  have hRHS : ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x}
        = ⨆ n, ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    rw [show (fun α => volume {x | ENNReal.ofReal α < f x})
          = fun α => ⨆ n, volume {x | ENNReal.ofReal α < fN n x} from
        funext fun α => by rw [← h_set_iUnion α,
          (h_set_mono α).measure_iUnion]]
    exact MeasureTheory.lintegral_iSup (fun n => h_meas_vol n)
      (fun m n hmn α => MeasureTheory.measure_mono (h_set_mono α hmn))
  rw [hLHS, hRHS]
  exact iSup_congr h_per_n

private theorem ennreal_geom_mean_le_arith_mean2_weighted
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (a b : ℝ≥0∞) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  by_cases ha : a = ⊤
  · subst ha
    have h_rhs : ENNReal.ofReal t * ⊤ + ENNReal.ofReal (1 - t) * b = ⊤ := by
      have : ENNReal.ofReal t ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  by_cases hb : b = ⊤
  · subst hb
    have h_rhs : ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * ⊤ = ⊤ := by
      have : ENNReal.ofReal (1 - t) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top

  set A : ℝ := a.toReal with hA_def
  set B : ℝ := b.toReal with hB_def
  have hA_nn : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB_nn : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hofa : ENNReal.ofReal A = a := ENNReal.ofReal_toReal ha
  have hofb : ENNReal.ofReal B = b := ENNReal.ofReal_toReal hb
  have h_real : A ^ t * B ^ (1 - t) ≤ t * A + (1 - t) * B :=
    Real.geom_mean_le_arith_mean2_weighted ht_pos.le h1t_pos.le hA_nn hB_nn
      (by linarith)
  have hAt_nn : (0 : ℝ) ≤ A ^ t := Real.rpow_nonneg hA_nn t
  have hBt_nn : (0 : ℝ) ≤ B ^ (1 - t) := Real.rpow_nonneg hB_nn (1 - t)
  calc a ^ t * b ^ (1 - t)
      = ENNReal.ofReal A ^ t * ENNReal.ofReal B ^ (1 - t) := by rw [hofa, hofb]
    _ = ENNReal.ofReal (A ^ t) * ENNReal.ofReal (B ^ (1 - t)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA_nn ht_pos.le,
            ENNReal.ofReal_rpow_of_nonneg hB_nn h1t_pos.le]
    _ = ENNReal.ofReal (A ^ t * B ^ (1 - t)) := by
        rw [← ENNReal.ofReal_mul hAt_nn]
    _ ≤ ENNReal.ofReal (t * A + (1 - t) * B) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (t * A) + ENNReal.ofReal ((1 - t) * B) :=
        ENNReal.ofReal_add (mul_nonneg ht_pos.le hA_nn)
          (mul_nonneg h1t_pos.le hB_nn)
    _ = ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
        rw [ENNReal.ofReal_mul ht_pos.le, ENNReal.ofReal_mul h1t_pos.le,
            hofa, hofb]

private theorem prekopaLeindler_1d_arithBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (h_ess_eq : essSup f volume = essSup g volume) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ y, g y)
      ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set M : ℝ≥0∞ := essSup f volume with hM_def

  have h_pos_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, β < M → 0 < volume {x | β < φ x} := by
    intro φ hφ_ess β hβ
    by_contra h_neg
    rw [not_lt, nonpos_iff_eq_zero] at h_neg
    have h_ae : φ ≤ᵐ[volume] fun _ => β := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simpa using h_neg
    have : essSup φ volume ≤ β := essSup_le_of_ae_le β h_ae
    rw [hφ_ess] at this
    exact absurd this (not_le.mpr hβ)

  have h_null_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, M ≤ β → volume {x | β < φ x} = 0 := by
    intro φ hφ_ess β hβ
    have h_essSup_le : essSup φ volume ≤ β := hφ_ess.trans_le hβ

    have h_sub : {x | β < φ x} ⊆ {x | essSup φ volume < φ x} :=
      fun x hx => lt_of_le_of_lt h_essSup_le hx
    refine le_antisymm ?_ (by positivity)
    calc volume {x | β < φ x}
        ≤ volume {x | essSup φ volume < φ x} := MeasureTheory.measure_mono h_sub
      _ = 0 := meas_essSup_lt

  let volF : ℝ → ℝ≥0∞ := fun α => volume {x | ENNReal.ofReal α < f x}
  let volG : ℝ → ℝ≥0∞ := fun α => volume {y | ENNReal.ofReal α < g y}
  let volH : ℝ → ℝ≥0∞ := fun α => volume {z | ENNReal.ofReal α < h z}
  have hvolF_meas : Measurable volF :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hf_meas.comp measurable_snd))
  have hvolG_meas : Measurable volG :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hg_meas.comp measurable_snd))

  have h_pointwise : ∀ α : ℝ, 0 < α →
      ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α := by
    intro α hα
    have hα_pos_e : (0 : ℝ≥0∞) < ENNReal.ofReal α :=
      ENNReal.ofReal_pos.mpr hα
    have hα_top : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
    by_cases hαM : ENNReal.ofReal α < M
    ·
      have hA_pos : 0 < volume {x | ENNReal.ofReal α < f x} :=
        h_pos_meas hM_def.symm hαM
      have hB_pos : 0 < volume {y | ENNReal.ofReal α < g y} :=
        h_pos_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      have hA_ne : ({x | ENNReal.ofReal α < f x} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hA_pos.ne'
      have hB_ne : ({y | ENNReal.ofReal α < g y} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hB_pos.ne'
      exact prekopaLeindler_1d_levelMeasureBound hf_meas hg_meas hh_meas
        ht_pos ht_lt h_le hα_pos_e hα_top hA_ne hB_ne
    ·
      rw [not_lt] at hαM
      have hf_null : volF α = 0 := h_null_meas hM_def.symm hαM
      have hg_null : volG α = 0 := h_null_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      change ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α
      rw [hf_null, hg_null, mul_zero, mul_zero, zero_add]
      positivity

  rw [lintegral_eq_lintegral_meas_lt_ennreal hf_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hg_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hh_meas]

  change ENNReal.ofReal t * (∫⁻ α in Ioi (0:ℝ), volF α)
       + ENNReal.ofReal (1 - t) * (∫⁻ α in Ioi (0:ℝ), volG α)
       ≤ ∫⁻ α in Ioi (0:ℝ), volH α

  rw [← MeasureTheory.lintegral_const_mul _ hvolF_meas,
      ← MeasureTheory.lintegral_const_mul _ hvolG_meas]

  rw [← MeasureTheory.lintegral_add_left (hvolF_meas.const_mul _)]

  exact MeasureTheory.setLIntegral_mono'
    measurableSet_Ioi (fun α hα => h_pointwise α hα)

private theorem prekopaLeindler_1d_essBdd
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (hMf_top : essSup f volume ≠ ⊤) (hMg_top : essSup g volume ≠ ⊤) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set Mf := essSup f volume with hMf_def
  set Mg := essSup g volume with hMg_def

  by_cases hMf_zero : Mf = 0
  · have hf_int_zero : ∫⁻ x, f x = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hf_meas]
      filter_upwards [ENNReal.ae_le_essSup f] with x hx
      rw [← hMf_def, hMf_zero] at hx
      exact le_antisymm hx (by positivity)
    rw [hf_int_zero, ENNReal.zero_rpow_of_pos ht_pos, zero_mul]
    positivity

  by_cases hMg_zero : Mg = 0
  · have hg_int_zero : ∫⁻ y, g y = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hg_meas]
      filter_upwards [ENNReal.ae_le_essSup g] with y hy
      rw [← hMg_def, hMg_zero] at hy
      exact le_antisymm hy (by positivity)
    rw [hg_int_zero, ENNReal.zero_rpow_of_pos h1t_pos, mul_zero]
    positivity

  set c : ℝ≥0∞ := Mg / Mf with hc_def
  have hc_pos : (0 : ℝ≥0∞) < c := ENNReal.div_pos hMg_zero hMf_top
  have hc_top : c ≠ ⊤ := by
    rw [hc_def]
    exact (ENNReal.div_lt_top hMg_top hMf_zero).ne
  have hcMf_eq_Mg : c * Mf = Mg := by
    rw [hc_def, ENNReal.div_mul_cancel hMf_zero hMf_top]

  set f' : ℝ → ℝ≥0∞ := fun x => c * f x with hf'_def
  set h' : ℝ → ℝ≥0∞ := fun z => c ^ t * h z with hh'_def
  have hf'_meas : Measurable f' := hf_meas.const_mul c
  have hh'_meas : Measurable h' := hh_meas.const_mul (c ^ t)

  have hf'_essSup : essSup f' volume = Mg := by
    change essSup (fun x => c * f x) volume = Mg
    rw [ENNReal.essSup_const_mul, hcMf_eq_Mg]

  have h_le' : ∀ x y : ℝ,
      f' x ^ t * g y ^ (1 - t) ≤ h' (t * x + (1 - t) * y) := by
    intro x y
    change (c * f x) ^ t * g y ^ (1 - t) ≤ c ^ t * h (t * x + (1 - t) * y)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc]
    gcongr
    exact h_le x y

  have h_amgm := ennreal_geom_mean_le_arith_mean2_weighted ht_pos ht_lt
    (∫⁻ x, f' x) (∫⁻ y, g y)
  have h_arith := prekopaLeindler_1d_arithBound hf'_meas hg_meas hh'_meas
    ht_pos ht_lt h_le' (hf'_essSup.trans hMg_def.symm)
  have h_pl_rescaled :
      (∫⁻ x, f' x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h' z :=
    le_trans h_amgm h_arith

  rw [show ∫⁻ x, f' x = c * ∫⁻ x, f x from
        MeasureTheory.lintegral_const_mul c hf_meas,
      show ∫⁻ z, h' z = c ^ t * ∫⁻ z, h z from
        MeasureTheory.lintegral_const_mul (c ^ t) hh_meas,
      ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc] at h_pl_rescaled

  have hct_ne_zero : c ^ t ≠ 0 := (ENNReal.rpow_pos hc_pos hc_top).ne'
  have hct_ne_top : c ^ t ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ht_pos.le hc_top).ne

  rw [mul_comm (c ^ t) _, mul_comm (c ^ t) _] at h_pl_rescaled
  exact (ENNReal.mul_le_mul_iff_left hct_ne_zero hct_ne_top).mp h_pl_rescaled

theorem prekopaLeindler_1d
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  set gN : ℕ → ℝ → ℝ≥0∞ := fun n y => g y ⊓ (n : ℝ≥0∞) with hgN_def
  have hfN_meas : ∀ n, Measurable (fN n) := fun n => hf_meas.inf measurable_const
  have hgN_meas : ∀ n, Measurable (gN n) := fun n => hg_meas.inf measurable_const
  have hfN_essSup_top : ∀ n, essSup (fN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (fN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  have hgN_essSup_top : ∀ n, essSup (gN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (gN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)

  have h_le_N : ∀ n m, ∀ x y : ℝ,
      fN n x ^ t * gN m y ^ (1 - t) ≤ h (t * x + (1 - t) * y) := by
    intro n m x y
    calc fN n x ^ t * gN m y ^ (1 - t)
        ≤ f x ^ t * g y ^ (1 - t) := by
          gcongr <;> exact inf_le_left
      _ ≤ h (t * x + (1 - t) * y) := h_le x y

  have h_per_nm : ∀ n m,
      (∫⁻ x, fN n x) ^ t * (∫⁻ y, gN m y) ^ (1 - t) ≤ ∫⁻ z, h z := fun n m =>
    prekopaLeindler_1d_essBdd (hfN_meas n) (hgN_meas m) hh_meas ht_pos ht_lt
      (h_le_N n m) (hfN_essSup_top n) (hgN_essSup_top m)

  have hfN_mono : Monotone fun n => ∫⁻ x, fN n x := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro x; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hgN_mono : Monotone fun m => ∫⁻ y, gN m y := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro y; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hfN_iSup : ⨆ n, ∫⁻ x, fN n x = ∫⁻ x, f x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas (fun n m hnm x =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro x
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hgN_iSup : ⨆ m, ∫⁻ y, gN m y = ∫⁻ y, g y := by
    rw [← MeasureTheory.lintegral_iSup hgN_meas (fun n m hnm y =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro y
    simp only [gN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have h_rpow_iSup : ∀ (a : ℕ → ℝ≥0∞) (p : ℝ), 0 ≤ p → Monotone a →
      (⨆ n, a n) ^ p = ⨆ n, a n ^ p := by
    intro a p hp ha_mono
    have h_tendsto : Filter.Tendsto a Filter.atTop (𝓝 (⨆ n, a n)) :=
      tendsto_atTop_iSup ha_mono
    have h_tendsto_pow : Filter.Tendsto (fun n => a n ^ p) Filter.atTop
        (𝓝 ((⨆ n, a n) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_tendsto
    have ha_pow_mono : Monotone (fun n => a n ^ p) := fun n m hnm =>
      ENNReal.rpow_le_rpow (ha_mono hnm) hp
    exact tendsto_nhds_unique h_tendsto_pow (tendsto_atTop_iSup ha_pow_mono)
  rw [← hfN_iSup, ← hgN_iSup]

  rw [h_rpow_iSup _ t ht_pos.le hfN_mono,
      h_rpow_iSup _ (1 - t) h1t_pos.le hgN_mono]

  rw [ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_

  exact h_per_nm n m

theorem prekopaLeindler.{u}
    {ι : Type u} [Fintype ι]
    {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ι → ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by

  suffices H : ∀ (κ : Type u) [Fintype κ] (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z by
    exact H ι f g h hf_meas hg_meas hh_meas ht_pos ht_lt h_le
  intro κ _Fκ
  refine Fintype.induction_empty_option
    (P := fun κ [Fintype κ] => ∀ (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z) ?_ ?_ ?_ κ
  ·

    intro α β _Fβ e IH f g h hf hg hh s hs hs1 hle
    let : Fintype α := Fintype.ofEquiv β e.symm
    set ψ : (β → ℝ) ≃ᵐ (α → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e.symm with hψ_def

    have hψ_smul : ∀ x y : α → ℝ,
        ψ.symm (s • x + (1 - s) • y) = s • ψ.symm x + (1 - s) • ψ.symm y := fun _ _ => rfl

    have h_vol_fwd : (volume : Measure (β → ℝ)).map ψ = (volume : Measure (α → ℝ)) := by
      conv_lhs => rw [MeasureTheory.volume_pi]
      conv_rhs => rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piCongrLeft e.symm (fun _ : α => volume)
    have h_vol : (volume : Measure (α → ℝ)).map ψ.symm = (volume : Measure (β → ℝ)) := by
      rw [← h_vol_fwd, MeasurableEquiv.map_symm_map]

    have hf' : Measurable (f ∘ ψ.symm) := hf.comp ψ.symm.measurable
    have hg' : Measurable (g ∘ ψ.symm) := hg.comp ψ.symm.measurable
    have hh' : Measurable (h ∘ ψ.symm) := hh.comp ψ.symm.measurable
    have hle' : ∀ x y : α → ℝ,
        (f ∘ ψ.symm) x ^ s * (g ∘ ψ.symm) y ^ (1 - s)
        ≤ (h ∘ ψ.symm) (s • x + (1 - s) • y) := by
      intro x y
      change f (ψ.symm x) ^ s * g (ψ.symm y) ^ (1 - s) ≤ h (ψ.symm (s • x + (1 - s) • y))
      rw [hψ_smul x y]
      exact hle (ψ.symm x) (ψ.symm y)

    have hf_int : ∫⁻ y, f y = ∫⁻ x, f (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hf ψ.symm.measurable
    have hg_int : ∫⁻ y, g y = ∫⁻ x, g (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hg ψ.symm.measurable
    have hh_int : ∫⁻ y, h y = ∫⁻ x, h (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hh ψ.symm.measurable
    rw [hf_int, hg_int, hh_int]
    exact IH (f ∘ ψ.symm) (g ∘ ψ.symm) (h ∘ ψ.symm) hf' hg' hh' hs hs1 hle'
  ·

    intro f g h hf_meas hg_meas hh_meas s hs_pos hs_lt h_le
    have h_volume : (volume : Measure (PEmpty → ℝ))
        = Measure.dirac (fun a : PEmpty => isEmptyElim a) :=
      Measure.volume_pi_eq_dirac _
    rw [h_volume, lintegral_dirac' _ hf_meas, lintegral_dirac' _ hg_meas,
        lintegral_dirac' _ hh_meas]
    have h_pl := h_le (fun a => isEmptyElim a) (fun a => isEmptyElim a)
    have h_smul : s • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                  + (1 - s) • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                = (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ) := by
      funext a; exact isEmptyElim a
    rwa [h_smul] at h_pl
  ·

    intro α _Fα IH f g h hf hg hh s hs hs1 hle
    let E : ((i : Option α) → ℝ) ≃ᵐ ((i : α) → ℝ) × ℝ :=
      MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)

    have hE_none : ∀ (x' : α → ℝ) (u : ℝ),
        E.symm (x', u) none = u := fun _ _ => rfl
    have hE_some : ∀ (x' : α → ℝ) (u : ℝ) (a : α),
        E.symm (x', u) (some a) = x' a := fun _ _ _ => rfl

    have hE_smul : ∀ (x' y' : α → ℝ) (u v : ℝ),
        s • E.symm (x', u) + (1 - s) • E.symm (y', v)
        = E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v) := by
      intro x' y' u v
      funext i
      cases i with
      | none =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * u + (1 - s) * v = s * u + (1 - s) * v
        rfl
      | some a =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * x' a + (1 - s) * y' a = s * x' a + (1 - s) * y' a
        rfl

    have h_vol : ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        = (volume : Measure (Option α → ℝ)) := by
      conv_rhs => rw [MeasureTheory.volume_pi]
      conv_lhs => rw [show (volume : Measure (α → ℝ))
          = MeasureTheory.Measure.pi (fun _ : α => volume) from MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piOptionEquivProd
        (fun _ : Option α => volume)

    set F : ℝ → ℝ≥0∞ := fun u => ∫⁻ x' : α → ℝ, f (E.symm (x', u)) with hF_def
    set G : ℝ → ℝ≥0∞ := fun v => ∫⁻ y' : α → ℝ, g (E.symm (y', v)) with hG_def
    set H_marg : ℝ → ℝ≥0∞ := fun w => ∫⁻ z' : α → ℝ, h (E.symm (z', w)) with hH_def

    have hf_comp : Measurable (fun p : (α → ℝ) × ℝ => f (E.symm p)) :=
      hf.comp E.symm.measurable
    have hg_comp : Measurable (fun p : (α → ℝ) × ℝ => g (E.symm p)) :=
      hg.comp E.symm.measurable
    have hh_comp : Measurable (fun p : (α → ℝ) × ℝ => h (E.symm p)) :=
      hh.comp E.symm.measurable
    have hF_meas : Measurable F := Measurable.lintegral_prod_left' hf_comp
    have hG_meas : Measurable G := Measurable.lintegral_prod_left' hg_comp
    have hH_marg_meas : Measurable H_marg := Measurable.lintegral_prod_left' hh_comp

    have h_FGH_le : ∀ u v : ℝ,
        F u ^ s * G v ^ (1 - s) ≤ H_marg (s * u + (1 - s) * v) := by
      intro u v
      have hf_slice : Measurable (fun x' : α → ℝ => f (E.symm (x', u))) :=
        hf.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hg_slice : Measurable (fun y' : α → ℝ => g (E.symm (y', v))) :=
        hg.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hh_slice : Measurable (fun z' : α → ℝ =>
          h (E.symm (z', s * u + (1 - s) * v))) :=
        hh.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have h_slice_le : ∀ x' y' : α → ℝ,
          f (E.symm (x', u)) ^ s * g (E.symm (y', v)) ^ (1 - s)
          ≤ h (E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v)) := by
        intro x' y'
        have h_pl := hle (E.symm (x', u)) (E.symm (y', v))
        rw [hE_smul] at h_pl
        exact h_pl
      exact IH _ _ _ hf_slice hg_slice hh_slice hs hs1 h_slice_le

    have h_1d := prekopaLeindler_1d hF_meas hG_meas hH_marg_meas hs hs1 h_FGH_le

    have h_int_split : ∀ (k : (Option α → ℝ) → ℝ≥0∞), Measurable k →
        ∫⁻ z, k z = ∫⁻ u : ℝ, ∫⁻ x' : α → ℝ, k (E.symm (x', u)) := by
      intro k hk
      conv_lhs => rw [show (volume : Measure (Option α → ℝ))
          = ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        from h_vol.symm]
      rw [MeasureTheory.lintegral_map hk E.symm.measurable]
      exact MeasureTheory.lintegral_prod_symm' _ (hk.comp E.symm.measurable)
    rw [h_int_split f hf, h_int_split g hg, h_int_split h hh]
    exact h_1d

end AsymptoticStatistics

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_FiniteBoxPrekopa
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the finite-box Prékopa–Leindler input

The finite-function-space Prékopa–Leindler inequality applies to the nonnegative
indicators of the three box unions. Compact-box continuity supplies all
measurability and integrability obligations without assumptions outside
the common box.
-/
namespace ContingencyTables.PublishedInputs
open MeasureTheory Set
open scoped ENNReal
noncomputable section

private theorem integral_interpolation {q : ℕ} {f g h : Point q → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y, f x ^ t * g y ^ (1-t) ≤ h (t • x+(1-t) • y)) :
    (∫ x, f x)^t * (∫ y, g y)^(1-t) ≤ ∫ z, h z := by
  have hp := AsymptoticStatistics.prekopaLeindler hf.ennreal_ofReal hg.ennreal_ofReal
    hh.ennreal_ofReal ht ht1 (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht.le,
        ENNReal.ofReal_rpow_of_nonneg (hg0 y) (sub_pos.mpr ht1).le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
      exact ENNReal.ofReal_le_ofReal (hfg x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0)] at hp
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ht.le,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) t)] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)).mp hp

private theorem box_indicator {q : ℕ} {lower upper : Point q} {S : Set (Point q)}
    {f : Point q → ℝ} (hS : IsFiniteBoxUnion S)
    (hbox : closure S ⊆ Icc lower upper) (hf : ContinuousOn f (Icc lower upper))
    (hp : ∀ x ∈ Icc lower upper, 0 < f x) :
    (∀ x, 0 ≤ S.indicator f x) ∧ Measurable (S.indicator f) ∧
      Integrable (S.indicator f) := by
  classical
  have hs := hS.isOpen.measurableSet
  have hsub : S ⊆ Icc lower upper := subset_closure.trans hbox
  refine ⟨?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ S
    · simpa only [indicator_of_mem hx] using (hp x (hsub hx)).le
    · simp only [indicator_of_notMem hx, le_refl]
  · change Measurable (S.piecewise f (fun _ => 0))
    exact (hf.mono hsub).measurable_piecewise continuousOn_const hs
  · exact (hf.integrableOn_Icc.mono_set hsub).integrable_indicator hs

/-- The exact published analytic hypothesis required by both manuscripts. -/
theorem finiteBoxPrekopaLeindler (q : ℕ) : FiniteBoxPrekopaLeindler q := by
  intro t ht ht1 lower upper S₀ S₁ S₂ f₀ f₁ f₂ hS₀ hS₁ hS₂
    hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hp₀ hp₁ hp₂ hcover hle
  obtain ⟨h₀,hm₀,hi₀⟩ := box_indicator hS₀ hb₀ hc₀ hp₀
  obtain ⟨h₁,hm₁,hi₁⟩ := box_indicator hS₁ hb₁ hc₁ hp₁
  obtain ⟨h₂,hm₂,hi₂⟩ := box_indicator hS₂ hb₂ hc₂ hp₂
  have ht' : 0 < 1-t := sub_pos.mpr ht1
  have ht1' : 1-t < 1 := by linarith
  have H := integral_interpolation h₁ h₂ h₀ hm₁ hm₂ hm₀ hi₁ hi₂ hi₀ ht' ht1'
    (fun x y => by
      rw [show 1-(1-t)=t by ring]
      by_cases hx : x ∈ S₁
      · by_cases hy : y ∈ S₂
        · have hz : (1-t) • x+t • y ∈ S₀ := hcover ⟨x,hx,y,hy,rfl⟩
          simpa only [indicator_of_mem hx,indicator_of_mem hy,indicator_of_mem hz]
            using hle x hx y hy
        · rw [indicator_of_notMem hy,Real.zero_rpow (ne_of_gt ht),mul_zero]
          exact h₀ _
      · rw [indicator_of_notMem hx,Real.zero_rpow (ne_of_gt ht'),zero_mul]
        exact h₀ _)
  simpa only [integral_indicator hS₀.isOpen.measurableSet,
    integral_indicator hS₁.isOpen.measurableSet,integral_indicator hS₂.isOpen.measurableSet,
    sub_sub_cancel] using H

end
end ContingencyTables.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_FiniteCheegerProof
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the finite-chain Cheeger input by coarea and a weighted median -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

private lemma split_square (u : ℝ) : (max u 0)^2+(max (-u) 0)^2 = u^2 := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_left hu,max_eq_right (neg_nonpos.mpr hu)]
    ring
  · rw [max_eq_right (le_of_not_ge hu),max_eq_left (by linarith)]
    ring

private lemma split_difference (u v : ℝ) :
    (max u 0-max v 0)^2+(max (-u) 0-max (-v) 0)^2 ≤ (u-v)^2 := by
  by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
  · rw [max_eq_left hu,max_eq_left hv,max_eq_right (neg_nonpos.mpr hu),
      max_eq_right (neg_nonpos.mpr hv)]
    simp
  · have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_left hu,max_eq_right hv',max_eq_right (neg_nonpos.mpr hu),
      max_eq_left (neg_nonneg.mpr hv')]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hu hv']
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [max_eq_right hu',max_eq_left hv,max_eq_left (neg_nonneg.mpr hu'),
      max_eq_right (neg_nonpos.mpr hv)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hu' hv]
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hu',max_eq_right hv',max_eq_left (neg_nonneg.mpr hu'),
      max_eq_left (neg_nonneg.mpr hv')]
    nlinarith

variable {X : Type*} [Fintype X]

/-- Levin–Peres Theorem 13.10 lower bound, in the exact finite Poincaré form used here. -/
theorem finiteCheeger : PublishedInputs.FiniteCheeger X := by
  intro C κ hk hcut f
  obtain ⟨a,hbelow,habove⟩ := exists_median C f
  let p : X → ℝ := fun x => max (f x-a) 0
  let n : X → ℝ := fun x => max (a-f x) 0
  have hp : mass C (Finset.univ.filter fun x => 0 < p x) ≤ 1/2 := by
    simpa only [p,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using habove
  have hn : mass C (Finset.univ.filter fun x => 0 < n x) ≤ 1/2 := by
    simpa only [n,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using hbelow
  have hcut' : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S := hcut
  have hpe := positive_energy C κ hk hcut' p (fun _ => le_max_right _ _) hp
  have hne := positive_energy C κ hk hcut' n (fun _ => le_max_right _ _) hn
  have hnorm : (∑ x, C.π x*(p x)^2)+(∑ x, C.π x*(n x)^2) =
      ∑ x, C.π x*(f x-a)^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [p,n]
    rw [← mul_add,show a-f x = -(f x-a) by ring,split_square]
  have he : C.energy p+C.energy n ≤ C.energy f := by
    rw [C.energy_eq,C.energy_eq,C.energy_eq,← add_div,
      ← Finset.sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (C.positive x).le (C.nonnegative x y))
    dsimp [p,n]
    convert split_difference (f x-a) (f y-a) using 1
    all_goals first | rfl | ring | (congr 2; ring_nf) | (simp only [neg_sub])
  have hv := mul_le_mul_of_nonneg_left (variance_le_centered C f a) (sq_nonneg κ)
  have hb : κ^2*C.variance f ≤ 2*C.energy f := by
    rw [← hnorm] at hv
    nlinarith [hpe,hne,he]
  have hk2 : 0 < κ^2 := sq_pos_of_pos hk
  calc
    C.variance f ≤ (2*C.energy f)/κ^2 := (le_div_iff₀ hk2).mpr (by nlinarith [hb])
    _ = (2/κ^2)*C.energy f := by ring

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_AdaptiveStream
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

lemma average_const (n : ℕ) (a : ℚ) : average (fun _ : Bits n=>a)=a := by
  simp [average]

lemma average_split {n m : ℕ} (f : Bits (n+m) → ℚ) :
    average f=average (fun a : Bits n=>average (fun b : Bits m=>f (concat a b))) := by
  unfold average
  have h : (∑ b : Bits (n+m),f b)=∑ a : Bits n,∑ b : Bits m,f (concat a b) := by
    calc
      _ = ∑ ab : Bits n × Bits m,f (concat ab.1 ab.2) :=
        Fintype.sum_equiv (split n m) f (fun ab=>f (concat ab.1 ab.2)) (fun b=>by
          change f b=f ((split n m).symm ((split n m) b))
          rw [Equiv.symm_apply_apply])
      _ = _ := Fintype.sum_prod_type _
  rw [h,←sum_div,pow_add,div_div]
  congr 1
  ring

lemma average_one (f : Bits 1 → ℚ) :
    average f=(f (fun _=>false)+f (fun _=>true))/2 := by
  have h : (∑ b : Bits 1,f b)=f (fun _=>false)+f (fun _=>true) := by
    let e : Bits 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
    have hh:=Fintype.sum_equiv e f (fun b=>f (fun _=>b)) (fun b=>by
      congr 1; funext i; exact congrArg b (Subsingleton.elim i default))
    simpa only [Fintype.sum_bool,add_comm] using hh
  simp only [average,h,pow_one]

lemma shift_extend_concat {n m : ℕ} (a : Bits n) (b : Bits m) (i : ℕ) (hi : i < m) :
    shift n (extend (concat a b)) i=extend b i := by
  have hni : n+i<n+m := Nat.add_lt_add_left hi n
  simp only [shift,extend,dite_eq_left hi,dite_eq_left hni]
  exact concat_right a b ⟨i,hi⟩

lemma extend_concat_zero {m : ℕ} (a : Bits 1) (b : Bits m) :
    extend (concat a b) 0=a 0 := by
  simp only [extend,dite_eq_left (by omega : 0<1+m)]
  exact concat_left a b 0

namespace Experiment
variable {α β : Type}

lemma run_cost (p : Experiment α) (b : Stream) : (p.run b).2≤p.cost := by
  induction p generalizing b with
  | done a => rfl
  | read p ih =>
    simp only [run,cost]
    have h:=ih (b 0) (shift 1 b)
    cases hb : b 0 <;> simp only [hb] at h <;> omega
  | delay n p ih => exact Nat.add_le_add_left (ih (shift n b)) n

lemma run_congr (p : Experiment α) (a b : Stream)
    (h : ∀ i,i<p.cost → a i=b i) : p.run a=p.run b := by
  induction p generalizing a b with
  | done x => rfl
  | read p ih =>
    have h0 : a 0=b 0 := h 0 (by simp [cost])
    simp only [run,h0]
    have hh : run (p (b 0)) (shift 1 a)=run (p (b 0)) (shift 1 b) := by
      apply ih
      intro i hi
      apply h
      cases he : b 0 <;> simp only [he] at hi <;> simp only [cost] <;> omega
    rw [hh]
  | delay n p ih =>
    simp only [run]
    have hh : run p (shift n a)=run p (shift n b) := by
      apply ih
      intro i hi
      exact h (n+i) (by simp only [cost]; omega)
    rw [hh]

lemma run_suffix {n m : ℕ} (p : Experiment α) (h : p.cost ≤ m)
    (a : Bits n) (b : Bits m) :
    p.run (shift n (extend (concat a b)))=p.run (extend b) := by
  apply run_congr
  intro i hi
  exact shift_extend_concat a b i (lt_of_lt_of_le hi h)

theorem average_run (p : Experiment α) (f : α → ℚ) (n : ℕ) (hn : p.cost≤n) :
    average (fun b : Bits n=>f (p.run (extend b)).1)=p.mean f := by
  induction p generalizing n with
  | done a => exact average_const n (f a)
  | delay k p ih =>
    have hk : k≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm : p.cost ≤ m := by simpa only [cost,Nat.add_le_add_iff_left] using hn
    rw [average_split]
    have hrun (a : Bits k) (b : Bits m) :
        f ((delay k p).run (extend (concat a b))).1=f (p.run (extend b)).1 := by
      simp only [run,run_suffix p hm a b]
    simp_rw [hrun,ih m hm]
    exact average_const k (p.mean f)
  | read p ih =>
    have hk : 1≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm (b : Bool) : (p b).cost ≤ m := by
      simp only [cost,Nat.add_le_add_iff_left] at hn
      cases b <;> omega
    rw [average_split]
    have hrun (a : Bits 1) (b : Bits m) :
        f ((read p).run (extend (concat a b))).1=f ((p (a 0)).run (extend b)).1 := by
      simp only [run,extend_concat_zero,run_suffix _ (hm (a 0)) a b]
    simp_rw [hrun,ih _ m (hm _)]
    rw [average_one]
    rfl

end Experiment
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_ExperimentSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
lemma all_run (p : Experiment α) (P : α → Prop) (h : All p P) (b : Stream) : P (p.run b).1 := by
  induction p generalizing b with
  | done a => exact h
  | read p ih =>
    cases hb : b 0 <;> simp only [run,hb] <;> apply ih <;> first | exact h.1 | exact h.2
  | delay n p ih => exact ih h (shift n b)
lemma all_bind (p : Experiment α) (q : α → Experiment β) (P : β → Prop) :
    All (p.bind q) P ↔ All p (fun a=>All (q a) P) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,All,ih]
  | delay n p ih => exact ih
lemma all_map (p : Experiment α) (f : α → β) (P : β → Prop) :
    All (p.map f) P ↔ All p (fun a=>P (f a)) := by
  rw [map,all_bind]; rfl

end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_GuardMachineBase
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma statementCost_le_programCost [Fintype Λ] (l : Λ) :
    statementCost (M l)≤programCost M := Finset.le_sup (f:=fun l=>statementCost (M l)) (Finset.mem_univ l)
end MatchingFPRAS.MachineCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_BoolPostCompiler
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BoolPostCompiler
open Turing MachineCost
open scoped Classical

lemma down_up (b : Bool) : down (up b)=b := by cases b <;> decide
end MatchingFPRAS.BoolPostCompiler

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_FixedEncoding
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FixedEncoding
variable (Γ : Type*) [Fintype Γ] [Inhabited Γ]
lemma injective : Function.Injective (enc Γ) := by
  classical
  intro a b hab
  by_cases ha : a=default
  · by_cases hb : b=default
    · exact ha.trans hb.symm
    · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ b)) hab
      simp [enc,ha,hb] at hh
  · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ a)) hab
    simp only [enc,List.Vector.get_ofFn] at hh
    have ht : decide (b≠default ∧ Fintype.equivFin Γ b=Fintype.equivFin Γ a)=true := by
      simpa [ha] using hh.symm
    exact ((Fintype.equivFin Γ).injective (of_decide_eq_true ht).2).symm
end MatchingFPRAS.FixedEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TreeBits
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData

lemma bits_length (A : List Bool) : (encode (bits A)).length≤4*A.length+1 := by
  induction A with
  | nil => simp [encode]
  | cons b A ih => cases b <;> simp only [bits_cons,encode,bit,Bool.false_eq_true,↓reduceIte,
      List.length_cons,List.length_append,List.length_nil] <;> omega
end MatchingFPRAS.TreeData

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeList
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma size_encode_list (as : List A) :
    TreeFunction.size (encode as) = 1+as.length+(as.map (fun a=>TreeFunction.size (encode a))).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [encode_list_cons,size_cons,ih,List.length_cons,List.map_cons,List.sum_cons]; omega

lemma size_encode_mem {as : List A} {a : A} (ha : a ∈ as) :
    TreeFunction.size (encode a) ≤ TreeFunction.size (encode as) := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    simp only [encode_list_cons,size_cons]
    rcases ha with rfl|ha
    · omega
    · have := ih ha; omega

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma weight_pos (a : A) : 0<weight a := by
  change 0<TreeFunction.size (encode a)
  cases encode a <;> simp only [size_nil,size_cons] <;> omega
lemma list_length_le_weight (as : List A) : as.length≤weight as := by
  rw [weight,size_encode_list]; omega
lemma weight_mem {as : List A} {a : A} (ha : a∈as) : weight a≤weight as := size_encode_mem ha

lemma polynomial_eval_monotone (p : Polynomial ℕ) : Monotone (fun n=>p.eval n) := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum,Polynomial.sum_def]
  exact Finset.sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

lemma polynomial_identity : PolynomialTime (identity (A:=A)) := by
  refine ⟨X+1,?_⟩
  intro a
  simp [identity,weight,Polynomial.eval_add,Polynomial.eval_X, Nat.add_comm]
lemma polynomial_first : PolynomialTime (first (A:=A) (B:=B)) := by
  refine ⟨7*X+11,?_⟩
  intro ⟨a,b⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change 6*weight a+weight b+11+weight a≤7*(1+weight a+weight b)+11
  omega
lemma polynomial_second : PolynomialTime (second (A:=A) (B:=B)) := by
  refine ⟨4*X+7,?_⟩
  intro ⟨a,b⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change 3*weight a+7+weight b≤4*(1+weight a+weight b)+7
  omega

lemma polynomial_composition {f : A → B} {g : B → C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (composition F G) := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := hG
  refine ⟨p+q.comp p,fun a=>?_⟩
  have h1 := hp a
  have h2 := hq (f a)
  have h3 := polynomial_eval_monotone q (show weight (f a)≤p.eval (weight a) by omega)
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  change F.cost a+G.cost (f a)+weight (g (f a))≤_
  dsimp only at h3
  omega
lemma polynomial_pair {f : A → B} {g : A → C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (pair F G) := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := hG
  refine ⟨7*p+q+11*X+32,fun a=>?_⟩
  have h1 := hp a
  have h2 := hq a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  rw [weight_prod]
  change F.cost a+G.cost a+11*weight a+6*weight (f a)+31+(1+weight (f a)+weight (g a))≤_
  omega
lemma polynomial_congr {f g : A → B} {F : Realizer f} (h : ∀ a,f a=g a)
    (hF : PolynomialTime F) : PolynomialTime (F.congr h) := by
  obtain ⟨p,hp⟩ := hF
  exact ⟨p,fun a=>by simpa only [Realizer.congr,←h a] using hp a⟩
lemma polynomial_choose {f : A → Bool} {g h : A → B} {F : Realizer f} {G : Realizer g} {H : Realizer h}
    (hF : PolynomialTime F) (hG : PolynomialTime G) (hH : PolynomialTime H) :
    PolynomialTime (choose F G H) := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := hG
  obtain ⟨r,hr⟩ := hH
  refine ⟨p+q+r+7*X+18,fun a=>?_⟩
  have h1 := hp a
  have h2 := hq a
  have h3 := hr a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change F.cost a+(if f a then G.cost a else H.cost a)+7*weight a+18+
    weight (if f a then g a else h a)≤_
  cases f a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
lemma polynomial_constantData (b : Data) : PolynomialTime (constantData (A:=A) b) := by
  induction b with
  | nil => refine ⟨X+3,fun a=>?_⟩; simp [constantData,weight,Codec.encode,size_nil]
  | cons b c hb hc =>
    obtain ⟨p,hp⟩ := polynomial_pair hb hc
    exact ⟨p,hp⟩
lemma polynomial_constant (b : B) : PolynomialTime (constant (A:=A) b) :=
  polynomial_constantData (encode b)

omit [Codec B] in
lemma Fold.cost_prefix_bound {f : A×B → B} (t : A×B → ℕ) (as : List A) (b : B) (T S : ℕ)
    (hs : weight as≤S)
    (hstep : ∀ pre a post,as=pre++a::post → t (a,pre.foldl (fun z c=>f (c,z)) b)≤T) :
    Fold.cost f t as b≤as.length*(T+14*S+34)+10 := by
  induction as generalizing b with
  | nil => simp [Fold.cost]
  | cons a as ih =>
    have ht := hstep [] a as rfl
    simp only [List.foldl_nil] at ht
    have hs' : weight as≤S := by rw [weight_cons] at hs; omega
    have hi := ih (f (a,b)) hs' (by
      intro pre c post he
      have hh := hstep (a::pre) c post (by simp only [List.cons_append,he])
      exact hh)
    simp only [Fold.cost,List.length_cons]
    change t (a,b)+6*weight a+8*weight as+34+Fold.cost f t as (f (a,b))≤_
    have ha : weight a≤S := by rw [weight_cons] at hs; omega
    nlinarith

lemma polynomial_fold {f : A×B → B} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ)
    (hsize : ∀ (as : List A) (b : B) pre post,as=pre++post →
      weight (pre.foldl (fun z a=>f (a,z)) b)≤p.eval (weight (as,b))) :
    PolynomialTime (fold F) := by
  obtain ⟨q,hq⟩ := hF
  refine ⟨X*(q.comp (1+X+p)+14*X+34)+10+p,fun ⟨as,b⟩=>?_⟩
  let S:=weight (as,b)
  let T:=q.eval (1+S+p.eval S)
  have hs : weight as≤S := by dsimp [S]; rw [weight_prod]; omega
  have hc := Fold.cost_prefix_bound (f:=f) F.cost as b T S hs (by
    intro pre a post he
    have hz := hsize as b pre (a::post) he
    change _≤p.eval S at hz
    have ha : weight a≤S := (weight_mem (by simp [he])).trans hs
    have hq' := hq (a,pre.foldl (fun z c=>f (c,z)) b)
    have hm := polynomial_eval_monotone q (show weight (a,pre.foldl (fun z c=>f (c,z)) b)≤1+S+p.eval S by rw [weight_prod]; omega)
    dsimp only at hm
    dsimp only [T]
    omega)
  have hout := hsize as b as [] (by simp)
  change _≤p.eval S at hout
  have hlen : as.length≤S := (list_length_le_weight as).trans hs
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
  change Fold.cost f F.cost as b+weight (as.foldl (fun z a=>f (a,z)) b)≤_
  change _≤S*(T+14*S+34)+10+p.eval S
  nlinarith
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

lemma weight_bool (b : Bool) : weight b≤3 := by cases b <;> decide
lemma weight_bits (bs : List Bool) : weight bs≤4*bs.length+1 := TreeData.bits_length bs
lemma weight_nat (n : ℕ) : weight n=weight n.bits := rfl
lemma weight_nat_le (n : ℕ) : weight n≤4*n.size+1 := by
  rw [weight_nat,←Nat.size_eq_bits_len]; exact weight_bits _
lemma size_le_weight (n : ℕ) : n.size≤weight n := by
  rw [weight_nat,←Nat.size_eq_bits_len]; exact list_length_le_weight _
lemma weight_nat_small {a b : ℕ} (h : a≤b) : weight a≤4*weight b+1 := by
  have h1:=Nat.size_le_size h
  have h2:=weight_nat_le a
  have h3:=size_le_weight b
  omega
lemma nat_size_add (a b : ℕ) : (a+b).size≤ max a.size b.size+1 := by
  apply Nat.size_le.mpr
  have ha : a<2^(max a.size b.size) := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hb : b<2^(max a.size b.size) := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [pow_succ]; omega
lemma nat_size_mul (a b : ℕ) : (a*b).size≤a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.le_of_lt (Nat.lt_size_self b))).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))
lemma weight_add (a b : ℕ) : weight (a+b)≤4*(weight a+weight b+1)+1 := by
  have h:=weight_nat_le (a+b)
  have h1:=nat_size_add a b
  have h2:=size_le_weight a
  have h3:=size_le_weight b
  have hm : max a.size b.size≤weight a+weight b := max_le (by omega) (by omega)
  omega
lemma polynomial_add : PolynomialTime add := by
  refine ⟨20*X+30,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have ho:=weight_add a b
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change (2*weight a+5+9*(a.bits.length+b.bits.length)+20)+weight (a+b)≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  omega
lemma polynomial_less : PolynomialTime less := by
  refine ⟨8*X+40,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have ho:=weight_bool (decide (a<b))
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change (2*weight a+3*(a.bits.length+b.bits.length)+31)+weight (decide (a<b))≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  omega
lemma polynomial_subtract : PolynomialTime subtract := by
  refine ⟨50*X+100,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have hc:=weight_nat_small (Nat.sub_le a b)
  have ho:=weight_bool (decide (a<b))
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change (2*weight a+3*(a.bits.length+b.bits.length)+31)+
    (if decide (a<b) then weight (a,b)+2 else
      2*weight a+9*(a.bits.length+b.bits.length)+4*weight (a-b)+32)+
      7*weight (a,b)+18+weight (a-b)≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len,weight_prod]
  split <;> omega
lemma polynomial_toBits : PolynomialTime toBits := by
  refine ⟨X+1,fun _=>?_⟩
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change 1+weight _ ≤ weight _+1
  rw [weight_nat]; omega
lemma polynomial_listCons {A : Type} [Codec A] : PolynomialTime (listCons (A:=A)) := by
  refine ⟨X+1,fun ⟨a,as⟩=>?_⟩
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,weight_prod,weight_cons]
  change 1+(1+weight a+weight as)≤(1+weight a+weight as)+1
  omega
lemma polynomial_double : PolynomialTime double :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity) polynomial_add)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialLists
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma polynomial_fst {f : A → B×C} {F : Realizer f} (h : PolynomialTime F) :
    PolynomialTime (composition F first) := polynomial_composition h polynomial_first
lemma polynomial_snd {f : A → B×C} {F : Realizer f} (h : PolynomialTime F) :
    PolynomialTime (composition F second) := polynomial_composition h polynomial_second
lemma weight_append (as bs : List A) : weight (as++bs)+1=weight as+weight bs := by
  induction as with
  | nil => simp only [List.nil_append,weight_nil]; omega
  | cons a as ih => simp only [List.cons_append,weight_cons]; omega
lemma weight_reverse (as : List A) : weight as.reverse=weight as := by
  simp only [weight,size_encode_list,List.length_reverse,List.map_reverse,List.sum_reverse]
lemma weight_prefix {as pre post : List A} (h : as=pre++post) : weight pre≤weight as := by
  have := weight_append pre post
  have := weight_pos post
  rw [h]; omega
omit [Codec A] in
lemma weight_map_bound {f : A → B} {as : List A} {N : ℕ}
    (h : ∀ a∈as,weight (f a)≤N) : weight (as.map f)≤as.length*(N+1)+1 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ht:=ih (fun b hb=>h b (by simp [hb]))
    have ha:=h a (by simp)
    simp only [List.map_cons,weight_cons,List.length_cons]
    nlinarith
lemma polynomial_reverse : PolynomialTime (reverse (A:=A)) := by
  unfold reverse
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
  apply polynomial_fold polynomial_listCons (2*X+1)
  intro as bs pre post he
  have hp := weight_prefix he
  have h:=weight_append pre.reverse bs
  rw [weight_reverse] at h
  simp only [List.foldl_flip_cons_eq_append']
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
lemma polynomial_mulStep : PolynomialTime mulStepRealizer := by
  unfold mulStepRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_composition polynomial_second polynomial_first)
  apply polynomial_composition _ polynomial_add
  apply polynomial_pair
  · exact polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_double
  · exact polynomial_choose polynomial_first
      (polynomial_composition polynomial_second polynomial_first) (polynomial_constant 0)
lemma mulStep_size (b : Bool) (n c : ℕ) : (mulStep (b,(n,c))).2.size ≤ c.size+n.size+3 := by
  have hh:=nat_size_mul 2 c
  have ha:=nat_size_add (2*c) (if b then n else 0)
  have hb : (if b then n else 0).size≤n.size := by cases b <;> simp
  have h2 : Nat.size 2=2 := by decide
  have hm : max (2*c).size (if b then n else 0).size ≤ c.size+n.size+2 := max_le (by omega) (by omega)
  change (2*c+(if b then n else 0)).size≤_
  omega
lemma mulStep_fold_first (bs : List Bool) (n c : ℕ) :
    (bs.foldl (fun z b=>mulStep (b,z)) (n,c)).1=n := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => exact ih _
lemma mulStep_fold_size (bs : List Bool) (n c : ℕ) :
    (bs.foldl (fun z b=>mulStep (b,z)) (n,c)).2.size ≤ c.size+bs.length*(n.size+3) := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih =>
    have hs:=mulStep_size b n c
    have ht:=ih (2*c+(if b then n else 0))
    change (bs.foldl _ (mulStep (b,(n,c)))).2.size≤_
    simp only [mulStep] at hs
    simp only [List.length_cons]
    change (bs.foldl _ (n,2*c+(if b then n else 0))).2.size≤_
    nlinarith
lemma polynomial_mulFold : PolynomialTime (fold mulStepRealizer) := by
  apply polynomial_fold polynomial_mulStep (10*(X+1)^2)
  rintro bs ⟨n,c⟩ pre post he
  let S:=weight (bs,(n,c))
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have hn : n.size≤S := by have h:=size_le_weight n; dsimp [S]; simp only [weight_prod]; omega
  have hc : c.size≤S := by have h:=size_le_weight c; dsimp [S]; simp only [weight_prod]; omega
  have hn' : weight n≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hs:=mulStep_fold_size pre n c
  have ho:=weight_nat_le (pre.foldl (fun z b=>mulStep (b,z)) (n,c)).2
  have hr:=mulStep_fold_first pre n c
  rw [←Prod.eta (pre.foldl (fun z b=>mulStep (b,z)) (n,c)),weight_prod,hr]
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤10*(S+1)^2
  have hmul : pre.length*(n.size+3)≤S*(S+3) := Nat.mul_le_mul hpre (by omega)
  nlinarith
lemma polynomial_multiply : PolynomialTime multiply := by
  unfold multiply
  apply polynomial_congr
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_mulFold
  apply polynomial_pair
  · exact polynomial_composition (polynomial_composition polynomial_first polynomial_toBits) polynomial_reverse
  · exact polynomial_pair polynomial_second (polynomial_constant 0)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialLoop
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B : Type} [Codec A] [Codec B]

lemma polynomial_listLength : PolynomialTime (listLength (A:=A)) := by
  unfold listLength
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 0))
  apply polynomial_fold (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 1)) polynomial_add)
    (4*X+5)
  intro as n pre post he
  have hf : pre.foldl (fun z (_ : A)=>z+1) n=n+pre.length := by
    clear he
    induction pre generalizing n with
    | nil => simp
    | cons a pre ih => simp only [List.foldl_cons,ih,List.length_cons]; omega
  change weight (pre.foldl (fun z (_ : A)=>z+1) n)≤_
  rw [hf]
  have h:=weight_nat_le (n+pre.length)
  have hs:=nat_size_add n pre.length
  have hl : pre.length.size≤pre.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have hn:=size_le_weight n
  have hp:pre.length≤weight as := (list_length_le_weight pre).trans (weight_prefix he)
  have hm : max n.size pre.length.size≤weight as+weight n := max_le (by omega) (by omega)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialGCD
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

lemma polynomial_boolNot : PolynomialTime boolNot := by
  unfold boolNot
  exact polynomial_congr _ (polynomial_choose polynomial_identity (polynomial_constant false) (polynomial_constant true))
lemma polynomial_boolAnd : PolynomialTime boolAnd := by
  unfold boolAnd
  exact polynomial_congr _ (polynomial_choose polynomial_first polynomial_second (polynomial_constant false))
lemma polynomial_natEqual : PolynomialTime natEqual := by
  unfold natEqual
  apply polynomial_congr
  apply polynomial_choose polynomial_less (polynomial_constant false)
  exact polynomial_choose (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less)
    (polynomial_constant false) (polynomial_constant true)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialCollections
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma weight_sublist {as bs : List A} (h : as.Sublist bs) : weight as≤weight bs := by
  induction h with
  | slnil => exact le_rfl
  | cons a h ih => rw [weight_cons]; omega
  | cons_cons a h ih => simp only [weight_cons]; omega
lemma polynomial_append : PolynomialTime (append (A:=A)) := by
  unfold append
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_reverse) polynomial_second)
  apply polynomial_fold polynomial_listCons (2*X+1)
  intro as bs pre post he
  simp only [List.foldl_flip_cons_eq_append']
  have hh:=weight_append pre.reverse bs
  rw [weight_reverse] at hh
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
lemma polynomial_mapStep {f : A×B → C} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (mapStepRealizer F) := by
  unfold mapStepRealizer
  exact polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_first) hF)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_listCons)
lemma polynomial_mapWith {f : A×B → C} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (mapWith F) := by
  unfold mapWith
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_composition polynomial_second polynomial_reverse)
  apply polynomial_composition (polynomial_pair polynomial_second (polynomial_pair polynomial_first (polynomial_constant [])))
  obtain ⟨p,hp⟩:=hF
  apply polynomial_fold (polynomial_mapStep ⟨p,hp⟩) (2*X+X*(p.comp (1+2*X)+1)+2)
  rintro bs ⟨a,cs⟩ pre post he
  let S:=weight (bs,(a,cs))
  have hb : weight bs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have ha : weight a≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hc : weight cs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hl : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans hb)
  have hm:=weight_map_bound (f:=fun b=>f (a,b)) (as:=pre) (N:=p.eval (1+2*S)) (by
    intro b hmem
    have hbs:=weight_mem hmem
    have hpre:=weight_prefix he
    have hh:=hp (a,b)
    have ht:=polynomial_eval_monotone p (show weight (a,b)≤1+2*S by rw [weight_prod]; omega)
    dsimp only at ht
    omega)
  rw [mapStep_fold,weight_prod]
  have happ:=weight_append (pre.map fun b=>f (a,b)).reverse cs
  rw [weight_reverse] at happ
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
  change _≤2*S+S*(p.eval (1+2*S)+1)+2
  nlinarith [Nat.mul_le_mul_right (p.eval (1+2*S)+1) hl]
lemma polynomial_map {f : A → B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (map F) := by
  unfold map
  apply polynomial_congr
  apply polynomial_composition _ polynomial_reverse
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
  obtain ⟨p,hp⟩:=hF
  apply polynomial_fold (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first ⟨p,hp⟩) polynomial_second) polynomial_listCons)
    (X+X*(p+1)+1)
  intro as bs pre post he
  let S:=weight (as,bs)
  have ha : weight as≤S := by dsimp [S]; rw [weight_prod]; omega
  have hb : weight bs≤S := by dsimp [S]; rw [weight_prod]; omega
  have hl : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans ha)
  have hm:=weight_map_bound (f:=f) (as:=pre) (N:=p.eval S) (by
    intro a hmem
    have hh:=hp a
    have ht:=polynomial_eval_monotone p ((weight_mem hmem).trans ((weight_prefix he).trans ha))
    dsimp only at ht
    omega)
  have hfold : pre.foldl (fun bs a=>f a::bs) bs=(pre.map f).reverse++bs := by
    simp [List.foldl_flip_cons_eq_append]
  change weight (pre.foldl (fun bs a=>f a::bs) bs)≤_
  rw [hfold]
  have happ:=weight_append (pre.map f).reverse bs
  rw [weight_reverse] at happ
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
  change _≤S+S*(p.eval S+1)+1
  nlinarith [Nat.mul_le_mul_right (p.eval S+1) hl]
omit [Codec A] in
lemma filter_fold (f : A → Bool) (as bs : List A) :
    as.foldl (fun bs a=>if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => cases hf:f a <;> simp [List.foldl_cons,hf,ih,List.append_assoc]
lemma polynomial_filter {f : A → Bool} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (filter F) := by
  unfold filter
  apply polynomial_congr
  apply polynomial_composition _ polynomial_reverse
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
  apply polynomial_fold (polynomial_choose (polynomial_composition polynomial_first hF) polynomial_listCons polynomial_second) (2*X+1)
  intro as bs pre post he
  change weight (pre.foldl (fun bs a=>if f a then a::bs else bs) bs)≤_
  rw [filter_fold]
  have happ:=weight_append (pre.filter f).reverse bs
  rw [weight_reverse] at happ
  have hf:=weight_sublist (List.filter_sublist (p:=f) (l:=pre))
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
lemma weight_bool_le (b : Bool) : weight b≤3 := by cases b <;> decide
lemma polynomial_any : PolynomialTime any := by
  unfold any
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
  apply polynomial_fold (polynomial_choose polynomial_first (polynomial_constant true) polynomial_second) 3
  intro as b pre post he
  simpa using weight_bool_le (pre.foldl (fun z b=>if b then true else z) b)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeCanonical
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

lemma polynomial_contains [DecidableEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (contains E) := by
  unfold contains
  exact polynomial_congr _ (polynomial_composition (polynomial_mapWith hE) polynomial_any)

lemma weight_dedupFold [DecidableEq A] (as bs : List A) :
    weight (as.foldl (fun bs a=>dedupStep (a,bs)) bs)≤weight as+weight bs := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons]
    have hh:=ih (dedupStep (a,bs))
    simp only [weight_cons]
    have hs : weight (dedupStep (a,bs))≤1+weight a+weight bs := by
      change weight (if a∈bs then bs else a::bs)≤_
      split_ifs
      · omega
      · rw [weight_cons]
    omega
lemma polynomial_dedup [DecidableEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (dedup E) := by
  unfold dedup
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold (polynomial_congr _ (polynomial_choose (polynomial_contains hE) polynomial_second polynomial_listCons)) (2*X+1)
  intro as bs pre post he
  have hh:=weight_dedupFold pre bs
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

variable (r : A → A → Prop) [DecidableRel r]
lemma weight_perm {as bs : List A} (h : as.Perm bs) : weight as=weight bs := by
  simp only [weight,size_encode_list,h.length_eq,(h.map (fun a=>TreeFunction.size (encode a))).sum_eq]
lemma weight_orderedInsert (a : A) (as : List A) :
    weight (List.orderedInsert r a as)=1+weight a+weight as := by
  rw [weight_perm (List.perm_orderedInsert r a as),weight_cons]
lemma polynomial_insertStep {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (insertStepRealizer r R) := by
  unfold insertStepRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_fst polynomial_second)
  apply polynomial_pair (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst (polynomial_snd polynomial_second))) polynomial_listCons)
  exact polynomial_choose (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) polynomial_first) hR)
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst (polynomial_snd polynomial_second))) polynomial_listCons)) polynomial_listCons)
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_snd (polynomial_snd polynomial_second))) polynomial_listCons)
lemma insert_fold_bound (as bs cs : List A) (a : A) :
    weight ((as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).2.1)≤weight as+weight bs ∧
    weight ((as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).2.2)≤2*weight as+weight bs+weight cs+weight a+1 ∧
    (as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).1=a := by
  induction as generalizing bs cs with
  | nil =>
    change weight bs≤1+weight bs ∧ weight cs≤2+weight bs+weight cs+weight a+1 ∧ a=a
    exact ⟨by omega,by omega,rfl⟩
  | cons b as ih =>
    rw [List.foldl_cons]
    by_cases h : r a b
    · have hs : insertStep r (b,(a,(bs,cs)))=(a,(b::bs,a::b::bs)) := by simp [insertStep,h]
      rw [hs]
      have he:=insert_fold r as.reverse (b::bs) a
      simp only [List.reverse_reverse] at he
      have ho : List.orderedInsert r a (b::bs)=a::b::bs := by simp [h]
      rw [ho] at he
      rw [he]
      have hw:=weight_append as.reverse (b::bs)
      rw [weight_reverse,weight_cons] at hw
      simp only [weight_orderedInsert,weight_cons]
      exact ⟨by omega,by omega,trivial⟩
    · have hs : insertStep r (b,(a,(bs,cs)))=(a,(b::bs,b::cs)) := by simp [insertStep,h]
      rw [hs]
      have hh:=ih (b::bs) (b::cs)
      simp only [weight_cons] at hh ⊢
      exact ⟨by omega,by omega,hh.2.2⟩
lemma polynomial_orderedInsert {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (orderedInsert r R) := by
  unfold orderedInsert
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_snd polynomial_second)
  apply polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_reverse)
    (polynomial_pair polynomial_first (polynomial_pair (polynomial_constant [])
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant [])) polynomial_listCons))))
  apply polynomial_fold (polynomial_insertStep r hR) (5*X+10)
  rintro as ⟨a,bs,cs⟩ pre post he
  have hh:=insert_fold_bound r pre bs cs a
  have hp:=weight_prefix he
  rw [weight_prod,hh.2.2,weight_prod]
  calc
    _ ≤ 1+weight a+(1+(weight pre+weight bs)+(2*weight pre+weight bs+weight cs+weight a+1)) := by
      gcongr
      · exact hh.1
      · exact hh.2.1
    _ ≤ _ := by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
      omega

lemma weight_insertFold (as bs : List A) :
    weight (as.foldl (fun bs a=>List.orderedInsert r a bs) bs)+1=weight as+weight bs := by
  induction as generalizing bs with
  | nil => simp only [List.foldl_nil,weight_nil]; omega
  | cons a as ih =>
    rw [List.foldl_cons]
    have hh:=ih (List.orderedInsert r a bs)
    rw [weight_orderedInsert] at hh
    rw [weight_cons]
    omega
lemma polynomial_insertionSort {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (insertionSort r R) := by
  unfold insertionSort
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold (polynomial_orderedInsert r hR) (2*X+1)
  intro as bs pre post he
  have hh:=weight_insertFold r pre bs
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

variable [DecidableEq A]
lemma polynomial_canonical {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (canonical r E R) :=
  polynomial_composition (polynomial_dedup hE) (polynomial_insertionSort r hR)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFinite
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

lemma polynomial_recode {f : C → D} {F : Realizer f} (i : A → C) (g : A → B)
    (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a))
    (hF : PolynomialTime F) : PolynomialTime (F.recode i g hi ho) := by
  obtain ⟨p,hp⟩:=hF
  refine ⟨p,fun a=>?_⟩
  have h:=hp (i a)
  change F.cost (i a)+weight (g a)≤_
  simpa only [weight,hi,ho] using h

variable [LinearOrder A]

lemma polynomial_finsetList : PolynomialTime (finsetList (A:=A)) := by
  unfold finsetList
  exact polynomial_recode _ _ _ _ polynomial_identity

lemma polynomial_listFinset {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (listFinset E R) := by
  unfold listFinset
  exact polynomial_recode _ _ _ _ (polynomial_canonical _ hE hR)

lemma polynomial_finsetMember {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetMember E) := by
  unfold finsetMember
  exact polynomial_recode _ _ _ _ (polynomial_contains hE)

lemma polynomial_finsetCard : PolynomialTime (finsetCard (A:=A)) := by
  unfold finsetCard
  exact polynomial_congr _ (polynomial_composition polynomial_finsetList polynomial_listLength)

lemma polynomial_finsetUnion {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetUnion E R) := by
  unfold finsetUnion
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_finsetList)
      (polynomial_composition polynomial_second polynomial_finsetList)) polynomial_append)
    (polynomial_listFinset hE hR))

lemma polynomial_finsetImage [LinearOrder B] {f : A → B} {F : Realizer f}
    {E : Realizer (fun x : B×B=>decide (x.1=x.2))}
    {R : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hF : PolynomialTime F) (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetImage F E R) := by
  unfold finsetImage
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_finsetList (polynomial_map hF)) (polynomial_listFinset hE hR))

lemma polynomial_finsetFilter {p : A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetFilter P) := by
  unfold finsetFilter
  exact polynomial_recode _ _ _ _ (polynomial_filter hP)

omit [LinearOrder A] in
lemma polynomial_filterWith {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (filterWith P) := by
  unfold filterWith
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_mapWith (polynomial_pair polynomial_second hP))
      (polynomial_filter polynomial_second)) (polynomial_map polynomial_first))
lemma polynomial_finsetFilterWith {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetFilterWith P) := by
  unfold finsetFilterWith
  exact polynomial_recode _ _ _ _ (polynomial_filterWith hP)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma polynomial_all : PolynomialTime all := by
  unfold all
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_map polynomial_boolNot) polynomial_any) polynomial_boolNot)

lemma polynomial_pairEqual [DecidableEq A] [DecidableEq B]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {F : Realizer (fun x : B×B=>decide (x.1=x.2))}
    (hE : PolynomialTime E) (hF : PolynomialTime F) : PolynomialTime (pairEqual E F) := by
  unfold pairEqual
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hE)
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) hF)) polynomial_boolAnd)

lemma polynomial_leNat : PolynomialTime leNat := by
  unfold leNat
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less) polynomial_boolNot)

variable [LinearOrder A]
lemma polynomial_finsetAny {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetAny P) := by
  unfold finsetAny
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith hP)) polynomial_any)

lemma polynomial_finsetAll {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetAll P) := by
  unfold finsetAll
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith hP)) polynomial_all)

lemma polynomial_finsetSubset {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetSubset E) := by
  unfold finsetSubset
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetAll (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE))))

lemma polynomial_finsetEqual {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetEqual E) := by
  unfold finsetEqual
  exact polynomial_congr _ (polynomial_composition (polynomial_pair (polynomial_finsetSubset hE)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetSubset hE))) polynomial_boolAnd)

lemma polynomial_finsetSDiff {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetSDiff E) := by
  unfold finsetSDiff
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetFilterWith (polynomial_composition
      (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE)) polynomial_boolNot)))

lemma polynomial_finsetInter {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetInter E) := by
  unfold finsetInter
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetFilterWith (polynomial_composition
      (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE))))

lemma polynomial_finsetErase {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetErase E) := by
  unfold finsetErase
  exact polynomial_congr _ (polynomial_finsetFilterWith (polynomial_composition hE polynomial_boolNot))
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeColex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B] [LinearOrder A] [LinearOrder B]

lemma polynomial_boolOr : PolynomialTime boolOr := by
  unfold boolOr
  exact polynomial_congr _ (polynomial_choose polynomial_first (polynomial_constant true) polynomial_second)

lemma polynomial_colexLe {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (colexLe E R) := by
  unfold colexLe
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetSDiff hE))
    (polynomial_finsetSDiff hE))
    (polynomial_finsetAll (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_finsetAny hR)))

lemma polynomial_lexLe {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    {S : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) (hS : PolynomialTime S) :
    PolynomialTime (lexLe E R S) := by
  unfold lexLe
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hR)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hE) polynomial_boolNot)
      (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) hS)) polynomial_boolOr))
    polynomial_boolAnd)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteCollections
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma weight_flatten (as : List (List A)) : weight as.flatten≤weight as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatten_cons,weight_cons]
    have h:=weight_append a as.flatten
    omega

lemma polynomial_flatten : PolynomialTime (flatten (A:=A)) := by
  unfold flatten
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold polynomial_append (2*X+1)
  intro as bs pre post he
  rw [fold_prepend]
  have h1:=weight_append pre.reverse.flatten bs
  have h2:=weight_flatten pre.reverse
  rw [weight_reverse] at h2
  have h3:=weight_prefix he
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma polynomial_flatMapPoly {f : A → List B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (flatMapPoly F) :=
  polynomial_congr _ (polynomial_composition (polynomial_map hF) polynomial_flatten)

variable [LinearOrder A]
lemma polynomial_finsetSingleton : PolynomialTime (finsetSingleton (A:=A)) := by
  unfold finsetSingleton
  exact polynomial_recode _ _ _ _ (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_constant [])) polynomial_listCons)

lemma polynomial_finsetInsert {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetInsert E R) :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_finsetSingleton) polynomial_second)
    (polynomial_finsetUnion hE hR))

variable [LinearOrder B]
lemma polynomial_finsetBiUnion {f : C×A → Finset B} {F : Realizer f}
    {E : Realizer (fun x : B×B=>decide (x.1=x.2))}
    {R : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hF : PolynomialTime F) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (finsetBiUnion F E R) := by
  unfold finsetBiUnion
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith (polynomial_composition hF polynomial_finsetList))) polynomial_flatten)
    (polynomial_listFinset hE hR)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalPost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R : Type} [Inhabited Γ]

lemma execute_add (M : Table Γ Q) (n m : ℕ) (c : Cfg Γ Q) (b : Stream) :
    execute M (n+m) c b=execute M m (execute M n c b) (shift n b) := by
  induction n generalizing c b with
  | zero => simp only [execute,Nat.zero_add,shift_zero]
  | succ n ih =>
    rw [Nat.succ_add,execute,ih,execute]
    congr 1
    funext i
    simp only [shift]
    congr 1
    omega

lemma execute_halted (M : Table Γ Q) (n : ℕ) (T : Tape Γ) (b : Stream) :
    execute M n ⟨none,T⟩ b=⟨none,T⟩ := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => exact ih (shift 1 b)

lemma experiment_cost (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) :
    (experiment M n c).cost=n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [experiment,Experiment.cost,ih,max_self]; omega

lemma experiment_run (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Stream) :
    (experiment M n c).run b=(execute M n c b,n) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => simp only [experiment,Experiment.run,ih,execute]; congr 1; omega

theorem physical_law (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (f : Cfg Γ Q → ℚ) :
    average (fun b : Bits n=>f (execute M n c (extend b)))=(experiment M n c).mean f := by
  have h:=Experiment.average_run (experiment M n c) f n (by rw [experiment_cost])
  simpa only [experiment_run] using h

variable [Fintype Q] [Inhabited Q]

lemma tick_seal (M : Table Symbol Q) (c : Cfg Symbol Q) (b : Bool) :
    MatchingFPRAS.tick (machine M) (sealCfg M c) b=sealCfg M (tick M c b) := by
  cases c with
  | mk s T => cases s with
    | none => rfl
    | some q =>
      simp only [MatchingFPRAS.tick,sealCfg,machine,Option.map_some,Equiv.symm_apply_apply,tick]
      cases h:M q T.head b with
      | none => rfl
      | some qa => rcases qa with ⟨q',a⟩; cases a <;> rfl

omit [Fintype Q] [Inhabited Q] in
lemma execute_list (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Bits n) :
    execute M n c (extend b)=(List.ofFn b).foldl (tick M) c := by
  induction n generalizing c with
  | zero => simp [execute]
  | succ n ih =>
    rw [execute,List.ofFn_succ,List.foldl_cons]
    have h0 : extend b 0=b 0 := by simp [extend]
    rw [h0,←ih]
    have he : ∀ i, i<n → shift 1 (extend b) i=extend (fun j : Fin n=>b j.succ) i := by
      intro i hi
      simp only [shift,extend,dite_eq_left hi,dite_eq_left (by omega : 1+i<n+1)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hc : ∀ (k : ℕ) (a d : Stream), (∀ i,i<k→a i=d i) →
        ∀ c, execute M k c a=execute M k c d := by
      intro k
      induction k with
      | zero => intros; rfl
      | succ k hk =>
        intro a d had c
        simp only [execute,had 0 (by omega)]
        apply hk
        intro i hi
        exact had (1+i) (by omega)
    exact hc n _ _ he _

lemma foldl_seal (M : Table Symbol Q) (bs : List Bool) (c : Cfg Symbol Q) :
    bs.foldl (MatchingFPRAS.tick (machine M)) (sealCfg M c)=sealCfg M (bs.foldl (tick M) c) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => rw [List.foldl_cons,tick_seal,ih,List.foldl_cons]

lemma initial_seal (M : Table Symbol Q) (input : List Symbol) :
    sealCfg M ⟨some default,Tape.mk₁ input⟩=MatchingFPRAS.initial (machine M) input := by
  change (⟨some (enumeration default),Tape.mk₁ input⟩ : Configuration (machine M))=⟨some 0,Tape.mk₁ input⟩
  rw [enumeration_default]
  rfl

theorem run_seal (M : Table Symbol Q) (input : List Symbol) (n : ℕ) (b : Bits n) :
    MatchingFPRAS.run (machine M) input b=
      sealCfg M (execute M n ⟨some default,Tape.mk₁ input⟩ (extend b)) := by
  unfold MatchingFPRAS.run
  rw [←initial_seal,foldl_seal,execute_list]

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_CoinTM1
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

lemma execute_first_eq (M : PhysicalPost.Table Γ (State Γ Λ σ))
    (x y : PhysicalPost.Cfg Γ (State Γ Λ σ)) (h : ∀ b,PhysicalPost.tick M x b=PhysicalPost.tick M y b)
    {n : ℕ} (hn : 0 < n) (b : Stream) : PhysicalPost.execute M n x b=PhysicalPost.execute M n y b := by
  cases n with
  | zero => omega
  | succ n => simp only [PhysicalPost.execute,h]

theorem statement_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ k,0 < k ∧ k ≤ statementCost q ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (pending q v T) b=trCfg (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.move d)
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | write f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.write (f T.head v))
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | load f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih (f T.head v) T
    refine ⟨k,hk,hc,fun b=>?_⟩
    rw [execute_first_eq (table M coin) (pending (.load f q) v T) (pending q (f T.head v) T) (fun _=>rfl) hk]
    exact he b
  | branch f q r ihq ihr =>
    cases h:f T.head v with
    | false =>
      obtain ⟨k,hk,hc,he⟩:=ihr v T
      refine ⟨k,hk,hc.trans (le_max_right _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending r v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,Bool.false_eq_true,ite_false]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_false] using he b
    | true =>
      obtain ⟨k,hk,hc,he⟩:=ihq v T
      refine ⟨k,hk,hc.trans (le_max_left _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending q v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,ite_true, if_true]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_true] using he b
  | goto f =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    simp only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux,trCfg,Option.map_some,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    rfl

lemma entry_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (l : Λ) (v : σ) (T : Tape Γ) (hl : coin l=none) :
    ∃ k,0 < k ∧ k ≤ statementCost (M l) ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (trCfg ⟨some l,v,T⟩) b=
        trCfg (TM1.stepAux (M l) v T) := by
  obtain ⟨k,hk,hc,he⟩:=statement_ticks M coin (M l) v T
  refine ⟨k,hk,hc,fun b=>?_⟩
  rw [execute_first_eq (table M coin) (trCfg ⟨some l,v,T⟩) (pending (M l) v T) (fun _=>by
    simp only [PhysicalPost.tick,trCfg,Option.map_some,table,hl,pending]) hk]
  exact he b

end MatchingFPRAS.CoinTM1

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalRestriction
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q : Type} [Inhabited Γ]

lemma tick_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (c : Cfg Γ {q // q∈S}) (b : Bool) :
    tick M (liftCfg S c) b=liftCfg S (tick (restrict M S h) c b) := by
  cases c with
  | mk state T => cases state with
    | none => rfl
    | some q =>
      cases e:M q.val T.head b with
      | none => simp only [tick,liftCfg,Option.map_some,restrict,e,Option.map_none]
      | some qa =>
        rcases qa with ⟨q',act⟩
        have hq' : q'∈S:=h q.val q.property T.head b q' act e
        simp only [tick,liftCfg,Option.map_some,restrict,e,dite_eq_left hq']

lemma execute_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (n : ℕ) (c : Cfg Γ {q // q∈S}) (b : Stream) :
    execute M n (liftCfg S c) b=liftCfg S (execute (restrict M S h) n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_lift,ih,execute]

lemma restrictedMachine_run (M : Table Symbol Q) (S : Finset Q)
    (h : Supported M S) (q₀ : Q) (hq₀ : q₀∈S)
    (input : List Symbol) (n : ℕ) (b : Bits n) :
    letI : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
    MatchingFPRAS.run (restrictedMachine M S h q₀ hq₀) input b=
      sealCfg (restrict M S h)
        (execute (restrict M S h) n ⟨some default,Tape.mk₁ input⟩ (extend b)) :=
by
  let : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
  exact run_seal (restrict M S h) input n b

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_SafeTrace
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SafeTrace
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

namespace Path
variable {M : Λ → TM1.Stmt Γ Λ σ} {safe : Λ → Prop}
lemma of_run (n : ℕ) (c : TM1.Cfg Γ Λ σ)
    (h : ∀ i,i<n→∀ l,(MachineCost.run (TM1.step M) i c).l=some l→safe l) :
    Path M safe n c (MachineCost.run (TM1.step M) n c) := by
  induction n generalizing c with
  | zero => exact .refl _
  | succ n ih =>
    refine .cons (h 0 (by omega)) (ih _ ?_)
    intro i hi l hl
    exact h (i+1) (by omega) l hl

theorem physical {n : ℕ} {a b : TM1.Cfg Γ Λ σ} (h : Path M safe n a b)
    (coin : CoinTM1.Coins Λ) (hcoin : ∀ l,safe l→coin l=none)
    (C : ℕ) (hC : ∀ l,safe l→statementCost (M l)≤C) :
    ∃ k,k≤n*C ∧ ∀ bits : Stream,
      PhysicalPost.execute (CoinTM1.table M coin) k (CoinTM1.trCfg a) bits=CoinTM1.trCfg b := by
  induction h with
  | refl a => exact ⟨0,by simp,fun _=>rfl⟩
  | @cons n c d hc hr ih =>
    obtain ⟨k,hk,he⟩:=ih
    rcases c with ⟨l,v,T⟩
    cases l with
    | none =>
      refine ⟨k,le_trans hk ?_,he⟩
      exact Nat.mul_le_mul_right C (by omega)
    | some l =>
      have hs:=hc l rfl
      obtain ⟨j,hj,hjc,hje⟩:=CoinTM1.entry_ticks M coin l v T (hcoin l hs)
      refine ⟨j+k,?_,fun bits=>?_⟩
      · have hb:=hC l hs
        calc j+k≤C+n*C := Nat.add_le_add (hjc.trans hb) hk
             _=(n+1)*C := by ring
      · rw [PhysicalPost.execute_add,hje]
        exact he (shift j bits)
end Path
end MatchingFPRAS.SafeTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProcess
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q α β : Type} [Inhabited Γ]

namespace Implements
variable {M : Table Γ Q} {out : α → Cfg Γ Q} {c : Cfg Γ Q} {p : Experiment α}

lemma execution (h : Implements M out c p) (b : Stream) :
    execute M (p.run b).2 c b=out (p.run b).1 := by
  induction h generalizing b with
  | done a => rfl
  | read c f h ih =>
    simp only [Experiment.run,execute_add]
    exact ih (b 0) (shift 1 b)
  | delay c d n p hs hr ih =>
    simp only [Experiment.run,execute_add,hs]
    exact ih (shift n b)

lemma bind (h : Implements M out c p) (q : α → Experiment β)
    (out' : β → Cfg Γ Q) (hq : ∀ a,Implements M out' (out a) (q a)) :
    Implements M out' c (p.bind q) := by
  induction h with
  | done a => exact hq a
  | read c f h ih => exact .read c _ ih
  | delay c d n p hs hr ih => exact .delay c d n _ hs ih

lemma padded_execution (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (b : Stream) :
    execute M n c b=out (p.run b).1 := by
  have hb : (p.run b).2 ≤ n:=(Experiment.run_cost p b).trans hn
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hb
  rw [hk,execute_add,h.execution b]
  have he : out (p.run b).1=⟨none,(out (p.run b).1).tape⟩ := by
    cases e:out (p.run b).1 with
    | mk state tape =>
      have hstate := halt (p.run b).1
      rw [e] at hstate
      change state = none at hstate
      subst state
      rfl
  rw [he,execute_halted]

theorem fair_law (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (f : Cfg Γ Q → ℚ) :
    average (fun b : Bits n=>f (execute M n c (extend b)))=p.mean (fun a=>f (out a)) := by
  simp_rw [h.padded_execution halt n hn]
  exact Experiment.average_run p (fun a=>f (out a)) n hn

end Implements
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineStackCompiler
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream SafeTrace
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
omit [DecidableEq K] [∀ k,Fintype (Γ k)] in
lemma height_bound (S : ∀ k,List (Γ k)) : StackCost.StackBound S (height S) :=
  fun k=>Finset.le_sup (f:=fun k=>(S k).length) (Finset.mem_univ k)
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Online
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream

variable {K Λ σ α : Type} {Γ : K → Type} [DecidableEq K]

namespace Executes
variable {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
  {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}

variable [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ]

omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_mono [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H H' n n' : ℕ) (hH : H≤H') (hn : n≤n') :
    factor M H n ≤ factor M H' n' := by unfold factor; gcongr
end Executes
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalSequential
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R α β : Type} [Inhabited Γ]

lemma tick_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (q : Q) (T : Tape Γ) (b : Bool) :
    tick (seq M N r₀) (leftCfg r₀ ⟨some q,T⟩) b=leftCfg r₀ (tick M ⟨some q,T⟩ b) := by
  cases h : M q T.head b with
  | none => simp only [tick,leftCfg,seq,h,Option.elim_some,Option.elim_none,Tape.write_self]
  | some qa => rcases qa with ⟨q',act⟩;cases act <;> simp only [tick,leftCfg,seq,h,Option.elim_some]
lemma tick_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (c : Cfg Γ R) (b : Bool) :
    tick (seq M N r₀) (rightCfg c) b=rightCfg (tick N c b) := by
  rcases c with ⟨s,T⟩
  cases s with
  | none => rfl
  | some r =>
    cases h:N r T.head b with
    | none => simp only [tick,rightCfg,Option.map_some,seq,h,Option.map_none]
    | some ra => rcases ra with ⟨r',act⟩;cases act <;> simp only [tick,rightCfg,seq,h,Option.map_some]
lemma execute_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ R) (b : Stream) :
    execute (seq M N r₀) n (rightCfg c) b=rightCfg (execute N n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_right,ih,execute]
lemma Implements.right {M : Table Γ Q} {N : Table Γ R} (r₀ : R) {out : α→Cfg Γ R}
    {c : Cfg Γ R} {p : Experiment α} (h : Implements N out c p) :
    Implements (seq M N r₀) (rightCfg ∘ out) (rightCfg c) p := by
  induction h with
  | done a => exact .done a
  | read c f h ih => apply Implements.read;intro b;rw [tick_right];exact ih b
  | delay c d n p hs hr ih =>
    exact .delay _ _ n _ (fun b=>by rw [execute_right,hs]) ih

lemma early_cost (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : (early M n c).cost≤n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    cases h:c.state <;> simp only [early,h,Experiment.cost]
    · omega
    · have h0:=ih (tick M c false); have h1:=ih (tick M c true); omega
lemma early_run (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Stream) :
    ((early M n c).run b).1=execute M n c b := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => rw [execute_halted];rfl
    | some q => simp only [early,Experiment.run,execute];exact ih _ _
lemma early_mean (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=average (fun b : Bits n=>f (execute M n c (extend b))) := by
  simpa only [early_run] using (Experiment.average_run (early M n c) f n (early_cost M n c)).symm
lemma early_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ Q) :
    Implements (seq M N r₀) (leftCfg r₀) (leftCfg r₀ c) (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q =>
      apply Implements.read
      intro b
      rw [tick_left]
      exact ih _
lemma Implements.early_mean {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=p.mean (fun a=>f (out a)) := by
  rw [PhysicalPost.early_mean]
  exact h.fair_law halt n hn f
lemma Implements.bind_all {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (q : α→Experiment β) (out' : β→Cfg Γ Q)
    (hq : p.All (fun a=>Implements M out' (out a) (q a))) :
    Implements M out' c (p.bind q) := by
  induction h with
  | done a => exact hq
  | read c f h ih => exact .read c _ (fun b=>by cases b;exact ih false hq.1;exact ih true hq.2)
  | delay c d n p hs hr ih => exact .delay c d n _ hs (ih hq)
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TapeTools
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
lemma mk₂_left_nil (R : List Γ) :
    (Tape.mk₂ [] R).move .left=Tape.mk₂ [] (default::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk,ListBlank.tail_mk,ListBlank.head_mk]
lemma blank_zero (n : ℕ) : (ListBlank.mk (List.replicate n (default : Γ)))=ListBlank.mk [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,←ListBlank.cons_mk,ih]; exact ListBlank.cons_head_tail (ListBlank.mk [])
lemma blank_append_zero (L : List Γ) (n : ℕ) :
    ListBlank.mk (L++List.replicate n default)=ListBlank.mk L := by
  induction L with
  | nil => exact blank_zero n
  | cons a L ih => rw [List.cons_append,←ListBlank.cons_mk,ih,ListBlank.cons_mk]

lemma Exec.refl (M : Λ→TM1.Stmt Γ Λ σ) (c : TM1.Cfg Γ Λ σ) : Exec M c c 0 := ⟨0,le_rfl,rfl⟩
lemma Exec.step (M : Λ→TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) (T : Tape Γ) :
    Exec M ⟨some l,v,T⟩ (TM1.stepAux (M l) v T) 1 := ⟨1,le_rfl,rfl⟩
lemma Exec.trans {M : Λ→TM1.Stmt Γ Λ σ} {c d e : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (g : Exec M d e t) : Exec M c e (s+t) := by
  obtain ⟨i,hi,he⟩:=h
  obtain ⟨j,hj,hf⟩:=g
  exact ⟨i+j,Nat.add_le_add hi hj,by rw [MachineCost.run_add,he,hf]⟩
lemma Exec.mono {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (hst : s≤t) : Exec M c d t :=
  let ⟨k,hk,he⟩:=h; ⟨k,hk.trans hst,he⟩

lemma select_step [DecidableEq σ] (vs : List σ) (f : σ→TM1.Stmt Γ Λ σ)
    (fallback : TM1.Stmt Γ Λ σ) (v : σ) (hv : v∈vs) (T : Tape Γ) :
    TM1.stepAux (select vs f fallback) v T=TM1.stepAux (f v) v T := by
  induction vs with
  | nil => simp at hv
  | cons a as ih =>
    simp only [List.mem_cons] at hv
    simp only [select,List.foldr_cons,TM1.stepAux]
    by_cases h:v=a
    · simp only [h,decide_true,Bool.cond_true]
    · simp only [h,decide_false,Bool.cond_false]
      exact ih (hv.resolve_left h)

lemma writeLeft_step (xs : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) (R : List Γ) :
    TM1.stepAux (writeLeft xs q) v (Tape.mk₂ [] (default::R))=
      TM1.stepAux q v (Tape.mk₂ [] (default::xs.reverse++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeLeft,List.foldr_cons,TM1.stepAux,mk₂_write,mk₂_left_nil]
    rw [show List.foldr (fun a tail=>TM1.Stmt.write (fun _ _=>a) (.move .left tail)) q bs=writeLeft bs q from rfl,ih]
    simp only [List.reverse_cons,List.cons_append,List.append_assoc,List.nil_append]

lemma eraseToLeft_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseToLeft xs.length q) v (Tape.mk₂ (xs++L) R)=
      TM1.stepAux q v (Tape.mk₂ L (List.replicate xs.length default++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseToLeft,TM1.stepAux,List.cons_append,mk₂_left,mk₂_write]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.move .left (.write (fun _ _=>default) tail)) xs.length=eraseToLeft xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]

variable {I : Type} [DecidableEq I]
lemma grab_step (is : List I) (f v : I→Γ) (q : TM1.Stmt Γ Λ (I→Γ)) (L R : List Γ) :
    TM1.stepAux (grab is q) v (Tape.mk₂ L (is.map f++R))=
      TM1.stepAux q (is.foldl (fun v i=>Function.update v i (f i)) v)
        (Tape.mk₂ ((is.map f).reverse++L) R) := by
  induction is generalizing v L with
  | nil => rfl
  | cons i is ih =>
    simp only [grab,List.foldr_cons,List.map_cons,List.cons_append,TM1.stepAux,mk₂_head,mk₂_right,List.foldl_cons]
    rw [show List.foldr (fun i tail=>TM1.Stmt.load (fun a v=>Function.update v i a) (.move .right tail)) q is=grab is q from rfl,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
omit [Inhabited Γ] in
lemma fold_updates (is : List I) (f v : I→Γ) (i : I) :
    (is.foldl (fun v i=>Function.update v i (f i)) v) i=if i∈is then f i else v i := by
  induction is generalizing v with
  | nil => simp
  | cons a is ih =>
    rw [List.foldl_cons,ih]
    by_cases hi:i∈is <;> by_cases ha:i=a <;> simp [hi,ha]
lemma grab_fin (n : ℕ) (f v : Fin n→Γ) (q : TM1.Stmt Γ Λ (Fin n→Γ)) (L R : List Γ) :
    TM1.stepAux (grab (List.finRange n) q) v (Tape.mk₂ L (List.ofFn f++R))=
      TM1.stepAux q f (Tape.mk₂ ((List.ofFn f).reverse++L) R) := by
  have he : (List.finRange n).map f=List.ofFn f := List.ofFn_eq_map.symm
  rw [←he,grab_step]
  have hf : (List.finRange n).foldl (fun v i=>Function.update v i (f i)) v=f := by
    funext i
    rw [fold_updates]
    simp
  rw [hf]
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Physical
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Fintype Λ] [Fintype σ] [Inhabited σ]
omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
lemma Exec.physical {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {t : ℕ}
    (h : Exec M c d t) : ∃ k,k≤t*programCost M ∧ ∀ b : Stream,
      PhysicalPost.execute (table M) k (CoinTM1.trCfg c) b=CoinTM1.trCfg d := by
  obtain ⟨n,hn,he⟩:=h
  have hp:=SafeTrace.Path.of_run (safe:=fun _=>True) (M:=M) n c (fun _ _ _ _=>trivial)
  rw [he] at hp
  obtain ⟨k,hk,hb⟩:=hp.physical (fun _=>none) (fun _ _=>rfl) (programCost M)
    (fun l _=>statementCost_le_programCost M l)
  exact ⟨k,hk.trans (Nat.mul_le_mul_right _ hn),hb⟩
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A : Type}
lemma mean_congr_all (p : Experiment A) (f g : A→ℚ) (h : p.All (fun a=>f a=g a)) : p.mean f=p.mean g := by
  induction p with
  | done a => exact h
  | delay n p ih => exact ih h
  | read p ih => simp only [mean,ih false h.1,ih true h.2]
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q A B : Type} [Inhabited Γ]
lemma Implements.map_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (f : A→B) (out' : B→Cfg Γ Q)
    (he : p.All (fun a=>out a=out' (f a))) : Implements M out' c (p.map f) := by
  induction h with
  | done a => rw [he];exact .done (f a)
  | read c p h ih => exact .read _ _ (fun b=>by cases b;exact ih false he.1;exact ih true he.2)
  | delay c d n p hs hr ih => exact .delay _ _ n _ hs (ih he)
lemma early_implements (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : Implements M id c (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q => exact .read _ _ (fun b=>ih _)
lemma Implements.early_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) : (early M n c).All (fun d=>d.state=none) := by
  apply Experiment.all_of_mean_eq (p:=(p.map out)) (fun f=>by rw [Experiment.mean_map];exact h.early_mean halt n hn f)
  rw [Experiment.all_map]
  exact (Experiment.all_true _).mono (fun a _=>halt a)

namespace Program
lemma earlyTapes_cost (P : Program) (n : ℕ) (T : Tape Symbol) : (P.earlyTapes n T).cost≤n := by
  rw [earlyTapes,Experiment.cost_map];exact early_cost _ _ _
lemma Realizes.early {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (h : P.Realizes input f N) :
    Implements P.table P.final (P.initial input) (P.earlyTapes N input) ∧
      (∀ w,(P.earlyTapes N input).mean w=f.mean w) := by
  obtain ⟨p,hp,hm,hc⟩:=h
  refine ⟨?_,fun w=>?_⟩
  · apply (early_implements P.table N (P.initial input)).map_all Cfg.tape P.final
    exact (hp.early_all (fun _=>rfl) N hc).mono (by intro d hd;cases d; simp only [id_eq,final] at *;cases hd;rfl)
  · rw [earlyTapes,Experiment.mean_map,hp.early_mean (fun _=>rfl) N hc]
    exact hm w
lemma seq_realizes (P R : Program) (input : Tape Symbol) (f : Experiment (Tape Symbol))
    (g : Tape Symbol→Experiment (Tape Symbol)) (N S : ℕ)
    (hP : P.Realizes input f N) (hR : f.All (fun T=>R.Realizes T (g T) S)) :
    (P.seq R).Realizes input (f.bind g) (N+S) := by
  let p:=early P.table N (P.initial input)
  let q:=fun c : Cfg Symbol P.State=>R.earlyTapes S c.tape
  have hmean (h : Cfg Symbol P.State→ℚ) : p.mean h=f.mean (fun T=>h (P.final T)) := by
    obtain ⟨v,hv,hm,hc⟩:=hP
    rw [hv.early_mean (fun _=>rfl) N hc]
    exact hm _
  have hall : p.All (fun c=>c.state=none ∧ R.Realizes c.tape (g c.tape) S) := by
    apply Experiment.all_of_mean_eq (p:=f.map P.final) (fun h=>by rw [Experiment.mean_map];exact hmean h)
    rw [Experiment.all_map]
    exact hR.mono (fun T hT=>⟨rfl,hT⟩)
  have himpl : Implements (P.seq R).table (fun T=>rightCfg (R.final T))
      ((P.seq R).initial input) (p.bind q) := by
    apply (early_left P.table R.table R.entry N (P.initial input)).bind_all q _
    exact hall.mono (by
      intro c hc
      have hq:=(hc.2.early).1.right (M:=P.table) R.entry
      have he:leftCfg R.entry c=rightCfg (R.initial c.tape) := by
        rcases c with ⟨s,T⟩;simp only at hc;cases hc.1;rfl
      rw [he]
      exact hq)
  refine ⟨p.bind q,himpl,?_,?_⟩
  · intro w
    rw [Experiment.mean_bind,hmean,Experiment.mean_bind]
    apply Experiment.mean_congr_all
    exact hR.mono (fun T hT=>hT.early.2 w)
  · exact (Experiment.cost_bind_le p q S (fun c=>earlyTapes_cost R S c.tape)).trans
      (Nat.add_le_add_right (early_cost _ N _) S)

lemma realizes_TM1 {Λ σ : Type} [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (v v' : σ) (input output : Tape Symbol) (n : ℕ)
    (he : LiteralTape.Exec M ⟨some l,v,input⟩ ⟨none,v',output⟩ n) :
    (ofTM1 M l v).Realizes input (.done output) (n*MachineCost.programCost M) := by
  obtain ⟨k,hk,hb⟩:=he.physical
  refine ⟨.delay k (.done output),?_,fun _=>rfl,by simpa only [Experiment.cost,Nat.add_zero] using hk⟩
  exact .delay _ _ k _ hb (.done output)
end Program
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePostRealization
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

lemma inputStacks_bound {A : Type} [Codec A] (a : A) : StackCost.StackBound (inputStacks a) (weight a) := by
  intro i
  have h:=weight_pos a
  cases i with
  | inr i => simp [inputStacks,encodeEnv]
  | inl i =>
    simp only [inputStacks,encodeEnv,env]
    split_ifs <;> first
    | exact le_rfl
    | simpa only [TreeData.encode,List.length_singleton] using (Nat.succ_le_iff.mpr h)

end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlinePhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing TreeTyped TreeData TreeFunction TreeMachine TreePost PhysicalPost PhysicalStream

lemma input_height {A : Type} [Codec A] (a : A) : OnlineStack.height (inputStacks a)=weight a := by
  apply le_antisymm
  · exact Finset.sup_le (fun k _=>inputStacks_bound a k)
  · have h:=OnlineStack.height_bound (inputStacks a) (Sum.inl (0 : Reg))
    simpa only [inputStacks,encodeEnv,env,ite_true, if_true,weight,TreeFunction.size] using h

lemma cfg_packed {A : Type} [Codec A] (P : OnlineProc.Proc (K Reg)) (a : A) (l : Option P.Label) :
    upCfg (OnlineStack.cfg (⟨l,none,inputStacks a⟩ : StoreCfg P))=
      ⟨l.map (fun u=>(Sum.inl (TM1to1.Λ'.normal (TM2to1.Λ'.normal u)),none)),Tape.mk₁ (packed a)⟩ := by
  simp only [upCfg,OnlineStack.cfg,OnlineStack.stackCfg,input_height,CoinTM1.trCfg,
    TM1to1.trCfg,TM1to1.trTape,TM1to1.trTape',Tape.mk₁,Tape.mk₂,Tape.mk'_left,Tape.mk'_right₀,
    ListBlank.flatMap_mk,List.flatMap_nil,Option.map_map]
  rw [Tape.map_mk']
  rfl

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

lemma polynomial_fromBit : PolynomialTime fromBitRealizer :=
  polynomial_choose polynomial_identity (polynomial_constant _) (polynomial_constant _)
lemma polynomial_natWord : PolynomialTime natWordRealizer := by
  unfold natWordRealizer
  apply polynomial_congr
  have := polynomial_fromBit
  have := polynomial_toBits
  have := polynomial_map polynomial_fromBit
  ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe | apply polynomial_congr)))
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgramMap
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma Realizes.mono {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N S : ℕ}
    (h : P.Realizes input f N) (hn : N≤S) : P.Realizes input f S := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,hm,hc.trans hn⟩
end MatchingFPRAS.PhysicalPost.Program

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_BlockMap
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Λ σ : Type}
lemma scan_left (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .left⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,(Tape.mk₂ (xs++mark::L) R).move .left⟩
      ⟨some l,v,Tape.mk₂ L (mark::(xs.reverse++R))⟩ xs.length := by
  induction xs generalizing R with
  | nil => simpa using Exec.refl M (⟨some l,v,Tape.mk₂ L (mark::R)⟩ : TM1.Cfg Symbol Λ σ)
  | cons a xs ih =>
    simp only [List.cons_append,mk₂_left]
    have h1:=Exec.step M l v (Tape.mk₂ (xs++mark::L) (a::R))
    rw [hs v _ (by simpa using hx a (by simp))] at h1
    have h2:=ih (a::R) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
lemma scan_right (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .right⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,Tape.mk₂ L (xs++mark::R)⟩
      ⟨some l,v,Tape.mk₂ (xs.reverse++L) (mark::R)⟩ xs.length := by
  induction xs generalizing L with
  | nil => exact Exec.refl M _
  | cons a xs ih =>
    simp only [List.cons_append]
    have h1:=Exec.step M l v (Tape.mk₂ L (a::(xs++mark::R)))
    rw [hs v _ (by simpa using hx a (by simp)),mk₂_right] at h1
    have h2:=ih (a::L) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
end MatchingFPRAS.LiteralTape

namespace MatchingFPRAS.LiteralBlockMap
open Turing LiteralTape

variable (w : ℕ) (h : Block w→List Symbol) (header : List Symbol)
local notation "M" => code w h header
lemma seek_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .seek) v T=⟨some .seek,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma back_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .back) v T=⟨some .back,v,T.move .right⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopSep_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .stopSep) v T=⟨some .stopSep,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopOut_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .stopOut) v T=⟨some .stopOut,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]

lemma start_step (input : List Symbol) (v : Block w) :
    Exec M ⟨some .start,v,Tape.mk₁ input⟩ ⟨some .read,v,working [] 0 input⟩ 1 := by
  have hh:=Exec.step M .start v (Tape.mk₁ input)
  simpa only [code,TM1.stepAux,Tape.mk₁,mk₂_left_nil,mk₂_write,mk₂_right,working,List.replicate_zero,
    List.reverse_nil,List.nil_append] using hh

lemma seek_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .seek,v,Tape.mk₂ [] (6::R)⟩
      ⟨some .back,v,Tape.mk₂ [6] (h v++R)⟩ 1 := by
  have hh:=Exec.step M .seek v (Tape.mk₂ [] (6::R))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true] at hh
  rw [select_step _ _ _ v (by simp)] at hh
  have hs:=writeLeft_step (Γ:=Symbol) (h v).reverse
    (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>Label.back)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [TM1.stepAux,mk₂_write,hs] using hh
lemma stopOut_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .stopOut,v,Tape.mk₂ [] (6::R)⟩
      ⟨none,v,Tape.mk₂ [0] (header++R)⟩ 1 := by
  have hh:=Exec.step M .stopOut v (Tape.mk₂ [] (6::R))
  have hs:=writeLeft_step (Γ:=Symbol) header.reverse
    (.write (fun _ _=>0) (.move .right (.halt : TM1.Stmt Symbol Label (Block w)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write,hs] using hh

lemma read_block (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .seek,b,(Tape.mk₂ (List.replicate gap 0++out.reverse++[6])
        (List.replicate w 0++7::input)).move .left⟩ 1 := by
  have hh:=Exec.step M .read v (working out gap (List.ofFn b++input))
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at hh
  rw [working,grab_fin] at hh
  simp only [TM1.stepAux,hb,decide_false,Bool.cond_false] at hh
  cases hr : (List.ofFn b).reverse with
  | nil => have hl:=congrArg List.length hr; simp at hl; omega
  | cons a xs =>
    have hl : (xs++[7]).length=w := by
      have hh:=congrArg List.length hr
      simp only [List.length_reverse,List.length_ofFn,List.length_cons] at hh
      simp only [List.length_append,List.length_singleton]; omega
    rw [hr] at hh
    simp only [List.cons_append,mk₂_left,mk₂_write] at hh
    rw [show xs++7::(List.replicate gap 0++out.reverse++[6])=
      (xs++[7])++(List.replicate gap 0++out.reverse++[6]) by simp] at hh
    have ht:=eraseToLeft_step (xs++[7]) (List.replicate gap 0++out.reverse++[6]) (7::input)
      (.move .left (.goto (fun _ _=>Label.seek))) b
    rw [hl] at ht
    rw [ht] at hh
    exact hh
lemma cycle (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) (hh : ∀ a∈h b,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .read,b,working (h b++out) (gap+w) input⟩
      (3+2*(out.length+gap)+(h b).length+w) := by
  have ha:=read_block w h header hw b v hb out input gap
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := (List.eq_of_mem_replicate ha); subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hs:=scan_left M .seek 6 (seek_path w h header)
    (List.replicate gap 0++out.reverse) [] (List.replicate w 0++7::input) b hx
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(List.replicate w 0++7::input)=
      out++List.replicate (gap+w) 0++7::input := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc]
  rw [he] at hs
  have ht:=seek_write w h header b (out++List.replicate (gap+w) 0++7::input)
  have hy : ∀ a∈h b++out++List.replicate (gap+w) (0:Symbol),a≠7 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_append.mp ha with ha|ha
      · exact (hh a ha).2
      · exact (ho a ha).2
    · have := List.eq_of_mem_replicate ha; subst a; decide
  have hu:=scan_right M .back 7 (back_path w h header)
    (h b++out++List.replicate (gap+w) 0) [6] input b hy
  have hv:=Exec.step M .back b
    (Tape.mk₂ ((h b++out++List.replicate (gap+w) 0).reverse++[6]) (7::input))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_right] at hv
  simp only [List.append_assoc] at ha hs ht hu hv
  have hh:=((ha.trans hs).trans ht).trans (hu.trans hv)
  simp only [working,List.append_assoc,List.reverse_append,List.reverse_replicate,List.length_append,
    List.length_replicate,List.length_reverse] at hh ⊢
  apply Exec.mono hh
  omega

lemma mk₂_blanks (L R : List Symbol) (n : ℕ) :
    Tape.mk₂ L (R++List.replicate n 0)=Tape.mk₂ L R := by
  simp only [Tape.mk₂,show (0:Symbol)=default from rfl,blank_append_zero]
lemma mk₂_replicate (L : List Symbol) (n : ℕ) :
    Tape.mk₂ L (List.replicate n 0)=Tape.mk₂ L [] := by
  simpa only [List.nil_append] using mk₂_blanks L [] n
lemma mk₂_zero_left (R : List Symbol) : Tape.mk₂ [0] R=Tape.mk₁ R := by
  change Tape.mk' (ListBlank.mk (List.replicate 1 (default:Symbol))) _=Tape.mk' (ListBlank.mk []) _
  rw [blank_zero]

lemma finish (v : Block w) (out : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap []⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++out)⟩ (3+w+gap+out.length) := by
  have hz : List.ofFn (fun _ : Fin w=>(0:Symbol))=List.replicate w 0 := by simp
  have ha:=Exec.step M .read v (working out gap [])
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at ha
  rw [working,←mk₂_blanks _ [] w] at ha
  simp only [List.nil_append,←hz] at ha
  rw [show List.ofFn (fun _ : Fin w=>(0:Symbol))=
    List.ofFn (fun _ : Fin w=>(0:Symbol))++[] by simp,grab_fin] at ha
  simp only [TM1.stepAux,decide_true,Bool.cond_true,hz,List.reverse_replicate] at ha
  have hs:=scan_left M .stopSep 7 (stopSep_path w h header) (List.replicate w 0)
    (List.replicate gap 0++out.reverse++[6]) [] (fun _=>0)
    (by intro a ha; have := List.eq_of_mem_replicate ha; subst a; decide)
  have ht:=Exec.step M .stopSep (fun _ : Fin w=>(0:Symbol))
    (Tape.mk₂ (List.replicate gap 0++out.reverse++[6]) (7::List.replicate w 0))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write] at ht
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := List.eq_of_mem_replicate ha; subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hu:=scan_left M .stopOut 6 (stopOut_path w h header)
    (List.replicate gap 0++out.reverse) [] (0::List.replicate w 0) (fun _=>0) hx
  have hv:=stopOut_write w h header (fun _=>0)
    (out++List.replicate (gap+1+w) 0)
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(0::List.replicate w 0)=
      out++List.replicate (gap+1+w) 0 := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc,List.replicate_one,List.singleton_append]
  rw [he] at hu
  simp only [List.length_replicate,List.reverse_replicate,List.append_nil] at hs
  have hb:=((ha.trans hs).trans ht).trans (hu.trans hv)
  rw [←List.append_assoc,mk₂_blanks,mk₂_zero_left] at hb
  simp only [List.append_assoc,List.length_append,List.length_reverse,List.length_replicate] at hb
  simp only [List.append_nil,mk₂_replicate] at hb
  simp only [working,List.append_assoc]
  apply Exec.mono hb
  omega

lemma blocks (hw : 0<w) (bs : List (Block w)) (v : Block w) (out : List Symbol) (gap H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h++out)⟩
      (budget w H bs.length (out.length+gap)) := by
  induction bs generalizing v out gap with
  | nil =>
    simpa only [List.flatMap_nil,List.reverse_nil,List.append_nil,List.nil_append]
      using (finish w h header v out gap ho).mono (by simp only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.one_mul]; omega)
  | cons b bs ih =>
    have ha:=cycle w h header hw b v (hb b (by simp)) out (bs.flatMap List.ofFn) gap ho (hh b (by simp))
    have hs:=ih b (h b++out) (gap+w)
      (fun a ha=>hb a (by simp [ha])) (fun a ha=>hh a (by simp [ha]))
      (fun a ha=>hH a (by simp [ha]))
      (by intro a ha; rcases List.mem_append.mp ha with ha|ha; exact hh b (by simp) a ha; exact ho a ha)
    have he:=ha.trans hs
    simp only [List.reverse_cons,List.flatMap_append,List.append_assoc,
      List.flatMap_cons] at he ⊢
    apply he.mono
    have hlen:=hH b (by simp)
    simp only [budget,List.length_cons,List.length_append]
    nlinarith

lemma computes (hw : 0<w) (bs : List (Block w)) (H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H) :
    Exec M ⟨some .start,(fun _=>0),Tape.mk₁ (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h)⟩
      (1+budget w H bs.length 0) := by
  have ha:=start_step w h header (bs.flatMap List.ofFn) (fun _=>0)
  have hs:=blocks w h header hw bs (fun _=>0) [] 0 H hb hh hH (by simp)
  simpa only [List.append_nil,List.length_nil,Nat.zero_add] using ha.trans hs

end MatchingFPRAS.LiteralBlockMap

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

lemma rows_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.rows (inputStacks a) (weight a)=baseRow::bs.map bitRow := by
  have hw : weight a=bs.length+1 := by
    have h:=congrArg List.length hs
    simpa only [List.length_reverse,List.length_cons,weight,TreeFunction.size] using h
  apply List.ext_getElem
  · simp only [StackWords.rows,List.length_ofFn,List.length_cons,List.length_map,hw]
  · intro i hi hj
    simp only [StackWords.rows,List.getElem_ofFn]
    funext k
    cases k with
    | inr k =>
      cases i <;> simp [inputStacks,encodeEnv,baseRow,bitRow]
    | inl r =>
      by_cases hr:r=0
      · subst r
        simp only [inputStacks,encodeEnv,env,ite_true, if_true,hs]
        cases i <;> simp [baseRow,bitRow]
      · have hn : env (TreeTyped.encode a) .nil .nil r=.nil := by simp [env,hr]
        simp only [inputStacks,encodeEnv,hn,TreeData.encode,List.reverse_singleton]
        cases i <;> simp [baseRow,bitRow,hr]
lemma word_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.word (inputStacks a) (weight a)=bottom::bs.map letter := by
  rw [StackWords.word,rows_eq a bs hs]
  simp only [List.headI_cons,List.tail_cons]
  change (true,baseRow)::(bs.map bitRow).map (fun a=>(false,a)) = (true,baseRow)::bs.map LiteralPacked.letter
  rw [List.map_map]
  rfl

lemma list_bits (as : List Symbol) :
    (TreeData.encode (TreeTyped.encode as)).reverse=false::as.reverse.flatMap symbolBits := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [TreeTyped.encode_list_cons,TreeData.encode,List.reverse_cons,List.reverse_append,ih,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,symbolBits,
      List.cons_append,List.append_assoc]

lemma packed_eq (as : List Symbol) : TreePost.packed as=header++as.reverse.flatMap chunk := by
  unfold TreePost.packed StackWords.encoded FixedAlphabetCompiler.word FixedAlphabetCompiler.bitsWord
  rw [word_eq as _ (list_bits as)]
  simp only [List.flatMap_cons,List.map_append,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,LiteralPacked.header,LiteralPacked.block]
  rfl
lemma block_alphabet (a : Alphabet) (s : Symbol) (hs : s∈block a) : s=0 ∨ s=1 := by
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs
  cases b <;> simp [BoolPostCompiler.up]
lemma chunk_alphabet (a s : Symbol) (hs : s∈chunk a) : s≠6 ∧ s≠7 := by
  obtain ⟨b,_,hb⟩:=List.mem_flatMap.mp hs
  rcases block_alphabet _ _ hb with rfl|rfl <;> decide
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TreeEncodingInjective
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
lemma encode_prefix_injective (a : Data) : ∀ b xs ys,
    encode a++xs=encode b++ys → a=b ∧ xs=ys := by
  induction a with
  | nil=>
    intro b xs ys h
    cases b with
    | nil=>simpa [encode] using h
    | cons b c=>simp [encode] at h
  | cons a c ia ic=>
    intro b xs ys h
    cases b with
    | nil=>simp [encode] at h
    | cons b d=>
      simp only [encode,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      obtain ⟨hab,he⟩:=ia b _ _ h
      obtain ⟨hcd,hxy⟩:=ic d xs ys he
      exact ⟨congrArg₂ Data.cons hab hcd,hxy⟩
lemma encode_injective : Function.Injective encode := by
  intro a b h
  exact (encode_prefix_injective a b [] [] (by simpa using h)).1
lemma ofList_injective : Function.Injective ofList := by
  intro a
  induction a with
  | nil=>intro b h; cases b <;> simp_all [ofList]
  | cons a as ih=>
    intro b h
    cases b with
    | nil=>simp [ofList] at h
    | cons b bs=>
      obtain ⟨rfl,he⟩:=Data.cons.inj h
      rw [ih he]
lemma bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeTyped
open TreeData

lemma list_encode_injective {A : Type} [Codec A] (hf : Function.Injective (encode (A:=A))) :
    Function.Injective (encode (A:=List A)) := by
  intro a b h
  exact (List.map_injective_iff.mpr hf) (ofList_injective h)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedInverse
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreePost

lemma symbol_encode_injective : Function.Injective (TreeTyped.encode (A:=Symbol)) := by
  intro a b h
  have hh : TreeTyped.encode (LiteralCodec.parts a)=TreeTyped.encode (LiteralCodec.parts b) := h
  have he := (TreeData.Data.cons.inj hh).1
  have hs : (LiteralCodec.parts a).1=(LiteralCodec.parts b).1 :=
    list_encode_injective (show Function.Injective (TreeTyped.encode (A:=Bool)) from bit_injective) he
  apply Fin.ext
  simpa only [LiteralCodec.parts,List.length_replicate] using congrArg List.length hs
lemma symbolBits_injective : Function.Injective symbolBits := by
  intro a b h
  have h1:=List.append_cancel_right (show _++[true]=_++[true] from h)
  exact symbol_encode_injective (TreeData.encode_injective (List.reverse_injective h1))
lemma encoding_injective (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    Function.Injective (fun a : Γ=>(FixedEncoding.enc Γ a).toList.map BoolPostCompiler.up) := by
  intro a b h
  have hb : (FixedEncoding.enc Γ a).toList=(FixedEncoding.enc Γ b).toList :=
    List.map_injective_iff.mpr (Function.LeftInverse.injective BoolPostCompiler.down_up) h
  exact FixedEncoding.injective Γ (Subtype.ext hb)
lemma block_injective : Function.Injective block := encoding_injective Alphabet
lemma flatMap_injective_fixed {A B : Type} (f : A→List B) (w : ℕ) (hw : 0<w)
    (hl : ∀ a,(f a).length=w) (hi : Function.Injective f) : Function.Injective (List.flatMap f) := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons b bs => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
    | cons b bs =>
      have h1 := List.append_inj_left h ((hl a).trans (hl b).symm)
      have h2 := List.append_inj_right h ((hl a).trans (hl b).symm)
      exact congrArg₂ List.cons (hi h1) (ih h2)
lemma width_pos : 0<width := Fintype.card_pos
lemma letter_injective : Function.Injective letter := by
  intro a b h
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h
  simpa only [letter,bitRow,ite_true, if_true,Option.some.injEq] using hh
lemma chunk_injective : Function.Injective chunk := by
  intro a b h
  have hi : Function.Injective (fun b=>block (letter b)) := by
    intro b c he
    exact letter_injective (block_injective he)
  have hh : (symbolBits a).flatMap (fun b=>block (letter b)) =
      (symbolBits b).flatMap (fun b=>block (letter b)) := h
  exact symbolBits_injective (flatMap_injective_fixed (fun b=>block (letter b)) width width_pos
    (fun b=>block_length (letter b)) hi hh)
lemma encoding_blank (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    (FixedEncoding.enc Γ default).toList.map BoolPostCompiler.up=
      List.replicate (Fintype.card Γ) (0:Symbol) := by
  rw [FixedEncoding.blank]
  change (List.replicate (Fintype.card Γ) false).map _ = _
  rw [List.map_replicate]
  rfl
lemma block_blank : block default=List.replicate width 0 := encoding_blank Alphabet
lemma block_ne_zero (a : Alphabet) (ha : a≠default) : block a≠List.replicate width 0 := by
  intro he
  exact ha (block_injective (he.trans block_blank.symm))
lemma chunk_nonzero (a : Symbol) : ∃ s∈chunk a,s≠0 := by
  classical
  by_contra h
  push Not at h
  have h1 : ∀ s∈block (letter true),s=(0:Symbol) := by
    intro s hs
    exact h s (List.mem_flatMap.mpr ⟨true,by simp [symbolBits],hs⟩)
  have he : block (letter true)=List.replicate width 0 := by
    rw [←block_length (letter true)]
    exact List.eq_replicate_of_mem h1
  apply block_ne_zero (letter true) _ he
  intro h2
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h2
  change (some true : Option Bool)=none at hh
  exact Option.some_ne_none true hh
lemma chunkFn_word (a : Symbol) : List.ofFn (chunkFn a)=chunk a := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,chunk_length]
  · intro i hi hj; simp only [List.getElem_ofFn,chunkFn]
lemma unchunk_chunkFn (a : Symbol) : unchunk (chunkFn a)=[a] := by
  rw [unchunk,chunkFn_word,Function.leftInverse_invFun chunk_injective]
lemma chunkFn_nonzero (a : Symbol) : chunkFn a≠fun _=>0 := by
  intro he
  have hh:=congrArg List.ofFn he
  rw [chunkFn_word,List.ofFn_const] at hh
  obtain ⟨s,hs,hn⟩:=chunk_nonzero a
  rw [hh] at hs
  exact hn (List.eq_of_mem_replicate hs)
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open Turing LiteralTape LiteralBlockMap

lemma singletonBlock_word (a : Symbol) : List.ofFn (singletonBlock a)=[a] := by simp [singletonBlock,List.ofFn_succ]
lemma pack_exec (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    Exec packCode ⟨some .start,(fun _=>0),Tape.mk₁ as⟩
      ⟨none,(fun _=>0),Tape.mk₁ (TreePost.packed as)⟩
      (1+LiteralBlockMap.budget 1 (18*width) as.length 0) := by
  have h:=LiteralBlockMap.computes 1 (fun b=>chunk (b 0)) header (by decide)
    (as.map singletonBlock) (18*width) ?_ ?_ ?_
  · simpa only [packCode,List.flatMap_map,singletonBlock_word,List.flatMap_singleton,List.flatMap_singleton',List.length_map,
      ←List.map_reverse,singletonBlock,←packed_eq] using h
  · intro b hb
    obtain ⟨a,ha',rfl⟩:=List.mem_map.mp hb
    intro he
    exact ha a ha' (congrFun he 0)
  · intro b _ a had
    exact chunk_alphabet _ _ had
  · intro b _
    exact (chunk_length _).le
lemma unpack_exec (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    Exec unpackCode ⟨some .start,(fun _=>0),Tape.mk₁ (as.reverse.flatMap chunk)⟩
      ⟨none,(fun _=>0),Tape.mk₁ as⟩
      (1+LiteralBlockMap.budget (18*width) 1 as.length 0) := by
  have h:=LiteralBlockMap.computes (18*width) unchunk [] (Nat.mul_pos (by decide) width_pos)
    (as.reverse.map chunkFn) 1 ?_ ?_ ?_
  · simpa only [unpackCode,List.flatMap_map,chunkFn_word,←List.map_reverse,List.reverse_reverse,
      unchunk_chunkFn,List.flatMap_singleton,List.flatMap_singleton',List.nil_append,List.length_map,List.length_reverse] using h
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    exact chunkFn_nonzero a
  · intro b hb a had
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn,List.mem_singleton] at had
    subst a
    exact ha c (List.mem_reverse.mp hc)
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn];rfl
end MatchingFPRAS.LiteralPacked

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
lemma eraseRight_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseRight xs.length q) v (Tape.mk₂ L (xs++R))=
      TM1.stepAux q v (Tape.mk₂ (List.replicate xs.length default++L) R) := by
  induction xs generalizing L with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseRight,TM1.stepAux,List.cons_append,mk₂_write,mk₂_right]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.write (fun _ _=>default) (.move .right tail)) xs.length=eraseRight xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
lemma erase_exec (xs R : List Symbol) :
    Exec (eraseCode xs.length) ⟨some (),(),Tape.mk₁ (xs++R)⟩ ⟨none,(),Tape.mk₁ R⟩ 1 := by
  have h:=Exec.step (eraseCode xs.length) () () (Tape.mk₁ (xs++R))
  change Exec _ _ (TM1.stepAux (eraseRight xs.length .halt) () (Tape.mk₂ [] (xs++R))) 1 at h
  rw [eraseRight_step] at h
  have he : Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R=Tape.mk₁ R := by
    simp only [List.append_nil,Tape.mk₂,Tape.mk₁]
    rw [show (ListBlank.mk (List.replicate xs.length (0:Symbol)))=ListBlank.mk [] from blank_zero xs.length]
  change Exec _ _ (TM1.stepAux (.halt : TM1.Stmt Symbol Unit Unit) () (Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R)) 1 at h
  simpa only [TM1.stepAux,he] using h
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LiteralProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

lemma postTime_mono {n m : ℕ} (h : n ≤ m) : postTime n ≤ postTime m := by
  unfold postTime LiteralBlockMap.budget
  gcongr

lemma pack_realizes (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    pack.Realizes (Tape.mk₁ as) (.done (Tape.mk₁ (TreePost.packed as))) (packTime as.length) :=
  Program.realizes_TM1 _ _ _ _ _ _ _ (pack_exec as ha)

lemma post_realizes (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    post.Realizes (Tape.mk₁ (TreePost.packed as)) (.done (Tape.mk₁ as)) (postTime as.length) := by
  have h1 : erase.Realizes (Tape.mk₁ (TreePost.packed as))
      (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
      (MachineCost.programCost (LiteralTape.eraseCode header.length)) := by
    rw [packed_eq]
    exact (Program.realizes_TM1 _ _ _ _ _ _ _
      (LiteralTape.erase_exec header (as.reverse.flatMap chunk))).mono (by simp only [Nat.one_mul]; rfl)
  have h2 : unpack.Realizes (Tape.mk₁ (as.reverse.flatMap chunk)) (.done (Tape.mk₁ as))
      ((1+LiteralBlockMap.budget (18*width) 1 as.length 0)*MachineCost.programCost unpackCode) :=
    Program.realizes_TM1 _ _ _ _ _ _ _ (unpack_exec as ha)
  exact Program.seq_realizes erase unpack _ (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
    (fun _ => .done (Tape.mk₁ as)) _ _ h1 h2

end ContingencyTables.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Parse
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

lemma bits_fold (n : ℕ) (ns : List ℕ) :
    (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=n::ns := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn,List.map_cons,List.foldr_cons,ih]
    cases b <;> simp [fromBit,numStep,Nat.bit]
lemma encodeNat_fold (n : ℕ) (ns : List ℕ) :
    (encodeNat n).foldr (fun a ns=>numStep (a,ns)) ns=n::ns := by
  change (n.bits.map fromBit++[3]).foldr _ ns=_
  rw [List.foldr_append]
  change (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=_
  exact bits_fold n ns
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public margins and printing the greedy matrix

All operations are existing binary list programs. The bounded take and
drop operations also terminate polynomially on malformed headers.
-/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS TreeTyped LiteralCodec LiteralParse
open scoped BigOperators

lemma polynomial_printMatrix : PolynomialTime printMatrixRealizer :=
  polynomial_flatMapPoly (polynomial_flatMapPoly polynomial_natWord)

lemma natWords_fold (ns tail : List ℕ) :
    (ns.flatMap encodeNat).foldr (fun a ns => numStep (a,ns)) tail=ns++tail := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold,List.cons_append]

lemma parse_natWords (ns : List ℕ) : parse (ns.flatMap encodeNat)=ns := by
  simpa only [parse,List.append_nil] using natWords_fold ns []

lemma encodeMargins_natWords {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Algorithms.encodeMargins r c=
      (m::n::(List.ofFn r++List.ofFn c)).flatMap encodeNat := by
  simp only [Algorithms.encodeMargins,List.flatMap_cons,List.flatMap_append]
  simp only [List.ofFn_comp',List.flatMap_def,List.append_assoc]

lemma printMatrix_ofFn {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    printMatrix (List.ofFn (fun i => List.ofFn (X i)))=Algorithms.encodeMatrix X := by
  simp only [printMatrix,Algorithms.encodeMatrix,List.flatMap_def,List.ofFn_comp',List.map_map,
    Function.comp_def]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixEncoding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The public matrix encoding uniquely identifies a fixed-shape table -/

namespace ContingencyTables.Algorithms
open MatchingFPRAS MatchingFPRAS.LiteralParse Turing

lemma encodeMatrix_flat {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    encodeMatrix X=((List.ofFn fun i => List.ofFn (X i)).flatten).flatMap encodeNat := by
  rw [←GreedyFeasibleTable.printMatrix_ofFn]
  simp only [GreedyFeasibleTable.printMatrix,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq]

lemma matrix_flat_injective (m n : ℕ) (X Y : Fin m → Fin n → ℕ)
    (h : (List.ofFn (fun i => List.ofFn (X i))).flatten=
      (List.ofFn (fun i => List.ofFn (Y i))).flatten) : X=Y := by
  have hr : List.ofFn (fun i => List.ofFn (X i))=List.ofFn (fun i => List.ofFn (Y i)) :=
    List.eq_iff_flatten_eq.mpr ⟨h,by
      simp only [List.map_ofFn]
      congr 1
      funext i
      exact (List.length_ofFn).trans (List.length_ofFn.symm)⟩
  have hf := List.ofFn_injective hr
  funext i
  exact List.ofFn_injective (congrFun hf i)

lemma blankMatrix_injective {m n : ℕ} (X Y : Fin m → Fin n → ℕ)
    (h : ListBlank.mk (encodeMatrix X)=ListBlank.mk (encodeMatrix Y)) : X=Y := by
  have hp := congrArg blankNumbers h
  change parse (encodeMatrix X)=parse (encodeMatrix Y) at hp
  rw [encodeMatrix_flat,encodeMatrix_flat,GreedyFeasibleTable.parse_natWords,
    GreedyFeasibleTable.parse_natWords] at hp
  exact matrix_flat_injective m n X Y hp

end ContingencyTables.Algorithms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicMachine
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The greedy initializer on the public binary tape -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS Turing
open scoped BigOperators

private lemma encodeNat_nonzero (n : ℕ) (a : Symbol) (ha : a∈encodeNat n) : a≠0 := by
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

lemma encodeMargins_nonzero {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    ∀ a∈Algorithms.encodeMargins r c,a≠0 := by
  rw [encodeMargins_natWords]
  intro a ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  exact encodeNat_nonzero n a ha

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfilePublicMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical execution of the computed public profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.LiteralCodec Turing

lemma printMatrix_alphabet (rows : DensePrograms.MatrixCode) :
    ∀ a∈GreedyFeasibleTable.printMatrix rows,a≠6 ∧ a≠7 := by
  intro a ha
  obtain ⟨row,_,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PackedMatrixInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packed physical output still identifies its contingency table -/

namespace ContingencyTables.PackedMatrixInjective
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing

lemma deterministic_unique (P : Program) (input X Y : Tape Symbol) (n m : ℕ)
    (hX : P.Realizes input (.done X) n) (hY : P.Realizes input (.done Y) m) : X=Y := by
  obtain ⟨p,hp,hpm,_⟩ := hX
  obtain ⟨q,hq,hqm,_⟩ := hY
  have ha : p.All (fun T => T=X) := Experiment.all_of_mean_eq hpm _ rfl
  have hb : q.All (fun T => T=Y) := Experiment.all_of_mean_eq hqm _ rfl
  have he := hp.padded_execution (fun _ => rfl) (p.cost+q.cost) (Nat.le_add_right _ _) (fun _ => false)
  have hf := hq.padded_execution (fun _ => rfl) (p.cost+q.cost) (Nat.le_add_left _ _) (fun _ => false)
  rw [Experiment.all_run p _ ha] at he
  rw [Experiment.all_run q _ hb] at hf
  exact congrArg Cfg.tape (he.symm.trans hf)

lemma table_injective {m n : ℕ} {r : Fin m → ℕ} {c : Fin n → ℕ} (X Y : Table r c)
    (h : Tape.mk₁ (TreePost.packed (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode X.val)))=
      Tape.mk₁ (TreePost.packed (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode Y.val)))) : X=Y := by
  have hx := LiteralProgram.post_realizes (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode X.val))
    (ProfilePrograms.printMatrix_alphabet _)
  have hy := LiteralProgram.post_realizes (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode Y.val))
    (ProfilePrograms.printMatrix_alphabet _)
  rw [←h] at hy
  have ht := deterministic_unique LiteralProgram.post _ _ _ _ _ hx hy
  have he := congrArg Tape.right₀ ht
  simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀,DensePrograms.matrixCode,GreedyFeasibleTable.printMatrix_ofFn] at he
  exact Subtype.ext (Algorithms.blankMatrix_injective X.val Y.val he)

end ContingencyTables.PackedMatrixInjective

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_QuadraticPrefixRuntime
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expected time from geometrically accurate quadratic-cost prefixes -/

namespace ContingencyTables.QuadraticPrefixRuntime
open scoped BigOperators

lemma weighted_geometric : HasSum (fun k : ℕ => (2*(k:ℝ)+3)*(1/2:ℝ)^k) 10 := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)
  convert (h1.mul_left 2).add (h0.mul_left 3) using 1
  all_goals first | rfl | (funext k; ring) | norm_num

/-- Quadratic simulation overhead preserves a finite expected running time.
The small prefactor `δ` is retained through the entire estimate. -/
theorem quadratic_bound (f : ℕ → ℝ) (T : ℕ) (hT : 0<T) (δ : ℝ) (hδ : 0≤δ)
    (h0 : ∀ t,0≤f t) (hm : Antitone f) (hstart : f 0≤δ)
    (hstep : ∀ N,f (T*(N+1)^2)≤δ*(1/2:ℝ)^N) :
    Summable f ∧ (∑' t,f t)≤11*δ*T := by
  let u : ℕ → ℕ := fun N => T*(N+1)^2
  have hu : Monotone u := by
    intro a b hab
    dsimp only [u]
    exact Nat.mul_le_mul_left T (Nat.pow_le_pow_left (by omega) 2)
  have hup (N : ℕ) : 0<u N := Nat.mul_pos hT (pow_pos (by omega) _)
  have hbound (R : ℕ) : ∑ t ∈ Finset.range R,f t≤11*δ*T := by
    have hR : R≤u R := by
      have ha : R≤(R+1)^2 := by nlinarith
      have hb := Nat.mul_le_mul_right ((R+1)^2) (show 1≤T from hT)
      exact ha.trans (by simpa only [Nat.one_mul] using hb)
    have hs := Finset.le_sum_schlomilch (f := f) (u := u)
      (by intro a b _ hab; exact hm hab) hup hu R
    have hp : ∑ t ∈ Finset.range (u 0),f t≤T*δ := by
      calc
        _ ≤ ∑ _t ∈ Finset.range (u 0),δ := Finset.sum_le_sum (fun t _ => (hm (Nat.zero_le t)).trans hstart)
        _ = T*δ := by simp [u]
    have hb (k : ℕ) : (u (k+1)-u k) • f (u k)≤
        (T:ℝ)*δ*((2*(k:ℝ)+3)*(1/2:ℝ)^k) := by
      have he : u (k+1)=u k+T*(2*k+3) := by dsimp only [u]; ring
      rw [he,Nat.add_sub_cancel_left,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,
        Nat.cast_mul,Nat.cast_ofNat]
      have hh := mul_le_mul_of_nonneg_left (hstep k) (by positivity : (0:ℝ)≤T*(2*k+3))
      exact hh.trans_eq (by ring)
    have hr : ∑ k ∈ Finset.range R,(u (k+1)-u k) • f (u k)≤10*T*δ := by
      calc
        _ ≤ ∑ k ∈ Finset.range R,(T:ℝ)*δ*((2*(k:ℝ)+3)*(1/2:ℝ)^k) :=
          Finset.sum_le_sum (fun k _ => hb k)
        _ = (T:ℝ)*δ*(∑ k ∈ Finset.range R,(2*(k:ℝ)+3)*(1/2:ℝ)^k) := by rw [Finset.mul_sum]
        _ ≤ (T:ℝ)*δ*10 := mul_le_mul_of_nonneg_left
          ((weighted_geometric.summable.sum_le_tsum (Finset.range R)
            (fun k _ => by positivity)).trans_eq weighted_geometric.tsum_eq) (by positivity)
        _ = 10*T*δ := by ring
    have hi : ∑ t ∈ Finset.range R,f t≤∑ t ∈ Finset.range (u R),f t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hR) (fun t _ _ => h0 t)
    exact (hi.trans hs).trans ((add_le_add hp hr).trans_eq (by ring))
  exact ⟨summable_of_sum_range_le h0 hbound,Real.tsum_le_of_sum_range_le h0 hbound⟩

/-- A bounded cheap prefix followed by a rare quadratic-cost correction. -/
theorem expected_time (tail : ℕ → ℝ) (S T : ℕ) (hT : 0<T) (δ : ℝ) (hδ : 0≤δ)
    (h0 : ∀ t,0≤tail t) (h1 : ∀ t,tail t≤1) (hm : Antitone tail)
    (hgate : tail S≤δ)
    (hstep : ∀ N,tail (S+T*(N+1)^2)≤δ*(1/2:ℝ)^N) :
    Summable tail ∧ (∑' t,tail t)≤S+11*δ*T := by
  obtain ⟨hs,hb⟩ := quadratic_bound (fun t => tail (t+S)) T hT δ hδ
    (fun t => h0 _) (fun _ _ h => hm (Nat.add_le_add_right h S))
    (by simpa only [Nat.zero_add] using hgate)
    (by intro N; simpa only [Nat.add_comm] using hstep N)
  have ht : Summable tail := (summable_nat_add_iff S).mp hs
  refine ⟨ht,?_⟩
  rw [←ht.sum_add_tsum_nat_add S]
  have hp : ∑ t ∈ Finset.range S,tail t≤(S:ℝ) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range S,(1:ℝ) := Finset.sum_le_sum (fun t _ => h1 t)
      _ = (S:ℝ) := by simp
  exact add_le_add hp hb

end ContingencyTables.QuadraticPrefixRuntime

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRetryTail
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical halting tails from finite rejection prefixes -/

namespace ContingencyTables.PhysicalRetryTail
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open scoped BigOperators Classical

variable {Γ Q B : Type} [Inhabited Γ]

private lemma mean_mono {A : Type} (p : Experiment A) (f g : A → ℚ) (h : ∀ a,f a≤g a) :
    p.mean f≤p.mean g := by
  induction p with
  | done a => exact h a
  | read p ih => simp only [Experiment.mean]; linarith [ih false,ih true]
  | delay n p ih => exact ih

private lemma mean_const {A : Type} (p : Experiment A) (c : ℚ) : p.mean (fun _ => c)=c := by
  induction p with
  | done => rfl
  | read p ih => simp only [Experiment.mean,ih]; ring
  | delay n p ih => exact ih

lemma live_nonnegative (c : Cfg Γ Q) : 0≤live c := by unfold live; split_ifs <;> norm_num
lemma live_le_one (c : Cfg Γ Q) : live c≤1 := by unfold live; split_ifs <;> norm_num

lemma experiment_mean_add (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (n m : ℕ) (c : Cfg Γ Q) (g : Cfg Γ Q → ℚ) :
    (experiment M (n+m) c).mean g=
      (experiment M n c).mean (fun d => (experiment M m d).mean g) := by
  induction n generalizing c with
  | zero => simp only [Nat.zero_add,experiment,Experiment.mean]
  | succ n ih => simp only [Nat.succ_add,experiment,Experiment.mean,ih]

lemma halted_mean (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (h : c.state=none)
    (g : Cfg Γ Q → ℚ) : (experiment M n c).mean g=g c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht (b : Bool) : PhysicalPost.tick M c b=c := by simp [PhysicalPost.tick,h]
    simp only [experiment,Experiment.mean,ht,ih]
    ring

lemma future_live_le (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (n : ℕ) (c : Cfg Γ Q) :
    (experiment M n c).mean live≤live c := by
  by_cases h : c.state=none
  · rw [halted_mean M n c h]
  · have hm:=mean_mono (experiment M n c) live (fun _ => 1) live_le_one
    rw [mean_const] at hm
    simpa only [live,ite_eq_right h] using hm

lemma tail_nonnegative (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (c : Cfg Γ Q) (n : ℕ) : 0≤tail M c n := by
  have hm:=mean_mono (experiment M n c) (fun _ => 0) live live_nonnegative
  rw [mean_const] at hm
  unfold tail
  exact_mod_cast hm

lemma tail_antitone (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (c : Cfg Γ Q) : Antitone (tail M c) := by
  intro n m hnm
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hnm
  have hm : (experiment M (n+k) c).mean live≤(experiment M n c).mean live := by
    rw [experiment_mean_add]
    exact mean_mono _ _ _ (future_live_le M k)
  unfold tail
  exact_mod_cast hm

lemma padded_halted_result (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (out : B → Cfg Γ Q) (c : Cfg Γ Q)
    (p : Experiment B) (hp : Implements M out c p) (n : ℕ) (hn : p.cost≤n)
    (b : Stream) (hhalt : (out (p.run b).1).state=none) :
    execute M n c b=out (p.run b).1 := by
  have hb : (p.run b).2≤n := (Experiment.run_cost p b).trans hn
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hb
  rw [hk,execute_add,hp.execution b]
  have he : out (p.run b).1=⟨none,(out (p.run b).1).tape⟩ := by
    cases e:out (p.run b).1 with
    | mk state tape =>
      rw [e] at hhalt
      change state=none at hhalt
      subst state
      rfl
  rw [he,execute_halted]

/-- All successful prefix executions have halted by the prefix cost.
This implication is enough even though the failed endpoint is still live. -/
theorem tail_le_failure (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (out : Option B → Cfg Γ Q) (c : Cfg Γ Q)
    (p : Experiment (Option B)) (hp : Implements M out c p)
    (hhalt : ∀ b,(out (some b)).state=none) (n : ℕ) (hn : p.cost≤n) :
    tail M c n≤(p.mean (fun b => if b=none then 1 else 0):ℚ) := by
  have hb : (experiment M n c).mean live≤p.mean (fun b => if b=none then 1 else 0) := by
    rw [←physical_law,←Experiment.average_run p _ n hn]
    unfold average
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro b _
    cases he:(p.run (extend b)).1 with
    | none => simp only [ite_true, if_true]; exact live_le_one _
    | some x =>
      have hh : (out (p.run (extend b)).1).state=none := by rw [he]; exact hhalt x
      rw [padded_halted_result M out c p hp n hn (extend b) hh]
      simp [he,live,hhalt]
  unfold tail
  exact_mod_cast hb

end ContingencyTables.PhysicalRetryTail

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRuntimeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform public polynomial bound for the physical sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec Polynomial
open scoped BigOperators

lemma polynomial_scaled_power (p : Polynomial ℕ) (A x b : ℕ) (hx : 1≤x) :
    p.eval (A*x^b)≤p.eval A*x^(b*p.natDegree) := by
  rw [p.eval_eq_sum_range,p.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i≤p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [mul_pow,←pow_mul]
  calc
    p.coeff i*(A^i*x^(b*i))=(p.coeff i*A^i)*x^(b*i) := by ring
    _ ≤ (p.coeff i*A^i)*x^(b*p.natDegree) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (Nat.mul_le_mul_left b hi'))
    _ = _ := by ring

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPartialSequence
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequencing finite prefixes that can stop at a live configuration

A called prefix may have reached the continuation, or may still be inside
its first program. The construction stops exactly at that interface.
-/

namespace ContingencyTables.PhysicalPartialSequence
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing

variable {Γ Q R A : Type} [Inhabited Γ]

lemma mean_const (p : Experiment A) (v : ℚ) : p.mean (fun _ => v)=v := by
  induction p with
  | done => rfl
  | delay n p ih => exact ih
  | read p ih => simp only [Experiment.mean,ih]; ring

lemma halted_all {M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q} {out : A → Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (hc : c.state=none) :
    p.All (fun a => out a=c) := by
  induction h with
  | done a => rfl
  | read c p h ih =>
    have he (b : Bool) : PhysicalPost.tick M c b=c := by simp [PhysicalPost.tick,hc]
    exact ⟨by simpa only [he] using ih false (by rw [he]; exact hc),
      by simpa only [he] using ih true (by rw [he]; exact hc)⟩
  | delay c d n p hs hr ih =>
    have he : d=c := by
      rw [←hs (fun _ => false)]
      rcases c with ⟨q,T⟩
      cases hc
      exact execute_halted M n T (fun _ => false)
    subst d
    exact ih hc

lemma early_all_eq (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (c d : Cfg Γ Q) (n : ℕ)
    (h : ∀ b : Stream,execute M n c b=d) :
    (early M n c).All (fun x => x=d) := by
  classical
  rw [Experiment.all_indicator,PhysicalPost.early_mean]
  simp only [h,ite_true, if_true,average_const]

/-- Relabelling a physical prefix for sequential composition may shorten
its post-halt padding, and preserves the law of its endpoint configuration. -/
theorem left_prefix (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (N : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ R) (r₀ : R)
    (out : A → Cfg Γ Q) (c : Cfg Γ Q) (p : Experiment A)
    (h : Implements M out c p) :
    ∃ q : Experiment (Cfg Γ Q),
      Implements (seq M N r₀) (leftCfg r₀) (leftCfg r₀ c) q ∧
      (∀ f,q.mean f=p.mean (fun a => f (out a))) ∧ q.cost≤p.cost := by
  induction h with
  | done a => exact ⟨.done (out a),.done (out a),fun _ => rfl,le_rfl⟩
  | read c p h ih =>
    by_cases hc : c.state=none
    · have hall := halted_all (Implements.read c p h) hc
      refine ⟨.done c,.done c,?_,Nat.zero_le _⟩
      intro f
      have hm := Experiment.mean_congr_all (.read p) (fun a => f (out a)) (fun _ => f c)
        (hall.mono (by intro a ha; rw [ha]))
      exact (hm.trans (mean_const _ _)).symm
    · obtain ⟨q,hq,hqm,hqc⟩ := ih false
      obtain ⟨r,hr,hrm,hrc⟩ := ih true
      let v : Bool → Experiment (Cfg Γ Q) := fun b => if b then r else q
      refine ⟨.read v,?_,?_,?_⟩
      · apply Implements.read
        intro b
        rcases c with ⟨state,T⟩
        cases state with
        | none => exact False.elim (hc rfl)
        | some s =>
          rw [tick_left]
          cases b
          · exact hq
          · exact hr
      · intro f
        simp only [Experiment.mean,v,Bool.false_eq_true,ite_false,ite_true, if_true,hqm,hrm]
      · simp only [Experiment.cost,v,Bool.false_eq_true,ite_false,ite_true, if_true]
        omega
  | delay c d n p hs hr ih =>
    obtain ⟨q,hq,hqm,hqc⟩ := ih
    let u := early M n c
    have hu := early_left M N r₀ n c
    have hall : u.All (fun x => x=d) := early_all_eq M c d n hs
    refine ⟨u.bind (fun _ => q),?_,?_,?_⟩
    · apply hu.bind_all (fun _ => q) (leftCfg r₀)
      exact hall.mono (by intro x hx; rw [hx]; exact hq)
    · intro f
      rw [Experiment.mean_bind,mean_const,hqm]
      rfl
    · exact (Experiment.cost_bind_le u (fun _ => q) q.cost (fun _ => le_rfl)).trans
        (Nat.add_le_add (early_cost M n c) hqc)

/-- When endpoint configurations identify their labels, sequential composition
also preserves the complete label law, not just the endpoint law. -/
theorem left_prefix_injective [Nonempty A] (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (N : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ R) (r₀ : R)
    (out : A → Cfg Γ Q) (hinj : Function.Injective out) (c : Cfg Γ Q) (p : Experiment A)
    (h : Implements M out c p) :
    ∃ q : Experiment A,
      Implements (seq M N r₀) (fun a => leftCfg r₀ (out a)) (leftCfg r₀ c) q ∧
      (∀ f,q.mean f=p.mean f) ∧ q.cost≤p.cost := by
  classical
  obtain ⟨q,hq,hqm,hqc⟩ := left_prefix M N r₀ out c p h
  let dec : Cfg Γ Q → A := Function.invFun out
  have hd (a : A) : dec (out a)=a := Function.leftInverse_invFun hinj a
  have hall : q.All (fun x => out (dec x)=x) := by
    apply Experiment.all_of_mean_eq (p := p.map out) (q := q)
    · intro f
      rw [Experiment.mean_map]
      exact hqm f
    · rw [Experiment.all_map]
      exact (Experiment.all_true p).mono (by intro a _; rw [hd])
  refine ⟨q.map dec,hq.map_all dec (fun a => leftCfg r₀ (out a))
    (hall.mono (by intro x hx; rw [hx])),?_,?_⟩
  · intro f
    rw [Experiment.mean_map,hqm]
    simp only [hd]
  · simpa only [Experiment.cost_map] using hqc

end ContingencyTables.PhysicalPartialSequence

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPhysicalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical execution of the parsed and printed exact sampler -/

namespace ContingencyTables.ExactPhysicalProgram
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms

attribute [local irreducible] ExactTypedProgram.program

lemma output_some (as : List Symbol) (X : MatrixCode) :
    output as (some X)=program.final (Tape.mk₁ (packed (GreedyFeasibleTable.printMatrix X))) := by
  change upCfg (OnlineStack.cfg
    (⟨none,none,inputStacks (GreedyFeasibleTable.printMatrix X)⟩ :
      OnlineTree.StoreCfg ExactTypedProgram.program))=_
  exact OnlineTree.cfg_packed ExactTypedProgram.program (GreedyFeasibleTable.printMatrix X) none

lemma output_none_live (as : List Symbol) : (output as none).state≠none := by
  change (some _ : Option program.State)≠none
  exact Option.some_ne_none _

end ContingencyTables.ExactPhysicalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGatePhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cheap exact-sampling prefix on the same physical program -/

namespace ContingencyTables.ExactGatePhysical
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms ProfilePrograms

attribute [local irreducible] ExactTypedProgram.program

lemma output_some (as : List Symbol) (X : MatrixCode) :
    output as (some X)=ExactPhysicalProgram.program.final
      (Tape.mk₁ (packed (GreedyFeasibleTable.printMatrix X))) := by
  change upCfg (OnlineStack.cfg
    (⟨none,none,inputStacks (GreedyFeasibleTable.printMatrix X)⟩ :
      OnlineTree.StoreCfg ExactTypedProgram.program))=_
  exact OnlineTree.cfg_packed ExactTypedProgram.program (GreedyFeasibleTable.printMatrix X) none

lemma output_none_live (as : List Symbol) : (output as none).state≠none := by
  change (some _ : Option ExactPhysicalProgram.program.State)≠none
  exact Option.some_ne_none _

end ContingencyTables.ExactGatePhysical

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPhysicalCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A physical cost bound for every finite prefix of the exact sampler -/

namespace ContingencyTables.ExactPhysicalCost
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms ProfilePrograms ExactPhysicalProgram

attribute [local irreducible] ExactTypedProgram.program

lemma typedBudget_le_scaled (as : List Symbol) (N B : ℕ) :
    typedBudget as N B≤typedBudget as 1 B*(N+1) := by
  have hc := Nat.mul_le_mul_left (typedBudget as 0 B) (show 1≤N+1 by omega)
  unfold typedBudget ExactCoreCost.budget at hc ⊢
  simp only [Nat.one_mul,Nat.zero_mul] at hc ⊢
  nlinarith

lemma factor_le_scaled (H K V : ℕ) (hV : 1≤V) :
    OnlineStack.Executes.factor ExactTypedProgram.program.code H (K*V)≤
      OnlineStack.Executes.factor ExactTypedProgram.program.code H K*V := by
  let A := OnlineStack.accesses ExactTypedProgram.program.code
  let O := OnlineStack.overhead ExactTypedProgram.program.code
  have hH : H+1≤(H+1)*V := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (H+1) hV
  have hinner : H+K*V*A+1≤(H+K*A+1)*V := by nlinarith
  have hA := Nat.mul_le_mul_left (2*A) hinner
  have hO : 1+2*A*(H+K*V*A+1)≤(1+2*A*(H+K*A+1))*V := by nlinarith
  have hfinal := Nat.mul_le_mul_left O hO
  change O*(1+2*A*(H+K*V*A+1))+1≤(O*(1+2*A*(H+K*A+1))+1)*V
  nlinarith

/-- One fixed coefficient bounds the compiler overhead for all prefix lengths. -/
lemma quadratic_budget (as : List Symbol) (N B : ℕ) :
    budget as N B≤budget as 1 B*(N+1)^2 := by
  have ht := typedBudget_le_scaled as N B
  have hf := OnlineStack.Executes.factor_mono (M := ExactTypedProgram.program.code)
    (weight as) (weight as) (typedBudget as N B) (typedBudget as 1 B*(N+1)) le_rfl ht
  have hs := factor_le_scaled (weight as) (typedBudget as 1 B) (N+1) (by omega)
  calc
    budget as N B≤(typedBudget as 1 B*(N+1))*
        (OnlineStack.Executes.factor ExactTypedProgram.program.code (weight as)
          (typedBudget as 1 B)*(N+1)) := Nat.mul_le_mul ht (hf.trans hs)
    _ = budget as 1 B*(N+1)^2 := by unfold budget; ring

end ContingencyTables.ExactPhysicalCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPrintCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform printing cost for every feasible exact-sampling output -/

namespace ContingencyTables.ExactPrintCost
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms SmallGraphProfiles Polynomial
open scoped BigOperators Classical
noncomputable section

lemma weight_ofFn {A : Type} [Codec A] {n B : ℕ} (f : Fin n → A)
    (h : ∀ i,weight (f i) ≤ B) : weight (List.ofFn f) ≤ n*(B+1)+1 := by
  have hb := weight_map_bound (f := f) (as := List.finRange n) (fun i _ => h i)
  simpa only [←List.ofFn_eq_map,List.length_finRange] using hb

lemma matrix_weight {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Table r c) :
    weight (matrixCode X.val) ≤ matrixSize (n := n) r := by
  have row (i : Fin m) : weight (List.ofFn (X.val i)) ≤ n*(4*weight (∑ i,r i)+2)+1 := by
    apply weight_ofFn
    intro j
    exact weight_nat_small (entry_le_total X.property i j)
  exact weight_ofFn (fun i => List.ofFn (X.val i)) row

/-- One fixed polynomial bounds both printing time and printed word length
uniformly over the feasible set. -/
theorem polynomial_print_bound : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Table r c),
      GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)+
        weight (GreedyFeasibleTable.printMatrix (matrixCode X.val)) ≤ p.eval (matrixSize (n := n) r) := by
  obtain ⟨p,hp⟩ := GreedyFeasibleTable.polynomial_printMatrix
  exact ⟨p,fun _ _ r c X => (hp _).trans
    (polynomial_eval_monotone p (matrix_weight r c X))⟩

end
end ContingencyTables.ExactPrintCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactTablePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite physical prefixes indexed by feasible tables -/

namespace ContingencyTables.ExactTablePrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open DensePrograms SmallGraphProfiles Turing
open scoped Classical BigOperators
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
attribute [local irreducible] ExactCoreProgram.prefixExperiment
  ExactPhysicalProgram.program ExactPhysicalProgram.output

lemma output_injective : Function.Injective (output r c) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some Y =>
      have he := congrArg Cfg.state h
      change (ExactPhysicalProgram.output (input r c) none).state=
        (ExactPhysicalProgram.output (input r c) (some (matrixCode Y.val))).state at he
      rw [ExactPhysicalProgram.output_some] at he
      exact False.elim (ExactPhysicalProgram.output_none_live _ he)
  | some X =>
    cases b with
    | none =>
      have he := congrArg Cfg.state h
      change (ExactPhysicalProgram.output (input r c) (some (matrixCode X.val))).state=
        (ExactPhysicalProgram.output (input r c) none).state at he
      rw [ExactPhysicalProgram.output_some] at he
      exact False.elim (ExactPhysicalProgram.output_none_live _ he.symm)
    | some Y =>
      apply congrArg some
      apply PackedMatrixInjective.table_injective X Y
      change ExactPhysicalProgram.output _ (some (matrixCode X.val))=
        ExactPhysicalProgram.output _ (some (matrixCode Y.val)) at h
      rw [ExactPhysicalProgram.output_some,ExactPhysicalProgram.output_some] at h
      simpa only [Program.final,Cfg.mk.injEq,true_and] using h

end
end ContingencyTables.ExactTablePrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed exact-sampling machine on the literal public binary tape -/

namespace ContingencyTables.ExactPublicPrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma output_halted (X : Table r c) : (output r c (some X)).state=none := rfl

end
end ContingencyTables.ExactPublicPrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cost-preserving literal wrapping of exact-sampling prefixes -/

namespace ContingencyTables.ExactPublicCost
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

theorem wrap_prefix (out : Option (Table r c) → Cfg Symbol ExactPhysicalProgram.program.State)
    (hinj : Function.Injective out)
    (hout : ∀ X,out (some X)=ExactPhysicalProgram.program.final
      (Tape.mk₁ (TreePost.packed (ExactPublicPrefix.word r c X))))
    (L : ℕ) (hL : ∀ X,(ExactPublicPrefix.word r c X).length≤L)
    (p : Experiment (Option (Table r c)))
    (hp : Implements ExactPhysicalProgram.program.table out
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) p) :
    ∃ q,Implements ExactPublicPrefix.program.table (output r c out)
      (ExactPublicPrefix.program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) q ∧
      (∀ g : Option (Table r c) → ℚ,q.mean g=p.mean g) ∧
      q.cost≤LiteralProgram.packTime (ExactTablePrefix.input r c).length+p.cost+LiteralProgram.postTime L := by
  obtain ⟨v,hv,hvm,hvc⟩ := PhysicalPartialSequence.left_prefix_injective
    ExactPhysicalProgram.program.table LiteralProgram.post.table LiteralProgram.post.entry out hinj _ p hp
  have next (o : Option (Table r c)) : ∃ u,
      Implements ExactPublicPrefix.middle.table (middleOutput r c out)
        (leftCfg LiteralProgram.post.entry (out o)) u ∧
      (∀ g : Option (Table r c) → ℚ,u.mean g=g o) ∧ u.cost≤LiteralProgram.postTime L := by
    cases o with
    | none => exact ⟨.done none,.done none,(fun _ => rfl),Nat.zero_le _⟩
    | some X =>
      obtain ⟨u,hu,hum,huc⟩ := LiteralProgram.post_realizes (ExactPublicPrefix.word r c X)
        (ProfilePrograms.printMatrix_alphabet _)
      have hu' := hu.right (M := ExactPhysicalProgram.program.table) LiteralProgram.post.entry
      have hall : u.All (fun T => T=Tape.mk₁ (ExactPublicPrefix.word r c X)) :=
        Experiment.all_of_mean_eq hum _ rfl
      refine ⟨u.map (fun _ => some X),?_,?_,?_⟩
      · have h := hu'.map_all (fun _ => some X) (middleOutput r c out)
          (hall.mono (by intro T hT; rw [hT]; rfl))
        rw [hout]
        simpa only [ExactPublicPrefix.middle,Program.seq,leftCfg,Program.final,Program.initial,
          Option.elim_none,rightCfg,Option.map_some] using h
      · intro g
        rw [Experiment.mean_map,PhysicalPartialSequence.mean_const]
      · rw [Experiment.cost_map]
        exact huc.trans (LiteralProgram.postTime_mono (hL X))
  choose u hu hum huc using next
  let w := v.bind u
  have hw : Implements ExactPublicPrefix.middle.table (middleOutput r c out)
      (ExactPublicPrefix.middle.initial (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) w :=
    hv.bind u _ hu
  have hwm (g : Option (Table r c) → ℚ) : w.mean g=p.mean g := by
    change (v.bind u).mean g=p.mean g
    rw [Experiment.mean_bind]
    simp_rw [hum]
    exact hvm g
  have hwc : w.cost≤p.cost+LiteralProgram.postTime L :=
    (Experiment.cost_bind_le v u _ huc).trans (Nat.add_le_add_right hvc _)
  have hi : ∀ a∈ExactTablePrefix.input r c,a≠0 :=
    GreedyFeasibleTable.encodeMargins_nonzero r c
  obtain ⟨a,ha,ham,hac⟩ := LiteralProgram.pack_realizes (ExactTablePrefix.input r c) hi
  obtain ⟨b,hb,hbm,hbc⟩ := PhysicalPartialSequence.left_prefix LiteralProgram.pack.table
    ExactPublicPrefix.middle.table ExactPublicPrefix.middle.entry LiteralProgram.pack.final _ a ha
  have hall : b.All (fun x => x=LiteralProgram.pack.final
      (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) := by
    rw [Experiment.all_indicator,hbm,ham]
    simp only [Experiment.mean,ite_true, if_true]
  have hw' := hw.right (M := LiteralProgram.pack.table) ExactPublicPrefix.middle.entry
  refine ⟨b.bind (fun _ => w),?_,?_,?_⟩
  · apply hb.bind_all (fun _ => w) (output r c out)
    exact hall.mono (by intro x hx; rw [hx]; exact hw')
  · intro g
    rw [Experiment.mean_bind,PhysicalPartialSequence.mean_const]
    exact hwm g
  · have h := Experiment.cost_bind_le b (fun _ => w) w.cost (fun _ => le_rfl)
    omega

theorem prefix_correct_cost (htotal : (∑ i,r i)=∑ j,c j) (N B L : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B)
    (hL : ∀ X : Table r c,(ExactPublicPrefix.word r c X).length≤L) :
    ∃ p,Implements ExactPublicPrefix.program.table (ExactPublicPrefix.output r c)
      (ExactPublicPrefix.program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) p ∧
      (∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g) ∧
      p.cost≤budget r c N B L := by
  obtain ⟨p,hp,hm,hc⟩ := table_prefix r c htotal N B hB
  have hout (X : Table r c) : ExactTablePrefix.output r c (some X)=
      ExactPhysicalProgram.program.final
        (Tape.mk₁ (TreePost.packed (ExactPublicPrefix.word r c X))) := by
    exact ExactPhysicalProgram.output_some _ _
  obtain ⟨q,hq,hqm,hqc⟩ := wrap_prefix r c (ExactTablePrefix.output r c)
    (ExactTablePrefix.output_injective r c) hout L hL p hp
  refine ⟨q,hq,(fun g => (hqm g).trans (hm g)),?_⟩
  exact hqc.trans (by unfold budget; omega)

lemma quadratic_budget (N B L : ℕ) :
    budget r c N B L≤budget r c 1 B L*(N+1)^2 := by
  have hp := ExactPhysicalCost.quadratic_budget (ExactTablePrefix.input r c) N B
  have hsq : 1≤(N+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hc := Nat.mul_le_mul_left (LiteralProgram.packTime (ExactTablePrefix.input r c).length+
    LiteralProgram.postTime L) hsq
  unfold budget
  nlinarith

end
end ContingencyTables.ExactPublicCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGatePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cheap gate prefix on public binary input -/

namespace ContingencyTables.ExactGatePublic
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms ProfilePrograms SmallGraphProfiles
open ExactTablePrefix (code decode input)
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

attribute [local irreducible] exactOrdinary

lemma output_injective : Function.Injective (output r c) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some Y =>
      have he := congrArg Cfg.state h
      change (ExactGatePhysical.output (input r c) none).state=
        (ExactGatePhysical.output (input r c) (some (matrixCode Y.val))).state at he
      rw [ExactGatePhysical.output_some] at he
      exact False.elim (ExactGatePhysical.output_none_live _ he)
  | some X =>
    cases b with
    | none =>
      have he := congrArg Cfg.state h
      change (ExactGatePhysical.output (input r c) (some (matrixCode X.val))).state=
        (ExactGatePhysical.output (input r c) none).state at he
      rw [ExactGatePhysical.output_some] at he
      exact False.elim (ExactGatePhysical.output_none_live _ he.symm)
    | some Y =>
      apply congrArg some
      apply PackedMatrixInjective.table_injective X Y
      change ExactGatePhysical.output _ (some (matrixCode X.val))=
        ExactGatePhysical.output _ (some (matrixCode Y.val)) at h
      rw [ExactGatePhysical.output_some,ExactGatePhysical.output_some] at h
      simpa only [Program.final,Cfg.mk.injEq,true_and] using h

lemma publicOutput_halted (X : Table r c) : (publicOutput r c (some X)).state=none := rfl

theorem prefix_correct_cost (htotal : (∑ i,r i)=∑ j,c j) (B L : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B)
    (hL : ∀ X : Table r c,(ExactPublicPrefix.word r c X).length≤L) :
    ∃ p,Implements ExactPublicPrefix.program.table (publicOutput r c)
      (ExactPublicPrefix.program.initial (Tape.mk₁ (input r c))) p ∧
      (∀ g : Option (Table r c) → ℚ,p.mean g=(experiment r c).mean g) ∧ p.cost≤budget r c B L := by
  obtain ⟨p,hp,hm,hc⟩ := table_prefix r c htotal B hB
  have hout (X : Table r c) : output r c (some X)=ExactPhysicalProgram.program.final
      (Tape.mk₁ (TreePost.packed (ExactPublicPrefix.word r c X))) := ExactGatePhysical.output_some _ _
  obtain ⟨q,hq,hqm,hqc⟩ := ExactPublicCost.wrap_prefix r c (output r c)
    (output_injective r c) hout L hL p hp
  refine ⟨q,hq,(fun g => (hqm g).trans (hm g)),?_⟩
  exact hqc.trans (by unfold budget; omega)

end
end ContingencyTables.ExactGatePublic

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalEventBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal-event bounds from finite stopping prefixes -/

namespace ContingencyTables.PhysicalEventBounds
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open scoped BigOperators Classical
noncomputable section
variable {Γ Q A : Type} [Inhabited Γ]

lemma mean_mono (p : Experiment A) (f g : A → ℚ) (h : ∀ a,f a≤g a) :
    p.mean f≤p.mean g := by
  induction p with
  | done a => exact h a
  | read p ih => simp only [Experiment.mean]; linarith [ih false,ih true]
  | delay n p ih => exact ih

lemma mean_one_sub (p : Experiment A) (f : A → ℚ) :
    p.mean (fun a => 1-f a)=1-p.mean f := by
  induction p with
  | done a => rfl
  | read p ih => simp only [Experiment.mean,ih]; ring
  | delay n p ih => exact ih

lemma run_halted_iff (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).state=none ↔
      (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=none := by
  let : Inhabited {q //q∈P.states} := ⟨⟨P.entry,P.entry_mem⟩⟩
  have he := congrArg Cfg.state (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))
  rw [Program.machine,restrictedMachine_run]
  change ((execute (restrict P.table P.states P.supported) n
    ⟨some default,Tape.mk₁ input⟩ (extend b)).state.map enumeration)=none ↔ _
  change (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=_ at he
  rw [he]
  simp only [liftCfg,Option.map_eq_none_iff]

end
end ContingencyTables.PhysicalEventBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPublicLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public probabilities and physical terminal events -/

namespace ContingencyTables.PhysicalPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds
open scoped BigOperators Classical
noncomputable section

lemma haltMass_eq (P : Program) (input : List Symbol) (t : ℕ) :
    Algorithms.haltMass P.machine input t=
      ((experiment P.table t (P.initial (Tape.mk₁ input))).mean
        (event (fun d => d.state=none)):ℝ) := by
  have hm := physical_law P.table t (P.initial (Tape.mk₁ input))
    (event (fun d => d.state=none))
  have ha : average (fun b : Bits t => event (fun d => d.state=none)
      (execute P.table t (P.initial (Tape.mk₁ input)) (extend b)))=
      ((Finset.univ.filter fun b : Bits t => (MatchingFPRAS.run P.machine input b).state=none).card:ℚ)/
        (2:ℚ)^t := by
    simp only [average,event,←run_halted_iff,Finset.sum_boole]
  rw [ha] at hm
  have hc := congrArg (fun x : ℚ => (x:ℝ)) hm
  simpa only [Algorithms.haltMass,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using hc

lemma tail_eq (P : Program) (input : List Symbol) (t : ℕ) :
    1-Algorithms.haltMass P.machine input t=
      PhysicalRetryTail.tail P.table (P.initial (Tape.mk₁ input)) t := by
  rw [haltMass_eq]
  have he : event (fun d : Cfg Symbol P.State => d.state=none)=
      fun d => 1-PhysicalRetryTail.live d := by
    funext d
    unfold event PhysicalRetryTail.live
    split_ifs <;> norm_num
  rw [he,mean_one_sub]
  simp only [Rat.cast_sub,Rat.cast_one,PhysicalRetryTail.tail]
  ring

end
end ContingencyTables.PhysicalPublicLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactExpectedTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summability of the actual exact sampler's public runtime -/

namespace ContingencyTables.ExactExpectedTime
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms SmallGraphProfiles PhysicalRetryTail
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "dim" => CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)

attribute [local irreducible] ExactPublicPrefix.program ExactTablePrefix.experiment
  PublishedInputs.FiniteBoxPrekopaLeindler PublishedInputs.FiniteCheeger

/-- Expected runtime is bounded by the explicit costs of the ordinary
prefix and the probability-weighted correction branch. -/
theorem bound
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*k^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (B L : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B)
    (hL : ∀ X : Table r c,(ExactPublicPrefix.word r c X).length≤L) :
    let S := ExactGatePublic.budget r c B L
    let T := ExactPublicCost.budget r c 1 B L+1
    let tail := PhysicalRetryTail.tail ExactPublicPrefix.program.table
      (ExactPublicPrefix.program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))
    Summable tail ∧ (∑' t,tail t)≤(S:ℝ)+11*(1/(2:ℝ)^correctionPrecision r c)*T := by
  dsimp only
  let S := ExactGatePublic.budget r c B L
  let T := ExactPublicCost.budget r c 1 B L+1
  let M := ExactPublicPrefix.program.table
  let init := ExactPublicPrefix.program.initial (Tape.mk₁ (Algorithms.encodeMargins r c))
  refine QuadraticPrefixRuntime.expected_time (PhysicalRetryTail.tail M init) S T
    (Nat.zero_lt_succ _) (1/(2:ℝ)^correctionPrecision r c) (by positivity)
    (tail_nonnegative M init) ?_ (tail_antitone M init) ?_ ?_
  · intro t
    have h := PhysicalEventBounds.mean_mono (experiment M t init) live (fun _ => 1) live_le_one
    rw [PhysicalPartialSequence.mean_const] at h
    unfold PhysicalRetryTail.tail
    exact_mod_cast h
  · obtain ⟨p,hp,hm,hc⟩ := ExactGatePublic.prefix_correct_cost r c htotal B L hB hL
    have h := tail_le_failure M (ExactGatePublic.publicOutput r c) init p hp
      (ExactGatePublic.publicOutput_halted r c) S hc
    rw [hm,ExactGatePublic.failure r c htotal] at h
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using h
  · intro N
    obtain ⟨p,hp,hm,hc⟩ := ExactPublicCost.prefix_correct_cost r c htotal N B L hB hL
    have hcost : p.cost≤S+T*(N+1)^2 := by
      have hq := ExactPublicCost.quadratic_budget r c N B L
      have ht := Nat.mul_le_mul_right ((N+1)^2)
        (Nat.le_succ (ExactPublicCost.budget r c 1 B L))
      exact (hc.trans (hq.trans ht)).trans (Nat.le_add_left _ _)
    have h := tail_le_failure M (ExactPublicPrefix.output r c) init p hp
      (ExactPublicPrefix.output_halted r c) _ hcost
    rw [hm] at h
    have hf := ExactTablePrefix.failure_bound r c (hPL _) (hCheeger _ dim) htotal N
    have hfr := (Rat.cast_le (K := ℝ)).mpr hf
    exact h.trans (by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hfr)

/-- The physical tail is summable for every equal-total margin pair. -/
theorem summable
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*k^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    Summable (fun t => 1-Algorithms.haltMass ExactPublicPrefix.machine (Algorithms.encodeMargins r c) t) := by
  obtain ⟨p,hp⟩ := ExactPrintCost.polynomial_print_bound
  let B := p.eval (ExactPrintCost.matrixSize (n := n) r)
  have hB (X : Table r c) : GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B :=
    (Nat.le_add_right _ _).trans (hp m n r c X)
  have hL (X : Table r c) : (ExactPublicPrefix.word r c X).length≤B :=
    (MatchingFPRAS.TreeTyped.list_length_le_weight _).trans
      ((Nat.le_add_left _ _).trans (hp m n r c X))
  have hs := (bound r c hPL hCheeger htotal B B hB hL).1
  have he : (fun t => 1-Algorithms.haltMass ExactPublicPrefix.machine (Algorithms.encodeMargins r c) t)=
      PhysicalRetryTail.tail ExactPublicPrefix.program.table
        (ExactPublicPrefix.program.initial (Tape.mk₁ (Algorithms.encodeMargins r c))) := by
    funext t
    exact PhysicalPublicLaw.tail_eq _ _ _
  rw [he]
  exact hs

end
end ContingencyTables.ExactExpectedTime

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactSamplingMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact public sampler in uniform expected polynomial bit time -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream Turing
open ProfilePrograms DensePrograms Polynomial Algorithms
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] ExactPublicPrefix.program

theorem exact_expected_polynomial : ∃ p : Polynomial ℕ,
    ∀ (_hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
      (_hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*k^8))),
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    (∑' (t : ℕ), (1 - haltMass ExactPublicPrefix.machine (encodeMargins r c) t)) ≤
      ((p.eval (samplingSize n r 0) : ℕ) : ℝ) := by
  obtain ⟨print,hprint⟩ := ExactPrintCost.polynomial_print_bound
  obtain ⟨p,hp⟩ := ExactGatePolynomial.public_bound print
  obtain ⟨q,hq⟩ := exact_public_correction_bound print
  refine ⟨p+11*q,?_⟩
  intro hPL hCheeger m n r c htotal
  let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
  let S := ExactGatePublic.budget r c B B
  let T := ExactPublicCost.budget r c 1 B B+1
  let den : ℝ := (2:ℝ)^correctionPrecision r c
  have hB (X : Table r c) : GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val) ≤ B :=
    (Nat.le_add_right _ _).trans (hprint m n r c X)
  have hL (X : Table r c) : (ExactPublicPrefix.word r c X).length ≤ B :=
    (list_length_le_weight _).trans ((Nat.le_add_left _ _).trans (hprint m n r c X))
  have htail := (ExactExpectedTime.bound r c hPL hCheeger htotal B B hB hL).2
  have hgate : (S:ℝ) ≤ ((p.eval (samplingSize n r 0):ℕ):ℝ) := by exact_mod_cast hp m n r c htotal
  have hT : (T:ℝ) ≤ den*((q.eval (samplingSize n r 0):ℕ):ℝ) := by
    have hn : T ≤ 2^(correctionPrecision r c)*q.eval (samplingSize n r 0) := hq m n r c htotal
    have ht : (T:ℝ) ≤ ((2^(correctionPrecision r c)*q.eval (samplingSize n r 0):ℕ):ℝ) := by
      exact_mod_cast hn
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,den] using ht
  have hrare : (1/den)*T ≤ ((q.eval (samplingSize n r 0):ℕ):ℝ) := by
    have hden : 0 < den := by unfold den; positivity
    have ht : (T:ℝ)/den ≤ ((q.eval (samplingSize n r 0):ℕ):ℝ) :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hT)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using ht
  have he : (fun t => 1-haltMass ExactPublicPrefix.machine (encodeMargins r c) t)=
      PhysicalRetryTail.tail ExactPublicPrefix.program.table
        (ExactPublicPrefix.program.initial (Tape.mk₁ (encodeMargins r c))) := by
    funext t
    exact PhysicalPublicLaw.tail_eq _ _ _
  rw [←he] at htail
  change _ ≤ (S:ℝ)+11*(1/den)*T at htail
  simp only [eval_add,eval_mul,eval_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith

/-- Paper 200-01, main theorem (ii), conditional on the cited finite-box
Prékopa--Leindler and finite-grid Cheeger inputs. The machine is fixed,
including parsing, printing, and the unbiased-bit implementation. -/
theorem exactSampling_conditional
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*k^8))) :
    ExactSamplingStatement := by
  obtain ⟨p,hp⟩ := exact_expected_polynomial
  refine ⟨ExactPublicPrefix.machine,p.eval 1+1,p.natDegree,by omega,?_⟩
  intro m n r c htotal
  dsimp only
  refine ⟨ExactPublicLaw.halted_feasible r c hPL hCheeger htotal,
    ExactPublicLaw.tableMass_limit r c hPL hCheeger htotal,
    ExactPublicLaw.haltMass_limit r c hPL hCheeger htotal,
    ExactExpectedTime.summable r c hPL hCheeger htotal,?_⟩
  have hS : 1 ≤ samplingSize n r 0 := by unfold samplingSize; omega
  have hpoly : p.eval (samplingSize n r 0) ≤ p.eval 1*(samplingSize n r 0)^p.natDegree := by
    simpa only [one_mul,pow_one] using polynomial_scaled_power p 1 (samplingSize n r 0) 1 hS
  have hnat := hpoly.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  have hreal : ((p.eval (samplingSize n r 0):ℕ):ℝ) ≤
      (p.eval 1+1:ℕ)*(samplingSize n r 0:ℝ)^p.natDegree := by exact_mod_cast hnat
  exact (hp hPL hCheeger m n r c htotal).trans hreal

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampling and counting contingency tables with arbitrary margins

The finite-box Prékopa–Leindler inequality, finite Cheeger inequality
and Edmonds–Karp bound yield sampling and counting algorithms with
uniform polynomial bit-cost guarantees.
-/
namespace ContingencyTables

/-- Paper 200-01: exact uniform sampling in expected polynomial bit time. -/
theorem exactSampling_oai : Algorithms.ExactSamplingStatement :=
  SmallGraphProfiles.exactSampling_conditional
    PublishedInputs.finiteBoxPrekopaLeindler (fun _ _ => CheegerProof.finiteCheeger)

end ContingencyTables

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.exactSampling_oai := @OAI.ContingencyTables.exactSampling_oai
